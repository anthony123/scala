/* NSC -- new Scala compiler
 * Copyright 2005-2011 LAMP/EPFL
 * @author  Martin Odersky
 */


package scala.tools.nsc
package backend
package jvm

import scala.collection.{ mutable, immutable }
import scala.tools.nsc.symtab._
import scala.annotation.switch
import scala.tools.asm

/**
 *  Prepare in-memory representations of classfiles using the ASM Tree API, and serialize them to disk.
 *
 *  Three pipelines are at work, each taking work items from a queue dedicated to that pipeline:
 *
 *  (There's another pipeline so to speak, the one that populates queue-1 by traversing a CompilationUnit until ClassDefs are found,
 *   but the "interesting" pipelines are the ones described below)
 *
 *    (1) In the first queue, an item consists of a ClassDef along with its arrival position.
 *        This position is needed at the time classfiles are serialized to disk,
 *        so as to emit classfiles in the same order CleanUp handed them over.
 *        As a result, two runs of the compiler on the same files produce jars that are identical on a byte basis.
 *        See `ant test.stability`
 *
 *    (2) The second queue contains items where a ClassDef has been lowered into:
 *          (a) an optional mirror class,
 *          (b) a half-baked plain class, and
 *          (c) an optional bean class.
 *
 *        Both the mirror and the bean classes (if any) are ready to be written to disk,
 *        but that has to wait until the plain class is turned into an ASM Tree.
 *
 *        Pipeline 1
 *        ----------
 *
 *        The processing that takes place between queues 1 and 2 relies on typer, and thus has to be performed by a single thread.
 *        The thread in question is different from the main thread, for reasons that will become apparent below.
 *        As long as all operations on typer are carried out under a single thread (not necessarily the main thread), everything is fine.
 *
 *        Rather than performing all the work involved in lowering a ClassDef,
 *        pipeline-1 leaves in general for later those operations that don't require typer.
 *        All the @can-multi-thread operations that pipeline-2 performs can also run during pipeline-1, in fact some of them do.
 *        In contrast, typer operations can't be performed by pipeline-2.
 *        pipeline-2 consists of MAX_THREADS worker threads running concurrently.
 *
 *        Pipeline 2
 *        ----------
 *
 *        The operations that a worker thread of pipeline-2 can perform are those that rely only on the following abstractions:
 *          - BType:     a typer-independent representation of a JVM-level type,
 *          - Tracked:   a bundle of a BType B, its superclass (as a BType), and B's interfaces (as BTypes).
 *          - exemplars: a concurrent map to obtain the Tracked structure using internal class names as keys.
 *          - the tree-based representation of classfiles provided by the ASM Tree API.
 *        For example:
 *          - it's possible to determine whether a BType conforms to another without resorting to typer.
 *          - `CClassWriter.getCommonSuperclass()` is thread-reentrant (therefore, it accesses only thread-reentrant functionality).
 *             This comes handy because in pipelin-2, `MethodNode.visitMaxs()` invokes `getCommonSuperclass()` on different method nodes,
 *             and each of these activations accesses typer-independent structures (exemplars, Tracked) to compute its answer.
 *
 *        In the future, a pipeline-2 worker could also perform intra-method optimizations on the ASM tree
 *        before handing it over to queue-3, including:
 *          - collapsing jump-chains,
 *          - constant propagation,
 *          - arith and logical ops reductions,
 *          - pattern-based simplification aka peephole optimization,
 *          - eliminating unreachable-code, and
 *          - removing unused locals.
 *        See Ch. 8. "Method Analysis" in the ASM User Guide, http://download.forge.objectweb.org/asm/asm4-guide.pdf
 *
 *    (3) The third queue contains items ready for serialization.
 *        It's a priority queue that follows the original arrival order,
 *        so as to emit identical jars on repeated compilation of the same sources.
 *
 *        Pipeline 3
 *        ----------
 *
 *        This pipeline consist of just the main thread, which is the thread that some tools (including the Eclipse IDE)
 *        expect to be the sole performer of file-system modifications.
 *
 * ---------------------------------------------------------------------------------------------------------------------
 *
 *    Summing up, the key facts about this phase are:
 *
 *      (i) Three pipelines run in parallel, thus allowing finishing earlier.
 *
 *     (ii) Pipelines 1 and 3 are sequential.
 *          In contrast, pipeline-2 uses task-parallelism (where each of the N workers is limited to invoking ASM and BType operations).
 *
 *          All three queues are concurrent:
 *
 *    (iii) Queue-1 connects a single producer (BCodePhase) to a single consumer (Worker-1),
 *          but given they run on different threads, queue-1 has to be concurrent.
 *
 *     (iv) Queue-2 is concurrent because concurrent workers of pipeline-2 take items from it.
 *
 *      (v) Queue-3 is concurrent (it's in fact a priority queue) because those same concurrent workers add items to it.
 *
 *
 *
 *  @author  Miguel Garcia, http://lamp.epfl.ch/~magarcia/ScalaCompilerCornerReloaded/
 *  @version 1.0
 *
 */
abstract class GenBCode extends BCodeTypes {
  import global._
  import icodes._
  import icodes.opcodes._
  import definitions._

  val phaseName = "jvm"

  override def newPhase(prev: Phase) = new BCodePhase(prev)

  class BCodePhase(prev: Phase) extends StdPhase(prev) {

    override def name = phaseName
    override def description = "Generate bytecode from ASTs"
    override def erasedTypes = true

    // Once pipeline-2 starts doing optimizations more threads will be needed.
    val MAX_THREADS = scala.math.min(
      2,
      java.lang.Runtime.getRuntime.availableProcessors
    )

    private val woStarted = new java.util.concurrent.ConcurrentHashMap[Long, Long]  // debug
    private val woExited  = new java.util.concurrent.ConcurrentHashMap[Long, Item2] // debug

    private var bytecodeWriter  : BytecodeWriter   = null
    private var mirrorCodeGen   : JMirrorBuilder   = null
    private var beanInfoCodeGen : JBeanInfoBuilder = null

    // q1
    case class Item1(arrivalPos: Int, cd: ClassDef, cunit: CompilationUnit) {
      def isPoison = { arrivalPos == Int.MaxValue }
    }
    private val poison1 = Item1(Int.MaxValue, null, null)
    private val q1 = new _root_.java.util.concurrent.LinkedBlockingQueue[Item1]

    // q2
    case class Item2(arrivalPos: Int, mirror: SubItem2NonPlain, plain: SubItem2Plain, bean: SubItem2NonPlain) {
      def isPoison = { arrivalPos == Int.MaxValue }
    }
    private val poison2 = Item2(Int.MaxValue, null, null, null)
    private val q2 = new _root_.java.util.concurrent.LinkedBlockingQueue[Item2]

    // q3
    case class Item3(arrivalPos: Int, mirror: SubItem3, plain: SubItem3, bean: SubItem3) {
      def isPoison = { arrivalPos == Int.MaxValue }
    }
    private val i3comparator = new _root_.java.util.Comparator[Item3] {
      override def compare(a: Item3, b: Item3) = {
        if(a.arrivalPos < b.arrivalPos) -1
        else if(a.arrivalPos == b.arrivalPos) 0
        else 1
      }
    }
    private val poison3 = Item3(Int.MaxValue, null, null, null)
    private val q3 = new _root_.java.util.concurrent.PriorityBlockingQueue[Item3](1000, i3comparator)

    /**
     *  Pipeline that takes ClassDefs from queue-1, lowers them into an intermediate form, placing them on queue-2
     *
     *  @must-single-thread (because it relies on typer).
     */
    class Worker1(needsOutfileForSymbol: Boolean) extends _root_.java.lang.Runnable {

      def run() {
        while (true) {
          val item = q1.take
          if(item.isPoison) {
            for(i <- 1 to MAX_THREADS) { q2 put poison2 } // explanation in Worker2.run() as to why MAX_THREADS poison pills are needed on queue-2.
            return
          }
          else { visit(item) }
        }
      }

      def visit(item: Item1) {
        val Item1(arrivalPos, cd, cunit) = item
        val claszSymbol = cd.symbol

        // -------------- mirror class, if needed --------------
        var mirrorC: SubItem2NonPlain = null
        if (isStaticModule(claszSymbol) && isTopLevelModule(claszSymbol)) {
          if (claszSymbol.companionClass == NoSymbol) {
            mirrorC = mirrorCodeGen.genMirrorClass(claszSymbol, cunit)
          } else {
            log("No mirror class for module with linked class: " + claszSymbol.fullName)
          }
        }

        // -------------- "plain" class --------------
        val pcb = new PlainClassBuilder(cunit)
        pcb.genPlainClass(cd)
        val plainC: SubItem2Plain = {
          val label = "" + cd.symbol.name
          val outF: _root_.scala.tools.nsc.io.AbstractFile = {
            if(needsOutfileForSymbol) getFile(cd.symbol, pcb.thisName, ".class") else null
          }
          SubItem2Plain(label, pcb.thisName, pcb.cnode, outF)
        }

        // -------------- bean info class, if needed --------------
        var beanC: SubItem2NonPlain = null
        if (claszSymbol hasAnnotation BeanInfoAttr) {
          beanC =
            beanInfoCodeGen.genBeanInfoClass(
              claszSymbol, cunit,
              fieldSymbols(claszSymbol),
              methodSymbols(cd)
            )
        }

        q2 put Item2(arrivalPos, mirrorC, plainC, beanC)
      }

    }

    /**
     *  Pipeline that takes items from queue-2, lowers them into byte array classfiles, placing them on queue-3
     *
     *  @can-multi-thread
     */
    class Worker2 extends _root_.java.lang.Runnable {

      def run() {
        val id = java.lang.Thread.currentThread.getId
        woStarted.put(id, id)

        while (true) {
          val item = q2.take
          if(item.isPoison) {
            woExited.put(id, item)
            q3 put poison3 // therefore queue-3 will contain as many poison pills as worker threads in pipeline-2
            return // in order to terminate all workers, queue-1 must contain as many poison pills as worker threads in pipeline-2
          }
          else {
            visit(item)
          }
        }
      }

      def visit(item: Item2) {
        val Item2(arrivalPos, mirror, plain, bean) = item

        // -------------- mirror class, if needed --------------
        val mirrorC: SubItem3 =
          if (mirror != null) {
            SubItem3(mirror.label, mirror.jclassName, mirror.jclass.toByteArray(), mirror.outF)
          } else null;

        // -------------- "plain" class --------------
        val cw = new CClassWriter(extraProc)
        plain.cnode.accept(cw)
        val plainC =
          SubItem3(plain.label, plain.jclassName, cw.toByteArray, plain.outF)

        // -------------- bean info class, if needed --------------
        val beanC: SubItem3 =
          if (bean != null) {
            SubItem3(bean.label, bean.jclassName, bean.jclass.toByteArray(), bean.outF)
          } else null;

        q3 put Item3(arrivalPos, mirrorC, plainC, beanC)
      }

    }

    var arrivalPos = 0

    override def run() {
      arrivalPos = 0 // just in case
      scalaPrimitives.init
      initBCodeTypes()
      // initBytecodeWriter invokes fullName, thus we have to run it before the typer-dependent thread is activated.
      bytecodeWriter  = initBytecodeWriter(cleanup.getEntryPoints)
      val needsOutfileForSymbol = bytecodeWriter.isInstanceOf[ClassBytecodeWriter]
      mirrorCodeGen   = new JMirrorBuilder(  needsOutfileForSymbol)
      beanInfoCodeGen = new JBeanInfoBuilder(needsOutfileForSymbol)
      // -----------------------
      // Pipeline from q1 to q2.
      // -----------------------
      new _root_.java.lang.Thread(new Worker1(needsOutfileForSymbol)).start()
      // -----------------------
      // Pipeline from q2 to q3.
      // -----------------------
      val workers = for(i <- 1 to MAX_THREADS) yield { val w = new Worker2; val t = new _root_.java.lang.Thread(w); t.start(); t }
      // -------------------------------------------------------------------
      // Feed pipeline-1: place all ClassDefs on q1, recording their arrival position.
      // -------------------------------------------------------------------
      super.run()
      q1 put poison1
      // -------------------------------------------------------
      // Pipeline that writes classfile representations to disk.
      // -------------------------------------------------------
      drainQ3()
      // we're done
      assert(q1.isEmpty, "Some ClassDefs remained in the first queue: "   + q1.toString)
      assert(q2.isEmpty, "Some classfiles remained in the second queue: " + q2.toString)
      assert(q3.isEmpty, "Some classfiles weren't written to disk: "      + q3.toString)
      // assert(exec.isTerminated, "Some workers just keep working.")

      for(t <- workers) { assert(woExited.containsKey(t.getId)) } // debug
      assert(woExited.size == MAX_THREADS)                        // debug

      // clearing maps, closing output files.
      bytecodeWriter.close()
      clearBCodeTypes()
    }

    private def drainQ3() {

          def sendToDisk(cfr: SubItem3) {
            if(cfr != null){
              val SubItem3(label, jclassName, jclassBytes, outF) = cfr
              bytecodeWriter.writeClass(label, jclassName, jclassBytes, outF)
            }
          }

      var moreComing = true
      var remainingWorkers = MAX_THREADS
      // `expected` denotes the arrivalPos whose Item3 should be serialized next
      var expected = 0
      // `followers` contains items that arrived too soon, they're parked waiting for `expected` to be polled from queue-3
      val followers = new java.util.PriorityQueue[Item3](100, i3comparator)

      while (moreComing) {
        val incoming = q3.take
        if(incoming.isPoison) {
          remainingWorkers -= 1
          moreComing = (remainingWorkers != 0)
        } else {
          followers.add(incoming)
        }
        assert(
          if(!moreComing) { q3.isEmpty && followers.isEmpty } else true,
          "These queues can be tricky sometimes."
        )
        while(!followers.isEmpty && followers.peek.arrivalPos == expected) {
          val item = followers.poll
          sendToDisk(item.mirror)
          sendToDisk(item.plain); assert(item.plain != null, "One plain class per Item3, that's the rule.")
          sendToDisk(item.bean)
          expected += 1
        }
      }
    }

    /**
     *  Apply BCode phase to a compilation unit: enqueue each contained ClassDef in queue-1,
     *  so as to release the main thread for a duty it cannot delegate: writing classfiles to disk.
     *  See `drainQ3()`
     */
    override def apply(cunit: CompilationUnit): Unit = {

          def gen(tree: Tree) {
            tree match {
              case EmptyTree            => ()
              case PackageDef(_, stats) => stats foreach gen
              case cd: ClassDef         =>
                q1 put Item1(arrivalPos, cd, cunit)
                arrivalPos += 1
            }
          }

      gen(cunit.body)
    }

    final class PlainClassBuilder(cunit: CompilationUnit)
      extends BCInitGen
      with    BCJGenSigGen {

      // current class
      var cnode: asm.tree.ClassNode  = null
      var thisName: String           = null // the internal name of the class being emitted
      private var claszSymbol: Symbol        = null
      private var isParcelableClass          = false
      // current method
      private var mnode: asm.tree.MethodNode = null
      private var jMethodName: String        = null
      private var isModuleInitialized        = false // in GenASM this is local to genCode(), ie should get false whenever a new method is emitted (including fabricated ones eg addStaticInit())
      private var methSymbol: Symbol         = null
      // used by genLoadTry() and genSynchronized()
      private var earlyReturnVar: Symbol     = null
      private var shouldEmitCleanup          = false
      // used in connection with cleanups
      private var returnType: BType          = null
      // line numbers
      private var lastEmittedLineNr          = -1

      /**
       *  A jump node is represented as an Apply whose symbol denotes a LabelDef, the jump target.
       *  The `locLabel` map is used to find the asm.Label to use as destination (upon visiting a jump),
       *  and to associate an asm.Label with a LabelDef (upon visiting a jump destination).
       */
      private var locLabel: immutable.Map[ /* LabelDef */ Symbol, asm.Label ] = null
      def programPoint(labelSym: Symbol): asm.Label = {
        assert(labelSym.isLabel, "trying to map a non-label symbol to an asm.Label, at: " + labelSym.pos)
        locLabel.getOrElse(labelSym, {
          val pp = new asm.Label
          locLabel += (labelSym -> pp)
          pp
        })
      }

      /**
       *  A program point may be lexically nested (at some depth)
       *    (a) in the try-clause of a try-with-finally expression
       *    (b) in a synchronized block.
       *  Each of the constructs above establishes a "cleanup block" to execute upon
       *  both normal-exit and abrupt-termination of the instructions it encloses.
       *
       *  The `cleanups` LIFO queue represents the nesting of active (for the current program point)
       *  pending cleanups. For each such cleanup an asm.Label indicating the start of its cleanup-block.
       *  At any given time during traversal of the method body,
       *  the head of `cleanups` indicates the closest enclosing try-with-finally or synchronized-expression.
       *
       *  `cleanups` is used:
       *
       *    (1) upon visiting a Return statement.
       *        In case of pending cleanups, we can't just emit a RETURN instruction, but must instead:
       *          - store the result (if any) in `earlyReturnVar`, and
       *          - jump to the next pending cleanup.
       *        See `genReturn()`
       *
       *    (2) upon emitting a try-with-finally or a synchronized-expr,
       *        In these cases, the targets of the above jumps are emitted,
       *        provided an early exit was actually encountered somewhere in the protected clauses.
       *        See `genLoadTry()` and `genSynchronized()`
       *
       *  The code thus emitted for jumps and targets covers the early-return case.
       *  The case of abrupt, exceptional, termination is covered by exception handlers
       *  emitted for that purpose as described in `genLoadTry()` and `genSynchronized()`.
       */
      var cleanups: List[asm.Label] = Nil
      def registerCleanup(finCleanup: asm.Label) {
        if(finCleanup != null) { cleanups = finCleanup :: cleanups }
      }
      def unregisterCleanup(finCleanup: asm.Label) {
        if(finCleanup != null) {
          assert(cleanups.head eq finCleanup,
                 "Bad nesting of cleanup operations: " + cleanups + " trying to unregister: " + finCleanup)
          cleanups = cleanups.tail
        }
      }

      // bookkeeping for method-local vars and method-params
      private val locals = mutable.Map.empty[Symbol, Local] // (local-or-param-sym -> Local(TypeKind, name, idx))
      private var nxtIdx = -1 // next available index for local-var
      /** Make a fresh local variable, ensuring a unique name.
       *  The invoker must make sure inner classes are tracked for the sym's tpe. */
      def makeLocal(tk: BType, name: String): Symbol = {
        val sym = methSymbol.newVariable(cunit.freshTermName(name), NoPosition, Flags.SYNTHETIC) // setInfo tpe
        makeLocal(sym, tk)
        sym
      }
      def makeLocal(sym: Symbol, tk: BType): Local = {
        assert(!locals.contains(sym), "attempt to create duplicate local var.")
        assert(nxtIdx != -1, "not a valid start index")
        val loc = Local(tk, sym.javaSimpleName.toString, nxtIdx, sym.isSynthetic)
        locals += (sym -> loc)
        assert(tk.getSize > 0, "makeLocal called for a symbol whose type is Unit.")
        nxtIdx += tk.getSize
        loc
      }
      // don't confuse with `fieldStore` and `fieldLoad` which also take a symbol but a field-symbol.
      def store(locSym: Symbol) {
        val Local(tk, _, idx, _) = locals(locSym)
        bc.store(idx, tk)
      }
      def load(locSym: Symbol) {
        val Local(tk, _, idx, _) = locals(locSym)
        bc.load(idx, tk)
      }

      /**
       *  The semantics of try-with-finally and synchronized-expr require their cleanup code
       *  to be present in three forms in the emitted bytecode:
       *    (a) as normal-exit code, reached via fall-through from the last program point being protected,
       *    (b) the early-return case, described under `cleanups` above.
       *        The only difference between (a) and (b) is their next program-point:
       *          the former must continue with fall-through while
       *          the later must continue to the next early-return cleanup.
       *        Otherwise they are identical.
       *    (c) as exception-handler, reached via exceptional control flow.
       *
       *  The cleanup code may in general contain LabelDefs.
       *  As a result, when emitting duplicate code for the same cleanup AST, a distinction has to be made
       *  as to the jump-targets:
       *    (1) a jump emitted as part of the (a) version of a cleanup AST must target the (a) version of the LabelDef,
       *    (2) similary for (b) and for (c).
       *
       *  The two maps below provide the required bookkeeping:
       *    - `labelDefsAtOrUnder` lists all LabelDefs enclosed by a given Tree node (the key)
       *    - `labelDef` provides the LabelDef whose symbol is used as key.
       *
       *  Further details in `emitFinalizer()`, which is invoked from `genLoadTry()` and `genSynchronized()`.
       */
      var labelDefsAtOrUnder: collection.Map[Tree, List[LabelDef]] = null
      var labelDef: collection.Map[Symbol, LabelDef] = null// (LabelDef-sym -> LabelDef)

      // bookkeeping the scopes of non-synthetic local vars, to emit debug info (`emitVars`).
      var varsInScope: List[Pair[Symbol, asm.Label]] = null // (local-var-sym -> start-of-scope)

      // helpers around program-points.
      def lastInsn: asm.tree.AbstractInsnNode = {
        mnode.instructions.getLast
      }
      def currProgramPoint(): asm.Label = {
        lastInsn match {
          case labnode: asm.tree.LabelNode => labnode.getLabel
          case _ =>
            val pp = new asm.Label
            mnode visitLabel pp
            pp
        }
      }
      def markProgramPoint(lbl: asm.Label) {
        val skip = (lbl == null) || isAtProgramPoint(lbl)
        if(!skip) { mnode visitLabel lbl }
      }
      def isAtProgramPoint(lbl: asm.Label): Boolean = {
        (lastInsn match { case labnode: asm.tree.LabelNode => (labnode.getLabel == lbl); case _ => false } )
      }
      def lineNumber(tree: Tree) {
        if(!tree.pos.isDefined) return;
        val nr = tree.pos.line
        if(nr != lastEmittedLineNr) {
          lastEmittedLineNr = nr
          lastInsn match {
            case lnn: asm.tree.LineNumberNode =>
              if(lnn.line != nr) {
                // "overwrite" previous landmark as no instructions have been emitted for it
                mnode.instructions.remove(lnn)
                mnode.visitLineNumber(nr, currProgramPoint())
              } // otherwise do nothing.
            case _ =>
              mnode.visitLineNumber(nr, currProgramPoint())
          }
        }
      }

      def paramTKs(app: Apply): List[BType] = {
        val Apply(fun, _)  = app
        fun.symbol.info.paramTypes map toTypeKind
      }

      // on entering a method
      private def resetMethodBookkeeping(dd: DefDef) {
        locals.clear()
        locLabel = immutable.Map.empty[ /* LabelDef */ Symbol, asm.Label ]
        // populate labelDefsAtOrUnder
        val ldf = new LabelDefsFinder
        ldf.traverse(dd.rhs)
        labelDefsAtOrUnder = ldf.result.withDefaultValue(Nil)
        labelDef = labelDefsAtOrUnder(dd.rhs).map(ld => (ld.symbol -> ld)).toMap
        // check previous invocation of genDefDef exited as many varsInScope as it entered.
        assert(varsInScope == null, "Unbalanced entering/exiting of GenBCode's genBlock().")
        // check previous invocation of genDefDef unregistered as many cleanups as it registered.
        assert(cleanups == Nil, "Previous invocation of genDefDef didn't unregister as many cleanups as it registered.")
        isModuleInitialized = false
        earlyReturnVar      = null
        shouldEmitCleanup   = false
        // used in connection with cleanups
        returnType =
          if (dd.symbol.isConstructor) UNIT
          else toTypeKind(dd.symbol.info.resultType)
        lastEmittedLineNr = -1
      }

      override def getCurrentCUnit(): CompilationUnit = { cunit }

      // see https://github.com/scala/scala/commit/892ee3df93a10ffe24fb11b37ad7c3a9cb93d5de
      def isAccessorToStaticField(msym: Symbol) = { msym.isAccessor && msym.accessed.hasStaticAnnotation } // @must-single-thread

      object bc extends JCodeMethodN {
        override def jmethod = PlainClassBuilder.this.mnode
      }

      /** If the selector type has a member with the right name,
       *  it is the host class; otherwise the symbol's owner.
       */
      def findHostClass(selector: Type, sym: Symbol) = selector member sym.name match {
        case NoSymbol   => log(s"Rejecting $selector as host class for $sym") ; sym.owner
        case _          => selector.typeSymbol
      }

      /* ---------------- top-down traversal invoking ASM Tree API along the way ---------------- */

      def gen(tree: Tree) {
        tree match {
          case EmptyTree => ()

          case _: ModuleDef => abort("Modules should have been eliminated by refchecks: " + tree)

          case ValDef(mods, name, tpt, rhs) => () // fields are added in the case handler for ClassDef

          case dd : DefDef => genDefDef(dd)

          case Template(_, _, body) => body foreach gen

          case _ => abort("Illegal tree in gen: " + tree)
        }
      }

      /* ---------------- helper utils for generating classes and fiels ---------------- */

      def genPlainClass(cd: ClassDef) {
        assert(cnode == null, "GenBCode detected nested methods.")
        innerClassBufferASM.clear()

        claszSymbol = cd.symbol
        isParcelableClass = isAndroidParcelableClass(claszSymbol)
        thisName = internalName(claszSymbol)
        cnode = new asm.tree.ClassNode()
        initJClass(cnode, claszSymbol, thisName, getGenericSignature(claszSymbol, claszSymbol.owner), cunit)

        val hasStaticCtor = methodSymbols(cd) exists (_.isStaticConstructor)
        if(!hasStaticCtor) {
          // but needs one ...
          if(isStaticModule(claszSymbol) || isAndroidParcelableClass(claszSymbol)) {
            fabricateStaticInit()
          }
        }

        val optSerial: Option[Long] = serialVUID(claszSymbol)
        if(optSerial.isDefined) { addSerialVUID(optSerial.get, cnode)}

        addClassFields(claszSymbol)
        gen(cd.impl)
        addInnerClassesASM(claszSymbol, cnode)

        assert(cd.symbol == claszSymbol, "Someone messed up BCodePhase.claszSymbol during genPlainClass().")

      } // end of method genPlainClass()

      /**
       * @must-single-thread
       */
      private def fabricateStaticInit() {

        val clinit: asm.MethodVisitor = cnode.visitMethod(
          PublicStatic, // TODO confirm whether we really don't want ACC_SYNTHETIC nor ACC_DEPRECATED
          CLASS_CONSTRUCTOR_NAME,
          mdesc_arglessvoid,
          null, // no java-generic-signature
          null  // no throwable exceptions
        )
        clinit.visitCode()

        /* "legacy static initialization" */
        if (isStaticModule(claszSymbol)) {
          clinit.visitTypeInsn(asm.Opcodes.NEW, thisName)
          clinit.visitMethodInsn(asm.Opcodes.INVOKESPECIAL,
                                 thisName, INSTANCE_CONSTRUCTOR_NAME, mdesc_arglessvoid)
        }
        if (isParcelableClass) { legacyAddCreatorCode(clinit, cnode, thisName) }
        clinit.visitInsn(asm.Opcodes.RETURN)

        clinit.visitMaxs(0, 0) // just to follow protocol, dummy arguments
        clinit.visitEnd()
      }

      def addClassFields(cls: Symbol) {
        /** Non-method term members are fields, except for module members. Module
         *  members can only happen on .NET (no flatten) for inner traits. There,
         *  a module symbol is generated (transformInfo in mixin) which is used
         *  as owner for the members of the implementation class (so that the
         *  backend emits them as static).
         *  No code is needed for this module symbol.
         */
        for (f <- fieldSymbols(cls)) {
          val javagensig = getGenericSignature(f, cls)
          val flags = mkFlags(
            javaFieldFlags(f),
            if(isDeprecated(f)) asm.Opcodes.ACC_DEPRECATED else 0 // ASM pseudo access flag
          )

          val jfield = new asm.tree.FieldNode(
            flags,
            f.javaSimpleName.toString,
            toTypeKind(f.tpe).getDescriptor,
            javagensig,
            null // no initial value
          )
          cnode.fields.add(jfield)
          emitAnnotations(jfield, f.annotations)
        }

      } // end of method addClassFields()

      /* ---------------- helper utils for generating methods and code ---------------- */

      def emit(opc: Int) { mnode.visitInsn(opc) }
      def emit(i: asm.tree.AbstractInsnNode) { mnode.instructions.add(i) }
      def emit(is: List[asm.tree.AbstractInsnNode]) { for(i <- is) { mnode.instructions.add(i) } }

      def emitZeroOf(tk: BType) {
        (tk.sort: @switch) match {
          case asm.Type.BOOLEAN => bc.boolconst(false)
          case asm.Type.BYTE  |
               asm.Type.SHORT |
               asm.Type.CHAR  |
               asm.Type.INT     => bc.iconst(0)
          case asm.Type.LONG    => bc.lconst(0)
          case asm.Type.FLOAT   => bc.fconst(0)
          case asm.Type.DOUBLE  => bc.dconst(0)
          case asm.Type.VOID    => ()
          case _ => emit(asm.Opcodes.ACONST_NULL)
        }
      }

      def genDefDef(dd: DefDef) {
        // the only method whose implementation is not emitted: getClass()
        if(definitions.isGetClass(dd.symbol)) { return }

        assert(mnode == null, "GenBCode detected nested method.")
        val msym = dd.symbol
        // clear method-specific stuff
        resetMethodBookkeeping(dd)

        val DefDef(_, _, _, vparamss, _, rhs) = dd
        assert(vparamss.isEmpty || vparamss.tail.isEmpty, "Malformed parameter list: " + vparamss)
        val isNative = msym.hasAnnotation(definitions.NativeAttr)
        val isAbstractMethod = msym.isDeferred || msym.owner.isInterface

        val params = if(vparamss.isEmpty) Nil else vparamss.head
        methSymbol = msym

        // add method-local vars for params
        nxtIdx = if (msym.isStaticMember) 0 else 1;
        for (p <- params) { makeLocal(p.symbol, toTypeKind(p.symbol.info)) }

        val Pair(flags, jmethod0) = initJMethod(
          cnode,
          msym, isNative,
          claszSymbol,  claszSymbol.isInterface,
          params.map(p => locals(p.symbol).tk),
          params.map(p => p.symbol.annotations)
        )
        mnode       = jmethod0.asInstanceOf[asm.tree.MethodNode]
        jMethodName = msym.javaSimpleName.toString

        /* Add method-local vars for LabelDef-params.
         *
         * This makes sure that:
         *   (1) upon visiting any "forward-jumping" Apply (ie visited before its target LabelDef), and after
         *   (2) grabbing the corresponding param symbols,
         * those param-symbols can be used to access method-local vars.
         *
         * When duplicating a finally-contained LabelDef, another program-point is needed for the copy (each such copy has its own asm.Label),
         * but the same vars (given by the LabelDef's params) can be reused,
         * because no LabelDef ends up nested within itself after such duplication.
         */
        for(ld <- labelDefsAtOrUnder(dd.rhs); p <- ld.params; if !locals.contains(p.symbol)) {
          // the tail-calls xform results in symbols shared btw method-params and labelDef-params, thus the guard above.
          makeLocal(p.symbol, toTypeKind(p.symbol.info))
        }

              def emitBodyOfStaticAccessor(staticfield: Symbol) {
                // in companion object accessors to @static fields, we access the static field directly
                // see https://github.com/scala/scala/commit/892ee3df93a10ffe24fb11b37ad7c3a9cb93d5de
                val hostClass   = msym.owner.companionClass
                val fieldName   = msym.accessed.javaSimpleName.toString
                val fieldDescr  = toTypeKind(staticfield.tpe).getDescriptor
                val opc =
                  if (msym.isGetter) asm.Opcodes.GETSTATIC
                  else asm.Opcodes.PUTSTATIC
                val insn = new asm.tree.FieldInsnNode(opc, internalName(hostClass), fieldName.toString, fieldDescr)

                if (opc == asm.Opcodes.GETSTATIC) {
                  emit(insn) // GETSTATIC `hostClass`.`accessed`
                } else {
                  assert(msym.isSetter,
                         "neither getter nor setter found when emitting (GET/PUT)-STATIC, during emitBodyOfStaticAccessor().")
                  load(params.head.symbol) // push setter's argument
                  emit(insn) // PUTSTATIC `hostClass`.`accessed`
                }
                // RETURN `returnType`
                bc emitRETURN returnType
              } // end of emitBodyOfStaticAccessor()


        if (!isAbstractMethod && !isNative) {
          lineNumber(rhs)
          val staticField = if (isAccessorToStaticField(msym)) {
            // https://github.com/scala/scala/commit/cb393fcbe35d0a871f23189d791b44be1b826ed2
            val compClass = msym.owner.companionClass
            compClass.info.findMember(msym.accessed.name, NoFlags, NoFlags, false)
          } else NoSymbol
          if(staticField != NoSymbol) {
            // special-cased method body for an accessor to @static field
            emitBodyOfStaticAccessor(staticField)
          } else {

                def emitNormalMethodBody() {
                  val veryFirstProgramPoint = currProgramPoint()
                  genLoad(rhs, returnType)

                  rhs match {
                    case Block(_, Return(_)) => ()
                    case Return(_) => ()
                    case EmptyTree =>
                      globalError("Concrete method has no definition: " + dd + (
                        if (settings.debug.value) "(found: " + msym.owner.info.decls.toList.mkString(", ") + ")"
                        else "")
                      )
                    case _ =>
                      bc emitRETURN returnType
                  }
                  if(emitVars) {
                    // add entries to LocalVariableTable JVM attribute
                    val onePastLastProgramPoint = currProgramPoint()
                    val hasStaticBitSet = ((flags & asm.Opcodes.ACC_STATIC) != 0)
                    if (!hasStaticBitSet) {
                      mnode.visitLocalVariable(
                        "this",
                        "L" + thisName + ";",
                        null,
                        veryFirstProgramPoint,
                        onePastLastProgramPoint,
                        0
                      )
                    }
                    for (p <- params) { emitLocalVarScope(p.symbol, veryFirstProgramPoint, onePastLastProgramPoint, force = true) }
                  }

                  if(methSymbol.isStaticConstructor) {
                    appendToStaticCtor(dd)
                  }
                } // end of emitNormalMethodBody()

            emitNormalMethodBody()
          }

          // Note we don't invoke visitMax, thus there are no FrameNode among mnode.instructions.
          // The only non-instruction nodes to be found are LabelNode and LineNumberNode.
        }
        mnode = null
      } // end of method genDefDef()

      /**
       *  @must-single-thread
       *
       *  TODO document, explain interplay with `fabricateStaticInit()`
       **/
      private def appendToStaticCtor(dd: DefDef) {

            def insertBefore(
                  location: asm.tree.AbstractInsnNode,
                  i0: asm.tree.AbstractInsnNode,
                  i1: asm.tree.AbstractInsnNode) {
              mnode.instructions.insertBefore(location, i0)
              mnode.instructions.insertBefore(location, i1)
            }

        // collect all return instructions
        var rets: List[asm.tree.AbstractInsnNode] = Nil
        val iter = mnode.instructions.iterator()
        while(iter.hasNext) {
          val i = iter.next()
          if(i.getOpcode() == asm.Opcodes.RETURN) { rets ::= i  }
        }

        var andrFieldName:  String = null
        var andrFieldDescr: String = null
        if(isParcelableClass && rets.nonEmpty) {
          // add a static field ("CREATOR") to this class to cache android.os.Parcelable$Creator
          andrFieldName = androidFieldName.toString // TermName to String
          andrFieldDescr = toTypeKind(AndroidCreatorClass.tpe).getDescriptor
          cnode.visitField(
            asm.Opcodes.ACC_STATIC | asm.Opcodes.ACC_FINAL,
            andrFieldName,
            andrFieldDescr,
            null,
            null
          )
        }

        // insert a few instructions for initialization before each return instruction
        for(r <- rets) {

          if (isStaticModule(claszSymbol)) { // call object's private ctor from static ctor

            // NEW `moduleName`
            val className = internalName(methSymbol.enclClass)
            val i0 = new asm.tree.TypeInsnNode(asm.Opcodes.NEW, className)

            // INVOKESPECIAL <init>
            val callee = methSymbol.enclClass.primaryConstructor
            val jname  = callee.javaSimpleName.toString
            val jowner = internalName(callee.owner)
            val jtype  = asmMethodType(callee).getDescriptor
            val i1 = new asm.tree.MethodInsnNode(asm.Opcodes.INVOKESPECIAL, jowner, jname, jtype)

            insertBefore(r, i0, i1)
          }

          if(isParcelableClass) { // android creator code

            // INVOKESTATIC CREATOR(): android.os.Parcelable$Creator; -- TODO where does this Android method come from?
            val callee = definitions.getMember(claszSymbol.companionModule, androidFieldName)
            val jowner = internalName(callee.owner)
            val jname  = callee.javaSimpleName.toString
            val jtype  = asmMethodType(callee).getDescriptor
            val i0 = new asm.tree.MethodInsnNode(asm.Opcodes.INVOKESTATIC, jowner, jname, jtype)

            // PUTSTATIC `thisName`.CREATOR;
            val i1 = new asm.tree.FieldInsnNode(asm.Opcodes.PUTSTATIC, thisName, andrFieldName, andrFieldDescr)

            insertBefore(r, i0, i1)
          }

        }

      }

      private def emitLocalVarScope(sym: Symbol, start: asm.Label, end: asm.Label, force: Boolean = false) {
        val Local(tk, name, idx, isSynth) = locals(sym)
        if(force || !isSynth) {
          mnode.visitLocalVariable(name, tk.getDescriptor, null, start, end, idx)
        }
      }

      /**
       * Emits code that adds nothing to the operand stack.
       * Two main cases: `tree` is an assignment,
       * otherwise an `adapt()` to UNIT is performed if needed.
       */
      def genStat(tree: Tree) {
        lineNumber(tree)
        tree match {
          case Assign(lhs @ Select(_, _), rhs) =>
            val isStatic = lhs.symbol.isStaticMember
            if (!isStatic) { genLoadQualifier(lhs) }
            genLoad(rhs, toTypeKind(lhs.symbol.info))
            lineNumber(tree)
            fieldStore(lhs.symbol)

          case Assign(lhs, rhs) =>
            val s = lhs.symbol
            val Local(tk, _, idx, _) = locals.getOrElse(s, makeLocal(s, toTypeKind(s.info)))
            genLoad(rhs, tk)
            lineNumber(tree)
            bc.store(idx, tk)

          case _ =>
            genLoad(tree, UNIT)
        }
      }

      def genThrow(expr: Tree): BType = {
        require(expr.tpe <:< ThrowableClass.tpe, expr.tpe)

        val thrownKind = toTypeKind(expr.tpe)
        genLoad(expr, thrownKind)
        lineNumber(expr)
        emit(asm.Opcodes.ATHROW) // ICode enters here into enterIgnoreMode, we'll rely instead on DCE at ClassNode level.

        RT_NOTHING // always returns the same, the invoker should know :)
      }

      /** Generate code for primitive arithmetic operations. */
      def genArithmeticOp(tree: Tree, code: Int): BType = {
        val Apply(fun @ Select(larg, _), args) = tree
        var resKind = toTypeKind(larg.tpe)

        assert(args.length <= 1, "Too many arguments for primitive function: " + fun.symbol)
        assert(resKind.isNumericType || (resKind == BOOL),
                 resKind.toString + " is not a numeric or boolean type " + "[operation: " + fun.symbol + "]")

        args match {
          // unary operation
          case Nil =>
            genLoad(larg, resKind)
            code match {
              case scalaPrimitives.POS => () // nothing
              case scalaPrimitives.NEG => bc.neg(resKind)
              case scalaPrimitives.NOT => bc.genPrimitiveArithmetic(NOT, resKind)
              case _ => abort("Unknown unary operation: " + fun.symbol.fullName + " code: " + code)
            }

          // binary operation
          case rarg :: Nil =>
            resKind = maxType(toTypeKind(larg.tpe), toTypeKind(rarg.tpe))
            if (scalaPrimitives.isShiftOp(code) || scalaPrimitives.isBitwiseOp(code)) {
              assert(resKind.isIntegralType || (resKind == BOOL),
                     resKind.toString + " incompatible with arithmetic modulo operation.")
            }

            genLoad(larg, resKind)
            genLoad(rarg, // check .NET size of shift arguments!
                    if (scalaPrimitives.isShiftOp(code)) INT else resKind)

            (code: @switch) match {
              case scalaPrimitives.ADD => bc add resKind
              case scalaPrimitives.SUB => bc sub resKind
              case scalaPrimitives.MUL => bc mul resKind
              case scalaPrimitives.DIV => bc div resKind
              case scalaPrimitives.MOD => bc rem resKind

              case scalaPrimitives.OR  |
                   scalaPrimitives.XOR |
                   scalaPrimitives.AND => bc.genPrimitiveLogical(code, resKind)

              case scalaPrimitives.LSL |
                   scalaPrimitives.LSR |
                   scalaPrimitives.ASR => bc.genPrimitiveShift(code, resKind)

              case _                   => abort("Unknown primitive: " + fun.symbol + "[" + code + "]")
            }

          case _ =>
            abort("Too many arguments for primitive function: " + tree)
        }
        lineNumber(tree)
        resKind
      }

      /** Generate primitive array operations. */
      def genArrayOp(tree: Tree, code: Int, expectedType: BType): BType = {
        val Apply(Select(arrayObj, _), args) = tree
        val k    = toTypeKind(arrayObj.tpe)
        genLoad(arrayObj, k)
        val elementType = typeOfArrayOp.getOrElse(code, abort("Unknown operation on arrays: " + tree + " code: " + code))

        var generatedType = expectedType

        if (scalaPrimitives.isArrayGet(code)) {
          // load argument on stack
          assert(args.length == 1, "Too many arguments for array get operation: " + tree);
          genLoad(args.head, INT)
          generatedType = k.getComponentType
          bc.aload(elementType)
        }
        else if (scalaPrimitives.isArraySet(code)) {
          assert(args.length == 2, "Too many arguments for array set operation: " + tree);
          genLoad(args.head, INT)
          genLoad(args.tail.head, toTypeKind(args.tail.head.tpe))
          // the following line should really be here, but because of bugs in erasure
          // we pretend we generate whatever type is expected from us.
          //generatedType = UNIT
          bc.astore(elementType)
        }
        else {
          generatedType = INT
          emit(asm.Opcodes.ARRAYLENGTH)
        }
        lineNumber(tree)

        generatedType
      }

      def genSynchronized(tree: Apply, expectedType: BType): BType = {
        val Apply(fun, args) = tree
        val monitor = makeLocal(ObjectReference, "monitor")
        val monCleanup = new asm.Label

        // if the synchronized block returns a result, store it in a local variable.
        // Just leaving it on the stack is not valid in MSIL (stack is cleaned when leaving try-blocks).
        val hasResult = (expectedType != UNIT)
        val monitorResult: Symbol = if(hasResult) makeLocal(toTypeKind(args.head.tpe), "monitorResult") else null;

        /* ------ (1) pushing and entering the monitor, also keeping a reference to it in a local var. ------ */
        genLoadQualifier(fun)
        bc dup ObjectReference
        store(monitor)
        emit(asm.Opcodes.MONITORENTER)

        /* ------ (2) Synchronized block.
         *            Reached by fall-through from (1).
         *            Protected by:
         *            (2.a) the EH-version of the monitor-exit, and
         *            (2.b) whatever protects the whole synchronized expression.
         * ------
         */
        val startProtected = currProgramPoint()
        registerCleanup(monCleanup)
        genLoad(args.head, expectedType /* toTypeKind(tree.tpe.resultType) */)
        unregisterCleanup(monCleanup)
        if (hasResult) { store(monitorResult) }
        nopIfNeeded(startProtected)
        val endProtected = currProgramPoint()

        /* ------ (3) monitor-exit after normal, non-early-return, termination of (2).
         *            Reached by fall-through from (2).
         *            Protected by whatever protects the whole synchronized expression.
         * ------
         */
        load(monitor)
        emit(asm.Opcodes.MONITOREXIT)
        if(hasResult) { load(monitorResult) }
        val postHandler = new asm.Label
        bc goTo postHandler

        /* ------ (4) exception-handler version of monitor-exit code.
         *            Reached upon abrupt termination of (2).
         *            Protected by whatever protects the whole synchronized expression.
         * ------
         */
        protect(startProtected, endProtected, currProgramPoint(), ThrowableReference)
        load(monitor)
        emit(asm.Opcodes.MONITOREXIT)
        emit(asm.Opcodes.ATHROW)

        /* ------ (5) cleanup version of monitor-exit code.
         *            Reached upon early-return from (2).
         *            Protected by whatever protects the whole synchronized expression.
         * ------
         */
        if(shouldEmitCleanup) {
          markProgramPoint(monCleanup)
          load(monitor)
          emit(asm.Opcodes.MONITOREXIT)
          pendingCleanups()
        }

        /* ------ (6) normal exit of the synchronized expression.
         *            Reached after normal, non-early-return, termination of (3).
         *            Protected by whatever protects the whole synchronized expression.
         * ------
         */
        mnode visitLabel postHandler

        lineNumber(tree)

        expectedType
      }

      def genLoadIf(tree: If, expectedType: BType): BType = {
        val If(condp, thenp, elsep) = tree

        val success = new asm.Label
        val failure = new asm.Label

        val hasElse = !elsep.isEmpty
        val postIf  = if(hasElse) new asm.Label else failure

        genCond(condp, success, failure)

        val thenKind      = toTypeKind(thenp.tpe)
        val elseKind      = if (!hasElse) UNIT else toTypeKind(elsep.tpe)
        def hasUnitBranch = (thenKind == UNIT || elseKind == UNIT)
        val resKind       = if (hasUnitBranch) UNIT else toTypeKind(tree.tpe)

        markProgramPoint(success)
        genLoad(thenp, resKind)
        if(hasElse) { bc goTo postIf }
        markProgramPoint(failure)
        if(hasElse) {
          genLoad(elsep, resKind)
          markProgramPoint(postIf)
        }

        resKind
      }

      /** Detects whether no instructions have been emitted since label `lbl` (by checking whether the current program point is still `lbl`)
       *  and if so emits a NOP. This can be used to avoid an empty try-block being protected by exception handlers, which results in an illegal class file format exception. */
      def nopIfNeeded(lbl: asm.Label) {
        val noInstructionEmitted = isAtProgramPoint(lbl)
        if(noInstructionEmitted) { emit(asm.Opcodes.NOP) }
      }

      /** TODO documentation */
      def genLoadTry(tree: Try): BType = {

        val Try(block, catches, finalizer) = tree
        val kind = toTypeKind(tree.tpe)

        val caseHandlers: List[EHClause] =
          for (CaseDef(pat, _, caseBody) <- catches) yield {
            pat match {
              case Typed(Ident(nme.WILDCARD), tpt)  => NamelessEH(toTypeKind(tpt.tpe), caseBody)
              case Ident(nme.WILDCARD)              => NamelessEH(ThrowableReference,  caseBody)
              case Bind(_, _)                       => BoundEH   (pat.symbol, caseBody)
            }
          }

        // ------ (0) locals used later ------

        // points to (a) the finally-clause conceptually reached via fall-through from try-catch, or (b) program point right after the try-catch-finally.
        val postHandlers = new asm.Label
        val hasFinally   = (finalizer != EmptyTree)
        // used in the finally-clause reached via fall-through from try-catch, if any.
        val guardResult  = hasFinally && (kind != UNIT) && mayCleanStack(finalizer)
        // please notice `tmp` has type tree.tpe, while `earlyReturnVar` has the method return type. Because those two types can be different, dedicated vars are needed.
        val tmp          = if(guardResult) makeLocal(toTypeKind(tree.tpe), "tmp") else null;
        // upon early return from the try-body or one of its EHs (but not the EH-version of the finally-clause) AND hasFinally, a cleanup is needed.
        val finCleanup   = if(hasFinally) new asm.Label else null

        /* ------ (1) try-block, protected by:
         *                       (1.a) the EHs due to case-clauses,   emitted in (2),
         *                       (1.b) the EH  due to finally-clause, emitted in (3.A)
         *                       (1.c) whatever protects the whole try-catch-finally expression.
         * ------
         */

        val startTryBody = currProgramPoint()
        registerCleanup(finCleanup)
        genLoad(block, kind)
        unregisterCleanup(finCleanup)
        nopIfNeeded(startTryBody) // we can't elide an exception-handler protecting an empty try-body, that would change semantics (e.g. ClassNotFound due to the EH)
        val endTryBody = currProgramPoint()
        bc goTo postHandlers

        /* ------ (2) One EH for each case-clause (this does not include the EH-version of the finally-clause)
         *            An EH in (2) is reached upon abrupt termination of (1).
         *            An EH in (2) is protected by:
         *                         (2.a) the EH-version of the finally-clause, if any.
         *                         (2.b) whatever protects the whole try-catch-finally expression.
         * ------
         */

        for (ch <- caseHandlers) {

          // (2.a) emit case clause proper
          val startHandler = currProgramPoint()
          var endHandler: asm.Label = null
          var excType: BType = null
          registerCleanup(finCleanup)
          ch match {
            case NamelessEH(typeToDrop, caseBody) =>
              bc drop typeToDrop
              genLoad(caseBody, kind) // adapts caseBody to `kind`, thus it can be stored, if `guardResult`, in `tmp`.
              nopIfNeeded(startHandler)
              endHandler = currProgramPoint()
              excType = typeToDrop

            case BoundEH   (patSymbol,      caseBody) =>
              // test/files/run/contrib674.scala , a local-var already exists for patSymbol.
              // rather than creating on first-access, we do it right away to emit debug-info for the created local var.
              val Local(patTK, _, patIdx, _) = locals.getOrElse(patSymbol, makeLocal(patSymbol, toTypeKind(patSymbol.info)))
              bc.store(patIdx, patTK)
              genLoad(caseBody, kind)
              nopIfNeeded(startHandler)
              endHandler = currProgramPoint()
              emitLocalVarScope(patSymbol, startHandler, endHandler)
              excType = patTK
          }
          unregisterCleanup(finCleanup)
          // (2.b)  mark the try-body as protected by this case clause.
          protect(startTryBody, endTryBody, startHandler, excType)
          // (2.c) emit jump to the program point where the finally-clause-for-normal-exit starts, or in effect `after` if no finally-clause was given.
          bc goTo postHandlers

        }

        /* ------ (3.A) The exception-handler-version of the finally-clause.
         *              Reached upon abrupt termination of (1) or one of the EHs in (2).
         *              Protected only by whatever protects the whole try-catch-finally expression.
         * ------
         */

        // a note on terminology: this is not "postHandlers", despite appearences.
        // "postHandlers" as in the source-code view. And from that perspective, both (3.A) and (3.B) are invisible implementation artifacts.
        if(hasFinally) {
          nopIfNeeded(startTryBody)
          val finalHandler = currProgramPoint() // version of the finally-clause reached via unhandled exception.
          protect(startTryBody, finalHandler, finalHandler, null)
          val Local(eTK, _, eIdx, _) = locals(makeLocal(ThrowableReference, "exc"))
          bc.store(eIdx, eTK)
          emitFinalizer(finalizer, null, true)
          bc.load(eIdx, eTK)
          emit(asm.Opcodes.ATHROW)
        }

        /* ------ (3.B) Cleanup-version of the finally-clause.
         *              Reached upon early RETURN from (1) or upon early RETURN from one of the EHs in (2)
         *              (and only from there, ie reached only upon early RETURN from
         *               program regions bracketed by registerCleanup/unregisterCleanup).
         *              Protected only by whatever protects the whole try-catch-finally expression.
         * TODO explain what happens upon RETURN contained in (3.B)
         * ------
         */

        // this is not "postHandlers" either.
        // `shouldEmitCleanup` can be set, yet this try expression lack a finally-clause.
        // In other words, all combinations of (hasFinally, shouldEmitCleanup) are valid.
        if(hasFinally && shouldEmitCleanup) {
          markProgramPoint(finCleanup)
          // regarding return value, the protocol is: in place of a `return-stmt`, a sequence of `adapt, store, jump` are inserted.
          emitFinalizer(finalizer, null, false)
          pendingCleanups()
        }

        /* ------ (4) finally-clause-for-normal-nonEarlyReturn-exit
         *            Reached upon normal, non-early-return termination of (1) or one of the EHs in (2).
         *            Protected only by whatever protects the whole try-catch-finally expression.
         * TODO explain what happens upon RETURN contained in (4)
         * ------
         */

        markProgramPoint(postHandlers)
        if(hasFinally) {
          emitFinalizer(finalizer, tmp, false) // the only invocation of emitFinalizer with `isDuplicate == false`
        }

        kind
      } // end of genLoadTry()

      /** if no more pending cleanups, all that remains to do is return. Otherwise jump to the next (outer) pending cleanup. */
      private def pendingCleanups() {
        cleanups match {
          case Nil =>
            if(earlyReturnVar != null) {
              load(earlyReturnVar)
              bc.emitRETURN(locals(earlyReturnVar).tk)
            } else {
              bc emitRETURN UNIT
            }
            shouldEmitCleanup = false

          case nextCleanup :: _ =>
            bc goTo nextCleanup
        }
      }

      private def protect(start: asm.Label, end: asm.Label, handler: asm.Label, excType: BType) {
        val excInternalName: String =
          if (excType == null) null
          else excType.getInternalName
        assert(start != end, "protecting a range of zero instructions leads to illegal class format. Solution: add a NOP to that range.")
        mnode.visitTryCatchBlock(start, end, handler, excInternalName)
      }

      /** `tmp` (if non-null) is the symbol of the local-var used to preserve the result of the try-body, see `guardResult` */
      private def emitFinalizer(finalizer: Tree, tmp: Symbol, isDuplicate: Boolean) {
        var saved: immutable.Map[ /* LabelDef */ Symbol, asm.Label ] = null
        if(isDuplicate) {
          saved = locLabel
          for(ldef <- labelDefsAtOrUnder(finalizer)) {
            locLabel -= ldef.symbol
          }
        }
        // when duplicating, the above guarantees new asm.Labels are used for LabelDefs contained in the finalizer (their vars are reused, that's ok)
        if(tmp != null) { store(tmp) }
        genLoad(finalizer, UNIT)
        if(tmp != null) { load(tmp)  }
        if(isDuplicate) {
          locLabel = saved
        }
      }

      def genPrimitiveOp(tree: Apply, expectedType: BType): BType = {
        val sym = tree.symbol
        val Apply(fun @ Select(receiver, _), _) = tree
        val code = scalaPrimitives.getPrimitive(sym, receiver.tpe)

        import scalaPrimitives.{isArithmeticOp, isArrayOp, isLogicalOp, isComparisonOp}

        if (isArithmeticOp(code))                genArithmeticOp(tree, code)
        else if (code == scalaPrimitives.CONCAT) genStringConcat(tree)
        else if (code == scalaPrimitives.HASH)   genScalaHash(receiver)
        else if (isArrayOp(code))                genArrayOp(tree, code, expectedType)
        else if (isLogicalOp(code) || isComparisonOp(code)) {
          val success, failure, after = new asm.Label
          genCond(tree, success, failure)
          // success block
            markProgramPoint(success)
            bc boolconst true
            bc goTo after
          // failure block
            markProgramPoint(failure)
            bc boolconst false
          // after
          markProgramPoint(after)

          BOOL
        }
        else if (code == scalaPrimitives.SYNCHRONIZED)
          genSynchronized(tree, expectedType)
        else if (scalaPrimitives.isCoercion(code)) {
          genLoad(receiver, toTypeKind(receiver.tpe))
          lineNumber(tree)
          genCoercion(code)
          coercionTo(code)
        }
        else abort(
          "Primitive operation not handled yet: " + sym.fullName + "(" +
          fun.symbol.simpleName + ") " + " at: " + (tree.pos)
        )
      }

      /** Generate code for trees that produce values on the stack */
      def genLoad(tree: Tree, expectedType: BType) {
        var generatedType = expectedType

        lineNumber(tree)

        tree match {
          case lblDf : LabelDef => genLabelDef(lblDf, expectedType)

          case ValDef(_, nme.THIS, _, _) =>
            debuglog("skipping trivial assign to _$this: " + tree)

          case ValDef(_, _, _, rhs) =>
            val sym = tree.symbol
            /* most of the time, !locals.contains(sym), unless the current activation of genLoad() is being called
               while duplicating a finalizer that contains this ValDef. */
            val Local(tk, _, idx, isSynth) = locals.getOrElseUpdate(sym, makeLocal(sym, toTypeKind(sym.info)))
            if (rhs == EmptyTree) { emitZeroOf(tk) }
            else { genLoad(rhs, tk) }
            bc.store(idx, tk)
            if(!isSynth) { // there are case <synthetic> ValDef's emitted by patmat
              varsInScope ::= (sym -> currProgramPoint())
            }
            generatedType = UNIT

          case t : If =>
            generatedType = genLoadIf(t, expectedType)

          case r : Return =>
            genReturn(r)
            generatedType = expectedType

          case t : Try =>
            generatedType = genLoadTry(t)

          case Throw(expr) =>
            generatedType = genThrow(expr)

          case New(tpt) =>
            abort("Unexpected New(" + tpt.summaryString + "/" + tpt + ") reached GenBCode.\n" +
                  "  Call was genLoad" + ((tree, expectedType)))

          case app : Apply =>
            generatedType = genApply(app, expectedType)

          case ApplyDynamic(qual, args) => sys.error("No invokedynamic support yet.")

          case This(qual) =>
            assert(tree.symbol == claszSymbol || tree.symbol.isModuleClass,
                   "Trying to access the this of another class: " +
                   "tree.symbol = " + tree.symbol + ", class symbol = " + claszSymbol + " compilation unit:"+ cunit)
            if (tree.symbol.isModuleClass && tree.symbol != claszSymbol) {
              generatedType = genLoadModule(tree)
            }
            else {
              mnode.visitVarInsn(asm.Opcodes.ALOAD, 0)
              generatedType =
                if (tree.symbol == ArrayClass) ObjectReference
                else brefType(thisName) // inner class (if any) for claszSymbol already tracked.
            }

          case Select(Ident(nme.EMPTY_PACKAGE_NAME), module) =>
            assert(tree.symbol.isModule, "Selection of non-module from empty package: " + tree + " sym: " + tree.symbol + " at: " + (tree.pos))
            genLoadModule(tree)

          case Select(qualifier, selector) =>
            val sym = tree.symbol
            generatedType = toTypeKind(sym.info)
            val hostClass = findHostClass(qualifier.tpe, sym)
            log(s"Host class of $sym with qual $qualifier (${qualifier.tpe}) is $hostClass")

            if (sym.isModule)            { genLoadModule(tree) }
            else if (sym.isStaticMember) { fieldLoad(sym, hostClass) }
            else {
              genLoadQualifier(tree)
              fieldLoad(sym, hostClass)
            }

          case Ident(name) =>
            val sym = tree.symbol
            if (!sym.isPackage) {
              val tk = toTypeKind(sym.info)
              if (sym.isModule) { genLoadModule(tree) }
              else { load(sym) }
              generatedType = tk
            }

          case Literal(value) =>
            if (value.tag != UnitTag) (value.tag, expectedType) match {
              case (IntTag,   LONG  ) => bc.lconst(value.longValue);       generatedType = LONG
              case (FloatTag, DOUBLE) => bc.dconst(value.doubleValue);     generatedType = DOUBLE
              case (NullTag,  _     ) => bc.emit(asm.Opcodes.ACONST_NULL); generatedType = RT_NULL
              case _                  => genConstant(value);               generatedType = toTypeKind(tree.tpe)
            }

          case blck : Block => genBlock(blck, expectedType)

          case Typed(Super(_, _), _) => genLoad(This(claszSymbol), expectedType)

          case Typed(expr, _) => genLoad(expr, expectedType)

          case Assign(_, _) =>
            generatedType = UNIT
            genStat(tree)

          case av : ArrayValue =>
            generatedType = genArrayValue(av)

          case mtch : Match =>
            generatedType = genMatch(mtch)

          case EmptyTree => if (expectedType != UNIT) { emitZeroOf(expectedType) }

          case _ => abort("Unexpected tree in genLoad: " + tree + "/" + tree.getClass + " at: " + tree.pos)
        }

        // emit conversion
        if (generatedType != expectedType) {
          adapt(generatedType, expectedType)
        }

      } // end of GenBCode.genLoad()

      // ---------------- field load and store ----------------

      /**
       * @must-single-thread
       **/
      def fieldLoad( field: Symbol, hostClass: Symbol = null) {
        fieldOp(field, isLoad = true,  hostClass)
      }
      /**
       * @must-single-thread
       **/
      def fieldStore(field: Symbol, hostClass: Symbol = null) {
        fieldOp(field, isLoad = false, hostClass)
      }

      /**
       * @must-single-thread
       **/
      private def fieldOp(field: Symbol, isLoad: Boolean, hostClass: Symbol = null) {
        // LOAD_FIELD.hostClass , CALL_METHOD.hostClass , and #4283
        val owner      =
          if(hostClass == null) internalName(field.owner)
          else                  internalName(hostClass)
        val fieldJName = field.javaSimpleName.toString
        val fieldDescr = toTypeKind(field.tpe).getDescriptor
        val isStatic   = field.isStaticMember
        val opc =
          if(isLoad) { if (isStatic) asm.Opcodes.GETSTATIC else asm.Opcodes.GETFIELD }
          else       { if (isStatic) asm.Opcodes.PUTSTATIC else asm.Opcodes.PUTFIELD }
        mnode.visitFieldInsn(opc, owner, fieldJName, fieldDescr)

      }

      // ---------------- emitting constant values ----------------

      /**
       * For const.tag in {ClazzTag, EnumTag}
       *   @must-single-thread
       * Otherwise it's safe to call from multiple threads.
       **/
      def genConstant(const: Constant) {
        (const.tag: @switch) match {

          case BooleanTag => bc.boolconst(const.booleanValue)

          case ByteTag    => bc.iconst(const.byteValue)
          case ShortTag   => bc.iconst(const.shortValue)
          case CharTag    => bc.iconst(const.charValue)
          case IntTag     => bc.iconst(const.intValue)

          case LongTag    => bc.lconst(const.longValue)
          case FloatTag   => bc.fconst(const.floatValue)
          case DoubleTag  => bc.dconst(const.doubleValue)

          case UnitTag    => ()

          case StringTag  =>
            assert(const.value != null, const) // TODO this invariant isn't documented in `case class Constant`
            mnode.visitLdcInsn(const.stringValue) // `stringValue` special-cases null, but not for a const with StringTag

          case NullTag    => emit(asm.Opcodes.ACONST_NULL)

          case ClazzTag   =>
            val toPush: BType = {
              val kind = toTypeKind(const.typeValue)
              if (kind.isValueType) classLiteral(kind)
              else kind;
            }
            mnode.visitLdcInsn(toPush.toASMType)

          case EnumTag   =>
            val sym       = const.symbolValue
            val ownerName = internalName(sym.owner)
            val fieldName = sym.javaSimpleName.toString
            val fieldDesc = toTypeKind(sym.tpe.underlying).getDescriptor
            mnode.visitFieldInsn(
              asm.Opcodes.GETSTATIC,
              ownerName,
              fieldName,
              fieldDesc
            )

          case _ => abort("Unknown constant value: " + const)
        }
      }

      private def genLabelDef(lblDf: LabelDef, expectedType: BType) {
        // duplication of LabelDefs contained in `finally`-clauses is handled when emitting RETURN. No bookkeeping for that required here.
        // no need to call index() over lblDf.params, on first access that magic happens (moreover, no LocalVariableTable entries needed for them).
        markProgramPoint(programPoint(lblDf.symbol))
        lineNumber(lblDf)
        genLoad(lblDf.rhs, expectedType)
      }

      private def genReturn(r: Return) {
        val Return(expr) = r
        val returnedKind = toTypeKind(expr.tpe)
        genLoad(expr, returnedKind)
        adapt(returnedKind, returnType)
        val saveReturnValue = (returnType != UNIT)
        lineNumber(r)

        cleanups match {
          case Nil =>
            // not an assertion: !shouldEmitCleanup (at least not yet, pendingCleanups() may still have to run, and reset `shouldEmitCleanup`.
            bc emitRETURN returnType
          case nextCleanup :: rest =>
            if(saveReturnValue) {
              if(shouldEmitCleanup) {
                cunit.warning(r.pos, "Return statement found in finally-clause, discarding its return-value in favor of that of a more deeply nested return.")
                bc drop returnType
              } else {
                // regarding return value, the protocol is: in place of a `return-stmt`, a sequence of `adapt, store, jump` are inserted.
                if(earlyReturnVar == null) {
                  earlyReturnVar = makeLocal(returnType, "earlyReturnVar")
                }
                store(earlyReturnVar)
              }
            }
            bc goTo nextCleanup
            shouldEmitCleanup = true
        }

      } // end of genReturn()

      private def genApply(app: Apply, expectedType: BType): BType = {
        val BoxesRunTime = "scala/runtime/BoxesRunTime"
        var generatedType = expectedType
        lineNumber(app)
        app match {

          case Apply(TypeApply(fun, targs), _) =>

                def genTypeApply(): BType = {
                  val sym = fun.symbol
                  val cast = sym match {
                    case Object_isInstanceOf  => false
                    case Object_asInstanceOf  => true
                    case _                    => abort("Unexpected type application " + fun + "[sym: " + sym.fullName + "]" + " in: " + app)
                  }

                  val Select(obj, _) = fun
                  val l = toTypeKind(obj.tpe)
                  val r = toTypeKind(targs.head.tpe)
                  genLoadQualifier(fun)

                  if (l.isValueType && r.isValueType)
                    genConversion(l, r, cast)
                  else if (l.isValueType) {
                    bc drop l
                    if (cast) {
                      mnode.visitTypeInsn(asm.Opcodes.NEW, classCastExceptionType.getInternalName)
                      bc dup ObjectReference
                      emit(asm.Opcodes.ATHROW)
                    } else {
                      bc boolconst false
                    }
                  }
                  else if (r.isValueType && cast) {
                    assert(false, "Erasure should have added an unboxing operation to prevent this cast. Tree: " + app)
                  }
                  else if (r.isValueType) {
                    bc isInstance classLiteral(r)
                  }
                  else {
                    genCast(l, r, cast)
                  }

                  if (cast) r else BOOL
                } // end of genTypeApply()

            generatedType = genTypeApply()

          // 'super' call: Note: since constructors are supposed to
          // return an instance of what they construct, we have to take
          // special care. On JVM they are 'void', and Scala forbids (syntactically)
          // to call super constructors explicitly and/or use their 'returned' value.
          // therefore, we can ignore this fact, and generate code that leaves nothing
          // on the stack (contrary to what the type in the AST says).
          case Apply(fun @ Select(Super(_, mix), _), args) =>
            val invokeStyle = SuperCall(mix)
            // if (fun.symbol.isConstructor) Static(true) else SuperCall(mix);
            mnode.visitVarInsn(asm.Opcodes.ALOAD, 0)
            genLoadArguments(args, paramTKs(app))
            genCallMethod(fun.symbol, invokeStyle)
            generatedType =
              if (fun.symbol.isConstructor) UNIT
              else toTypeKind(fun.symbol.info.resultType)

          // 'new' constructor call: Note: since constructors are
          // thought to return an instance of what they construct,
          // we have to 'simulate' it by DUPlicating the freshly created
          // instance (on JVM, <init> methods return VOID).
          case Apply(fun @ Select(New(tpt), nme.CONSTRUCTOR), args) =>
            val ctor = fun.symbol
            assert(ctor.isClassConstructor, "'new' call to non-constructor: " + ctor.name)

            generatedType = toTypeKind(tpt.tpe)
            assert(generatedType.isRefOrArrayType, "Non reference type cannot be instantiated: " + generatedType)

            generatedType match {
              case arr if generatedType.isArray =>
                genLoadArguments(args, paramTKs(app))
                val dims = arr.getDimensions
                var elemKind = arr.getElementType
                val argsSize = args.length
                if (argsSize > dims) {
                  cunit.error(app.pos, "too many arguments for array constructor: found " + args.length +
                                        " but array has only " + dims + " dimension(s)")
                }
                if (argsSize < dims) {
                  /* The BType instantiation below denote the same type as
                   *    for (i <- args.length until dims) elemKind = arrayOf(elemKind)
                   * with the advantage of not requiring `arrayOf()`, a must-single-thread operation.
                   */
                  elemKind = new BType(BType.ARRAY, arr.off + argsSize, arr.len - argsSize)
                }
                (argsSize : @switch) match {
                  case 1 => bc newarray elemKind
                  case _ =>
                    val descr = ('[' * argsSize) + elemKind.getDescriptor // denotes the same as: arrayN(elemKind, argsSize).getDescriptor
                    mnode.visitMultiANewArrayInsn(descr, argsSize)
                }

              case rt if generatedType.hasObjectSort =>
                assert(exemplar(ctor.owner).c == rt, "Symbol " + ctor.owner.fullName + " is different from " + rt)
                mnode.visitTypeInsn(asm.Opcodes.NEW, rt.getInternalName)
                bc dup generatedType
                genLoadArguments(args, paramTKs(app))
                genCallMethod(ctor, Static(true))

              case _ =>
                abort("Cannot instantiate " + tpt + " of kind: " + generatedType)
            }

          case Apply(fun @ _, List(expr)) if (definitions.isBox(fun.symbol)) =>
            val nativeKind = toTypeKind(expr.tpe)
            genLoad(expr, nativeKind)
            if (settings.Xdce.value) { // TODO reminder for future work: MethodNode-based closelim and dce.
              // we store this boxed value to a local, even if not really needed.
              // boxing optimization might use it, and dead code elimination will
              // take care of unnecessary stores
              val loc1 = makeLocal(nativeKind, "boxed")
              store(loc1)
              load(loc1)
            }
            val MethodNameAndType(mname, mdesc) = asmBoxTo(nativeKind)
            bc.invokestatic(BoxesRunTime, mname, mdesc)
            generatedType = boxResultType(fun.symbol) // was toTypeKind(fun.symbol.tpe.resultType)

          case Apply(fun @ _, List(expr)) if (definitions.isUnbox(fun.symbol)) =>
            genLoad(expr, toTypeKind(expr.tpe))
            val boxType = unboxResultType(fun.symbol) // was toTypeKind(fun.symbol.owner.linkedClassOfClass.tpe)
            generatedType = boxType
            val MethodNameAndType(mname, mdesc) = asmUnboxTo(boxType)
            bc.invokestatic(BoxesRunTime, mname, mdesc)

          case Apply(fun @ Select(qual, _), args)
          if !methSymbol.isStaticConstructor
          && isAccessorToStaticField(fun.symbol)
          && qual.tpe.typeSymbol.orElse(fun.symbol.owner).companionClass != NoSymbol =>

                def emitLoadStaticField() {
                  // bypass the accessor to the companion object and load the static field directly
                  // this bypass is not done:
                  // - if the static intializer for the static field itself
                  // - if there is no companion class of the object owner - this happens in the REPL
                  // see https://github.com/scala/scala/commit/892ee3df93a10ffe24fb11b37ad7c3a9cb93d5de
                  // see https://github.com/scala/scala/commit/5a8dfad583b825158cf0abdae5d73a4a7f8cd997
                  // see https://github.com/scala/scala/commit/faa114e2fb6003031efa2cdd56a32a3c44aa71fb
                  val sym = fun.symbol
                  generatedType   = toTypeKind(sym.accessed.info)
                  val hostOwner   = qual.tpe.typeSymbol.orElse(sym.owner)
                  val hostClass   = hostOwner.companionClass
                  val fieldName   = sym.accessed.javaSimpleName.toString
                  val staticfield = hostClass.info.findMember(sym.accessed.name, NoFlags, NoFlags, false) orElse {
                    if (!currentRun.compiles(hostOwner)) {
                      // hostOwner was separately compiled -- the static field symbol needs to be recreated in hostClass
                      import Flags._
                      debuglog("recreating sym.accessed.name: " + sym.accessed.name)
                      val objectfield = hostOwner.info.findMember(sym.accessed.name, NoFlags, NoFlags, false)
                      val staticfield = hostClass.newVariable(newTermName(sym.accessed.name.toString), app.pos, STATIC | SYNTHETIC | FINAL) setInfo objectfield.tpe
                      staticfield.addAnnotation(definitions.StaticClass)
                      hostClass.info.decls enter staticfield
                      staticfield
                    } else NoSymbol
                  }
                  val fieldDescr  = toTypeKind(staticfield.tpe).getDescriptor
                  val opc  = if (sym.isGetter) asm.Opcodes.GETSTATIC else asm.Opcodes.PUTSTATIC
                  val insn = new asm.tree.FieldInsnNode(opc,internalName(hostClass), fieldName, fieldDescr)

                  if (opc == asm.Opcodes.GETSTATIC) {
                    emit(insn) // GETSTATIC `hostClass`.`accessed`
                  } else {
                    assert(sym.isSetter,
                           "neither getter nor setter when emitting (GET/PUT)-static, during genApply().")
                    genLoadArguments(args, paramTKs(app)) // push setter's argument
                    emit(insn) // PUTSTATIC `hostClass`.`accessed`
                    // push false
                    bc.boolconst(false) // TODO what purpose does this serve ...
                  }
                } // end of emitLoadStaticField()

            emitLoadStaticField()

          case app @ Apply(fun, args) =>
            val sym = fun.symbol

            if (sym.isLabel) {  // jump to a label
              genLoadLabelArguments(args, labelDef(sym), app.pos)
              bc goTo programPoint(sym)
            } else if (isPrimitive(sym)) { // primitive method call
              generatedType = genPrimitiveOp(app, expectedType)
            } else {  // normal method call

                  def genNormalMethodCall(): BType = {

                    val invokeStyle =
                      if (sym.isStaticMember) Static(false)
                      else if (sym.isPrivate || sym.isClassConstructor) Static(true)
                      else Dynamic;

                    if (invokeStyle.hasInstance) {
                      genLoadQualifier(fun)
                    }

                    genLoadArguments(args, paramTKs(app))

                    // In "a couple cases", squirrel away a extra information (hostClass, targetTypeKind). TODO Document what "in a couple cases" refers to.
                    var hostClass:      Symbol = null
                    var targetTypeKind: BType  = null
                    fun match {
                      case Select(qual, _) =>
                        val qualSym = findHostClass(qual.tpe, sym)
                        if (qualSym == ArrayClass) { targetTypeKind = toTypeKind(qual.tpe) }
                        else { hostClass = qualSym }

                        log(
                          if (qualSym == ArrayClass) "Stored target type kind " + targetTypeKind + " for " + sym.fullName
                          else s"Set more precise host class for ${sym.fullName} hostClass: $qualSym"
                        )
                      case _ =>
                    }
                    if((targetTypeKind != null) && (sym == definitions.Array_clone) && invokeStyle.isDynamic) {
                      val target: String = targetTypeKind.getInternalName
                      val mdesc_arrayClone  = "()Ljava/lang/Object;"
                      bc.invokevirtual(target, "clone", mdesc_arrayClone)
                    }
                    else {
                      genCallMethod(sym, invokeStyle, hostClass)
                    }

                    if (sym.isClassConstructor) UNIT
                    else toTypeKind(sym.info.resultType);

                  } // end of genNormalMethodCall()

              // TODO if (sym == ctx1.method.symbol) { ctx1.method.recursive = true }
              generatedType = genNormalMethodCall()
            }

        }

        generatedType
      } // end of GenBCode's genApply()

      private def genArrayValue(av: ArrayValue): BType = {
        val ArrayValue(tpt @ TypeTree(), elems) = av

        val elmKind       = toTypeKind(tpt.tpe)
        var generatedType = arrayOf(elmKind)

        lineNumber(av)
        bc iconst   elems.length
        bc newarray elmKind

        var i = 0
        var rest = elems
        while (!rest.isEmpty) {
          bc dup     generatedType
          bc iconst  i
          genLoad(rest.head, elmKind)
          bc astore  elmKind
          rest = rest.tail
          i = i + 1
        }

        generatedType
      }

      /**
       *  A Match node contains one or more case clauses,
       * each case clause lists one or more Int values to use as keys, and a code block.
       * Except the "default" case clause which (if it exists) doesn't list any Int key.
       *
       * On a first pass over the case clauses, we flatten the keys and their targets (the latter represented with asm.Labels).
       * That representation allows JCodeMethodV to emit a lookupswitch or a tableswitch.
       *
       * On a second pass, we emit the switch blocks, one for each different target. */
      private def genMatch(tree: Match): BType = {
        lineNumber(tree)
        genLoad(tree.selector, INT)
        val generatedType = toTypeKind(tree.tpe)

        var flatKeys: List[Int]       = Nil
        var targets:  List[asm.Label] = Nil
        var default:  asm.Label       = null
        var switchBlocks: List[Pair[asm.Label, Tree]] = Nil

        // collect switch blocks and their keys, but don't emit yet any switch-block.
        for (caze @ CaseDef(pat, guard, body) <- tree.cases) {
          assert(guard == EmptyTree, guard)
          val switchBlockPoint = new asm.Label
          switchBlocks ::= Pair(switchBlockPoint, body)
          pat match {
            case Literal(value) =>
              flatKeys ::= value.intValue
              targets  ::= switchBlockPoint
            case Ident(nme.WILDCARD) =>
              assert(default == null, "multiple default targets in a Match node, at " + tree.pos)
              default = switchBlockPoint
            case Alternative(alts) =>
              alts foreach {
                case Literal(value) =>
                  flatKeys ::= value.intValue
                  targets  ::= switchBlockPoint
                case _ =>
                  abort("Invalid alternative in alternative pattern in Match node: " + tree + " at: " + tree.pos)
              }
            case _ =>
              abort("Invalid pattern in Match node: " + tree + " at: " + tree.pos)
          }
        }
        bc.emitSWITCH(mkArrayReverse(flatKeys), mkArray(targets.reverse), default, MIN_SWITCH_DENSITY)

        // emit switch-blocks.
        val postMatch = new asm.Label
        for (sb <- switchBlocks.reverse) {
          val Pair(caseLabel, caseBody) = sb
          markProgramPoint(caseLabel)
          genLoad(caseBody, generatedType)
          bc goTo postMatch
        }

        markProgramPoint(postMatch)
        generatedType
      }

      def genBlock(tree: Block, expectedType: BType) {
        val Block(stats, expr) = tree
        val savedScope = varsInScope
        varsInScope = Nil
        stats foreach genStat
        genLoad(expr, expectedType)
        val end = currProgramPoint()
        if(emitVars) { // add entries to LocalVariableTable JVM attribute
          for (Pair(sym, start) <- varsInScope.reverse) { emitLocalVarScope(sym, start, end) }
        }
        varsInScope = savedScope
      }

      def adapt(from: BType, to: BType): Unit = {
        if (!conforms(from, to) && !(from.isNullType && to.isNothingType)) {
          to match {
            case UNIT => bc drop from
            case _    => bc.emitT2T(from, to)
          }
        } else if(from.isNothingType) {
          emit(asm.Opcodes.ATHROW) // ICode enters here into enterIgnoreMode, we'll rely instead on DCE at ClassNode level.
        } else if (from.isNullType) {
          bc drop from
          mnode.visitInsn(asm.Opcodes.ACONST_NULL)
        }
        else if (from == ThrowableReference && !conforms(ThrowableReference, to)) {
          bc checkCast to
        }
        else (from, to) match  {
          case (BYTE, LONG) | (SHORT, LONG) | (CHAR, LONG) | (INT, LONG) => bc.emitT2T(INT, LONG)
          case _ => ()
        }
      }

      /** Emit code to Load the qualifier of `tree` on top of the stack. */
      def genLoadQualifier(tree: Tree) {
        lineNumber(tree)
        tree match {
          case Select(qualifier, _) => genLoad(qualifier, toTypeKind(qualifier.tpe))
          case _                    => abort("Unknown qualifier " + tree)
        }
      }

      /** Generate code that loads args into label parameters. */
      def genLoadLabelArguments(args: List[Tree], lblDef: LabelDef, gotoPos: Position) {
        assert(args forall { a => !a.hasSymbol || a.hasSymbolWhich( s => !s.isLabel) }, "SI-6089 at: " + gotoPos) // SI-6089

        val aps = {
          val params: List[Symbol] = lblDef.params.map(_.symbol)
          assert(args.length == params.length, "Wrong number of arguments in call to label at: " + gotoPos)

              def isTrivial(kv: (Tree, Symbol)) = kv match {
                case (This(_), p) if p.name == nme.THIS     => true
                case (arg @ Ident(_), p) if arg.symbol == p => true
                case _                                      => false
              }

          (args zip params) filterNot isTrivial
        }

        // first push *all* arguments. This makes sure muliple uses of the same labelDef-var will all denote the (previous) value.
        aps foreach { case (arg, param) => genLoad(arg, locals(param).tk) } // `locals` is known to contain `param` because `genDefDef()` visited `labelDefsAtOrUnder`

        // second assign one by one to the LabelDef's variables.
        aps.reverse foreach {
          case (_, param) =>
            // TODO FIXME a "this" param results from tail-call xform. If so, the `else` branch seems perfectly fine. And the `then` branch must be wrong.
            if (param.name == nme.THIS) mnode.visitVarInsn(asm.Opcodes.ASTORE, 0)
            else store(param)
        }

      }

      def genLoadArguments(args: List[Tree], btpes: List[BType]) {
        (args zip btpes) foreach { case (arg, btpe) => genLoad(arg, btpe) }
      }

      def genLoadModule(tree: Tree): BType = {
        // Working around SI-5604.  Rather than failing the compile when we see a package here, check if there's a package object.
        val module = (
          if (!tree.symbol.isPackageClass) tree.symbol
          else tree.symbol.info.member(nme.PACKAGE) match {
            case NoSymbol => assert(false, "Cannot use package as value: " + tree) ; NoSymbol
            case s        => debugwarn("Bug: found package class where package object expected.  Converting.") ; s.moduleClass
          }
        )
        lineNumber(tree)
        genLoadModule(module)
        asmClassType(module)
      }

      def genLoadModule(module: Symbol) {
        if (claszSymbol == module.moduleClass && jMethodName != nme.readResolve.toString) {
          mnode.visitVarInsn(asm.Opcodes.ALOAD, 0)
        } else {
          mnode.visitFieldInsn(
            asm.Opcodes.GETSTATIC,
            internalName(module) /* + "$" */ ,
            strMODULE_INSTANCE_FIELD,
            toTypeKind(module.tpe).getDescriptor
          )
        }
      }

      def genConversion(from: BType, to: BType, cast: Boolean) = {
        if (cast) { bc.emitT2T(from, to) }
        else {
          bc drop from
          bc boolconst (from == to)
        }
      }

      def genCast(from: BType, to: BType, cast: Boolean) {
        if(cast) { bc checkCast  to }
        else     { bc isInstance to }
      }

      /** Is the given symbol a primitive operation? */
      def isPrimitive(fun: Symbol): Boolean = scalaPrimitives.isPrimitive(fun)

      /** Generate coercion denoted by "code" */
      def genCoercion(code: Int) = {
        import scalaPrimitives._
        (code: @switch) match {
          case B2B | S2S | C2C | I2I | L2L | F2F | D2D => ()
          case _ =>
            val from = coercionFrom(code)
            val to   = coercionTo(code)
            bc.emitT2T(from, to)
        }
      }

      /** The Object => String overload. */
      private lazy val String_valueOf: Symbol = getMember(StringModule, nme.valueOf) filter (sym =>
        sym.info.paramTypes match {
          case List(pt) => pt.typeSymbol == ObjectClass
          case _        => false
        }
      )

      def genStringConcat(tree: Tree): BType = {
        lineNumber(tree)
        liftStringConcat(tree) match {

          // Optimization for expressions of the form "" + x.  We can avoid the StringBuilder.
          case List(Literal(Constant("")), arg) =>
            genLoad(arg, ObjectReference)
            genCallMethod(String_valueOf, Static(false))

          case concatenations =>
            bc.genStartConcat
            for (elem <- concatenations) {
              val kind = toTypeKind(elem.tpe)
              genLoad(elem, kind)
              bc.genStringConcat(kind)
            }
            bc.genEndConcat

        }

        StringReference
      }

      def genCallMethod(method: Symbol, style: InvokeStyle, hostClass0: Symbol = null) {

        val siteSymbol = claszSymbol
        val hostSymbol = if(hostClass0 == null) method.owner else hostClass0;
        val methodOwner = method.owner
        // info calls so that types are up to date; erasure may add lateINTERFACE to traits
        hostSymbol.info ; methodOwner.info

            def isInterfaceCall(sym: Symbol) = (
                 sym.isInterface && methodOwner != definitions.ObjectClass
              || sym.isJavaDefined && sym.isNonBottomSubClass(definitions.ClassfileAnnotationClass)
            )

            def isAccessibleFrom(target: Symbol, site: Symbol): Boolean = {
              target.isPublic || target.isProtected && {
                (site.enclClass isSubClass target.enclClass) ||
                (site.enclosingPackage == target.privateWithin)
              }
            }

        // whether to reference the type of the receiver or
        // the type of the method owner (if not an interface!)
        val useMethodOwner = (
             style != Dynamic
          || !isInterfaceCall(hostSymbol) && isAccessibleFrom(methodOwner, siteSymbol)
          || hostSymbol.isBottomClass
        )
        val receiver = if (useMethodOwner) methodOwner else hostSymbol
        val jowner   = internalName(receiver)
        val jname    = method.javaSimpleName.toString
        val jtype    = asmMethodType(method).getDescriptor

            def dbg(invoke: String) {
              debuglog("%s %s %s.%s:%s".format(invoke, receiver.accessString, jowner, jname, jtype))
            }

            def initModule() {
              // we initialize the MODULE$ field immediately after the super ctor
              if (isStaticModule(siteSymbol) && !isModuleInitialized &&
                  jMethodName == INSTANCE_CONSTRUCTOR_NAME &&
                  jname == INSTANCE_CONSTRUCTOR_NAME) {
                isModuleInitialized = true
                mnode.visitVarInsn(asm.Opcodes.ALOAD, 0)
                mnode.visitFieldInsn(
                  asm.Opcodes.PUTSTATIC,
                  thisName,
                  strMODULE_INSTANCE_FIELD,
                  "L" + thisName + ";"
                )
              }
            }

        style match {
          case Static(true)                         => dbg("invokespecial");  bc.invokespecial  (jowner, jname, jtype)
          case Static(false)                        => dbg("invokestatic");   bc.invokestatic   (jowner, jname, jtype)
          case Dynamic if isInterfaceCall(receiver) => dbg("invokinterface"); bc.invokeinterface(jowner, jname, jtype)
          case Dynamic                              => dbg("invokevirtual");  bc.invokevirtual  (jowner, jname, jtype)
          case SuperCall(_)                         =>
            dbg("invokespecial")
            bc.invokespecial(jowner, jname, jtype)
            initModule()
        }

      } // end of genCallMethod()

      /** Generate the scala ## method. */
      def genScalaHash(tree: Tree): BType = {
        genLoadModule(ScalaRunTimeModule) // TODO why load ScalaRunTimeModule if ## has InvokeStyle of Static(false) ?
        genLoad(tree, ObjectReference)
        genCallMethod(hashMethodSym, Static(false))

        INT
      }

      /**
       * Returns a list of trees that each should be concatenated, from left to right.
       * It turns a chained call like "a".+("b").+("c") into a list of arguments.
       */
      def liftStringConcat(tree: Tree): List[Tree] = tree match {
        case Apply(fun @ Select(larg, method), rarg) =>
          if (isPrimitive(fun.symbol) &&
              scalaPrimitives.getPrimitive(fun.symbol) == scalaPrimitives.CONCAT)
            liftStringConcat(larg) ::: rarg
          else
            tree :: Nil
        case _ =>
          tree :: Nil
      }

      /** Some useful equality helpers. */
      def isNull(t: Tree) = {
        t match {
          case Literal(Constant(null)) => true
          case _ => false
        }
      }

      /* If l or r is constant null, returns the other ; otherwise null */
      def ifOneIsNull(l: Tree, r: Tree) = if (isNull(l)) r else if (isNull(r)) l else null

      /** Emit code to compare the two top-most stack values using the 'op' operator. */
      private def genCJUMP(success: asm.Label, failure: asm.Label, op: TestOp, tk: BType) {
        if(tk.isIntSizedType) { // BOOL, BYTE, CHAR, SHORT, or INT
          bc.emitIF_ICMP(op, success)
        } else if(tk.isRefOrArrayType) { // REFERENCE(_) | ARRAY(_)
          bc.emitIF_ACMP(op, success)
        } else {
          (tk: @unchecked) match {
            case LONG   => emit(asm.Opcodes.LCMP)
            case FLOAT  =>
              if (op == LT || op == LE) emit(asm.Opcodes.FCMPG)
              else                      emit(asm.Opcodes.FCMPL)
            case DOUBLE =>
              if (op == LT || op == LE) emit(asm.Opcodes.DCMPG)
              else                      emit(asm.Opcodes.DCMPL)
          }
          bc.emitIF(op, success)
        }
        bc goTo failure
      }

      /** Emits code to compare (and consume) stack-top and zero using the 'op' operator */
      private def genCZJUMP(success: asm.Label, failure: asm.Label, op: TestOp, tk: BType) {
        if(tk.isIntSizedType) { // BOOL, BYTE, CHAR, SHORT, or INT
          bc.emitIF(op, success)
        } else if(tk.isRefOrArrayType) { // REFERENCE(_) | ARRAY(_)
          // @unchecked because references aren't compared with GT, GE, LT, LE.
          (op : @unchecked) match {
            case EQ => bc emitIFNULL    success
            case NE => bc emitIFNONNULL success
          }
        } else {
          (tk: @unchecked) match {
            case LONG   =>
              emit(asm.Opcodes.LCONST_0)
              emit(asm.Opcodes.LCMP)
            case FLOAT  =>
              emit(asm.Opcodes.FCONST_0)
              if (op == LT || op == LE) emit(asm.Opcodes.FCMPG)
              else                      emit(asm.Opcodes.FCMPL)
            case DOUBLE =>
              emit(asm.Opcodes.DCONST_0)
              if (op == LT || op == LE) emit(asm.Opcodes.DCMPG)
              else                      emit(asm.Opcodes.DCMPL)
          }
          bc.emitIF(op, success)
        }
        bc goTo failure
      }

      val testOpForPrimitive: Array[TestOp] = Array(EQ, NE, EQ, NE, LT, LE, GE, GT)

      /**
       * Generate code for conditional expressions.
       * The jump targets success/failure of the test are `then-target` and `else-target` resp.
       */
      private def genCond(tree: Tree, success: asm.Label, failure: asm.Label) {

            def genComparisonOp(l: Tree, r: Tree, code: Int) {
              val op: TestOp = testOpForPrimitive(code - scalaPrimitives.ID)
              // special-case reference (in)equality test for null (null eq x, x eq null)
              var nonNullSide: Tree = null
              if (scalaPrimitives.isReferenceEqualityOp(code) &&
                  { nonNullSide = ifOneIsNull(l, r); nonNullSide != null }
              ) {
                genLoad(nonNullSide, ObjectReference)
                genCZJUMP(success, failure, op, ObjectReference)
              }
              else {
                val tk = maxType(toTypeKind(l.tpe), toTypeKind(r.tpe))
                genLoad(l, tk)
                genLoad(r, tk)
                genCJUMP(success, failure, op, tk)
              }
            }

            def default() = {
              genLoad(tree, BOOL)
              genCZJUMP(success, failure, NE, BOOL)
            }

        lineNumber(tree)
        tree match {

          case Apply(fun, args) if isPrimitive(fun.symbol) =>
            import scalaPrimitives.{ ZNOT, ZAND, ZOR, EQ, getPrimitive }

            // lhs and rhs of test
            lazy val Select(lhs, _) = fun
            val rhs = if(args.isEmpty) EmptyTree else args.head; // args.isEmpty only for ZNOT

                def genZandOrZor(and: Boolean) = { // TODO WRONG
                  // reaching "keepGoing" indicates the rhs should be evaluated too (ie not short-circuited).
                  val keepGoing = new asm.Label

                  if (and) genCond(lhs, keepGoing, failure)
                  else     genCond(lhs, success,   keepGoing)

                  markProgramPoint(keepGoing)
                  genCond(rhs, success, failure)
                }

            getPrimitive(fun.symbol) match {
              case ZNOT   => genCond(lhs, failure, success)
              case ZAND   => genZandOrZor(and = true)
              case ZOR    => genZandOrZor(and = false)
              case code   =>
                // TODO !!!!!!!!!! isReferenceType, in the sense of TypeKind? (ie non-array, non-boxed, non-nothing, may be null)
                if (scalaPrimitives.isUniversalEqualityOp(code) && toTypeKind(lhs.tpe).hasObjectSort) {
                  // `lhs` has reference type
                  if (code == EQ) genEqEqPrimitive(lhs, rhs, success, failure)
                  else            genEqEqPrimitive(lhs, rhs, failure, success)
                }
                else if (scalaPrimitives.isComparisonOp(code))
                  genComparisonOp(lhs, rhs, code)
                else
                  default
            }

          case _ => default
        }

      } // end of genCond()

      /**
       * Generate the "==" code for object references. It is equivalent of
       * if (l eq null) r eq null else l.equals(r);
       *
       * @param l       left-hand-side  of the '=='
       * @param r       right-hand-side of the '=='
       */
      def genEqEqPrimitive(l: Tree, r: Tree, success: asm.Label, failure: asm.Label) {

        val areSameFinals = l.tpe.isFinalType && r.tpe.isFinalType && (l.tpe =:= r.tpe)

        /** True if the equality comparison is between values that require the use of the rich equality
          * comparator (scala.runtime.Comparator.equals). This is the case when either side of the
          * comparison might have a run-time type subtype of java.lang.Number or java.lang.Character.
          * When it is statically known that both sides are equal and subtypes of Number of Character,
          * not using the rich equality is possible (their own equals method will do ok.)*/
        val mustUseAnyComparator: Boolean = {
          !areSameFinals && platform.isMaybeBoxed(l.tpe.typeSymbol) && platform.isMaybeBoxed(r.tpe.typeSymbol)
        }

        if (mustUseAnyComparator) {
          val equalsMethod = {
              def default = platform.externalEquals
              platform match {
                case x: JavaPlatform =>
                  import x._
                    if (l.tpe <:< BoxedNumberClass.tpe) {
                      if (r.tpe <:< BoxedNumberClass.tpe) externalEqualsNumNum
                      else if (r.tpe <:< BoxedCharacterClass.tpe) externalEqualsNumChar
                      else externalEqualsNumObject
                    }
                    else default

                case _ => default
              }
            }
          genLoad(l, ObjectReference)
          genLoad(r, ObjectReference)
          genCallMethod(equalsMethod, Static(false))
          genCZJUMP(success, failure, NE, BOOL)
        }
        else {
          if (isNull(l)) {
            // null == expr -> expr eq null
            genLoad(r, ObjectReference)
            genCZJUMP(success, failure, EQ, ObjectReference)
          } else if (isNull(r)) {
            // expr == null -> expr eq null
            genLoad(l, ObjectReference)
            genCZJUMP(success, failure, EQ, ObjectReference)
          } else {
            // l == r -> if (l eq null) r eq null else l.equals(r)
            val eqEqTempLocal = makeLocal(AnyRefReference, nme.EQEQ_LOCAL_VAR)
            val lNull    = new asm.Label
            val lNonNull = new asm.Label

            genLoad(l, ObjectReference)
            genLoad(r, ObjectReference)
            store(eqEqTempLocal)
            bc dup ObjectReference
            genCZJUMP(lNull, lNonNull, EQ, ObjectReference)

            markProgramPoint(lNull)
            bc drop ObjectReference
            load(eqEqTempLocal)
            genCZJUMP(success, failure, EQ, ObjectReference)

            markProgramPoint(lNonNull)
            load(eqEqTempLocal)
            genCallMethod(Object_equals, Dynamic)
            genCZJUMP(success, failure, NE, BOOL)
          }
        }
      }

      /** Does this tree have a try-catch block? */
      def mayCleanStack(tree: Tree): Boolean = tree exists { t => t.isInstanceOf[Try] }

      /** @can-multi-thread **/
      def getMaxType(ts: List[Type]): BType = {
        ts map toTypeKind reduceLeft maxType
      }

      abstract class Cleanup(val value: AnyRef) {
        def contains(x: AnyRef) = value == x
      }
      case class MonitorRelease(v: Symbol) extends Cleanup(v) { }
      case class Finalizer(f: Tree) extends Cleanup (f) { }

      case class Local(tk: BType, name: String, idx: Int, isSynth: Boolean)

      trait EHClause
      case class NamelessEH(typeToDrop: BType,  caseBody: Tree) extends EHClause
      case class BoundEH    (patSymbol: Symbol, caseBody: Tree) extends EHClause

    } // end of class PlainClassBuilder

  } // end of class BCodePhase

} // end of class GenBCode
