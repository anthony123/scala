/* NSC -- new Scala compiler
 * Copyright 2005-2012 LAMP/EPFL
 * @author  Martin Odersky
 */


package scala.tools.nsc
package backend
package jvm

import scala.collection.{ mutable, immutable }
import scala.tools.nsc.symtab._
import scala.annotation.switch

import scala.tools.asm
import asm.tree.{FieldNode, MethodInsnNode, MethodNode}
import collection.immutable.HashMap
import collection.convert.Wrappers.JListWrapper

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
 *        All the can-multi-thread operations that pipeline-2 performs can also run during pipeline-1, in fact some of them do.
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
 *        A pipeline-2 worker performs intra-method optimizations on the ASM tree.
 *        In detail, `Worker2.visit()` instantiates a `BCodeOpt.BCodeCleanser` to perform those optimizations.
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
abstract class GenBCode extends BCodeOptInter {
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

    // number of woker threads for pipeline-2 (the one in charge of most optimizations except inlining).
    val MAX_THREADS = scala.math.min(
      if(settings.isIntraMethodOptimizOn) 64 else 8,
      java.lang.Runtime.getRuntime.availableProcessors
    )

    private val woStarted = new java.util.concurrent.ConcurrentHashMap[Long, Long]  // debug
    private val woExited  = new java.util.concurrent.ConcurrentHashMap[Long, Item2] // debug

    private var bytecodeWriter  : BytecodeWriter   = null
    private var mirrorCodeGen   : JMirrorBuilder   = null
    private var beanInfoCodeGen : JBeanInfoBuilder = null

    /* ---------------- q1 ---------------- */

    case class Item1(arrivalPos: Int, cd: ClassDef, cunit: CompilationUnit) {
      def isPoison = { arrivalPos == Int.MaxValue }
    }
    private val poison1 = Item1(Int.MaxValue, null, null)
    private val q1 = new _root_.java.util.concurrent.LinkedBlockingQueue[Item1]

    /* ---------------- q2 ---------------- */

    case class Item2(arrivalPos:   Int,
                     mirror:       SubItem2NonPlain,
                     plain:        SubItem2Plain,
                     bean:         SubItem2NonPlain,
                     lateClosures: List[asm.tree.ClassNode]) {
      def isPoison = { arrivalPos == Int.MaxValue }
    }

    // for inter-procedural optimization, we'd like to start working first on "large" classes for better load balanching of Worker2 threads
    private val i2LargeClassesFirst = new _root_.java.util.Comparator[Item2] {
      override def compare(a: Item2, b: Item2): Int = {
        if(a.isPoison) { return  1 }
        if(b.isPoison) { return -1 }
        val aSize = a.plain.cnode.methods.size()
        val bSize = b.plain.cnode.methods.size()

        if     (aSize  > bSize) -1
        else if(aSize == bSize)  0
        else 1
      }
    }

    // for intra-procedural or no optimization, we'd like to process classes according to arrival order, so as to serialize them faster.
    private val i2ArrivalOrder = new _root_.java.util.Comparator[Item2] {
      override def compare(a: Item2, b: Item2): Int = {
        val aSize = a.arrivalPos
        val bSize = b.arrivalPos

        if     (aSize <  bSize) -1
        else if(aSize == bSize)  0
        else 1
      }
    }
    private val poison2 = Item2(Int.MaxValue, null, null, null, null)
    private val q2 =
      new _root_.java.util.concurrent.PriorityBlockingQueue[Item2](
        1000,
        if(settings.isInterBasicOptimizOn) i2LargeClassesFirst else i2ArrivalOrder
      )

    /* ---------------- q3 ---------------- */

    case class Item3(arrivalPos: Int, mirror: SubItem3, plain: SubItem3, bean: SubItem3) {
      def isPoison  = { arrivalPos == Int.MaxValue }
      /*
       * The first condition below (plain == null) implies WholeProgramAnalysis did the eliding,
       * the second condition holds when an intra-class optimization did the eliding
       * (during BCodeCleanser.cleanseClass(), running after whole-program).
       * */
      def wasElided = {
        (plain == null) ||
        elidedClasses.contains(lookupRefBType(plain.jclassName)) }
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
     *  must-single-thread (because it relies on typer).
     */
    class Worker1(needsOutfileForSymbol: Boolean) extends _root_.java.lang.Runnable {

      def run() {
        while (true) {
          val item = q1.take
          if(item.isPoison) {
            for(i <- 1 to MAX_THREADS) { q2 put poison2 } // explanation in Worker2.run() as to why MAX_THREADS poison pills are needed on queue-2.
            return
          }
          else {
            try   { visit(item) }
            catch {
              case ex: Throwable =>
                ex.printStackTrace()
                error("Error while emitting " + item.cunit.source +  "\n"  + ex.getMessage)
            }
          }
        }
      }

      val caseInsensitively = mutable.Map.empty[String, Symbol]
      var lateClosuresCount = 0

      /**
       *  Checks for duplicate internal names case-insensitively,
       *  builds ASM ClassNodes for mirror, plain, bean, and late-closure classes;
       *  enqueues them in queue-2, and
       *  incrementally populates dclosure-maps for the Late-Closure-Classes just built.
       *
       * */
      def visit(item: Item1) {
        val Item1(arrivalPos, cd, cunit) = item
        val claszSymbol = cd.symbol

        // GenASM checks this before classfiles are emitted, https://github.com/scala/scala/commit/e4d1d930693ac75d8eb64c2c3c69f2fc22bec739
        val lowercaseJavaClassName = claszSymbol.javaClassName.toLowerCase
        caseInsensitively.get(lowercaseJavaClassName) match {
          case None =>
            caseInsensitively.put(lowercaseJavaClassName, claszSymbol)
          case Some(dupClassSym) =>
            item.cunit.warning(
              claszSymbol.pos,
              s"Class ${claszSymbol.javaClassName} differs only in case from ${dupClassSym.javaClassName}. " +
              "Such classes will overwrite one another on case-insensitive filesystems."
            )
        }

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
          val outF = getOutFolder(needsOutfileForSymbol, cd.symbol, pcb.thisName, cunit)
          assert(pcb.thisName == pcb.cnode.name)
          SubItem2Plain(label, pcb.cnode, outF)
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

        val item2 = Item2(arrivalPos + lateClosuresCount, mirrorC, plainC, beanC, pcb.lateClosures)
        lateClosuresCount += pcb.lateClosures.size

        q2 put item2

        assert(pcb.lateClosures.isEmpty == pcb.closuresForDelegates.isEmpty)

        if(pcb.lateClosures.nonEmpty) {
          populateDClosureMaps(pcb)
        }

      } // end of method visit(Item1)

      /**
       *  Adds entries to `closuRepo.dclosures` and `closuRepo.endpoint` for the Late-Closure-Classes just built.
       *
       *  After `BCodePhase.Worker1.visit()` has run
       *    (to recap, Worker1 takes ClassDefs as input and lowers them to ASM ClassNodes)
       *  for a plain class C, we know that all instantiations of C's Late-Closure-Classes are enclosed in C.
       *    (the only exceptions to this resulted in the past from a rewriting not performed that way anymore,
       *     by which DelayedInit delayed-initialization-statements would be transplanted to a separate closure-class;
       *     nowadays the rewriting is such that those statements remain in the class originally enclosing them,
       *     but in a different method).
       *     @see [[scala.tools.nsc.transform.Constructors]]'s `delayedEndpointDef()`
       *
       *  Looking ahead, `BCodeOptInter.WholeProgramAnalysis.inlining()`
       *  may break the property above (ie inlining may result in lambda usages,
       *  be they instantiations or endpoint-invocations, being transplanted to a class different from that
       *  originally enclosing them). Tracking those cases is the job of
       *  `BCodeOptInter.closuRepo.trackClosureUsageIfAny()`
       *
       *  Coming back to the property holding
       *  right after `BCodePhase.Worker1.visit()` has run for a plain class C
       *    (the property that all instantiations of C's Late-Closure-Classes are enclosed in C)
       *  details about that property are provided by map `dclosures` (populated by `genLateClosure()`).
       *  That map lets us know, given a plain class C, the Late-Closure-Classes it's responsible for.
       *
       * */
      private def populateDClosureMaps(pcb: PlainClassBuilder) {

        assert(pcb.lateClosures.size == pcb.closuresForDelegates.size)

        val masterBT = lookupRefBType(pcb.cnode.name) // this is the "master class" responsible for "its" dclosures

        // add entry to `closuRepo.endpoint`
        val isDelegateMethodName = (pcb.closuresForDelegates.values map (dce => dce.epName)).toSet
        val candidateMethods = (pcb.cnode.toMethodList filter (mn => isDelegateMethodName(mn.name)))
        for(dClosureEndpoint <- pcb.closuresForDelegates.values) {
          val candidates: List[MethodNode] =
            for(
              mn <- candidateMethods;
              if (mn.name == dClosureEndpoint.epName) && (mn.desc == dClosureEndpoint.epMT.getDescriptor)
            ) yield mn;

          assert(candidates.nonEmpty && candidates.tail.isEmpty)
          val delegateMethodNode = candidates.head

          assert(
            asm.optimiz.Util.isPublicMethod(delegateMethodNode),
            "PlainClassBuilder.genDefDef() forgot to make public: " + methodSignature(masterBT, delegateMethodNode)
          )

          val delegateMethodRef = MethodRef(masterBT, delegateMethodNode)
          closuRepo.endpoint.put(dClosureEndpoint.closuBT, delegateMethodRef)
        }

        // add entry to `closuRepo.dclosures`
        for(dClosureEndpoint <- pcb.closuresForDelegates.values) {
          val others = closuRepo.dclosures.getOrElse(masterBT, Nil)
          closuRepo.dclosures.put(masterBT, dClosureEndpoint.closuBT :: others)
        }

      } // end of method populateDClosureMaps()


    } // end of class BCodePhase.Worker1

    /**
     *  Pipeline that takes ClassNodes from queue-2. The unit of work depends on the optimization level:
     *
     *    (a) no optimization involves:
     *          - removing dead code, and then
     *          - converting the plain ClassNode to byte array and placing it on queue-3
     *
     *    (b) with intra-procedural optimization on,
     *          - cleanseClass() is invoked on the plain class, and then
     *          - the plain class is serialized as above (ending up in queue-3)
     *
     *    (c) with inter-procedural optimization on,
     *          - cleanseClass() runs first.
     *            The difference with (b) however has to do with master-classes and their dclosures.
     *            In the inter-procedural case, they are processed as a single (larger) unit of work by cleanseClass.
     *            That's why in this case "large classes" (see `i2LargeClassesFirst`) bubble up to queue-2's head.
     *          - once that (larger) unit of work is complete, all of its constituent classes are placed on queue-3.
     *
     *  can-multi-thread
     */
    class Worker2 extends _root_.java.lang.Runnable {

      def run() {
        val id = java.lang.Thread.currentThread.getId
        woStarted.put(id, id)

        while (true) {
          val item = q2.take
          if(item.isPoison) {
            woExited.put(id, item)
            q3 put poison3 // therefore queue-3 will contain as many poison pills as pipeline-2 threads.
            // to terminate all pipeline-2 workers, queue-1 must contain as many poison pills as pipeline-2 threads.
            return
          }
          else {
            try   { visit(item) }
            catch {
              case ex: Throwable =>
                ex.printStackTrace()
                error("Error while emitting " + item.plain.cnode.name +  "\n"  + ex.getMessage)
            }
          }
        }
      }

      /**
       *  Performs optimizations using task parallelism (a task has exclusive acceess to ASM ClassNodes
       *  that need to be mutated in-tandem, for example a master class and the dclosures it's responsible for).
       *  After mutation is over, addds the ClassNode(s) to queue-3.
       * */
      def visit(item: Item2) {

        val cleanser = new BCodeCleanser(item.plain.cnode)

        if(settings.isIntraMethodOptimizOn) {
          cleanser.cleanseClass()   // cleanseClass() may mutate dclosures cnode is responsible for
        } else {
          cleanser.removeDeadCode() // no optimization, but removing dead code still desirable
          // TODO cleanser.squashOuter()    // squashOuter() may mutate dclosures cnode is responsible for
          // TODO needed? cleanser.ppCollapser.transform(cName, mnode)    // propagate a DROP to the instruction(s) that produce the value in question, drop the DROP.
        }

        addToQ3(item)

      } // end of method visit(Item2)

      /**
       *  Item2 has a field for Late-Closure-Classes so as to delay adding those LCCs to queue-3
       *  until after all optimizations triggered by the master class have been completed
       *  (optimizations that in general mutate those LCCs).
       *  Otherwise the ClassNode for a delegating-closure could be written to disk too early.
       *
       *  Both live and elided dclosures go to q3: the arrivalPos of elided ones is required for progress in drainQ3()
       *
       * */
      private def addToQ3(item: Item2) {

            def getByteArray(cn: asm.tree.ClassNode): Array[Byte] = {
              val cw = new CClassWriter(extraProc)
              cn.accept(cw)
              cw.toByteArray
            }

        val Item2(arrivalPos, mirror, plain, bean, lateClosures) = item

        // TODO aren't mirror.outFolder , plain.outFolder , and bean.outFolder one and the same? Remove duplicity.

        // -------------- mirror class, if needed --------------
        val mirrorC: SubItem3 =
          if (mirror != null) {
            SubItem3(mirror.label, mirror.jclassName, mirror.jclass.toByteArray(), mirror.outFolder)
          } else null

        // -------------- "plain" class --------------
        val plainC =
          SubItem3(plain.label, plain.cnode.name, getByteArray(plain.cnode), plain.outFolder)

        // -------------- bean info class, if needed --------------
        val beanC: SubItem3 =
          if (bean != null) {
            SubItem3(bean.label, bean.jclassName, bean.jclass.toByteArray(), bean.outFolder)
          } else null

        q3 put Item3(arrivalPos, mirrorC, plainC, beanC)

        // -------------- Late-Closure-Classes, if any --------------
        val outFolder = plain.outFolder
        var lateClosuresCount = 0
        for(lateC <- lateClosures.reverse) {
          lateClosuresCount += 1
          q3 put Item3(arrivalPos + lateClosuresCount, null, SubItem3(lateC.name, lateC.name, getByteArray(lateC), outFolder), null)
        }

      }

    } // end of class BCodePhase.Worker2

    var arrivalPos = 0

    override def run() {

      log(s"Number of early vs late anon-closures, Traditional: ${uncurry.convertedTraditional} , Modern: ${uncurry.convertedModern}")

      arrivalPos = 0 // just in case
      scalaPrimitives.init
      initBCodeTypes()
      clearBCodePhase()

      // initBytecodeWriter invokes fullName, thus we have to run it before the typer-dependent thread is activated.
      bytecodeWriter  = initBytecodeWriter(cleanup.getEntryPoints)
      val needsOutfileForSymbol = bytecodeWriter.isInstanceOf[ClassBytecodeWriter]
      mirrorCodeGen   = new JMirrorBuilder(  needsOutfileForSymbol)
      beanInfoCodeGen = new JBeanInfoBuilder(needsOutfileForSymbol)

      if(settings.isInterBasicOptimizOn) {
        wholeProgramThenWriteToDisk(needsOutfileForSymbol)
      } else {
        buildAndSendToDiskInParallel(needsOutfileForSymbol)
      }

      // closing output files.
      bytecodeWriter.close()

      /* TODO Bytecode can be verified (now that all classfiles have been written to disk)
       *
       * (1) asm.util.CheckAdapter.verify()
       *       public static void verify(ClassReader cr, ClassLoader loader, boolean dump, PrintWriter pw)
       *     passing a custom ClassLoader to verify inter-dependent classes.
       *     Alternatively,
       *       - an offline-bytecode verifier could be used (e.g. Maxine brings one as separate tool).
       *       - -Xverify:all
       *
       * (2) if requested, check-java-signatures, over and beyond the syntactic checks in `getGenericSignature()`
       *
       */

      // clearing maps
      clearBCodeTypes()
      clearBCodePhase()
    }

    private def clearBCodePhase() {
      // no maps to clear, so far
    }

    /**
     *  The workflow where inter-procedural optimizations is ENABLED comprises:
     *    (a) sequentially build all ClassNodes (Worker1 takes care of this)
     *    (b) sequentially perform whole-program analysis on them
     *    (c) run in parallel:
     *          - intra-class (including intra-method) optimizations
     *          - a limited form of inter-class optimizations
     *            (those affecting a master-class and the delegating-closures it's responsible for, details below)
     *    (d) overlapping with (c), write non-elided classes to disk.
     *
     *  A useful distinction of inter-class optimizations involves:
     *    (e) method-inlining and closure-inlining, ie what `BCodeOptInter.WholeProgramAnalysis`  does
     *    (f) the "limited form" referred to above, ie what `BCodeOptInter.DClosureOptimizerImpl` does
     *        Unlike (e), different groups of ClassNodes in (f) can be optimized in parallel,
     *        where a "group" comprises a master-class and the dclosures the master-class is responsible for.
     *
     *  The distinction is useful because it explains why Item2 has a fields for Late-Closure-Classes:
     *  that way, LCCs are added to queue-3 only after all optimizations
     *  triggered by the master class have been completed, including (f).
     *  Otherwise the ClassNode for a delegating-closure could be written to disk too early.
     *
     */
    private def wholeProgramThenWriteToDisk(needsOutfileForSymbol: Boolean) {
      assert(settings.isInterBasicOptimizOn)

      // sequentially
      feedPipeline1()
      (new Worker1(needsOutfileForSymbol)).run()
      (new WholeProgramAnalysis(isMultithread = false)).optimize()

      // optimize different groups of ClassNodes in parallel, once done with each group queue its ClassNodes for disk serialization.
      spawnPipeline2()
      // overlapping with pipeline-2, serialize to disk.
      drainQ3()

    }

    /**
     *  The workflow where inter-procedural optimizations is DISABLED boils down to:
     *  As soon as each individual ClassNode is ready
     *     (if needed intra-class optimized, ok, ok,
     *     optimized along with the Late-Closure-Classes it's responsible for)
     *  it's also ready for disk serialization, ie it's ready to be added to queue-3.
     *
     * */
    private def buildAndSendToDiskInParallel(needsOutfileForSymbol: Boolean) {
      assert(!settings.isInterBasicOptimizOn)

      new _root_.java.lang.Thread(new Worker1(needsOutfileForSymbol), "bcode-typer").start()
      spawnPipeline2()
      feedPipeline1()
      drainQ3()

    }

    /** Feed pipeline-1: place all ClassDefs on q1, recording their arrival position. */
    private def feedPipeline1() {
      super.run()
      q1 put poison1
    }

    /** Pipeline from q2 to q3. */
    private def spawnPipeline2(): IndexedSeq[Thread] = {
      for(i <- 1 to MAX_THREADS) yield {
        val w = new Worker2
        val t = new _root_.java.lang.Thread(w, "bcode-worker-" + i)
        t.start()
        t
      }
    }

    /** Pipeline that writes classfile representations to disk. */
    private def drainQ3() {

          def sendToDisk(cfr: SubItem3) {
            if(cfr != null){
              val SubItem3(label, jclassName, jclassBytes, outFolder) = cfr
              val outFile =
                if(outFolder == null) null
                else getFileForClassfile(outFolder, jclassName, ".class")
              bytecodeWriter.writeClass(label, jclassName, jclassBytes, outFile)
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
        if(!moreComing) {
          val queuesOK = (q3.isEmpty && followers.isEmpty)
          if(!queuesOK) {
            error("GenBCode found class files waiting in queues to be written but an error prevented doing so.")
          }
        }
        while(!followers.isEmpty && followers.peek.arrivalPos == expected) {
          val item = followers.poll
          if(!item.wasElided) {
            sendToDisk(item.mirror)
            sendToDisk(item.plain)
            sendToDisk(item.bean)
          }
          expected += 1
        }
      }

      // we're done
      assert(q1.isEmpty, "Some ClassDefs remained in the first queue: "   + q1.toString)
      assert(q2.isEmpty, "Some classfiles remained in the second queue: " + q2.toString)
      assert(q3.isEmpty, "Some classfiles weren't written to disk: "      + q3.toString)

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
      extends BCClassGen
      with    BCAnnotGen
      with    BCInnerClassGen
      with    JAndroidBuilder
      with    BCForwardersGen
      with    BCPickles
      with    BCJGenSigGen {

      // current class
      var cnode: asm.tree.ClassNode  = null
      var thisName: String           = null // the internal name of the class being emitted
      var lateClosures: List[asm.tree.ClassNode] = Nil

          /**
           *  Besides emitting a Late-Closure-Class, `genLateClosure()` collects information
           *  about the endpoint targeted by that dclosure as a `DClosureEndpoint` instance.
           *  That way, once `PlainClassBuilder.genPlainClass()` has built an ASM ClassNode,
           *  the ASM MethodNodes for the endpoints can be added to the `BCodeOptInter.closuRepo.endpoint` map.
           *
           *  @param epName    name of the endpoint method
           *  @param epMT      ASM method type of the endpoint
           *  @param closuBT   BType of the dclosure-class targeting the endpoint
           *  @param closuCtor the only constructor of the dclosure
           *
           * */
          case class DClosureEndpoint(epName: String, epMT: BType, closuBT: BType, closuCtor: MethodNode)

      /**
       *  Allows a hand-off from UnCurry's "set of endpoints as methodsymbols" ie `uncurry.closureDelegates`
       *  to closuRepo.endpoint which maps dclosure to endpoint.
       * */
      val closuresForDelegates = mutable.Map.empty[MethodSymbol, DClosureEndpoint]

      private var claszSymbol: Symbol        = null
      private var isCZParcelable             = false
      private var isCZStaticModule           = false
      private var isCZRemote                 = false
      // current method
      private var mnode: asm.tree.MethodNode = null
      private var jMethodName: String        = null
      private var isMethSymStaticCtor        = false
      private var isMethSymBridge            = false
      private var returnType: BType          = null
      private var methSymbol: Symbol         = null
      private var cgn: CallGraphNode         = null
      // in GenASM this is local to genCode(), ie should get false whenever a new method is emitted (including fabricated ones eg addStaticInit())
      private var isModuleInitialized        = false
      // used by genLoadTry() and genSynchronized()
      private var earlyReturnVar: Symbol     = null
      private var shouldEmitCleanup          = false
      // line numbers
      private var lastEmittedLineNr          = -1

      /* ---------------- caches to avoid asking the same questions over and over to typer ---------------- */

      def paramTKs(app: Apply): List[BType] = {
        val Apply(fun, _)  = app
        val funSym = fun.symbol
        (funSym.info.paramTypes map toTypeKind) // this tracks mentioned inner classes (in innerClassBufferASM)
      }

      def symInfoTK(sym: Symbol): BType = {
        toTypeKind(sym.info) // this tracks mentioned inner classes (in innerClassBufferASM)
      }

      def tpeTK(tree: Tree): BType = { toTypeKind(tree.tpe) }

      def log(msg: => AnyRef) {
        global synchronized { global.log(msg) }
      }

      /* ---------------- Part 1 of program points, ie Labels in the ASM world ---------------- */

      /**
       *  A jump is represented as an Apply node whose symbol denotes a LabelDef, the target of the jump.
       *  The `jumpDest` map is used to:
       *    (a) find the asm.Label for the target, given an Apply node's symbol;
       *    (b) anchor an asm.Label in the instruction stream, given a LabelDef node.
       *  In other words, (a) is necessary when visiting a jump-source, and (b) when visiting a jump-target.
       *  A related map is `labelDef`: it has the same keys as `jumpDest` but its values are LabelDef nodes not asm.Labels.
       *
       */
      private var jumpDest: immutable.Map[ /* LabelDef */ Symbol, asm.Label ] = null
      def programPoint(labelSym: Symbol): asm.Label = {
        assert(labelSym.isLabel, "trying to map a non-label symbol to an asm.Label, at: " + labelSym.pos)
        jumpDest.getOrElse(labelSym, {
          val pp = new asm.Label
          jumpDest += (labelSym -> pp)
          pp
        })
      }

      /**
       *  A program point may be lexically nested (at some depth)
       *    (a) in the try-clause of a try-with-finally expression
       *    (b) in a synchronized block.
       *  Each of the constructs above establishes a "cleanup block" to execute upon
       *  both normal-exit, early-return, and abrupt-termination of the instructions it encloses.
       *
       *  The `cleanups` LIFO queue represents the nesting of active (for the current program point)
       *  pending cleanups. For each such cleanup an asm.Label indicates the start of its cleanup-block.
       *  At any given time during traversal of the method body,
       *  the head of `cleanups` denotes the cleanup-block for the closest enclosing try-with-finally or synchronized-expression.
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
       *  The case of abrupt (ie exceptional) termination is covered by exception handlers
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

      /* ---------------- local variables and params ---------------- */

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
      def makeLocal(sym: Symbol): Local = {
        makeLocal(sym, symInfoTK(sym))
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

      /* ---------------- ---------------- */

      // don't confuse with `fieldStore` and `fieldLoad` which also take a symbol but a field-symbol.
      def store(locSym: Symbol) {
        val Local(tk, _, idx, _) = locals(locSym)
        bc.store(idx, tk)
      }
      def load(locSym: Symbol) {
        val Local(tk, _, idx, _) = locals(locSym)
        bc.load(idx, tk)
      }

      /* ---------------- Part 2 of program points, ie Labels in the ASM world ---------------- */

      /**
       *  The semantics of try-with-finally and synchronized-expr require their cleanup code
       *  to be present in three forms in the emitted bytecode:
       *    (a) as normal-exit code, reached via fall-through from the last program point being protected,
       *    (b) as code reached upon early-return from an enclosed return statement.
       *        The only difference between (a) and (b) is their next program-point:
       *          the former must continue with fall-through while
       *          the latter must continue to the next early-return cleanup (if any, otherwise return from the method).
       *        Otherwise they are identical.
       *    (c) as exception-handler, reached via exceptional control flow,
       *        which rethrows the caught exception once it's done with the cleanup code.
       *
       *  A particular cleanup may in general contain LabelDefs. Care is needed when duplicating such jump-targets,
       *  so as to preserve agreement wit the (also duplicated) jump-sources.
       *  This is achieved based on the bookkeeping provided by two maps:
       *    - `labelDefsAtOrUnder` lists all LabelDefs enclosed by a given Tree node (the key)
       *    - `labelDef` provides the LabelDef node whose symbol is used as key.
       *       As a sidenote, a related map is `jumpDest`: it has the same keys as `labelDef` but its values are asm.Labels not LabelDef nodes.
       *
       *  Details in `emitFinalizer()`, which is invoked from `genLoadTry()` and `genSynchronized()`.
       */
      var labelDefsAtOrUnder: scala.collection.Map[Tree, List[LabelDef]] = null
      var labelDef: scala.collection.Map[Symbol, LabelDef] = null// (LabelDef-sym -> LabelDef)

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
        if(!emitLines || !tree.pos.isDefined) return;
        val nr = tree.pos.line
        if(nr != lastEmittedLineNr) {
          lastEmittedLineNr = nr
          lastInsn match {
            case lnn: asm.tree.LineNumberNode =>
              // overwrite previous landmark as no instructions have been emitted for it
              lnn.line = nr
            case _ =>
              mnode.visitLineNumber(nr, currProgramPoint())
          }
        }
      }

      /* ---------------- Code gen proper ---------------- */

      // on entering a method
      private def resetMethodBookkeeping(dd: DefDef) {
        locals.clear()
        jumpDest = immutable.Map.empty[ /* LabelDef */ Symbol, asm.Label ]
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

        lastEmittedLineNr = -1
      }

      override def getCurrentCUnit(): CompilationUnit = { cunit }

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

          case ValDef(mods, name, tpt, rhs) => () // fields are added in `genPlainClass()`, via `addClassFields()`

          case dd : DefDef => genDefDef(dd)

          case Template(_, _, body) => body foreach gen

          case _ => abort("Illegal tree in gen: " + tree)
        }
      }

      /* ---------------- helper utils for generating classes and fiels ---------------- */

      def genPlainClass(cd: ClassDef) {
        assert(cnode == null, "GenBCode detected nested methods.")
        innerClassBufferASM.clear()

        claszSymbol       = cd.symbol
        isCZParcelable    = isAndroidParcelableClass(claszSymbol)
        isCZStaticModule  = isStaticModule(claszSymbol)
        isCZRemote        = isRemote(claszSymbol)
        thisName          = internalName(claszSymbol)
        cnode             = new asm.tree.ClassNode()

        initJClass(cnode)

        val hasStaticCtor = methodSymbols(cd) exists (_.isStaticConstructor)
        if(!hasStaticCtor) {
          // but needs one ...
          if(isCZStaticModule || isCZParcelable) {
            fabricateStaticInit()
          }
        }

        val optSerial: Option[Long] = serialVUID(claszSymbol)
        if(optSerial.isDefined) { addSerialVUID(optSerial.get, cnode)}

        addClassFields()

        val lateClosuresBTs: List[BType] = lateClosures.map(lateC => lookupRefBType(lateC.name))
        innerClassBufferASM ++= trackMemberClasses(claszSymbol, lateClosuresBTs)

        gen(cd.impl)

        assert(cd.symbol == claszSymbol, "Someone messed up BCodePhase.claszSymbol during genPlainClass().")

        // ----------- all classes compiled in this run land in codeRepo.classes

            def trackInCodeRepo(compiled: asm.tree.ClassNode) {
              val bt = lookupRefBType(compiled.name)
              assert(!codeRepo.containsKey(bt))
              codeRepo.classes.put(bt, compiled)
            }

        trackInCodeRepo(cnode)
        for(lateC <- lateClosures) { trackInCodeRepo(lateC) }

        // ----------- add entries for Late-Closure-Classes to exemplars ( "plain class" already tracked by virtue of initJClass() )

        val trackedCNode = exemplars.get(lookupRefBType(cnode.name))
        for(lateC <- lateClosures) {
          val innersChain: Array[InnerClassEntry] = {
            /*
             * the list of classes containing a closure amounts to innersChain of its containing class
             * with the closure appended last.
             */
            val closuBT  = lookupRefBType(lateC.name)
            val closuICE = InnerClassEntry(lateC.name, cnode.name, closuBT.getSimpleName, lateC.access)
            if(trackedCNode.innersChain == null) {
              val outer = InnerClassEntry(cnode.name, null, null, cnode.access)
              Array(outer, closuICE)
            } else {
              val arr = new Array[InnerClassEntry](trackedCNode.innersChain.size + 1)
              trackedCNode.innersChain.copyToArray(arr)
              arr(arr.size - 1) = closuICE
              arr
            }
          }
          val trackedClosu = buildExemplarForClassNode(lateC, innersChain)
          exemplars.put(trackedClosu.c, trackedClosu)
        }

        // ----------- populate InnerClass JVM attribute, including Late-Closure-Classes

        // this requires exemplars to already track each BType in `innerClassBufferASM`, including those for Late-Closure-Classes
        addInnerClassesASM(cnode, innerClassBufferASM.toList)

        for(lateC <- lateClosures) {
          refreshInnerClasses(lateC)
        }

      } // end of method genPlainClass()

      /**
       *  precondition: the argument's internal name already registered as BType
       * */
      private def buildExemplarForClassNode(lateC: asm.tree.ClassNode, innersChain: Array[InnerClassEntry]): Tracked = {
        val key = lookupRefBType(lateC.name)
        assert(!exemplars.containsKey(key))

        // the only interface an anonymous closure class implements is scala.Serializable,
        val ifacesArr: Array[Tracked] =
          if(lateC.interfaces.isEmpty) EMPTY_TRACKED_ARRAY
          else {
            (JListWrapper(lateC.interfaces) map lookupRefBType).map(bt => exemplars.get(bt)).toArray
           }

        val tsc: Tracked = if(lateC.superName == null) null else exemplars.get(lookupRefBType(lateC.superName))

        val tr = Tracked(key, lateC.access, tsc, ifacesArr, innersChain)

        // under -closurify:delegating or -closurify:MH , an anon-closure-class has no member classes.
        tr.directMemberClasses = Nil

        tr
      } // end of method buildExemplarForLateClosure()

      /**
       * must-single-thread
       */
      private def initJClass(jclass: asm.ClassVisitor) {

        val ps = claszSymbol.info.parents
        val superClass: String = if(ps.isEmpty) JAVA_LANG_OBJECT.getInternalName else internalName(ps.head.typeSymbol);
        val ifaces: Array[String] = {
          val arrIfacesTr: Array[Tracked] = exemplar(claszSymbol).ifaces
          val arrIfaces = new Array[String](arrIfacesTr.length)
          var i = 0
          while(i < arrIfacesTr.length) {
            val ifaceTr = arrIfacesTr(i)
            val bt = ifaceTr.c
            if(ifaceTr.isInnerClass) { innerClassBufferASM += bt }
            arrIfaces(i) = bt.getInternalName
            i += 1
          }
          arrIfaces
        }
        // `internalName()` tracks inner classes.

        val flags = mkFlags(
          javaFlags(claszSymbol),
          if(isDeprecated(claszSymbol)) asm.Opcodes.ACC_DEPRECATED else 0 // ASM pseudo access flag
        )

        val thisSignature = getGenericSignature(claszSymbol, claszSymbol.owner)
        cnode.visit(classfileVersion, flags,
                    thisName, thisSignature,
                    superClass, ifaces)

        if(emitSource) {
          cnode.visitSource(cunit.source.toString, null /* SourceDebugExtension */)
        }

        val enclM = getEnclosingMethodAttribute(claszSymbol)
        if(enclM != null) {
          val EnclMethodEntry(className, methodName, methodType) = enclM
          cnode.visitOuterClass(className, methodName, methodType.getDescriptor)
        }

        val ssa = getAnnotPickle(thisName, claszSymbol)
        cnode.visitAttribute(if(ssa.isDefined) pickleMarkerLocal else pickleMarkerForeign)
        emitAnnotations(cnode, claszSymbol.annotations ++ ssa)

        if (isCZStaticModule || isCZParcelable) {

          if (isCZStaticModule) { addModuleInstanceField() }

        } else {

          val skipStaticForwarders = (claszSymbol.isInterface || settings.noForwarders.value)
          if (!skipStaticForwarders) {
            val lmoc = claszSymbol.companionModule
            // add static forwarders if there are no name conflicts; see bugs #363 and #1735
            if (lmoc != NoSymbol) {
              // it must be a top level class (name contains no $s)
              val isCandidateForForwarders = {
                exitingPickler { !(lmoc.name.toString contains '$') && lmoc.hasModuleFlag && !lmoc.isImplClass && !lmoc.isNestedClass }
              }
              if (isCandidateForForwarders) {
                log("Adding static forwarders from '%s' to implementations in '%s'".format(claszSymbol, lmoc))
                addForwarders(isRemote(claszSymbol), cnode, thisName, lmoc.moduleClass)
              }
            }
          }

        }

        // the invoker is responsible for adding a class-static constructor.

      } // end of method initJClass

      /**
       * can-multi-thread
       */
      private def addModuleInstanceField() {
        val fv =
          cnode.visitField(PublicStaticFinal, // TODO confirm whether we really don't want ACC_SYNTHETIC nor ACC_DEPRECATED
                           strMODULE_INSTANCE_FIELD,
                           "L" + thisName + ";",
                           null, // no java-generic-signature
                           null  // no initial value
          )

        fv.visitEnd()
      }

      /**
       * must-single-thread
       */
      def initJMethod(flags: Int, paramAnnotations: List[List[AnnotationInfo]]) {

        val jgensig = getGenericSignature(methSymbol, claszSymbol)
        addRemoteExceptionAnnot(isCZRemote, hasPublicBitSet(flags), methSymbol)
        val (excs, others) = methSymbol.annotations partition (_.symbol == definitions.ThrowsClass)
        val thrownExceptions: List[String] = getExceptions(excs)

        val bytecodeName =
          if(isMethSymStaticCtor) CLASS_CONSTRUCTOR_NAME
          else jMethodName

        val mdesc = asmMethodType(methSymbol).getDescriptor
        mnode = cnode.visitMethod(
          flags,
          bytecodeName,
          mdesc,
          jgensig,
          mkArray(thrownExceptions)
        ).asInstanceOf[asm.tree.MethodNode]

        mnode.isLiftedMethod = methSymbol.isLiftedMethod

        // TODO param names: (m.params map (p => javaName(p.sym)))

        emitAnnotations(mnode, others)
        emitParamAnnotations(mnode, paramAnnotations)

      } // end of method initJMethod

      /**
       * must-single-thread
       */
      private def fabricateStaticInit() {

        val clinit: asm.MethodVisitor = cnode.visitMethod(
          PublicStatic, // TODO confirm whether we really don't want ACC_SYNTHETIC nor ACC_DEPRECATED
          CLASS_CONSTRUCTOR_NAME,
          "()V",
          null, // no java-generic-signature
          null  // no throwable exceptions
        )
        clinit.visitCode()

        /* "legacy static initialization" */
        if (isCZStaticModule) {
          clinit.visitTypeInsn(asm.Opcodes.NEW, thisName)
          clinit.visitMethodInsn(asm.Opcodes.INVOKESPECIAL,
                                 thisName, INSTANCE_CONSTRUCTOR_NAME, "()V")
        }
        if (isCZParcelable) { legacyAddCreatorCode(clinit, cnode, thisName) }
        clinit.visitInsn(asm.Opcodes.RETURN)

        clinit.visitMaxs(0, 0) // just to follow protocol, dummy arguments
        clinit.visitEnd()
      }

      def addClassFields() {
        /** Non-method term members are fields, except for module members. Module
         *  members can only happen on .NET (no flatten) for inner traits. There,
         *  a module symbol is generated (transformInfo in mixin) which is used
         *  as owner for the members of the implementation class (so that the
         *  backend emits them as static).
         *  No code is needed for this module symbol.
         */
        for (f <- fieldSymbols(claszSymbol)) {
          val javagensig = getGenericSignature(f, claszSymbol)
          val flags = mkFlags(
            javaFieldFlags(f),
            if(isDeprecated(f)) asm.Opcodes.ACC_DEPRECATED else 0 // ASM pseudo access flag
          )

          val jfield = new asm.tree.FieldNode(
            flags,
            f.javaSimpleName.toString,
            symInfoTK(f).getDescriptor,
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

        if(isClosureDelegate(dd.symbol)) {
          dd.symbol.makePublic
        }

        methSymbol  = dd.symbol
        jMethodName = methSymbol.javaSimpleName.toString
        returnType  = asmMethodType(dd.symbol).getReturnType
        isMethSymStaticCtor = methSymbol.isStaticConstructor
        isMethSymBridge     = methSymbol.isBridge

        resetMethodBookkeeping(dd)

        // add method-local vars for params
        val DefDef(_, _, _, vparamss, _, rhs) = dd
        assert(vparamss.isEmpty || vparamss.tail.isEmpty, "Malformed parameter list: " + vparamss)
        val params = if(vparamss.isEmpty) Nil else vparamss.head
        nxtIdx = if (methSymbol.isStaticMember) 0 else 1;
        for (p <- params) { makeLocal(p.symbol) }
        // debug assert((params.map(p => locals(p.symbol).tk)) == asmMethodType(methSymbol).getArgumentTypes.toList, "debug")

        val isNative         = methSymbol.hasAnnotation(definitions.NativeAttr)
        val isAbstractMethod = (methSymbol.isDeferred || methSymbol.owner.isInterface)
        val flags = mkFlags(
          javaFlags(methSymbol),
          if (claszSymbol.isInterface) asm.Opcodes.ACC_ABSTRACT   else 0,
          if (methSymbol.isStrictFP)   asm.Opcodes.ACC_STRICT     else 0,
          if (isNative)                asm.Opcodes.ACC_NATIVE     else 0, // native methods of objects are generated in mirror classes
          if(isDeprecated(methSymbol)) asm.Opcodes.ACC_DEPRECATED else 0  // ASM pseudo access flag
        )

        // TODO needed? for(ann <- m.symbol.annotations) { ann.symbol.initialize }
        initJMethod(flags, params.map(p => p.symbol.annotations))

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
        for(ld <- labelDefsAtOrUnder(dd.rhs); ldp <- ld.params; if !locals.contains(ldp.symbol)) {
          // the tail-calls xform results in symbols shared btw method-params and labelDef-params, thus the guard above.
          makeLocal(ldp.symbol)
        }

        if (!isAbstractMethod && !isNative) {

              def emitNormalMethodBody() {
                val veryFirstProgramPoint = currProgramPoint()
                genLoad(rhs, returnType)

                rhs match {
                  case Block(_, Return(_)) => ()
                  case Return(_) => ()
                  case EmptyTree =>
                    globalError("Concrete method has no definition: " + dd + (
                      if (settings.debug.value) "(found: " + methSymbol.owner.info.decls.toList.mkString(", ") + ")"
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

                if(isMethSymStaticCtor) { appendToStaticCtor(dd) }
              } // end of emitNormalMethodBody()

          lineNumber(rhs)
          cgn = new CallGraphNode(cnode, mnode)
          emitNormalMethodBody()
          if(!cgn.isEmpty) {
            cgns += cgn
          }

          // Note we don't invoke visitMax, thus there are no FrameNode among mnode.instructions.
          // The only non-instruction nodes to be found are LabelNode and LineNumberNode.
        }
        mnode = null
      } // end of method genDefDef()

      /**
       *  must-single-thread
       *
       *  TODO document, explain interplay with `fabricateStaticInit()`
       **/
      private def appendToStaticCtor(dd: DefDef) {

            def insertBefore(
                  location: asm.tree.AbstractInsnNode,
                  i0: asm.tree.AbstractInsnNode,
                  i1: asm.tree.AbstractInsnNode) {
              if(i0 != null) {
                mnode.instructions.insertBefore(location, i0.clone(null))
                mnode.instructions.insertBefore(location, i1.clone(null))
              }
            }

        // collect all return instructions
        var rets: List[asm.tree.AbstractInsnNode] = Nil
        mnode foreachInsn { i => if(i.getOpcode() == asm.Opcodes.RETURN) { rets ::= i  } }
        if(rets.isEmpty) { return }

        var insnModA: asm.tree.AbstractInsnNode = null
        var insnModB: asm.tree.AbstractInsnNode = null
        // call object's private ctor from static ctor
        if (isCZStaticModule) {
          // NEW `moduleName`
          val className = internalName(methSymbol.enclClass)
          insnModA      = new asm.tree.TypeInsnNode(asm.Opcodes.NEW, className)
          // INVOKESPECIAL <init>
          val callee = methSymbol.enclClass.primaryConstructor
          val jname  = callee.javaSimpleName.toString
          val jowner = internalName(callee.owner)
          val jtype  = asmMethodType(callee).getDescriptor
          insnModB   = new asm.tree.MethodInsnNode(asm.Opcodes.INVOKESPECIAL, jowner, jname, jtype)
        }

        var insnParcA: asm.tree.AbstractInsnNode = null
        var insnParcB: asm.tree.AbstractInsnNode = null
        // android creator code
        if(isCZParcelable) {
          // add a static field ("CREATOR") to this class to cache android.os.Parcelable$Creator
          val andrFieldDescr = asmClassType(AndroidCreatorClass).getDescriptor
          cnode.visitField(
            asm.Opcodes.ACC_STATIC | asm.Opcodes.ACC_FINAL,
            "CREATOR",
            andrFieldDescr,
            null,
            null
          )
          // INVOKESTATIC CREATOR(): android.os.Parcelable$Creator; -- TODO where does this Android method come from?
          val callee = definitions.getMember(claszSymbol.companionModule, androidFieldName)
          val jowner = internalName(callee.owner)
          val jname  = callee.javaSimpleName.toString
          val jtype  = asmMethodType(callee).getDescriptor
          insnParcA  = new asm.tree.MethodInsnNode(asm.Opcodes.INVOKESTATIC, jowner, jname, jtype)
          // PUTSTATIC `thisName`.CREATOR;
          insnParcB  = new asm.tree.FieldInsnNode(asm.Opcodes.PUTSTATIC, thisName, "CREATOR", andrFieldDescr)
        }

        // insert a few instructions for initialization before each return instruction
        for(r <- rets) {
          insertBefore(r, insnModA,  insnModB)
          insertBefore(r, insnParcA, insnParcB)
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
            genLoad(rhs, symInfoTK(lhs.symbol))
            lineNumber(tree)
            fieldStore(lhs.symbol)

          case Assign(lhs, rhs) =>
            val s = lhs.symbol
            val Local(tk, _, idx, _) = locals.getOrElse(s, makeLocal(s))
            genLoad(rhs, tk)
            lineNumber(tree)
            bc.store(idx, tk)

          case _ =>
            genLoad(tree, UNIT)
        }
      }

      def genThrow(expr: Tree): BType = {
        val thrownKind = tpeTK(expr)
        assert(exemplars.get(thrownKind).isSubtypeOf(ThrowableReference))
        genLoad(expr, thrownKind)
        lineNumber(expr)
        emit(asm.Opcodes.ATHROW) // ICode enters here into enterIgnoreMode, we'll rely instead on DCE at ClassNode level.

        RT_NOTHING // always returns the same, the invoker should know :)
      }

      /** Generate code for primitive arithmetic operations. */
      def genArithmeticOp(tree: Tree, code: Int): BType = {
        val Apply(fun @ Select(larg, _), args) = tree
        var resKind = tpeTK(larg)

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
            resKind = maxType(tpeTK(larg), tpeTK(rarg))
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
        val k = tpeTK(arrayObj)
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
          genLoad(args.tail.head, tpeTK(args.tail.head))
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
        val monitorResult: Symbol = if(hasResult) makeLocal(tpeTK(args.head), "monitorResult") else null;

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

        val thenKind      = tpeTK(thenp)
        val elseKind      = if (!hasElse) UNIT else tpeTK(elsep)
        def hasUnitBranch = (thenKind == UNIT || elseKind == UNIT)
        val resKind       = if (hasUnitBranch) UNIT else tpeTK(tree)

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
        val kind = tpeTK(tree)

        val caseHandlers: List[EHClause] =
          for (CaseDef(pat, _, caseBody) <- catches) yield {
            pat match {
              case Typed(Ident(nme.WILDCARD), tpt)  => NamelessEH(tpeTK(tpt), caseBody)
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
        val tmp          = if(guardResult) makeLocal(tpeTK(tree), "tmp") else null;
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
        nopIfNeeded(startTryBody) // we can't elide an exception-handler protecting an empty try-body, that would change semantics (e.g. NoClassDefFoundError due to the EH)
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

            case BoundEH   (patSymbol,  caseBody) =>
              // test/files/run/contrib674.scala , a local-var already exists for patSymbol.
              // rather than creating on first-access, we do it right away to emit debug-info for the created local var.
              val Local(patTK, _, patIdx, _) = locals.getOrElse(patSymbol, makeLocal(patSymbol))
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
          saved = jumpDest
          for(ldef <- labelDefsAtOrUnder(finalizer)) {
            jumpDest -= ldef.symbol
          }
        }
        // when duplicating, the above guarantees new asm.Labels are used for LabelDefs contained in the finalizer (their vars are reused, that's ok)
        if(tmp != null) { store(tmp) }
        genLoad(finalizer, UNIT)
        if(tmp != null) { load(tmp)  }
        if(isDuplicate) {
          jumpDest = saved
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
          genLoad(receiver, tpeTK(receiver))
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
            val Local(tk, _, idx, isSynth) = locals.getOrElseUpdate(sym, makeLocal(sym))
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
            val symIsModuleClass = tree.symbol.isModuleClass
            assert(tree.symbol == claszSymbol || symIsModuleClass,
                   "Trying to access the this of another class: " +
                   "tree.symbol = " + tree.symbol + ", class symbol = " + claszSymbol + " compilation unit:"+ cunit)
            if (symIsModuleClass && tree.symbol != claszSymbol) {
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
            generatedType = symInfoTK(sym)
            val hostClass = findHostClass(qualifier.tpe, sym)
            log(s"Host class of $sym with qual $qualifier (${qualifier.tpe}) is $hostClass")
            val qualSafeToElide = treeInfo isQualifierSafeToElide qualifier

            def genLoadQualUnlessElidable() { if (!qualSafeToElide) { genLoadQualifier(tree) } }

            if (sym.isModule) {
              genLoadQualUnlessElidable()
              genLoadModule(tree)
            }
            else if (sym.isStaticMember) {
              genLoadQualUnlessElidable()
              fieldLoad(sym, hostClass)
            }
            else {
              genLoadQualifier(tree)
              fieldLoad(sym, hostClass)
            }

          case Ident(name) =>
            val sym = tree.symbol
            if (!sym.isPackage) {
              val tk = symInfoTK(sym)
              if (sym.isModule) { genLoadModule(tree) }
              else { load(sym) }
              generatedType = tk
            }

          case Literal(value) =>
            if (value.tag != UnitTag) (value.tag, expectedType) match {
              case (IntTag,   LONG  ) => bc.lconst(value.longValue);       generatedType = LONG
              case (FloatTag, DOUBLE) => bc.dconst(value.doubleValue);     generatedType = DOUBLE
              case (NullTag,  _     ) => bc.emit(asm.Opcodes.ACONST_NULL); generatedType = RT_NULL
              case _                  => genConstant(value);               generatedType = tpeTK(tree)
            }

          case blck : Block => genBlock(blck, expectedType)

          case Typed(Super(_, _), _) => genLoad(This(claszSymbol), expectedType)

          case Typed(expr, _) =>
            expr match {
              case app: Apply if isLateClosuresOn && isClosureDelegate(app.symbol) =>
                // we arrive here when closureConversionModern found a Function node with Nothing return type,
                // was desugared there into: fakeCallsite.asInstanceOf[scala.runtime.AbstractFunctionX[...,Nothing]]
                genLateClosure(app, tpeTK(tree))
              case _ =>
                genLoad(expr, expectedType)
            }

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
       * must-single-thread
       **/
      def fieldLoad( field: Symbol, hostClass: Symbol = null) {
        fieldOp(field, isLoad = true,  hostClass)
      }
      /**
       * must-single-thread
       **/
      def fieldStore(field: Symbol, hostClass: Symbol = null) {
        fieldOp(field, isLoad = false, hostClass)
      }

      /**
       * must-single-thread
       **/
      private def fieldOp(field: Symbol, isLoad: Boolean, hostClass: Symbol = null) {
        // LOAD_FIELD.hostClass , CALL_METHOD.hostClass , and #4283
        val owner      =
          if(hostClass == null) internalName(field.owner)
          else                  internalName(hostClass)
        val fieldJName = field.javaSimpleName.toString
        val fieldDescr = symInfoTK(field).getDescriptor
        val isStatic   = field.isStaticMember
        val opc =
          if(isLoad) { if (isStatic) asm.Opcodes.GETSTATIC else asm.Opcodes.GETFIELD }
          else       { if (isStatic) asm.Opcodes.PUTSTATIC else asm.Opcodes.PUTFIELD }
        mnode.visitFieldInsn(opc, owner, fieldJName, fieldDescr)

      }

      // ---------------- emitting constant values ----------------

      /**
       * For const.tag in {ClazzTag, EnumTag}
       *   must-single-thread
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
        val returnedKind = tpeTK(expr)
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
        var generatedType = expectedType
        lineNumber(app)
        app match {

          case Apply(TypeApply(fun, targs), _) =>

            val sym = fun.symbol
            val cast = sym match {
              case Object_isInstanceOf  => false
              case Object_asInstanceOf  => true
              case _                    => abort("Unexpected type application " + fun + "[sym: " + sym.fullName + "]" + " in: " + app)
            }

            val Select(obj, _) = fun
            val l = tpeTK(obj)
            val r = tpeTK(targs.head)

                def genTypeApply(): BType = {
                  genLoadQualifier(fun)

                  if (l.isValueType && r.isValueType)
                    genConversion(l, r, cast)
                  else if (l.isValueType) {
                    bc drop l
                    if (cast) {
                      mnode.visitTypeInsn(asm.Opcodes.NEW, classCastExceptionReference.getInternalName)
                      bc dup ObjectReference
                      emit(asm.Opcodes.ATHROW)
                    } else {
                      bc boolconst false
                    }
                  }
                  else if (r.isValueType && cast) {
                    abort("Erasure should have added an unboxing operation to prevent this cast. Tree: " + app)
                  }
                  else if (r.isValueType) {
                    bc isInstance classLiteral(r)
                  }
                  else {
                    genCast(r, cast)
                  }

                  if (cast) r else BOOL
                } // end of genTypeApply()

                def fakeCallsiteExtractor(): Apply = {
                  if(isLateClosuresOn && cast) {
                    val arity = abstractFunctionArity(r)
                    if(arity != -1) {
                      val preScreened =
                        obj match {
                          case Block(List(found), expr) =>
                            // this case results for example from scala.runtime.AbstractFunction1[Int,Unit]
                            // TODO assert expr is scala.runtime.BoxedUnit.UNIT . Somewhat weaker: l == Lscala/runtime/BoxedUnit;
                            found
                          case Apply(boxOp, List(found)) if definitions.isBox(boxOp.symbol) =>
                            // this case results for example from scala.runtime.AbstractFunction1[Int,Int]
                            // TODO assert boxOp is boxing (e.g. "scala.Int.box"). Somewhat weaker: l == Ljava/lang/Object;
                            found
                          case found =>
                            // this case results for example from scala.runtime.AbstractFunction1[Int,String]
                            // TODO assert l == delegate.resultType
                            found
                        }

                      if(preScreened.isInstanceOf[Apply]) {
                        val fakeApp = preScreened.asInstanceOf[Apply]
                        if(isClosureDelegate(fakeApp.fun.symbol)) {
                          return fakeApp
                        }
                      }

                    }
                  }
                  null
                }

            val fakeCallsite: Apply = fakeCallsiteExtractor()

            generatedType =
              if(fakeCallsite == null) genTypeApply()
              else { genLateClosure(fakeCallsite, r) }

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
            genCallMethod(fun.symbol, invokeStyle, pos = app.pos)
            generatedType = asmMethodType(fun.symbol).getReturnType

          // 'new' constructor call: Note: since constructors are
          // thought to return an instance of what they construct,
          // we have to 'simulate' it by DUPlicating the freshly created
          // instance (on JVM, <init> methods return VOID).
          case Apply(fun @ Select(New(tpt), nme.CONSTRUCTOR), args) =>
            val ctor = fun.symbol
            assert(ctor.isClassConstructor, "'new' call to non-constructor: " + ctor.name)

            generatedType = tpeTK(tpt)
            assert(generatedType.isRefOrArrayType, "Non reference type cannot be instantiated: " + generatedType)

            generatedType match {
              case arr if generatedType.isArray =>
                genLoadArguments(args, paramTKs(app))
                val dims     = arr.getDimensions
                var elemKind = arr.getElementType
                val argsSize = args.length
                if (argsSize > dims) {
                  cunit.error(app.pos, "too many arguments for array constructor: found " + args.length +
                                        " but array has only " + dims + " dimension(s)")
                }
                if (argsSize < dims) {
                  /* In one step:
                   *   elemKind = new BType(BType.ARRAY, arr.off + argsSize, arr.len - argsSize)
                   * however the above does not enter a TypeName for each nested arrays in chrs.
                   */
                  val elemKind2 = new BType(BType.ARRAY, arr.off + argsSize, arr.len - argsSize)
                  for (i <- args.length until dims) elemKind = arrayOf(elemKind)
                  assert(elemKind == elemKind2 , "elemKind != elemKind2")
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
            val nativeKind = tpeTK(expr)
            genLoad(expr, nativeKind)
            val MethodNameAndType(mname, mdesc) = asmBoxTo(nativeKind)
            bc.invokestatic(BoxesRunTime.getInternalName, mname, mdesc)
            generatedType = boxResultType(fun.symbol) // was toTypeKind(fun.symbol.tpe.resultType)

          case Apply(fun @ _, List(expr)) if (definitions.isUnbox(fun.symbol)) =>
            genLoad(expr, tpeTK(expr))
            val boxType = unboxResultType(fun.symbol) // was toTypeKind(fun.symbol.owner.linkedClassOfClass.tpe)
            generatedType = boxType
            val MethodNameAndType(mname, mdesc) = asmUnboxTo(boxType)
            bc.invokestatic(BoxesRunTime.getInternalName, mname, mdesc)

          case app @ Apply(fun, args) =>
            val sym = fun.symbol

            if (sym.isLabel) {  // jump to a label
              genLoadLabelArguments(args, labelDef(sym), app.pos)
              bc goTo programPoint(sym)
            } else if (isPrimitive(sym)) { // primitive method call
              generatedType = genPrimitiveOp(app, expectedType)
            } else {  // normal method call

                  def genNormalMethodCall() {

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
                        if (qualSym == ArrayClass) {
                          targetTypeKind = tpeTK(qual)
                          log(s"Stored target type kind for {$sym.fullName} as $targetTypeKind")
                        }
                        else {
                          hostClass = qualSym
                          if (qual.tpe.typeSymbol != qualSym) {
                            log(s"Precisified host class for $sym from ${qual.tpe.typeSymbol.fullName} to ${qualSym.fullName}")
                          }
                        }

                      case _ =>
                    }
                    if((targetTypeKind != null) && (sym == definitions.Array_clone) && invokeStyle.isDynamic) {
                      val target: String = targetTypeKind.getInternalName
                      bc.invokevirtual(target, "clone", "()Ljava/lang/Object;")
                    }
                    else {
                      genCallMethod(sym, invokeStyle, hostClass, app.pos)
                    }

                  } // end of genNormalMethodCall()

              // inter-procedural optimization: directly target final method in trait
              val detour = mixer.detouredFinalTraitMethods.getOrElse(sym, null)
              if(detour != null) {
                // selfRefBType is (also) the type of the self-param of an implementaion method
                val selfRefBType          = toTypeKind(detour.firstParam.tpe)
                val Select(qualifier, _)  = fun
                val qualifierExpectedType = tpeTK(qualifier)
                val isAdapted             = !exemplars.get(selfRefBType).isSubtypeOf(qualifierExpectedType)
                log(
                  s"Rewiring to directly invokestatic final method $detour in trait $qualifierExpectedType , " +
                  s"used to be an invokeinterface to $sym"
                )
                genLoad(qualifier, qualifierExpectedType)
                val lastInsn = mnode.instructions.getLast
                if(
                  isAdapted &&
                  (lastInsn.getOpcode == asm.Opcodes.CHECKCAST)
                ) {
                  val ti = lastInsn.asInstanceOf[asm.tree.TypeInsnNode]
                  if(lookupRefBType(ti.desc) != selfRefBType) {
                    log(s"As part of rewiring a final trait method (SI-4767), removed ${insnPosInMethodSignature(ti, mnode, cnode)} ")
                    mnode.instructions.remove(lastInsn)
                  }
                }
                genLoadArguments(args, paramTKs(app))
                genCallMethod(detour, Static(false), detour.owner, app.pos)
              } else {
                genNormalMethodCall()
              }

              generatedType = asmMethodType(sym).getReturnType
        }

        }

        generatedType
      } // end of PlainClassBuilder's genApply()

      /**
       *  This method works in tandem with UnCurry's closureConversionModern()
       *
       *  Rather than emitting a fakeCallsite, the initialization of a closure instance is emitted, along with
       *  a closure class that is synthesized on the spot.
       *  The result is undistinguishable from what UnCurry, Specialization, Erasure, would have produced.
       *
       *  Terminology: arity is used throughout `genLateClosure()` as shorthand for closure-arity
       *
       *  The starting point is the "fake calliste" targeting the closure entrypoint (aka "delegate").
       *
       *    (a) The "fake calliste" may target:
       *          - a static method (e.g., for closures enclosed in modules, or in implementation classes);
       *        or
       *          - an instance method (the receiver being the outer instance of the closure).
       *
       *    (b) Whenever the delegate is an instance method,
       *        the leading `arity` arguments to the fakeCallsite are Trees denoting zeroes.
       *        The above also applies in case of a static delegate unless declared in an implementation class.
       *        In that case:
       *          - the first argument stands for the self-instance, which should be captured by the closure.
       *          - the following `arity` arguments are zeroes.
       *
       *    (c) remaining arguments denote non-outer captured values.
       *        Whether an outer-instance is needed is determined by whether the delegate will be invoked via
       *        invokevirtual or invokestatic, in turn determined by `delegateSym.isStaticMember`.
       *
       *  The resulting Late-Closure-Class is registered in `codeRepo.classes` and `exemplars`
       *  by `PlainClassBuilder.plainClass()` , see `PlainClassBuilder.lateClosures`
       *
       *  The resulting Late-Closure-Class consists of:
       *
       *    (d) one public constructor taking as argument the outer value (if needed) followed by (c).
       *    (e) a private final field for each constructor param
       *    (f) one, two, or three "apply()" overrides to account for specialization.
       *
       *  @return the closure-type, ie the 2nd argument (`castToBT`)
       *
       * */
      private def genLateClosure(fakeCallsite: Apply, castToBT: BType): BType = {
        val Apply(Select(rcv, _), args) = fakeCallsite
        val arity = abstractFunctionArity(castToBT)

        val delegateSym = fakeCallsite.symbol.asInstanceOf[MethodSymbol]
        val hasOuter    = !delegateSym.isStaticMember
        val isStaticImplMethod = delegateSym.owner.isImplClass

        assert(
          uncurry.closureDelegates.contains(delegateSym),
          s"Not a dclosure-endpoint: ${delegateSym.fullLocationString}"
        )
        assert(
          if(isStaticImplMethod) !hasOuter else true,
           "How come a delegate-method (for a Late-Closure-Class) is static yet the dclosure is supposed to have an outer-instance. " +
          s"Delegate: ${delegateSym.fullLocationString}"
        )
        assert(
          if(hasOuter) !isStaticImplMethod else true,
           "A Late-Closure-Class that captures an outer-instance can't delegate to a (static) method in an implementation class. " +
          s"Delegate: ${delegateSym.fullLocationString}"
        )

        // checking working assumptions

        // outerTK is a poor name choice because sometimes there's no outer instance yet there's always a delegateOwnerTK
        val outerTK     = brefType(internalName(delegateSym.owner))
        val enclClassBT = brefType(cnode.name)
        assert(outerTK.hasObjectSort, s"Not of object sort: $outerTK")
        assert(
          outerTK == enclClassBT,
           "Probable cause: a regression in the way DelayedInit is lowered. " +
          s"outerTK != enclClassBT , where outerTK is $outerTK and enclClassBT is $enclClassBT"
        )

        /*
         * Pieces of information for building the closure class:
         *   - closure-state (names and types),
         *   - apply-params-section (types).
         */

        val delegateMT: BType = asmMethodType(delegateSym)
        val delegateJavaName  = delegateSym.javaSimpleName.toString

        val delegateParamTs = delegateMT.getArgumentTypes.toList
        val closuStateBTs: List[BType] = {
          if(!isStaticImplMethod) {
            val tmp = delegateParamTs.drop(arity)
            if(hasOuter) outerTK :: tmp else tmp
          }
          else {
            delegateParamTs.head :: delegateParamTs.drop(arity + 1)
          }
        }

        val closuStateNames: List[String] = {
          val delegateParamNames: List[String] = uniquify(
            for(paramSym <- delegateSym.paramss.head) yield paramSym.name.toString
          )
          assert(allDifferent(delegateParamNames), "Duplicate param names found among " + delegateParamNames.mkString(" , "))
          if(!isStaticImplMethod) {
            val tmp = delegateParamNames.drop(arity)
            if(hasOuter) nme.OUTER.toString :: tmp else tmp
          }
          else {
            delegateParamNames.head :: delegateParamNames.drop(arity + 1)
          }
        }

        val delegateApplySection: List[BType] = {
          if(!isStaticImplMethod) { delegateParamTs.take(arity) }
          else { delegateParamTs.tail.take(arity) }
        }

            def emitClosureInstantiation(closuInternalName: String, ctorDescr: String) {
              assert(closuInternalName != null)
              assert(ctorDescr != null)
              // NEW, DUP
              mnode.visitTypeInsn(asm.Opcodes.NEW, closuInternalName)
              mnode.visitInsn(asm.Opcodes.DUP)
              // outer value, if any
              val restClosureStateBTs: List[BType] =
                if(hasOuter) {
                  genLoad(rcv, outerTK)
                  closuStateBTs.drop(1)
                } else {
                  closuStateBTs
                }
              // the rest of captured values
              val capturedValues: List[Tree] = {
                if(!isStaticImplMethod) { args.drop(arity) }
                else { args.head :: args.drop(arity + 1) }
              }
              assert(
                restClosureStateBTs.size == capturedValues.size,
                s"Mismatch btw ${restClosureStateBTs.mkString} and ${capturedValues.mkString}"
              )
              map2(capturedValues, restClosureStateBTs) { (captureValue, ctorParamBT) =>
                genLoad(captureValue, ctorParamBT)
              }
              // <init> invocation
              mnode.visitMethodInsn(asm.Opcodes.INVOKESPECIAL, closuInternalName, nme.CONSTRUCTOR.toString, ctorDescr)
            }

        {
          val alreadyLCC: DClosureEndpoint = closuresForDelegates.getOrElse(delegateSym, null)
          if(alreadyLCC != null) {
            log(
               "Visiting a second time a dclosure-endpoint E for which a Late-Closure-Class LCC has been created already. " +
              s"Who plays each role: E is ${delegateSym.fullLocationString} , LCC is ${alreadyLCC.closuBT.getInternalName} , " +
              s" method enclosing the closure instantation: ${methodSignature(cnode, mnode)} , position in source file: ${fakeCallsite.pos}. " +
               "This happens when duplicating an exception-handler or finally clause (which exist in two forms: " +
               "reachable-via-fall-through and reachable-via-exceptional-control-flow)."
            )
            val closuIName = alreadyLCC.closuBT.getInternalName
            emitClosureInstantiation(closuIName, alreadyLCC.closuCtor.desc)
            return castToBT
          }
        }

            /** primitive and void erase to themselves, all others (including arrays) to j.l.Object */
            def spclzdErasure(bt: BType): BType = { if(bt.isPrimitiveOrVoid) bt else ObjectReference }
            def spclzdDescriptors(bts: List[BType]): List[String] = {
              for(bt <- bts; spEra = spclzdErasure(bt))
              yield {
                if(spEra.isPrimitiveOrVoid) { spEra.getDescriptor }
                else { assert(spEra.hasObjectSort); "L" }
              }
            }

            /**
             *  initBCodeTypes() populates exemplars for all s.r.AbstractFunctionX and any specialized subclasses.
             *  We query that map to find out whether the specialization given by `key` exists.
             *
             *  @param key a string of the form $mc...$sp which may be the postfix of the internal name of
             *             an AbstractFunctionX specialized subclass.
             * */
            def isValidSpclztion(key: String): Boolean = {
              val candidate = castToBT.getInternalName // `castToBT` is a non-specialized s.r.AbstractFunctionX class
              exemplarIfExisting(candidate + key) != null
            }

            /**
             *  Two cases:
             *
             *  (a) In case the closure can be specialized,
             *      the closure class to create should extend a subclass of `castToBT`,
             *      ie a subclass with name of the form s.r.AbstractFunctionX$mc...$sp ,
             *      and override an "ultimate apply()" (ie an apply method with most-specific types).
             *      Another apply-method (with "fully-erased" method signature) is also added whose task is:
             *        - unboxing arguments,
             *        - invoking the ultimate apply, and
             *        - boxing the result.
             *
             *  (b) In case the closure can't be specialized,
             *      the closure class to create extends `castToBT`, and
             *      overrides the fully-erased apply() method corresponding to the closure's arity.
             *
             *  That's what this method figures out, based on symbols inspected during initBCodeTypes()
             *
             *  @return a Pair(superClassName, list-of-overriding-methods) where:
             *
             *            - the head of the method list denotes the "ultimate-apply" override that invokes the delegate
             *
             *            - the rest are "plumbing" methods to invoke the aforementioned ultimate-apply.
             *
             *  The returned overrides are part of the closure-class being built, but the method bodies themselves are not added yet.
             **/
            def takingIntoAccountSpecialization(): Pair[String, List[MethodNode]] = {

                  def getUltimateAndPlumbing(key: String, mdescr: String): List[asm.tree.MethodNode] = {
                    val closuIName = castToBT.getInternalName
                    val fullyErasedDescr = BType.getMethodDescriptor(ObjectReference, Array.fill(arity){ ObjectReference })
                    val fullyErasedMNode = new asm.tree.MethodNode(
                      asm.Opcodes.ASM4,
                      (asm.Opcodes.ACC_PUBLIC | asm.Opcodes.ACC_FINAL),
                      "apply", fullyErasedDescr,
                      null, null
                    )
                    val plumbings: List[asm.tree.MethodNode] =
                      if(mdescr == null) Nil
                      else {

                        assert(key    != null)
                        assert(mdescr != fullyErasedDescr, "Fully-erased-apply and bridge-apply undistinguishable (same name, ie apply, same method descriptor)")

                        /*
                         * The 2nd plumbing method below (called simply "apply") is a so called "bridge apply", for example `int apply(int)`.
                         * You might think it isn't needed, bc nobody invokes it (spclztion rewrites callsites to target the spclzd version instead)
                         * HOWEVER, just because an "specialized interface" (in the example, scala.Function1$mcII$sp) declares it,
                         * and s.r.AbstractFunction1$mcII$sp extends that interface, we've got to add bytecode in each subclass,
                         * TODO THEREFORE a lot of boilerplate would be saved if that method were implemented in s.r.AbstractFunction1$mcII$sp already.
                         * */

                         List(
                          "apply" + key,
                          "apply"
                        ).map( applyName =>
                          new MethodNode(
                            asm.Opcodes.ASM4,
                            (asm.Opcodes.ACC_PUBLIC | asm.Opcodes.ACC_FINAL),
                            applyName, mdescr,
                            null, null
                          )
                        )
                      }

                    plumbings ::: List(fullyErasedMNode)
                  }

              if(arity <= 2) { // TODO for now hardcoded

                val maybeSpczld = {
                  (delegateApplySection exists { bt => bt.isNonUnitValueType }) ||
                  (delegateMT.getReturnType.isPrimitiveOrVoid)
                }

                if(maybeSpczld) {
                  val key = {
                    "$mc" +
                    spclzdErasure(delegateMT.getReturnType).getDescriptor +
                    spclzdDescriptors(delegateApplySection).mkString +
                    "$sp"
                  }
                  if(isValidSpclztion(key)) {
                    /* method descriptor for the "ultimate apply" ie the one with primitive types. */
                    val spzldDescr: String = {
                      spclzdDescriptors(delegateApplySection).mkString("(", "", ")") +
                      spclzdErasure(delegateMT.getReturnType).getDescriptor
                    }
                    return Pair(castToBT.getInternalName + key, getUltimateAndPlumbing(key, spzldDescr))
                  }
                }

              }

              val nonSpzld = castToBT.getInternalName
              assert(!nonSpzld.contains('$'), s"Unexpected specialized AbstractFunction: $nonSpzld")

              Pair(nonSpzld, getUltimateAndPlumbing(null, null))
            } // end of helper method takingIntoAccountSpecialization()


        val Pair(superClassName, ultimate :: plumbings) = takingIntoAccountSpecialization()
        val superClassBT = brefType(superClassName)

            /**
             *  A Late-Closure-Class is created as a ClassNode.
             *  Except for the apply methods everything else is added: parents, fields, and constructor.
             *
             *  @return the initialized closure-class, and its only constructor.
             * */
            def createAnonClosu(): Pair[asm.tree.ClassNode, asm.tree.MethodNode] = {
              val c = new asm.tree.ClassNode() // interfaces, innerClasses, fields, methods

              val simpleName = cunit.freshTypeName(
                enclClassBT.getSimpleName + "$LCC$" + nme.ANON_FUN_NAME.toString + "$" + mnode.name + "$"
              ).toString
              c.name = {
                val pak = enclClassBT.getRuntimePackage
                if(pak.isEmpty) simpleName else (pak + "/" + simpleName)
              }
              c.version   = classfileVersion
              c.access    = asm.Opcodes.ACC_PUBLIC | asm.Opcodes.ACC_FINAL | asm.Opcodes.ACC_SUPER // TODO is ACC_SUPER also needed?
              c.superName = superClassName

              c.interfaces.add(scalaSerializableReference.getInternalName)
              addSerialVUID(0, c)

              c.outerClass      = outerTK.getInternalName // internal name of the enclosing class of the class
              c.outerMethod     = mnode.name              // name of the method that contains the class
              c.outerMethodDesc = mnode.desc              // descriptor of the method that contains the class

              // add closure state (fields)
              for(Pair(name, bt) <- closuStateNames.zip(closuStateBTs)) {
                val fn = new FieldNode(
                  asm.Opcodes.ACC_PRIVATE | asm.Opcodes.ACC_FINAL,
                  name, bt.getDescriptor,
                  null, null
                )
                c.fields.add(fn)
              }

                def createClosuCtor(): asm.tree.MethodNode = {

                  // registers the (possibly unseen) descriptor in Names.chrs via global.newTypeName
                  val ctorDescr = BType.getMethodType(BType.VOID_TYPE, closuStateBTs.toArray).getDescriptor

                  val ctor = new asm.tree.MethodNode(
                    asm.Opcodes.ASM4, asm.Opcodes.ACC_PUBLIC,
                    nme.CONSTRUCTOR.toString, ctorDescr,
                    null, null
                  )

                     def loadTHIS() { ctor.visitVarInsn(asm.Opcodes.ALOAD, 0) }

                     def loadLocal(idx: Int, tk: BType) { ctor.visitVarInsn(tk.getOpcode(asm.Opcodes.ILOAD), idx) }

                  /*
                   * In case of outer instance, emit the following preamble,
                   * consisting of six instructions and a LabelNode, at the beginning of the ctor.
                   * TODO Scala v2.11 should let a scala.runtime static method encapsulate that boilerplate.
                   *
                   *     ALOAD 1
                   *     IFNONNULL L0
                   *     NEW java/lang/NullPointerException
                   *     DUP
                   *     INVOKESPECIAL java/lang/NullPointerException.<init> ()V
                   *     ATHROW
                   *  L1:
                   *
                   * */
                  if(hasOuter) {
                    ctor.visitVarInsn(asm.Opcodes.ALOAD, 1)
                    val lnode = new asm.tree.LabelNode(new asm.Label)
                    ctor.instructions.add(new asm.tree.JumpInsnNode(asm.Opcodes.IFNONNULL, lnode))
                    ctor.visitTypeInsn(asm.Opcodes.NEW, jlNPEReference.getInternalName)
                    ctor.visitInsn(asm.Opcodes.DUP)
                    ctor.visitMethodInsn(asm.Opcodes.INVOKESPECIAL, jlNPEReference.getInternalName, nme.CONSTRUCTOR.toString, "()V")
                    ctor.visitInsn(asm.Opcodes.ATHROW)
                    ctor.instructions.add(lnode)
                  }

                  /*
                   *  ... init fields from params
                   */
                  var paramIdx = 1
                  for(Pair(fieldName, fieldType) <- closuStateNames.zip(closuStateBTs)) {
                    loadTHIS()
                    loadLocal(paramIdx, fieldType)
                    ctor.visitFieldInsn(asm.Opcodes.PUTFIELD, c.name, fieldName, fieldType.getDescriptor)
                    paramIdx += fieldType.getSize
                  }

                  /*
                   *  ALOAD 0
                   *  INVOKESPECIAL scala/runtime/AbstractFunctionX.<init> ()V // or a specialized subclass
                   *  RETURN
                   *
                   */
                  loadTHIS()
                  ctor.visitMethodInsn(asm.Opcodes.INVOKESPECIAL, superClassName, nme.CONSTRUCTOR.toString, "()V")
                  ctor.visitInsn(asm.Opcodes.RETURN)

                  // asm.optimiz.Util.computeMaxLocalsMaxStack(ctor)
                  ctor
                }

              val ctor = createClosuCtor()

              Pair(c, ctor)
            } // end of method createAnonClosu()

        val Pair(closuCNode, ctor) = createAnonClosu()

        // registers the closure's internal name in Names.chrs, and let populateDClosureMaps() know about closure endpoint
        val closuBT = brefType(closuCNode.name)
        assert(!codeRepo.containsKey(closuBT))

        val fieldsMap: Map[String, BType] = closuStateNames.zip(closuStateBTs).toMap

            /**
             *  A plumbing-apply needs to unbox arguments before invoking the ultimate apply,
             *  and box the result ( in case Object is expected but void produced, insert scala.runtime.BoxedUnit.UNIT )
             * */
            def spclzdAdapt(mnode: MethodNode, from: BType, to: BType) {
              if(from == to) { return }
              if(from.isUnitType) {
                assert(to == ObjectReference, "Expecting j.l.Object but got: " + to)
                // GETSTATIC scala/runtime/BoxedUnit.UNIT : Lscala/runtime/BoxedUnit;
                mnode.visitFieldInsn(asm.Opcodes.GETSTATIC, srBoxedUnit.getInternalName, "UNIT", srBoxedUnit.getDescriptor)
              }
              else if(to.isNonUnitValueType) {
                // must be on the way towards ultimate
                assert(from == ObjectReference, "Expecting j.l.Object but got: " + from)
                val MethodNameAndType(mname, mdesc) = asmUnboxTo(to)
                mnode.visitMethodInsn(asm.Opcodes.INVOKESTATIC, BoxesRunTime.getInternalName, mname, mdesc)
              }
              else if(from.isNonUnitValueType) {
                // must be on the way towards ultimate
                assert(to == ObjectReference, "Expecting j.l.Object but got: " + to)
                val MethodNameAndType(mname, mdesc) = asmBoxTo(from)
                mnode.visitMethodInsn(asm.Opcodes.INVOKESTATIC, BoxesRunTime.getInternalName, mname, mdesc)
              } else {
                // no need to CHECKCAST the result of a method that returns Lscala/runtime/Nothing$;
                if(!from.isNothingType) {
                  assert(from.isRefOrArrayType, "Expecting array or object type but got: " + from)
                  assert(to.isRefOrArrayType,   "Expecting array or object type but got: " + to)
                  mnode.visitTypeInsn(asm.Opcodes.CHECKCAST, to.getInternalName)
                }
              }
            }

            /**
             *  Adds instrucitons to the ultimate-apply (received as argument) to invoke the delegate.
             * */
            def buildUltimateBody() {
              ultimate.instructions = new asm.tree.InsnList

                  def loadField(fieldName: String) {
                    ultimate.visitVarInsn(asm.Opcodes.ALOAD, 0)
                    val fieldType = fieldsMap(fieldName)
                    ultimate.visitFieldInsn(asm.Opcodes.GETFIELD, closuCNode.name, fieldName, fieldType.getDescriptor)
                  }

                  def loadLocal(idx: Int, tk: BType) {
                    ultimate.visitVarInsn(tk.getOpcode(asm.Opcodes.ILOAD), idx)
                  }

              val ultimateMT = BType.getMethodType(ultimate.desc)

              // in order to invoke the delegate, load the receiver if any
              if(!isStaticImplMethod) {
                if(hasOuter) { loadField(nme.OUTER.toString) }
              } else {
                loadField(closuStateNames.head)
              }

              // after that, load each apply-argument
              val callerParamsBTs = ultimateMT.getArgumentTypes.toList
              assert(callerParamsBTs.size == delegateApplySection.size)
              var idx = 1
              for(Pair(callerParamBT, calleeParamBT) <- callerParamsBTs.zip(delegateApplySection)) {
                loadLocal(idx, callerParamBT)
                spclzdAdapt(ultimate, callerParamBT, calleeParamBT)
                idx += callerParamBT.getSize
              }

              // now it only remains to load non-outer closure-state fields
              val restFieldNames = {
                if(!isStaticImplMethod) {
                  if(hasOuter) closuStateNames.tail else closuStateNames
                } else {
                  closuStateNames.tail
                }
              }
              for(fieldName <- restFieldNames) {
                loadField(fieldName)
                // no adapt needed because the closure-fields were derived from the delegate's params for captured valued.
              }

              val callOpc = if(hasOuter) asm.Opcodes.INVOKEVIRTUAL else asm.Opcodes.INVOKESTATIC
              ultimate.visitMethodInsn(
                callOpc,
                outerTK.getInternalName,
                delegateJavaName,
                delegateMT.getDescriptor
              )

              spclzdAdapt(ultimate, delegateMT.getReturnType, ultimateMT.getReturnType)

              ultimate.visitInsn(ultimateMT.getReturnType.getOpcode(asm.Opcodes.IRETURN))

            } // end of helper method buildUltimateBody()

            /**
             *  Emit in `caller` instructions that convey the arguments it receives
             *  to the invocation of `ultimate` (after adapting those arguments),
             *  also adapting the result before returning.
             * */
            def buildPlumbingBody(caller: MethodNode) {

              caller.instructions = new asm.tree.InsnList

                  def loadLocal(idx: Int, tk: BType) { caller.visitVarInsn(tk.getOpcode(asm.Opcodes.ILOAD), idx) }

              val ultimateMT = BType.getMethodType(ultimate.desc)
              val callerMT   = BType.getMethodType(caller.desc)

              // first, load the receiver (THIS)
              caller.visitVarInsn(asm.Opcodes.ALOAD, 0)

              // then, proceed to load each apply-argument
              val callerParamsBTs = callerMT.getArgumentTypes.toList
              val calleeParamsBTs = ultimateMT.getArgumentTypes.toList
              assert(callerParamsBTs.size == calleeParamsBTs.size)
              var idx = 1
              for(Pair(callerParamBT, calleeParamBT) <- callerParamsBTs.zip(calleeParamsBTs)) {
                loadLocal(idx, callerParamBT)
                spclzdAdapt(caller, callerParamBT, calleeParamBT)
                idx += callerParamBT.getSize
              }

              caller.visitMethodInsn(
                asm.Opcodes.INVOKEVIRTUAL,
                closuCNode.name,
                ultimate.name,
                ultimate.desc
              )

              spclzdAdapt(caller, ultimateMT.getReturnType, callerMT.getReturnType)

              caller.visitInsn(callerMT.getReturnType.getOpcode(asm.Opcodes.IRETURN))

            } // end of helper method buildPlumbingBody()

        buildUltimateBody()
        closuCNode.methods.add(ultimate)

        for(plumbing <- plumbings) {
          buildPlumbingBody(plumbing)
          closuCNode.methods.add(plumbing)
        }

        closuCNode.methods.add(ctor)

        for(closuMethod <- closuCNode.toMethodList) {
          // exemplars can be added only after all classes being compiled have been added to codeRepo.classes
          codeRepo.registerUnseenTypeNames(closuMethod.instructions, enterExemplars = false) // must-single-thread
        }

        log(
          s"genLateClosure: added Late-Closure-Class ${closuCNode.name} " +
          s"for endpoint ${delegateJavaName}${delegateMT} " +
          s"in class ${outerTK.getInternalName}. Enclosing method ${methodSignature(cnode, mnode)} , " +
          s"position in source file: ${fakeCallsite.pos}"
        )

        emitClosureInstantiation(closuCNode.name, ctor.desc)

        lateClosures ::= closuCNode

        closuresForDelegates.put(
          delegateSym,
          DClosureEndpoint(delegateJavaName, delegateMT, closuBT, ctor)
        )

        ifDebug {
          asm.optimiz.Util.basicInterpret(closuCNode)
        }

        castToBT
      } // end of PlainClassBuilder's genLateClosure()

      private def genArrayValue(av: ArrayValue): BType = {
        val ArrayValue(tpt @ TypeTree(), elems) = av

        val elmKind       = tpeTK(tpt)
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
       * A Match node contains one or more case clauses,
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
        val generatedType = tpeTK(tree)

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

      def adapt(from: BType, to: BType) {
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
          case Select(qualifier, _) => genLoad(qualifier, tpeTK(qualifier))
          case _                    => abort("Unknown qualifier " + tree)
        }
      }

      /** Generate code that loads args into label parameters. */
      def genLoadLabelArguments(args: List[Tree], lblDef: LabelDef, gotoPos: Position) {
        assert(args forall { a => !a.hasSymbolField || a.hasSymbolWhich( s => !s.isLabel) }, "SI-6089 at: " + gotoPos) // SI-6089

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
            case NoSymbol => abort("Cannot use package as value: " + tree) ; NoSymbol
            case s        => devWarning("Bug: found package class where package object expected.  Converting.") ; s.moduleClass
          }
        )
        lineNumber(tree)
        genLoadModule(module)
        asmClassType(module)
      }

      def genLoadModule(module: Symbol) {
        if (claszSymbol == module.moduleClass && jMethodName != "readResolve") {
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

      def genCast(to: BType, cast: Boolean) {
        if(cast) { bc checkCast  to }
        else     { bc isInstance to }
      }

      /** Is the given symbol a primitive operation? */
      def isPrimitive(fun: Symbol): Boolean = scalaPrimitives.isPrimitive(fun)

      /** Is the given symbol a MethodSymbol that was created by UnCurry's closureConversionModern() ? */
      def isClosureDelegate(msym: Symbol): Boolean = {
        msym.isInstanceOf[MethodSymbol] &&
        uncurry.closureDelegates(msym.asInstanceOf[MethodSymbol])
      }

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
              val kind = tpeTK(elem)
              genLoad(elem, kind)
              bc.genStringConcat(kind)
            }
            bc.genEndConcat

        }

        StringReference
      }

      def genCallMethod(method: Symbol, style: InvokeStyle, hostClass0: Symbol = null, pos: Position = NoPosition) {

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
        val bmOwner  = asmClassType(receiver)
        val jowner   = bmOwner.getInternalName
        val jname    = method.javaSimpleName.toString
        val bmType   = asmMethodType(method)
        val mdescr   = bmType.getDescriptor

            def initModule() {
              // we initialize the MODULE$ field immediately after the super ctor
              if (!isModuleInitialized &&
                  jMethodName == INSTANCE_CONSTRUCTOR_NAME &&
                  jname == INSTANCE_CONSTRUCTOR_NAME &&
                  isStaticModule(siteSymbol)) {
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

        if(style.isStatic) {
          if(style.hasInstance) { bc.invokespecial  (jowner, jname, mdescr) }
          else                  { bc.invokestatic   (jowner, jname, mdescr) }
        }
        else if(style.isDynamic) {
          if(isInterfaceCall(receiver)) { bc.invokeinterface(jowner, jname, mdescr) }
          else                          { bc.invokevirtual  (jowner, jname, mdescr) }
        }
        else {
          assert(style.isSuper, "An unknown InvokeStyle: " + style)
          bc.invokespecial(jowner, jname, mdescr)
          initModule()
        }

        if(settings.isIntraMethodOptimizOn) {

          /**
           * Gather data for "caching of stable values".
           *
           * The pattern matcher (and possible others) emit stable methods that take args. Our analysis won't cache invocations to them.
           */
          if(method.isStable && (bmType.getArgumentCount == 0) && !bmType.getReturnType.isUnitType) {
            repeatableReads.markAsRepeatableRead(bmOwner, jname, bmType)
          }

        } // intra-procedural optimizations

        if(settings.isInterBasicOptimizOn) {

          /**
           * Gather data for "method inlining".
           *
           * Conditions on the target method:
           *
           *   (a.1) must be marked @inline AND one of:
           *         - called via INVOKESTATIC, INVOKESPECIAL, or INVOKEVIRTUAL
           *         - method.isEffectivelyFinal (in particular, method.isFinal)
           *         The above amounts to "cannot be overridden"
           *         Therefore, the actual (runtime) method to dispatch can be determined statically,
           *         moreover without type-flow analysis. Instead, walking up the superclass-hierarchy is enough.
           *
           *   (a.2) not a self-recursive call
           *
           *   (a.3) not a super-call
           *
           * Conditions on the host method (ie the method being emitted, which hosts the callsite candidate for inlining):
           *   (b.1) not a bridge method
           * Therefore, marking a method @inline does not preclude inlining inside it.
           *
           * The callsite thus tracked may be amenable to
           *   - "closure inlining" (in case it takes one ore more closures as arguments)
           *   - or "method inlining".
           * The former will be tried first.
           */
          val knockOuts = (isMethSymBridge || (method == methSymbol) || style.isSuper)
          if(!knockOuts && hasInline(method)) {
            val callsite = mnode.instructions.getLast.asInstanceOf[MethodInsnNode]
            val opc = callsite.getOpcode
            val cannotBeOverridden = (
              opc == asm.Opcodes.INVOKESTATIC  ||
              opc == asm.Opcodes.INVOKESPECIAL ||
              method.isFinal ||
              method.isEffectivelyFinal
            ) && (
              opc != asm.Opcodes.INVOKEDYNAMIC   &&
              opc != asm.Opcodes.INVOKEINTERFACE &&
              callsite.name != "<init>"          &&
              callsite.name != "<clinit>"
            )
            if(cannotBeOverridden) {
              val isHiO = isHigherOrderMethod(bmType)
              // the callsite may be INVOKEVIRTUAL (but not INVOKEINTERFACE) in addition to INVOKESTATIC or INVOKESPECIAL.
              val inlnTarget = new InlineTarget(callsite, cunit, pos)
              if(isHiO) { cgn.hiOs  ::= inlnTarget }
              else      { cgn.procs ::= inlnTarget }
            }
          }

        } // inter-procedural optimizations

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
                val tk = maxType(tpeTK(l), tpeTK(r))
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
                if (scalaPrimitives.isUniversalEqualityOp(code) && tpeTK(lhs).hasObjectSort) {
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

        /** True if the equality comparison is between values that require the use of the rich equality
          * comparator (scala.runtime.Comparator.equals). This is the case when either side of the
          * comparison might have a run-time type subtype of java.lang.Number or java.lang.Character.
          * When it is statically known that both sides are equal and subtypes of Number of Character,
          * not using the rich equality is possible (their own equals method will do ok.)*/
        val mustUseAnyComparator: Boolean = {
          val areSameFinals = l.tpe.isFinalType && r.tpe.isFinalType && (l.tpe =:= r.tpe)

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
            val eqEqTempLocal = makeLocal(AnyRefReference, nme.EQEQ_LOCAL_VAR.toString)
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

      /** can-multi-thread **/
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
