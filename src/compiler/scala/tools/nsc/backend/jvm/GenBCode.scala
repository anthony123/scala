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

/** Prepare in-memory representations of classfiles using the ASM Tree API, and serialize them to disk.
 *
 *  @author  Miguel Garcia, http://lamp.epfl.ch/~magarcia/ScalaCompilerCornerReloaded/
 *  @version 1.0
 */
abstract class GenBCode extends BCodeUtils with BCodeTypes {
  import global._
  import icodes._
  import icodes.opcodes._
  import definitions._

  val phaseName = "jvm"

  override def newPhase(prev: Phase) = new BCodePhase(prev)

  class BCodePhase(prev: Phase)
    extends StdPhase(prev)
    with    BCInitGen
    with    BCJGenSigGen
    with    BCCommonPhase {

    override def name = phaseName
    override def description = "Generate bytecode from ASTs"
    override def erasedTypes = true

    private var bytecodeWriter  : BytecodeWriter   = null
    private var mirrorCodeGen   : JMirrorBuilder   = null
    private var beanInfoCodeGen : JBeanInfoBuilder = null

    /* ---------------- what is currently being visited ---------------- */

    // current compilation unit and package
    private var cunit: CompilationUnit     = null
    private val pkg = new mutable.Stack[String]
    // current class
    private var cnode: asm.tree.ClassNode  = null
    private var thisName: String           = null // the internal name of the class being emitted
    private var claszSymbol: Symbol        = null
    // current method
    private var mnode: asm.tree.MethodNode = null
    private var jMethodName: String        = null
    private var isModuleInitialized        = false // in GenASM this is local to genCode(), ie should get false whenever a new method is emitted (including fabricated ones eg addStaticInit())
    private var methSymbol: Symbol         = null
    // used by genLoadTry() and genSynchronized()
    private var earlyReturnVar: Symbol     = null
    private var shouldEmitCleanup          = false
    // used in connection with cleanups
    private var returnType: asm.Type       = null
    private var returnTpe:  Type           = null
    // line numbers
    private var lastEmittedLineNr          = -1

    // bookkeeping for program points within a method associated to LabelDefs (other program points aren't tracked here).
    private var locLabel: immutable.Map[ /* LabelDef */ Symbol, asm.Label ] = null
    def programPoint(labelSym: Symbol): asm.Label = {
      assert(labelSym.isLabel, "trying to map a non-label symbol to an asm.Label, at: " + labelSym.pos)
      locLabel.getOrElse(labelSym, {
        val pp = new asm.Label
        locLabel += (labelSym -> pp)
        pp
      })
    }

    // bookkeeping for cleanup tasks to perform on leaving a method due to return statement under active (monitor-exits, finally-clauses)
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

    // bookkeeping for method-local vars and params
    private val locals = mutable.Map.empty[Symbol, Local] // (local-or-param-sym -> Local(TypeKind, name, idx))
    private var nxtIdx = -1 // next available index for local-var
    def index(sym: Symbol): Int = {
      locals.getOrElseUpdate(sym, makeLocal(sym)).idx
    }
    /** Make a fresh local variable, ensuring a unique name.
     *  The invoker must make sure inner classes are tracked for the sym's tpe. */
    def makeLocal(tpe: Type, name: String): Symbol = {
      val sym = methSymbol.newVariable(cunit.freshTermName(name), NoPosition, Flags.SYNTHETIC) setInfo tpe
      makeLocal(sym)
      sym
    }
    def makeLocal(sym: Symbol): Local = {
      assert(!locals.contains(sym), "attempt to create duplicate local var.")
      assert(nxtIdx != -1, "not a valid start index")
      val tk  = toTypeKind(sym.info)
      val loc = Local(tk, sym.javaSimpleName.toString, nxtIdx)
      locals += (sym -> loc)
      assert(tk.getSize > 0, "makeLocal called for a symbol whose type is Unit.")
      nxtIdx += tk.getSize
      loc
    }
    def store(locSym: Symbol) {
      val Local(tk, _, idx) = locals(locSym)
      bc.store(idx, tk)
    }
    def load(locSym: Symbol) {
      val Local(tk, _, idx) = locals(locSym)
      bc.load(idx, tk)
    }

    // bookkeeping: all LabelDefs a method contains (useful when duplicating any `finally` clauses containing one or more LabelDef)
    var labelDefsAtOrUnder: collection.Map[Tree, List[LabelDef]] = null
    var labelDef: collection.Map[Symbol, LabelDef] = null// (LabelDef-sym -> LabelDef)

    // bookkeeping the scopes of non-synthetic local vars, to emit debug info (`emitVars`).
    var varsInScope: immutable.Map[Symbol, asm.Label] = null // (local-var-sym -> start-of-scope)

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
      if (dd.symbol.isConstructor) {
        returnTpe  = null // not needed in this case
        returnType = UNIT
      }
      else {
        returnTpe  = dd.symbol.info.resultType
        returnType = toTypeKind(returnTpe)
      }
      lastEmittedLineNr = -1
    }

    override def getCurrentCUnit(): CompilationUnit = { cunit }

    def isParcelableClass = isAndroidParcelableClass(claszSymbol)

    // see https://github.com/scala/scala/commit/892ee3df93a10ffe24fb11b37ad7c3a9cb93d5de
    def isAccessorToStaticField(msym: Symbol) = { msym.isAccessor && msym.accessed.hasStaticAnnotation }
    def isStaticField(fsym: Symbol) = {  fsym.owner.isModuleClass && fsym.hasStaticAnnotation }

    override def run() {
      scalaPrimitives.init
      bytecodeWriter  = initBytecodeWriter(cleanup.getEntryPoints)
      mirrorCodeGen   = new JMirrorBuilder(bytecodeWriter)
      beanInfoCodeGen = new JBeanInfoBuilder(bytecodeWriter)
      super.run()
      bytecodeWriter.close()
      reverseJavaName.clear()
    }

    override def apply(unit: CompilationUnit): Unit = {
      this.cunit = unit
      gen(unit.body)
      this.cunit = NoCompilationUnit
    }

    object bc extends JCodeMethodN {
      override def jmethod = BCodePhase.this.mnode
    }

    /** If the selector type has a member with the right name,
     *  it is the host class; otherwise the symbol's owner.
     */
    def findHostClass(selector: Type, sym: Symbol) = selector member sym.name match { // TODO de-duplicate with GenICode
      case NoSymbol   => log(s"Rejecting $selector as host class for $sym") ; sym.owner
      case _          => selector.typeSymbol
    }

    /* ---------------- top-down traversal invoking ASM Tree API along the way ---------------- */

    def gen(tree: Tree) {
      tree match {
        case EmptyTree => ()

        case PackageDef(pid, stats) =>
          pkg push pid.name.toString
          stats foreach gen
          pkg.pop()

        case cd: ClassDef =>
          claszSymbol = cd.symbol
          // mirror class, if needed
          if (isStaticModule(claszSymbol) && isTopLevelModule(claszSymbol)) {
            if (claszSymbol.companionClass == NoSymbol) {
              mirrorCodeGen.genMirrorClass(claszSymbol, cunit)
            } else {
              log("No mirror class for module with linked class: " + claszSymbol.fullName)
            }
          }
          // "plain" class
          genPlainClass(cd)
          // bean info class, if needed
          if (claszSymbol hasAnnotation BeanInfoAttr) {
            beanInfoCodeGen.genBeanInfoClass(
              claszSymbol, cunit,
              fieldSymbols(claszSymbol),
              methodSymbols(cd)
            )
          }

        case _: ModuleDef => abort("Modules should have been eliminated by refchecks: " + tree)

        case ValDef(mods, name, tpt, rhs) => () // fields are added in the case handler for ClassDef

        case dd : DefDef => genDefDef(dd)

        case Template(_, _, body) => body foreach gen

        case _ => abort("Illegal tree in gen: " + tree)
      }
    } // end of method gen(Tree)

    /* if you look closely, you'll notice almost no code duplication with JBuilder's `writeIfNotTooBig()` */
    def writeIfNotTooBig(label: String, jclassName: String, cnode: asm.tree.ClassNode, sym: Symbol) {
      try {
        val cw = new CClassWriter(extraProc)
        cnode.accept(cw)
        val arr = cw.toByteArray
        bytecodeWriter.writeClass(label, jclassName, arr, sym)
      } catch {
        case e: java.lang.RuntimeException if(e.getMessage() == "Class file too large!") =>
          // TODO check where ASM throws the equivalent of CodeSizeTooBigException
          log("Skipped class "+jclassName+" because it exceeds JVM limits (it's too big or has methods that are too long).")
      }
    }

    /* ---------------- helper utils for generating classes and fiels ---------------- */

    def genPlainClass(cd: ClassDef) {
      assert(cnode == null, "GenBCode detected nested methods.")
      innerClassBuffer.clear()

      val csym = cd.symbol
      thisName = javaName(csym)
      cnode = new asm.tree.ClassNode()
      initJClass(cnode, csym, thisName, getGenericSignature(csym, csym.owner), cunit)

      val hasStaticCtor = methodSymbols(cd) exists (_.isStaticConstructor)
      if(!hasStaticCtor) {
        // but needs one ...
        if(isStaticModule(claszSymbol) || isAndroidParcelableClass(claszSymbol)) {
          fabricateStaticInit()
        }
      }

      addSerialVUID(csym, cnode)
      addClassFields(csym)
      gen(cd.impl)
      addInnerClasses(csym, cnode)

      /*
       * TODO this is a good time to collapse jump-chains, perform dce and remove unused locals, on the asm.tree.ClassNode.
       * See Ch. 8. "Method Analysis" in the ASM User Guide, http://download.forge.objectweb.org/asm/asm4-guide.pdf
       **/
      writeIfNotTooBig("" + csym.name, thisName, cnode, csym)
      cnode = null

      assert(cd.symbol == claszSymbol, "Someone messed up BCodePhase.claszSymbol during genPlainClass().")

    } // end of method genPlainClass()

    /** TODO document, explain interplay with `appendToStaticCtor()` */
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
      if (isParcelableClass) { legacyAddCreatorCode(clinit, cnode, claszSymbol, thisName) }
      clinit.visitInsn(asm.Opcodes.RETURN)

      clinit.visitMaxs(0, 0) // just to follow protocol, dummy arguments
      clinit.visitEnd()
    }

    private def fieldSymbols(cls: Symbol): List[Symbol] = {
      for (f <- cls.info.decls.toList ;
           if !f.isMethod && f.isTerm && !f.isModule && !isStaticField(f)
      ) yield f;
    }

    private def skipMethod(msym: Symbol): Boolean = {
      msym.isStaticConstructor || definitions.isGetClass(msym)
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
          toTypeKind(f.tpe).getDescriptor(),
          javagensig,
          null // no initial value
        )
        cnode.fields.add(jfield)
        emitAnnotations(jfield, f.annotations)
      }

    } // end of method addClassFields()

    /* ---------------- helper utils for generating methods and code ---------------- */

    @inline final def emit(opc: Int) { mnode.visitInsn(opc) }
    @inline final def emit(i: asm.tree.AbstractInsnNode) { mnode.instructions.add(i) }

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

      val params      = if(vparamss.isEmpty) Nil else vparamss.head
      methSymbol      = msym
      val Pair(flags, jmethod0) = initJMethod(
        cnode,
        msym, isNative,
        claszSymbol,  claszSymbol.isInterface,
        params.map(p => toTypeKind(p.symbol.info)),
        params.map(p => p.symbol.annotations)
      )
      mnode       = jmethod0.asInstanceOf[asm.tree.MethodNode]
      jMethodName = msym.javaSimpleName.toString

      // add method-local vars for params
      nxtIdx = if (msym.isStaticMember) 0 else 1;
      for (p <- params) { makeLocal(p.symbol) }
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
        makeLocal(p.symbol)
      }

            def emitBodyOfStaticAccessor() {
              // in companion object accessors to @static fields, we access the static field directly
              // see https://github.com/scala/scala/commit/892ee3df93a10ffe24fb11b37ad7c3a9cb93d5de
              val hostClass   = msym.owner.companionClass
              val fieldName   = msym.accessed.javaSimpleName.toString
              val staticfield = hostClass.info.findMember(msym.accessed.name, NoFlags, NoFlags, false)
              val fieldDescr  = toTypeKind(staticfield.tpe).getDescriptor

              if (msym.isGetter) {
                // GETSTATIC `hostClass`.`accessed`
                emit(
                  new asm.tree.FieldInsnNode(asm.Opcodes.GETSTATIC,
                                             javaName(hostClass),
                                             fieldName.toString,
                                             fieldDescr)
                )
                // RETURN `returnType`
                bc emitRETURN returnType
              } else if (msym.isSetter) {
                // push setter's argument
                load(params.head.symbol)
                // GETSTATIC `hostClass`.`accessed`
                emit(
                  new asm.tree.FieldInsnNode(asm.Opcodes.PUTSTATIC,
                                             javaName(hostClass),
                                             fieldName.toString,
                                             fieldDescr)
                )
                // RETURN `returnType`
                bc emitRETURN returnType
              } else assert(false, "unreachable")
            }

      if (!isAbstractMethod && !isNative) {
        lineNumber(rhs)
        if(isAccessorToStaticField(msym)) {
          // special-cased method body for an accessor to @static field
          emitBodyOfStaticAccessor()
        } else {
          // normal method body
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
              mnode.visitLocalVariable("this", thisDescr(thisName), null, veryFirstProgramPoint, onePastLastProgramPoint, 0)
            }
            for (p <- params) { emitLocalVarScope(p.symbol, veryFirstProgramPoint, onePastLastProgramPoint, force = true) }
          }

          if(methSymbol.isStaticConstructor) {
            appendToStaticCtor(dd)
          }

        }

        // Note we don't invoke visitMax, thus there are no FrameNode among mnode.instructions.
        // The only non-instruction nodes to be found are LabelNode and LineNumberNode.
      }
      mnode = null
    } // end of method genDefDef()

    /** TODO document, explain interplay with `fabricateStaticInit()` */
    private def appendToStaticCtor(dd: DefDef) {

          def insertBefore(location: asm.tree.AbstractInsnNode, insns: List[asm.tree.AbstractInsnNode]) {
            insns foreach { i => mnode.instructions.insertBefore(location, i) }
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
        andrFieldName = newTermName(androidFieldName)
        val fieldAccess    = asm.Opcodes.ACC_STATIC | asm.Opcodes.ACC_FINAL
        val fieldType      = javaName(AndroidCreatorClass) // tracks inner classes if any.
        val andrFieldDescr = toTypeKind(AndroidCreatorClass.tpe).getDescriptor
        cnode.visitField(fieldAccess, andrFieldName, andrFieldDescr, null, null)
      }

      // insert a few instructions for initialization before each return instruction
      for(r <- rets) {

        if (isStaticModule(claszSymbol)) { // call object's private ctor from static ctor

          // NEW `moduleName`
          val className = javaName(methSymbol.enclClass)
          val i0 = new asm.tree.TypeInsnNode(asm.Opcodes.NEW, className)

          // INVOKESPECIAL <init>
          val callee = methSymbol.enclClass.primaryConstructor
          val jname  = callee.javaSimpleName.toString
          val jowner = javaName(callee.owner)
          val jtype  = asmMethodType(callee).getDescriptor()
          val i1 = new asm.tree.MethodInsnNode(asm.Opcodes.INVOKESPECIAL, jowner, jname, jtype)

          insertBefore(r, List(i0, i1))
        }

        if(isParcelableClass) { // android creator code

          // INVOKESTATIC CREATOR(): android.os.Parcelable$Creator; -- TODO where does this Android method come from?
          val callee = definitions.getMember(claszSymbol.companionModule, androidFieldName)
          val jowner = javaName(callee.owner)
          val jname  = callee.javaSimpleName.toString
          val jtype  = asmMethodType(callee).getDescriptor()
          val i0 = new asm.tree.MethodInsnNode(asm.Opcodes.INVOKESTATIC, jowner, jname, jtype)

          // PUTSTATIC `thisName`.CREATOR;
          val i1 = new asm.tree.FieldInsnNode(asm.Opcodes.PUTSTATIC, thisName, andrFieldName, andrFieldDescr)

          insertBefore(r, List(i0, i1))
        }

      }


    }

    private def emitLocalVarScope(sym: Symbol, start: asm.Label, end: asm.Label, force: Boolean = false) {
      if(force || !sym.isSynthetic /* TODO HIDDEN */ ) {
        val Local(tk, name, idx) = locals(sym)
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
          bc fieldStore lhs.symbol

        case Assign(lhs, rhs) =>
          val tk = toTypeKind(lhs.symbol.info)
          genLoad(rhs, tk)
          lineNumber(tree)
          bc.store(index(lhs.symbol), tk)

        case _ =>
          genLoad(tree, UNIT)
      }
    }

    def genThrow(expr: Tree): asm.Type = {
      require(expr.tpe <:< ThrowableClass.tpe, expr.tpe)

      val thrownKind = toTypeKind(expr.tpe)
      genLoad(expr, thrownKind)
      lineNumber(expr)
      emit(asm.Opcodes.ATHROW) // ICode enters here into enterIgnoreMode, we'll rely instead on DCE at ClassNode level.

      NothingReference // always returns the same, the invoker should know :)
    }

    /** Generate code for primitive arithmetic operations. */
    def genArithmeticOp(tree: Tree, code: Int): asm.Type = {
      val Apply(fun @ Select(larg, _), args) = tree
      var resKind = toTypeKind(larg.tpe)

      assert(args.length <= 1, "Too many arguments for primitive function: " + fun.symbol)
      assert(isNumericType(resKind) | resKind == BOOL,
               resKind.toString() + " is not a numeric or boolean type " + "[operation: " + fun.symbol + "]")

      args match {
        // unary operation
        case Nil =>
          genLoad(larg, resKind)
          code match {
            case scalaPrimitives.POS => () // nothing
            case scalaPrimitives.NEG => bc.genPrimitiveNegation(resKind)
            case scalaPrimitives.NOT => bc.genPrimitiveArithmetic(NOT, resKind)
            case _ => abort("Unknown unary operation: " + fun.symbol.fullName + " code: " + code)
          }

        // binary operation
        case rarg :: Nil =>
          resKind = getMaxType(larg.tpe :: rarg.tpe :: Nil);
          if (scalaPrimitives.isShiftOp(code) || scalaPrimitives.isBitwiseOp(code))
            assert(isIntegralType(resKind) | resKind == BOOL,
                   resKind.toString() + " incompatible with arithmetic modulo operation.");

          genLoad(larg, resKind)
          genLoad(rarg, // check .NET size of shift arguments!
                  if (scalaPrimitives.isShiftOp(code)) INT else resKind)

          code match {
            case scalaPrimitives.ADD    => bc.genPrimitiveArithmetic(ADD, resKind)
            case scalaPrimitives.SUB    => bc.genPrimitiveArithmetic(SUB, resKind)
            case scalaPrimitives.MUL    => bc.genPrimitiveArithmetic(MUL, resKind)
            case scalaPrimitives.DIV    => bc.genPrimitiveArithmetic(DIV, resKind)
            case scalaPrimitives.MOD    => bc.genPrimitiveArithmetic(REM, resKind)

            case scalaPrimitives.OR     => bc.genPrimitiveLogical(OR,  resKind)
            case scalaPrimitives.XOR    => bc.genPrimitiveLogical(XOR, resKind)
            case scalaPrimitives.AND    => bc.genPrimitiveLogical(AND, resKind)

            case scalaPrimitives.LSL    => bc.genPrimitiveShift(LSL, resKind)
            case scalaPrimitives.LSR    => bc.genPrimitiveShift(LSR, resKind)
            case scalaPrimitives.ASR    => bc.genPrimitiveShift(ASR, resKind)
            case _                      => abort("Unknown primitive: " + fun.symbol + "[" + code + "]")
          }

        case _ =>
          abort("Too many arguments for primitive function: " + tree)
      }
      lineNumber(tree)
      resKind
    }

    /** Generate primitive array operations. */
    def genArrayOp(tree: Tree, code: Int, expectedType: asm.Type): asm.Type = {
      val Apply(Select(arrayObj, _), args) = tree
      val k    = toTypeKind(arrayObj.tpe)
      val elem = componentType(k)
      genLoad(arrayObj, k)
      val elementType = typeOfArrayOp.getOrElse(code, abort("Unknown operation on arrays: " + tree + " code: " + code))

      var generatedType = expectedType

      if (scalaPrimitives.isArrayGet(code)) {
        // load argument on stack
        assert(args.length == 1, "Too many arguments for array get operation: " + tree);
        genLoad(args.head, INT)
        generatedType = elem
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

    def genSynchronized(tree: Apply, expectedType: asm.Type): asm.Type = {
      val Apply(fun, args) = tree
      val monitor = makeLocal(ObjectClass.tpe, "monitor")
      val monCleanup = new asm.Label

      // if the synchronized block returns a result, store it in a local variable.
      // Just leaving it on the stack is not valid in MSIL (stack is cleaned when leaving try-blocks).
      val hasResult = (expectedType != UNIT)
      val monitorResult: Symbol = if(hasResult) makeLocal(args.head.tpe, "monitorResult") else null;

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

    def genLoadIf(tree: If, expectedType: asm.Type): asm.Type = {
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
    def genLoadTry(tree: Try): asm.Type = {

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
      val tmp          = if(guardResult) makeLocal(tree.tpe, "tmp") else null;
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
        var excType: asm.Type     = null
        registerCleanup(finCleanup)
        ch match {
          case NamelessEH(typeToDrop, caseBody) =>
            bc drop typeToDrop
            genLoad(caseBody, kind) // adapts caseBody to `kind`, thus it can be stored, if `guardResult`, in `tmp`.
            nopIfNeeded(startHandler)
            endHandler = currProgramPoint()
            excType = typeToDrop

          case BoundEH   (patSymbol,      caseBody) =>
            if(!locals.contains(patSymbol)) { // test\files\run\contrib674.scala , a local-var already exists for patSymbol.
              makeLocal(patSymbol) // rather than creating on first-access, we do it right away to emit debug-info for the created local var.
            }
            store(patSymbol)
            genLoad(caseBody, kind)
            nopIfNeeded(startHandler)
            endHandler = currProgramPoint()
            emitLocalVarScope(patSymbol, startHandler, endHandler)
            excType = toTypeKind(patSymbol.tpe)
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
        val Local(eTK, _, eIdx) = locals(makeLocal(ThrowableClass.tpe, "exc"))
        bc.store(eIdx, eTK)
        emitFinalizer(finalizer, null, true)
        bc.load(eIdx, eTK)
        emit(asm.Opcodes.ATHROW)
      }

      /* ------ (3.B) Cleanup-version of the finally-clause.
       *              Reached upon early RETURN from (1) or from one of the EHs in (2)
       *                     (and only from there, ie the only from program regions bracketed by registerCleanup/unregisterCleanup).
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

    private def protect(start: asm.Label, end: asm.Label, handler: asm.Label, excType: asm.Type) {
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

    def genPrimitiveOp(tree: Apply, expectedType: asm.Type): asm.Type = {
      val sym = tree.symbol
      val Apply(fun @ Select(receiver, _), args) = tree
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
        genCoercion(tree, code)
        coercionTo(code)
      }
      else abort(
        "Primitive operation not handled yet: " + sym.fullName + "(" +
        fun.symbol.simpleName + ") " + " at: " + (tree.pos)
      )
    }

    /** Generate code for trees that produce values on the stack */
    def genLoad(tree: Tree, expectedType: asm.Type) {
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
          val Local(tk, _, idx) = locals.getOrElseUpdate(sym, makeLocal(sym))
          if (rhs == EmptyTree) { bc.genConstant(getZeroOf(tk)) }
          else { genLoad(rhs, tk) }
          bc.store(idx, tk)
          if(!sym.isSynthetic) { // there are case <synthetic> ValDef's emitted by patmat
            varsInScope += (sym -> currProgramPoint())
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
          abort("Unexpected New(" + tpt.summaryString + "/" + tpt + ") received in icode.\n" +
                "  Call was genLoad" + ((tree, expectedType)))

        case app : Apply =>
          generatedType = genApply(app, expectedType)

        case ApplyDynamic(qual, args) => sys.error("No invokedynamic support yet.")

        case This(qual) =>
          assert(tree.symbol == claszSymbol || tree.symbol.isModuleClass,
                 "Trying to access the this of another class: " +
                 "tree.symbol = " + tree.symbol + ", class symbol = " + claszSymbol + " compilation unit:"+ cunit)
          if (tree.symbol.isModuleClass && tree.symbol != claszSymbol) {
            genLoadModule(tree)
            generatedType = asm.Type.getObjectType(javaName(tree.symbol))
          }
          else {
            mnode.visitVarInsn(asm.Opcodes.ALOAD, 0)
            generatedType = if (tree.symbol == ArrayClass) ObjectReference else asm.Type.getObjectType(thisName)
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
          else if (sym.isStaticMember) { bc.fieldLoad(sym, hostClass) }
          else {
            genLoadQualifier(tree)
            bc.fieldLoad(sym, hostClass)
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
            case (NullTag,  _     ) => bc.emit(asm.Opcodes.ACONST_NULL); generatedType = NullReference
            case _                  => bc.genConstant(value);            generatedType = toTypeKind(tree.tpe)
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

        case EmptyTree => if (expectedType != UNIT) { bc genConstant getZeroOf(expectedType) }

        case _ => abort("Unexpected tree in genLoad: " + tree + "/" + tree.getClass + " at: " + tree.pos)
      }

      // emit conversion
      if (generatedType != expectedType) {
        adapt(generatedType, expectedType)
      }

    } // end of GenBCode.genLoad()

    private def genLabelDef(lblDf: LabelDef, expectedType: asm.Type) {
      // duplication of `finally`-contained LabelDefs is handled when emitting a RET. No bookkeeping for that required here.
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
                earlyReturnVar = makeLocal(returnTpe, "earlyReturnVar")
              }
              store(earlyReturnVar)
            }
          }
          bc goTo nextCleanup
          shouldEmitCleanup = true
      }

    } // end of genReturn()

    private def genApply(tree: Apply, expectedType: asm.Type): asm.Type = {
      var generatedType = expectedType
      lineNumber(tree)
      tree match {

        case Apply(TypeApply(fun, targs), _) =>
          val sym = fun.symbol
          val cast = sym match {
            case Object_isInstanceOf  => false
            case Object_asInstanceOf  => true
            case _                    => abort("Unexpected type application " + fun + "[sym: " + sym.fullName + "]" + " in: " + tree)
          }

          val Select(obj, _) = fun
          val l = toTypeKind(obj.tpe)
          val r = toTypeKind(targs.head.tpe)
          genLoadQualifier(fun)

          if (isValueType(l) && isValueType(r))
            genConversion(l, r, cast)
          else if (isValueType(l)) {
            bc drop l
            if (cast) {
              mnode.visitTypeInsn(asm.Opcodes.NEW, javaName(definitions.ClassCastExceptionClass))
              bc dup ObjectReference
              emit(asm.Opcodes.ATHROW)
            } else {
              bc boolconst false
            }
          }
          else if (isValueType(r) && cast) {
            assert(false, tree) /* Erasure should have added an unboxing operation to prevent that. */
          }
          else if (isValueType(r)) {
            bc isInstance classLiteral(r)
          }
          else {
            genCast(l, r, cast)
          }
          generatedType = if (cast) r else BOOL;

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
          genLoadArguments(args, fun.symbol.info.paramTypes)
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
          assert(isRefOrArrayType(generatedType), "Non reference type cannot be instantiated: " + generatedType)

          generatedType match {
            case arr if isArrayType(generatedType) =>
              genLoadArguments(args, ctor.info.paramTypes)
              val dims = arr.getDimensions
              var elemKind = arr.getElementType
              if (args.length > dims) {
                cunit.error(tree.pos, "too many arguments for array constructor: found " + args.length +
                                      " but array has only " + dims + " dimension(s)")
              }
              if (args.length != dims) {
                for (i <- args.length until dims) elemKind = arrayOf(elemKind)
              }
              args.length match {
                case 1          => bc newarray elemKind
                case dimensions => mnode.visitMultiANewArrayInsn(arrayN(elemKind, dimensions).getDescriptor, dimensions)
              }

            case rt if isReferenceType(generatedType) =>
              // TODO RE-ENABLE assert(ctor.owner == classSymbol(rt), "Symbol " + ctor.owner.fullName + " is different than " + tpt)
              mnode.visitTypeInsn(asm.Opcodes.NEW, rt.getInternalName)
              bc dup generatedType
              genLoadArguments(args, ctor.info.paramTypes)
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
            val loc1 = makeLocal(expr.tpe, "boxed")
            store(loc1)
            load(loc1)
          }
          val MethodNameAndType(mname, mdesc) = asmBoxTo(nativeKind)
          bc.invokestatic(BoxesRunTime, mname, mdesc)
          generatedType = toTypeKind(fun.symbol.tpe.resultType)

        case Apply(fun @ _, List(expr)) if (definitions.isUnbox(fun.symbol)) =>
          genLoad(expr, toTypeKind(expr.tpe))
          val boxType = toTypeKind(fun.symbol.owner.linkedClassOfClass.tpe)
          generatedType = boxType
          val MethodNameAndType(mname, mdesc) = asmUnboxTo(boxType)
          bc.invokestatic(BoxesRunTime, mname, mdesc)

        case app @ Apply(fun @ Select(qual, _), args)
        if !methSymbol.isStaticConstructor
        && isAccessorToStaticField(fun.symbol)
        && qual.tpe.typeSymbol.orElse(fun.symbol.owner).companionClass != NoSymbol =>
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
              val staticfield = hostClass.newVariable(newTermName(sym.accessed.name.toString), tree.pos, STATIC | SYNTHETIC | FINAL) setInfo objectfield.tpe
              staticfield.addAnnotation(definitions.StaticClass)
              hostClass.info.decls enter staticfield
              staticfield
            } else NoSymbol
          }
          val fieldDescr  = toTypeKind(staticfield.tpe).getDescriptor

          if (sym.isGetter) {
            // GETSTATIC `hostClass`.`accessed`
            emit(
              new asm.tree.FieldInsnNode(asm.Opcodes.GETSTATIC,
                                         javaName(hostClass),
                                         fieldName,
                                         fieldDescr)
            )
          } else if (sym.isSetter) {
            // push setter's argument
            genLoadArguments(args, sym.info.paramTypes)
            // GETSTATIC `hostClass`.`accessed`
            emit(
              new asm.tree.FieldInsnNode(asm.Opcodes.PUTSTATIC,
                                         javaName(hostClass),
                                         fieldName,
                                         fieldDescr)
            )
            // push false
            bc.boolconst(false) // TODO what purpose does this serve ...
          } else {
            assert(false, "supposedly unreachable")
          }

        case app @ Apply(fun, args) =>
          val sym = fun.symbol

          if (sym.isLabel) {  // jump to a label
            genLoadLabelArguments(args, labelDef(sym), tree.pos)
            bc goTo programPoint(sym)
          } else if (isPrimitive(sym)) { // primitive method call
            generatedType = genPrimitiveOp(app, expectedType)
          } else {  // normal method call
            val invokeStyle =
              if (sym.isStaticMember) Static(false)
              else if (sym.isPrivate || sym.isClassConstructor) Static(true)
              else Dynamic;

            if (invokeStyle.hasInstance) {
              genLoadQualifier(fun)
            }

            genLoadArguments(args, sym.info.paramTypes)

            // In "a couple cases", squirrel away a extra information (hostClass, targetTypeKind). TODO Document what "in a couple cases" refers to.
            var hostClass: Symbol        = null
            var targetTypeKind: asm.Type = null
            fun match {
              case Select(qual, _) =>
                val qualSym = findHostClass(qual.tpe, sym)
                if (qualSym == ArrayClass) { targetTypeKind = toTypeKind(qual.tpe) }
                else { hostClass = qualSym }

                log(
                  if (qualSym == ArrayClass) "Stored target type kind " + toTypeKind(qual.tpe) + " for " + sym.fullName
                  else s"Set more precise host class for ${sym.fullName} hostClass: $qualSym"
                )
              case _ =>
            }
            if((targetTypeKind != null) && (sym == definitions.Array_clone) && invokeStyle.isDynamic) {
              val target: String = targetTypeKind.getInternalName
              bc.invokevirtual(target, "clone", mdesc_arrayClone)
            }
            else {
              genCallMethod(sym, invokeStyle, hostClass)
            }

            // TODO if (sym == ctx1.method.symbol) { ctx1.method.recursive = true }
            generatedType =
              if (sym.isClassConstructor) UNIT
              else toTypeKind(sym.info.resultType);
          }

      }

      generatedType
    } // end of GenBCode's genApply()

    private def genArrayValue(av: ArrayValue): asm.Type = {
      val ArrayValue(tpt @ TypeTree(), elems0) = av

      val elmKind       = toTypeKind(tpt.tpe)
      var generatedType = arrayOf(elmKind)
      val elems         = elems0.toIndexedSeq

      lineNumber(av)
      bc iconst   elems.length
      bc newarray elmKind

      var i = 0
      while (i < elems.length) {
        bc dup     generatedType
        bc iconst  i
        genLoad(elems(i), elmKind)
        bc astore  elmKind
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
    private def genMatch(tree: Match): asm.Type = {
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
      bc.emitSWITCH(flatKeys.reverse.toArray, targets.reverse.toArray, default, MIN_SWITCH_DENSITY)

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

    def genBlock(tree: Block, expectedType: asm.Type) {
      val Block(stats, expr) = tree
      val savedScope = varsInScope
      varsInScope = immutable.Map.empty[Symbol, asm.Label]
      stats foreach genStat
      genLoad(expr, expectedType)
      val end = currProgramPoint()
      if(emitVars) { // add entries to LocalVariableTable JVM attribute
        for (Pair(sym, start) <- varsInScope) { emitLocalVarScope(sym, start, end) }
      }
      varsInScope = savedScope
    }

    def adapt(from: asm.Type, to: asm.Type): Unit = {
      if (!(<:<(from, to)) && !(from == NullReference && to == NothingReference)) {
        to match {
          case UNIT => bc drop from
          case _    => bc.emitT2T(from, to)
        }
      } else if (from == NothingReference) {
        emit(asm.Opcodes.ATHROW) // ICode enters here into enterIgnoreMode, we'll rely instead on DCE at ClassNode level.
      } else if (from == NullReference) {
        bc drop from
        mnode.visitInsn(asm.Opcodes.ACONST_NULL)
      }
      else if (from == ThrowableReference && !(ThrowableClass.tpe <:< toType(to))) {
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
      val params: List[Symbol] = lblDef.params.map(_.symbol)
      assert(args.length == params.length, "Wrong number of arguments in call to label at: " + gotoPos)

          def isTrivial(kv: (Tree, Symbol)) = kv match {
            case (This(_), p) if p.name == nme.THIS     => true
            case (arg @ Ident(_), p) if arg.symbol == p => true
            case _                                      => false
          }

      val aps = ((args zip params) filterNot isTrivial)

      // first push *all* arguments. This makes sure any labelDef-var will use the previous value.
      aps foreach { case (arg, param) => genLoad(arg, locals(param).tk) }

      // second assign one by one to the LabelDef's variables.
      aps.reverse foreach {
        case (_, param) =>
          // TODO FIXME a "this" param results from tail-call xform. If so, the `else` branch seems perfectly fine. And the `then` branch must be wrong.
          if (param.name == nme.THIS) mnode.visitVarInsn(asm.Opcodes.ASTORE, 0)
          else bc.store(index(param), locals(param).tk)
      }

    }

    def genLoadArguments(args: List[Tree], tpes: List[Type]) {
      (args zip tpes) foreach { case (arg, tpe) => genLoad(arg, toTypeKind(tpe)) }
    }

    def genLoadModule(tree: Tree) {
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
    }

    def genLoadModule(module: Symbol) {
      if (claszSymbol == module.moduleClass && jMethodName != nme.readResolve.toString) {
        mnode.visitVarInsn(asm.Opcodes.ALOAD, 0)
      } else {
        mnode.visitFieldInsn(
          asm.Opcodes.GETSTATIC,
          javaName(module) /* + "$" */ ,
          strMODULE_INSTANCE_FIELD,
          toTypeKind(module.tpe).getDescriptor
        )
      }
    }

    def genConversion(from: asm.Type, to: asm.Type, cast: Boolean) = {
      if (cast) { bc.emitT2T(from, to) }
      else {
        bc drop from
        bc boolconst (from == to)
      }
    }

    def genCast(from: asm.Type, to: asm.Type, cast: Boolean) {
      if(cast) { bc checkCast  to }
      else     { bc isInstance to }
    }

    def getZeroOf(k: asm.Type): Constant = k match {
      case UNIT    => Constant(())
      case BOOL    => Constant(false)
      case BYTE    => Constant(0: Byte)
      case SHORT   => Constant(0: Short)
      case CHAR    => Constant(0: Char)
      case INT     => Constant(0: Int)
      case LONG    => Constant(0: Long)
      case FLOAT   => Constant(0.0f)
      case DOUBLE  => Constant(0.0d)
      case _       => Constant(null: Any)
    }


    /** Is the given symbol a primitive operation? */
    def isPrimitive(fun: Symbol): Boolean = scalaPrimitives.isPrimitive(fun)

    /** Generate coercion denoted by "code" */
    def genCoercion(tree: Tree, code: Int) = {
      lineNumber(tree)
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

    def genStringConcat(tree: Tree): asm.Type = {
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

      val hostClass = if(hostClass0 == null) method.owner else hostClass0;

      isModuleInitialized =
        bc.genCallMethod(
          method,      style,     jMethodName,
          claszSymbol, hostClass, thisName,    isModuleInitialized
        )

    } // end of genCode()'s genCallMethod()

    /** Generate the scala ## method. */
    def genScalaHash(tree: Tree): asm.Type = {
      genLoadModule(ScalaRunTimeModule) // TODO why load ScalaRunTimeModule if ## has InvokeStyle of Static(false) ?
      genLoad(tree, ObjectReference)
      val hashMethod = getMember(ScalaRunTimeModule, nme.hash_)
      genCallMethod(hashMethod, Static(false))

      INT
    }

    /**
     * Returns a list of trees that each should be concatenated, from left to right.
     * It turns a chained call like "a".+("b").+("c") into a list of arguments.
     */
    def liftStringConcat(tree: Tree): List[Tree] = tree match { // TODO de-duplicate with GenICode
      case Apply(fun @ Select(larg, method), rarg) =>
        if (isPrimitive(fun.symbol) &&
            scalaPrimitives.getPrimitive(fun.symbol) == scalaPrimitives.CONCAT)
          liftStringConcat(larg) ::: rarg
        else
          List(tree)
      case _ =>
        List(tree)
    }

    /** Some useful equality helpers. */
    def isNull(t: Tree) = PartialFunction.cond(t) { case Literal(Constant(null)) => true } // TODO de-duplicate with GenICode

    /* If l or r is constant null, returns the other ; otherwise null */
    def ifOneIsNull(l: Tree, r: Tree) = if (isNull(l)) r else if (isNull(r)) l else null // TODO de-duplicate with GenICode

    /** Emit code to compare the two top-most stack values using the 'op' operator. */
    private def genCJUMP(success: asm.Label, failure: asm.Label, op: TestOp, tk: asm.Type) {
      if(isIntSizedType(tk)) { // BOOL, BYTE, CHAR, SHORT, or INT
        bc.emitIF_ICMP(op, success)
      } else if(isRefOrArrayType(tk)) { // REFERENCE(_) | ARRAY(_)
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
    private def genCZJUMP(success: asm.Label, failure: asm.Label, op: TestOp, tk: asm.Type) {
      if(isIntSizedType(tk)) { // BOOL, BYTE, CHAR, SHORT, or INT
        bc.emitIF(op, success)
      } else if(isRefOrArrayType(tk)) { // REFERENCE(_) | ARRAY(_)
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

    /**
     * Generate code for conditional expressions.
     * The jump targets success/failure of the test are `then-target` and `else-target` resp.
     */
    private def genCond(tree: Tree, success: asm.Label, failure: asm.Label) {

          def genComparisonOp(l: Tree, r: Tree, code: Int) {
            val op: TestOp = (code: @switch) match {
              case scalaPrimitives.LT => LT
              case scalaPrimitives.LE => LE
              case scalaPrimitives.GT => GT
              case scalaPrimitives.GE => GE
              case scalaPrimitives.ID | scalaPrimitives.EQ => EQ
              case scalaPrimitives.NI | scalaPrimitives.NE => NE

              case _ => abort("Unknown comparison primitive: " + code)
            }

            // special-case reference (in)equality test for null (null eq x, x eq null)
            lazy val nonNullSide = ifOneIsNull(l, r)
            if (scalaPrimitives.isReferenceEqualityOp(code) && nonNullSide != null) {
              genLoad(nonNullSide, ObjectReference)
              genCZJUMP(success, failure, op, ObjectReference)
            }
            else {
              val tk = getMaxType(l.tpe :: r.tpe :: Nil)
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
              if (scalaPrimitives.isUniversalEqualityOp(code) && isReferenceType(toTypeKind(lhs.tpe))) {
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
          val eqEqTempLocal = makeLocal(AnyRefClass.tpe, nme.EQEQ_LOCAL_VAR)
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
    def mayCleanStack(tree: Tree): Boolean = tree exists {
      case Try(_, _, _) => true
      case _            => false
    }

    def getMaxType(ts: List[Type]): asm.Type =
      ts map toTypeKind reduceLeft maxType

    abstract class Cleanup(val value: AnyRef) {
      def contains(x: AnyRef) = value == x
    }
    case class MonitorRelease(v: Symbol) extends Cleanup(v) { }
    case class Finalizer(f: Tree) extends Cleanup (f) { }

    case class Local(tk: asm.Type, name: String, idx: Int)

    trait EHClause
    case class NamelessEH(typeToDrop: asm.Type,   caseBody: Tree) extends EHClause
    case class BoundEH    (patSymbol:     Symbol, caseBody: Tree) extends EHClause

  } // end of class BCodePhase

} // end of class GenBCode
