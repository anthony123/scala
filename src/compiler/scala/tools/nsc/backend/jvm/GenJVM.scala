/* NSC -- new Scala compiler
 * Copyright 2005-2011 LAMP/EPFL
 * @author  Iulian Dragos
 */

package scala.tools.nsc
package backend.jvm

import java.nio.ByteBuffer
import scala.collection.{ mutable, immutable }
import scala.reflect.internal.pickling.{ PickleFormat, PickleBuffer }
import scala.tools.reflect.SigParser
import scala.tools.nsc.symtab._
import scala.tools.nsc.util.{ SourceFile, NoSourceFile }
import scala.reflect.internal.ClassfileConstants._
import ch.epfl.lamp.fjbg._
import JAccessFlags._
import JObjectType.{ JAVA_LANG_STRING, JAVA_LANG_OBJECT }
import scala.tools.nsc.io.AbstractFile

/** This class ...
 *
 *  @author  Iulian Dragos
 *  @version 1.0
 *
 */
abstract class GenJVM extends SubComponent with BytecodeWriters {
  import global._
  import icodes._
  import icodes.opcodes._
  import definitions._

  val phaseName = "jvm"

  /** Create a new phase */
  override def newPhase(p: Phase): Phase = new JvmPhase(p)

  private def outputDirectory(sym: Symbol): AbstractFile =
    settings.outputDirs outputDirFor beforeFlatten(sym.sourceFile)

  private def getFile(base: AbstractFile, clsName: String, suffix: String): AbstractFile = {
    var dir = base
    val pathParts = clsName.split("[./]").toList
    for (part <- pathParts.init) {
      dir = dir.subdirectoryNamed(part)
    }
    dir.fileNamed(pathParts.last + suffix)
  }
  private def getFile(sym: Symbol, clsName: String, suffix: String): AbstractFile =
    getFile(outputDirectory(sym), clsName, suffix)

  /** JVM code generation phase
   */
  class JvmPhase(prev: Phase) extends ICodePhase(prev) {
    def name = phaseName
    override def erasedTypes = true
    def apply(cls: IClass) = sys.error("no implementation")

    val BeanInfoAttr = definitions.getRequiredClass("scala.beans.BeanInfo")

    def isJavaEntryPoint(icls: IClass) = {
      val sym = icls.symbol
      def fail(msg: String, pos: Position = sym.pos) = {
        icls.cunit.warning(sym.pos,
          sym.name + " has a main method with parameter type Array[String], but " + sym.fullName('.') + " will not be a runnable program.\n" +
          "  Reason: " + msg
          // TODO: make this next claim true, if possible
          //   by generating valid main methods as static in module classes
          //   not sure what the jvm allows here
          // + "  You can still run the program by calling it as " + sym.javaSimpleName + " instead."
        )
        false
      }
      def failNoForwarder(msg: String) = {
        fail(msg + ", which means no static forwarder can be generated.\n")
      }
      val possibles = if (sym.hasModuleFlag) (sym.tpe nonPrivateMember nme.main).alternatives else Nil
      val hasApproximate = possibles exists { m =>
        m.info match {
          case MethodType(p :: Nil, _) => p.tpe.typeSymbol == ArrayClass
          case _                       => false
        }
      }
      // At this point it's a module with a main-looking method, so either succeed or warn that it isn't.
      hasApproximate && {
        // Before erasure so we can identify generic mains.
        beforeErasure {
          val companion     = sym.linkedClassOfClass
          val companionMain = companion.tpe.member(nme.main)

          if (hasJavaMainMethod(companion))
            failNoForwarder("companion contains its own main method")
          else if (companion.tpe.member(nme.main) != NoSymbol)
            // this is only because forwarders aren't smart enough yet
            failNoForwarder("companion contains its own main method (implementation restriction: no main is allowed, regardless of signature)")
          else if (companion.isTrait)
            failNoForwarder("companion is a trait")
          // Now either succeeed, or issue some additional warnings for things which look like
          // attempts to be java main methods.
          else possibles exists { m =>
            m.info match {
              case PolyType(_, _) =>
                fail("main methods cannot be generic.")
              case MethodType(params, res) =>
                if (res.typeSymbol :: params exists (_.isAbstractType))
                  fail("main methods cannot refer to type parameters or abstract types.", m.pos)
                else
                  isJavaMainMethod(m) || fail("main method must have exact signature (Array[String])Unit", m.pos)
              case tp =>
                fail("don't know what this is: " + tp, m.pos)
            }
          }
        }
      }
    }

    private def initBytecodeWriter(entryPoints: List[IClass]): BytecodeWriter = {
      settings.outputDirs.getSingleOutput match {
        case Some(f) if f hasExtension "jar" =>
          // If no main class was specified, see if there's only one
          // entry point among the classes going into the jar.
          if (settings.mainClass.isDefault) {
            entryPoints map (_.symbol fullName '.') match {
              case Nil      =>
                log("No Main-Class designated or discovered.")
              case name :: Nil =>
                log("Unique entry point: setting Main-Class to " + name)
                settings.mainClass.value = name
              case names =>
                log("No Main-Class due to multiple entry points:\n  " + names.mkString("\n  "))
            }
          }
          else log("Main-Class was specified: " + settings.mainClass.value)

          new DirectToJarfileWriter(f.file)

        case _                               =>
          if (settings.Ygenjavap.isDefault) {
            if(settings.Ydumpclasses.isDefault)
              new ClassBytecodeWriter { }
            else
              new ClassBytecodeWriter with DumpBytecodeWriter { }
          }
          else new ClassBytecodeWriter with JavapBytecodeWriter { }
      }
    }

    override def run() {

      if (settings.debug.value)
        inform("[running phase " + name + " on icode]")

      if (settings.Xdce.value)
        for ((sym, cls) <- icodes.classes if inliner.isClosureClass(sym) && !deadCode.liveClosures(sym))
          icodes.classes -= sym

      // For predictably ordered error messages.
      var sortedClasses = classes.values.toList sortBy ("" + _.symbol.fullName)

      debuglog("Created new bytecode generator for " + classes.size + " classes.")
      val bytecodeWriter  = initBytecodeWriter(sortedClasses filter isJavaEntryPoint)
      val plainCodeGen    = new JPlainBuilder(bytecodeWriter)
      val mirrorCodeGen   = new JMirrorBuilder(bytecodeWriter)
      val beanInfoCodeGen = new JBeanInfoBuilder(bytecodeWriter)

      while(!sortedClasses.isEmpty) {
        val c = sortedClasses.head
        try {

          if (isStaticModule(c.symbol) && isTopLevelModule(c.symbol)) {
            if (c.symbol.companionClass == NoSymbol) {
              mirrorCodeGen.genMirrorClass(c.symbol, c.cunit)
            } else {
              log("No mirror class for module with linked class: " + c.symbol.fullName)
            }
          }

          plainCodeGen.genClass(c)

          if (c.symbol hasAnnotation BeanInfoAttr) {
            beanInfoCodeGen.genBeanInfoClass(c)
          }

        } catch {
          case e: JCode.CodeSizeTooBigException =>
            log("Skipped class %s because it has methods that are too long.".format(c))
        }
        sortedClasses = sortedClasses.tail
        classes -= c.symbol // GC opportunity
      }

      bytecodeWriter.close()
      classes.clear()
      javaNameCache.clear()
    }
  }

  var pickledBytes = 0 // statistics

  // Don't put this in per run caches.
  val javaNameCache = new mutable.WeakHashMap[Symbol, Name]() ++= List(
    NothingClass        -> binarynme.RuntimeNothing,
    RuntimeNothingClass -> binarynme.RuntimeNothing,
    NullClass           -> binarynme.RuntimeNull,
    RuntimeNullClass    -> binarynme.RuntimeNull
  )

  private def mkFlags(args: Int*) = args.foldLeft(0)(_ | _)

  /**
   * Return the Java modifiers for the given symbol.
   * Java modifiers for classes:
   *  - public, abstract, final, strictfp (not used)
   * for interfaces:
   *  - the same as for classes, without 'final'
   * for fields:
   *  - public, private (*)
   *  - static, final
   * for methods:
   *  - the same as for fields, plus:
   *  - abstract, synchronized (not used), strictfp (not used), native (not used)
   *
   *  (*) protected cannot be used, since inner classes 'see' protected members,
   *      and they would fail verification after lifted.
   */
  def javaFlags(sym: Symbol): Int = {
    // constructors of module classes should be private
    // PP: why are they only being marked private at this stage and not earlier?
    val privateFlag =
      sym.isPrivate || (sym.isPrimaryConstructor && isTopLevelModule(sym.owner))

    // This does not check .isFinal (which checks flags for the FINAL flag),
    // instead checking rawflags for that flag so as to exclude symbols which
    // received lateFINAL.  These symbols are eligible for inlining, but to
    // avoid breaking proxy software which depends on subclassing, we avoid
    // insisting on their finality in the bytecode.
    val finalFlag = (
         ((sym.rawflags & (Flags.FINAL | Flags.MODULE)) != 0)
      && !sym.enclClass.isInterface
      && !sym.isClassConstructor
      && !sym.isMutable  // fix for SI-3569, it is too broad?
    )

    mkFlags(
      if (privateFlag) ACC_PRIVATE else ACC_PUBLIC,
      if (sym.isDeferred || sym.hasAbstractFlag) ACC_ABSTRACT else 0,
      if (sym.isInterface) ACC_INTERFACE else 0,
      if (finalFlag) ACC_FINAL else 0,
      if (sym.isStaticMember) ACC_STATIC else 0,
      if (sym.isBridge) ACC_BRIDGE | ACC_SYNTHETIC else 0,
      if (sym.isClass && !sym.isInterface) ACC_SUPER else 0,
      if (sym.isVarargsMethod) ACC_VARARGS else 0,
      if (sym.hasFlag(Flags.SYNCHRONIZED)) JAVA_ACC_SYNCHRONIZED else 0
    )
  }

  def javaFieldFlags(sym: Symbol) = {
    mkFlags(
      if (sym hasAnnotation TransientAttr) ACC_TRANSIENT else 0,
      if (sym hasAnnotation VolatileAttr) ACC_VOLATILE else 0,
      if (sym.isMutable) 0 else ACC_FINAL
    )
  }

  def isTopLevelModule(sym: Symbol): Boolean =
    afterPickler { sym.isModuleClass && !sym.isImplClass && !sym.isNestedClass }

  def isStaticModule(sym: Symbol): Boolean = {
    sym.isModuleClass && !sym.isImplClass && !sym.isLifted
  }

  /** basic functionality for class file building */
  abstract class JBuilder(bytecodeWriter: BytecodeWriter) {

    val fjbgContext = new FJBGContext(49, 0)

    /** Specialized array conversion to prevent calling
     *  java.lang.reflect.Array.newInstance via TraversableOnce.toArray
     */
    def mkArray(xs: Traversable[JType]): Array[JType] = { val a = new Array[JType](xs.size); xs.copyToArray(a); a }
    def mkArray(xs: Traversable[String]): Array[String] = { val a = new Array[String](xs.size); xs.copyToArray(a); a }

    // -----------------------------------------------------------------------------------------
    // Getters for (JVMS 4.2) internal and unqualified names (represented as JType instances).
    // These getters track behind the scenes the inner classes referred to in the class being emitted,
    // so as to build the InnerClasses attribute (JVMS 4.7.6) via `addInnerClasses()`
    // (which also adds as member classes those inner classes that have been declared,
    // thus also covering the case of inner classes declared but otherwise not referred).
    // -----------------------------------------------------------------------------------------

    val innerClassBuffer = mutable.LinkedHashSet[Symbol]()

    /** For given symbol return a symbol corresponding to a class that should be declared as inner class.
     *
     *  For example:
     *  class A {
     *    class B
     *    object C
     *  }
     *
     *  then method will return NoSymbol for A, the same symbol for A.B (corresponding to A$B class) and A$C$ symbol
     *  for A.C.
     */
    def innerClassSymbolFor(s: Symbol): Symbol =
      if (s.isClass) s else if (s.isModule) s.moduleClass else NoSymbol

    /** Return the a name of this symbol that can be used on the Java
     *  platform.  It removes spaces from names.
     *
     *  Special handling:
     *    scala.Nothing erases to scala.runtime.Nothing$
     *       scala.Null erases to scala.runtime.Null$
     *
     *  This is needed because they are not real classes, and they mean
     *  'abrupt termination upon evaluation of that expression' or null respectively.
     *  This handling is done already in GenICode, but here we need to remove
     *  references from method signatures to these types, because such classes can
     *  not exist in the classpath: the type checker will be very confused.
     */
    def javaName(sym: Symbol): String = {

        /**
         * Checks if given symbol corresponds to inner class/object and add it to innerClassBuffer
         *
         * Note: This method is called recursively thus making sure that we add complete chain
         * of inner class all until root class.
         */
        def collectInnerClass(s: Symbol): Unit = {
          // TODO: some beforeFlatten { ... } which accounts for
          // being nested in parameterized classes (if we're going to selectively flatten.)
          val x = innerClassSymbolFor(s)
          if(x ne NoSymbol) {
            assert(x.isClass, "not an inner-class symbol")
            val isInner = !x.rawowner.isPackageClass
            if (isInner) {
              innerClassBuffer += x
              collectInnerClass(x.rawowner)
            }
          }
        }

      collectInnerClass(sym)

      javaNameCache.getOrElseUpdate(sym, {
        if (sym.isClass || (sym.isModule && !sym.isMethod))
          sym.javaBinaryName
        else
          sym.javaSimpleName
      }).toString
    }

    def javaType(t: TypeKind): JType = (t: @unchecked) match {
      case UNIT            => JType.VOID
      case BOOL            => JType.BOOLEAN
      case BYTE            => JType.BYTE
      case SHORT           => JType.SHORT
      case CHAR            => JType.CHAR
      case INT             => JType.INT
      case LONG            => JType.LONG
      case FLOAT           => JType.FLOAT
      case DOUBLE          => JType.DOUBLE
      case REFERENCE(cls)  => new JObjectType(javaName(cls))
      case ARRAY(elem)     => new JArrayType(javaType(elem))
    }

    def javaType(t: Type): JType = javaType(toTypeKind(t))

    def javaType(s: Symbol): JType = {
      if (s.isMethod)
        new JMethodType(
          if (s.isClassConstructor) JType.VOID else javaType(s.tpe.resultType),
          mkArray(s.tpe.paramTypes map javaType)
        )
      else
        javaType(s.tpe)
    }

  } // end of class JBuilder


  /** functionality for building plain and mirror classes */
  abstract class JCommonBuilder(bytecodeWriter: BytecodeWriter) extends JBuilder(bytecodeWriter) {

    val INNER_CLASSES_FLAGS =
      (ACC_PUBLIC | ACC_PRIVATE | ACC_PROTECTED | ACC_STATIC | ACC_FINAL | ACC_INTERFACE | ACC_ABSTRACT)

    val PublicStatic      = ACC_PUBLIC | ACC_STATIC
    val PublicStaticFinal = ACC_PUBLIC | ACC_STATIC | ACC_FINAL


    // -----------------------------------------------------------------------------------------
    // Custom attribute (JVMS 4.7.1) "ScalaSig" used as marker only
    // (i.e., the pickle is contained in a custom annotation, see `addAnnotations()`, and TODO SIP).
    // That annotation in turn is not related to `addGenericSignature()` (JVMS 4.7.9)
    // other than both ending up encoded as attributes (JVMS 4.7)
    // (with the caveat that the "ScalaSig" attribute is associated to some classes,
    // while the "Signature" attribute can be associated to classes, methods, and fields.)
    // -----------------------------------------------------------------------------------------

    val versionPickle = {
      val vp = new PickleBuffer(new Array[Byte](16), -1, 0)
      assert(vp.writeIndex == 0, vp)
      vp writeNat PickleFormat.MajorVersion
      vp writeNat PickleFormat.MinorVersion
      vp writeNat 0
      vp
    }

    /** Returns a ScalaSignature annotation if it must be added to this class, none otherwise.
     *  This annotation must be added to the class' annotations list when generating them.
     *
     *  Depending on whether the returned option is defined, it adds to `jclass` one of:
     *    (a) the ScalaSig marker attribute
     *        (indicating that a scala-signature-annotation aka pickle is present in this class); or
     *    (b) the Scala marker attribute
     *        (indicating that a scala-signature-annotation aka pickle is to be found in another file).
     *
     *
     *  @param jclass The class file that is being readied.
     *  @param sym    The symbol for which the signature has been entered in the symData map.
     *                This is different than the symbol
     *                that is being generated in the case of a mirror class.
     *  @return       An option that is:
     *                - defined and contains an AnnotationInfo of the ScalaSignature type,
     *                  instantiated with the pickle signature for sym.
     *                - empty if the jclass/sym pair must not contain a pickle.
     *
     */
    def scalaSignatureAddingMarker(jclass: JClass, sym: Symbol): Option[AnnotationInfo] = {
      currentRun.symData get sym match {
        case Some(pickle) if !nme.isModuleName(newTermName(jclass.getName)) =>
          jclass addAttribute markerLocalPickle(jclass)
          val scalaAnnot = {
            val sigBytes = ScalaSigBytes(pickle.bytes.take(pickle.writeIndex))
            AnnotationInfo(sigBytes.sigAnnot, Nil, List((nme.bytes, sigBytes)))
          }
          pickledBytes += pickle.writeIndex
          currentRun.symData -= sym
          currentRun.symData -= sym.companionSymbol
          Some(scalaAnnot)
        case _ =>
          jclass addAttribute markerForeignPickle(jclass)
          None
      }
    }

    private def markerLocalPickle(jclass: JClass): JOtherAttribute = {
      fjbgContext.JOtherAttribute(jclass, jclass, tpnme.ScalaSignatureATTR.toString, versionPickle.bytes, versionPickle.writeIndex)
    }

    private def markerForeignPickle(jclass: JClass): JOtherAttribute = {
      fjbgContext.JOtherAttribute(jclass, jclass, tpnme.ScalaATTR.toString, new Array[Byte](0), 0)
    }

    /** Add the given 'throws' attributes to jmethod. */
    def addExceptionsAttribute(jmethod: JMethod, excs: List[AnnotationInfo]) {
      if (excs.isEmpty) return

      val cpool = jmethod.getConstantPool
      val buf: ByteBuffer = ByteBuffer.allocate(512)
      var nattr = 0

      // put some random value; the actual number is determined at the end
      buf putShort 0xbaba.toShort

      for (AnnotationInfo(tp, List(exc), _) <- excs.distinct if tp.typeSymbol == ThrowsClass) {
        val Literal(const) = exc
        buf.putShort(
          cpool.addClass(
            javaName(const.typeValue.typeSymbol)).shortValue)
        nattr += 1
      }

      assert(nattr > 0, nattr)
      buf.putShort(0, nattr.toShort)
      addAttribute(jmethod, tpnme.ExceptionsATTR, buf)
    }

    /** Whether an annotation should be emitted as a Java annotation
     *   .initialize: if 'annot' is read from pickle, atp might be un-initialized
     */
    private def shouldEmitAnnotation(annot: AnnotationInfo) =
      annot.symbol.initialize.isJavaDefined &&
      annot.matches(ClassfileAnnotationClass) &&
      annot.args.isEmpty

    private def emitJavaAnnotations(cpool: JConstantPool, buf: ByteBuffer, annotations: List[AnnotationInfo]): Int = {
      def emitArgument(arg: ClassfileAnnotArg): Unit = arg match {
        case LiteralAnnotArg(const) =>
          const.tag match {
            case BooleanTag =>
              buf put 'Z'.toByte
              buf putShort cpool.addInteger(if(const.booleanValue) 1 else 0).toShort
            case ByteTag    =>
              buf put 'B'.toByte
              buf putShort cpool.addInteger(const.byteValue).toShort
            case ShortTag   =>
              buf put 'S'.toByte
              buf putShort cpool.addInteger(const.shortValue).toShort
            case CharTag    =>
              buf put 'C'.toByte
              buf putShort cpool.addInteger(const.charValue).toShort
            case IntTag     =>
              buf put 'I'.toByte
              buf putShort cpool.addInteger(const.intValue).toShort
            case LongTag    =>
              buf put 'J'.toByte
              buf putShort cpool.addLong(const.longValue).toShort
            case FloatTag   =>
              buf put 'F'.toByte
              buf putShort cpool.addFloat(const.floatValue).toShort
            case DoubleTag  =>
              buf put 'D'.toByte
              buf putShort cpool.addDouble(const.doubleValue).toShort
            case StringTag  =>
              buf put 's'.toByte
              buf putShort cpool.addUtf8(const.stringValue).toShort
            case ClassTag   =>
              buf put 'c'.toByte
              buf putShort cpool.addUtf8(javaType(const.typeValue).getSignature()).toShort
            case EnumTag =>
              buf put 'e'.toByte
              buf putShort cpool.addUtf8(javaType(const.tpe).getSignature()).toShort
              buf putShort cpool.addUtf8(const.symbolValue.name.toString).toShort
          }

        case sb@ScalaSigBytes(bytes) if !sb.isLong =>
          buf put 's'.toByte
          buf putShort cpool.addUtf8(sb.encodedBytes).toShort

        case sb@ScalaSigBytes(bytes) if sb.isLong =>
          buf put '['.toByte
          val stringCount = (sb.encodedBytes.length / 65534) + 1
          buf putShort stringCount.toShort
          for (i <- 0 until stringCount) {
            buf put 's'.toByte
            val j = i * 65535
            val string = sb.encodedBytes.slice(j, j + 65535)
            buf putShort cpool.addUtf8(string).toShort
          }

        case ArrayAnnotArg(args) =>
          buf put '['.toByte
          buf putShort args.length.toShort
          args foreach emitArgument

        case NestedAnnotArg(annInfo) =>
          buf put '@'.toByte
          emitAnnotation(annInfo)
      }

      def emitAnnotation(annotInfo: AnnotationInfo) {
        val AnnotationInfo(typ, args, assocs) = annotInfo
        val jtype = javaType(typ)
        buf putShort cpool.addUtf8(jtype.getSignature()).toShort
        assert(args.isEmpty, args)
        buf putShort assocs.length.toShort
        for ((name, value) <- assocs) {
          buf putShort cpool.addUtf8(name.toString).toShort
          emitArgument(value)
        }
      }

      var nannots = 0
      val pos = buf.position()

      // put some random value; the actual number of annotations is determined at the end
      buf putShort 0xbaba.toShort

      for (annot <- annotations if shouldEmitAnnotation(annot)) {
        nannots += 1
        emitAnnotation(annot)
      }

      // save the number of annotations
      buf.putShort(pos, nannots.toShort)
      nannots
    }

    /**Run the signature parser to catch bogus signatures. */
    def isValidSignature(sym: Symbol, sig: String) = (
      if (sym.isMethod) SigParser verifyMethod sig
      else if (sym.isTerm) SigParser verifyType sig
      else SigParser verifyClass sig
    )

    // @M don't generate java generics sigs for (members of) implementation
    // classes, as they are monomorphic (TODO: ok?)
    private def needsGenericSignature(sym: Symbol) = !(
      // PP: This condition used to include sym.hasExpandedName, but this leads
      // to the total loss of generic information if a private member is
      // accessed from a closure: both the field and the accessor were generated
      // without it.  This is particularly bad because the availability of
      // generic information could disappear as a consequence of a seemingly
      // unrelated change.
         sym.isSynthetic
      || sym.isLiftedMethod
      || sym.isBridge
      || (sym.ownerChain exists (_.isImplClass))
    )

    def getCurrentCUnit(): CompilationUnit

    /** @return
     *   - `null` if no Java signature is to be added (`null` is what ASM expects in these cases).
     *   - otherwise the signature in question
     */
    def getGenericSignature(sym: Symbol, owner: Symbol): String = {
      if (!needsGenericSignature(sym)) { return null }

      val memberTpe = beforeErasure(owner.thisType.memberInfo(sym))
      // println("addGenericSignature sym: " + sym.fullName + " : " + memberTpe + " sym.info: " + sym.info)
      // println("addGenericSignature: "+ (sym.ownerChain map (x => (x.name, x.isImplClass))))

      val jsOpt = erasure.javaSig(sym, memberTpe)
      if (jsOpt.isEmpty) { return null }

      val sig = jsOpt.get

      // TODO ASM's CheckClassAdapter can be used to perform this check (without resort to SunSignatureParser)
      // TODO it delegates to one of CheckMethodAdapter.{ checkClassSignature(), checkMethodSignature(), checkFieldSignature() }
      // TODO All those checks (including SunSignatureParser's) seem to be syntactic only in nature.
      // TODO CheckClassAdapter lives in asm-util.jar (merely 37KB)

      /** Since we're using a sun internal class for signature validation,
       *  we have to allow for it not existing or otherwise malfunctioning:
       *  in which case we treat every signature as valid.  Medium term we
       *  should certainly write independent signature validation.
       */
      if (settings.Xverify.value && SigParser.isParserAvailable && !isValidSignature(sym, sig)) {
        getCurrentCUnit().warning(sym.pos,
            """|compiler bug: created invalid generic signature for %s in %s
               |signature: %s
               |if this is reproducible, please report bug at http://lampsvn.epfl.ch/trac/scala
            """.trim.stripMargin.format(sym, sym.owner.skipPackageObject.fullName, sig))
        return null
      }
      if ((settings.check.value contains "genjvm")) {
        val normalizedTpe = beforeErasure(erasure.prepareSigMap(memberTpe))
        val bytecodeTpe = owner.thisType.memberInfo(sym)
        if (!sym.isType && !sym.isConstructor && !(erasure.erasure(sym)(normalizedTpe) =:= bytecodeTpe)) {
          getCurrentCUnit().warning(sym.pos,
              """|compiler bug: created generic signature for %s in %s that does not conform to its erasure
                 |signature: %s
                 |original type: %s
                 |normalized type: %s
                 |erasure type: %s
                 |if this is reproducible, please report bug at http://lampsvn.epfl.ch/trac/scala
              """.trim.stripMargin.format(sym, sym.owner.skipPackageObject.fullName, sig, memberTpe, normalizedTpe, bytecodeTpe))
           return null
        }
      }

      sig
    }

    def addGenericSignature(jmember: JMember, sig: String) {
      if(sig != null) {
        val index = jmember.getConstantPool.addUtf8(sig).toShort

        val buf = ByteBuffer.allocate(2)
        buf putShort index
        addAttribute(jmember, tpnme.SignatureATTR, buf)
      }
    }

    def addAnnotations(jmember: JMember, annotations: List[AnnotationInfo]) {
      if (annotations exists (_ matches definitions.DeprecatedAttr)) {
        val attr = jmember.getContext().JOtherAttribute(
          jmember.getJClass(), jmember, tpnme.DeprecatedATTR.toString,
          new Array[Byte](0), 0)
        jmember addAttribute attr
      }

      val toEmit = annotations filter shouldEmitAnnotation
      if (toEmit.isEmpty) return

      val buf: ByteBuffer = ByteBuffer.allocate(2048)
      emitJavaAnnotations(jmember.getConstantPool, buf, toEmit)
      addAttribute(jmember, tpnme.RuntimeAnnotationATTR, buf)
    }

    def addParamAnnotations(jmethod: JMethod, pannotss: List[List[AnnotationInfo]]) {
      val annotations = pannotss map (_ filter shouldEmitAnnotation)
      if (annotations forall (_.isEmpty)) return

      val buf: ByteBuffer = ByteBuffer.allocate(2048)

      // number of parameters
      buf.put(annotations.length.toByte)
      for (annots <- annotations)
        emitJavaAnnotations(jmethod.getConstantPool, buf, annots)

      addAttribute(jmethod, tpnme.RuntimeParamAnnotationATTR, buf)
    }

    def addAttribute(jmember: JMember, name: Name, buf: ByteBuffer) {
      if (buf.position() < 2)
        return

      val length = buf.position()
      val arr = buf.array().slice(0, length)

      val attr = jmember.getContext().JOtherAttribute(jmember.getJClass(),
                                                      jmember,
                                                      name.toString,
                                                      arr,
                                                      length)
      jmember addAttribute attr
    }

    def addInnerClasses(csym: Symbol, jclass: JClass) {
      /** The outer name for this inner class. Note that it returns null
       *  when the inner class should not get an index in the constant pool.
       *  That means non-member classes (anonymous). See Section 4.7.5 in the JVMS.
       */
      def outerName(innerSym: Symbol): String = {
        if (innerSym.originalEnclosingMethod != NoSymbol)
          null
        else {
          val outerName = javaName(innerSym.rawowner)
          if (isTopLevelModule(innerSym.rawowner)) "" + nme.stripModuleSuffix(newTermName(outerName))
          else outerName
        }
      }

      def innerName(innerSym: Symbol): String =
        if (innerSym.isAnonymousClass || innerSym.isAnonymousFunction)
          null
        else
          innerSym.rawname + innerSym.moduleSuffix

      // add inner classes which might not have been referenced yet
      afterErasure {
        for (sym <- List(csym, csym.linkedClassOfClass); m <- sym.info.decls.map(innerClassSymbolFor) if m.isClass)
          innerClassBuffer += m
      }

      val allInners = innerClassBuffer.toList
      if (allInners.nonEmpty) {
        debuglog(csym.fullName('.') + " contains " + allInners.size + " inner classes.")
        val innerClassesAttr = jclass.getInnerClasses()
        // sort them so inner classes succeed their enclosing class
        // to satisfy the Eclipse Java compiler
        for (innerSym <- allInners sortBy (_.name.length)) { // TODO why not sortBy (_.name) ??
          val flags = {
            val staticFlag = if (innerSym.rawowner.hasModuleFlag) ACC_STATIC else 0
            (javaFlags(innerSym) | staticFlag) & INNER_CLASSES_FLAGS
          }
          val jname = javaName(innerSym)
          val oname = outerName(innerSym)
          val iname = innerName(innerSym)

          // Mimicking javap inner class output
          debuglog(
            if (oname == null || iname == null) "//class " + jname
            else "//%s=class %s of class %s".format(iname, jname, oname)
          )

          innerClassesAttr.addEntry(jname, oname, iname, flags)
        }
      }
    }

    /** Adds a @remote annotation, actual use unknown.
     *
     * Invoked from genMethod() and addForwarder().
     */
    def addRemoteExceptionAnnot(isRemoteClass: Boolean, isJMethodPublic: Boolean, meth: Symbol) {
      val needsAnnotation = (
        (  isRemoteClass ||
           (meth hasAnnotation RemoteAttr) && isJMethodPublic
        ) && !(meth.throwsAnnotations contains RemoteExceptionClass)
      )
      if (needsAnnotation) {
        val c   = Constant(RemoteExceptionClass.tpe)
        val arg = Literal(c) setType c.tpe
        meth.addAnnotation(ThrowsClass, arg)
      }
    }

    // -----------------------------------------------------------------------------------------
    // Static forwarders (related to mirror classes but also present in
    // a plain class lacking companion module, for details see `isCandidateForForwarders`).
    // -----------------------------------------------------------------------------------------

    val ExcludedForwarderFlags = {
      import Flags._
      // Should include DEFERRED but this breaks findMember.
      ( CASE | SPECIALIZED | LIFTED | PROTECTED | STATIC | EXPANDEDNAME | BridgeAndPrivateFlags )
    }

    /** Add a forwarder for method m.
     *
     *  Used only from addForwarders().
     *
     * */
    private def addForwarder(isRemoteClass: Boolean, jclass: JClass, module: Symbol, m: Symbol) {
      val moduleName     = javaName(module)
      val methodInfo     = module.thisType.memberInfo(m)
      val paramJavaTypes = methodInfo.paramTypes map javaType
      val paramNames     = 0 until paramJavaTypes.length map ("x_" + _)
      // TODO: evaluate the other flags we might be dropping on the floor here.
      val flags = PublicStatic | (
        if (m.isVarargsMethod) ACC_VARARGS else 0
      )

      // only add generic signature if the method is concrete; bug #1745
      val sig = if (m.isDeferred) null else getGenericSignature(m, module);

      /** Forwarders must not be marked final, as the JVM will not allow
       *  redefinition of a final static method, and we don't know what classes
       *  might be subclassing the companion class.  See SI-4827.
       */
      val mirrorMethod = jclass.addNewMethod(
        flags,
        javaName(m),
        javaType(methodInfo.resultType),
        mkArray(paramJavaTypes),
        mkArray(paramNames))

      addRemoteExceptionAnnot(isRemoteClass, mirrorMethod.isPublic, m)

      // typestate: entering mode with valid call sequences:
      //   [ visitAnnotationDefault ] ( visitAnnotation | visitParameterAnnotation | visitAttribute )*

      addGenericSignature(mirrorMethod, sig)

      val (throws, others) = m.annotations partition (_.symbol == ThrowsClass)
      addExceptionsAttribute(mirrorMethod, throws)
      addAnnotations(mirrorMethod, others)
      addParamAnnotations(mirrorMethod, m.info.params.map(_.annotations))

      // typestate: entering mode with valid call sequences:
      //   visitCode ( visitFrame | visitXInsn | visitLabel | visitTryCatchBlock | visitLocalVariable | visitLineNumber )* visitMaxs ] visitEnd

      val mirrorCode = mirrorMethod.getCode().asInstanceOf[JExtendedCode]
      mirrorCode.emitGETSTATIC(moduleName,
                               nme.MODULE_INSTANCE_FIELD.toString,
                               new JObjectType(moduleName))

      var i = 0
      var index = 0
      var argTypes = mirrorMethod.getArgumentTypes()
      while (i < argTypes.length) {
        mirrorCode.emitLOAD(index, argTypes(i))
        index += argTypes(i).getSize()
        i += 1
      }

      mirrorCode.emitINVOKEVIRTUAL(moduleName, mirrorMethod.getName, javaType(m).asInstanceOf[JMethodType])
      mirrorCode emitRETURN mirrorMethod.getReturnType()

    }

    /** Add forwarders for all methods defined in `module` that don't conflict
     *  with methods in the companion class of `module`. A conflict arises when
     *  a method with the same name is defined both in a class and its companion object:
     *  method signature is not taken into account.
     */
    def addForwarders(isRemoteClass: Boolean, jclass: JClass, moduleClass: Symbol) {
      assert(moduleClass.isModuleClass, moduleClass)
      debuglog("Dumping mirror class for object: " + moduleClass)

      val className    = jclass.getName
      val linkedClass  = moduleClass.companionClass
      val linkedModule = linkedClass.companionSymbol
      lazy val conflictingNames: Set[Name] = {
        linkedClass.info.members collect { case sym if sym.name.isTermName => sym.name } toSet
      }
      debuglog("Potentially conflicting names for forwarders: " + conflictingNames)

      for (m <- moduleClass.info.membersBasedOnFlags(ExcludedForwarderFlags, Flags.METHOD)) {
        if (m.isType || m.isDeferred || (m.owner eq ObjectClass) || m.isConstructor)
          debuglog("No forwarder for '%s' from %s to '%s'".format(m, className, moduleClass))
        else if (conflictingNames(m.name))
          log("No forwarder for " + m + " due to conflict with " + linkedClass.info.member(m.name))
        else {
          log("Adding static forwarder for '%s' from %s to '%s'".format(m, className, moduleClass))
          addForwarder(isRemoteClass, jclass, moduleClass, m)
        }
      }
    }

  } // end of class JCommonBuilder


  trait JAndroidBuilder {
    self: JPlainBuilder =>

    /** From the reference documentation of the Android SDK:
     *  The `Parcelable` interface identifies classes whose instances can be
     *  written to and restored from a `Parcel`. Classes implementing the
     *  `Parcelable` interface must also have a static field called `CREATOR`,
     *  which is an object implementing the `Parcelable.Creator` interface.
     */
    private val androidFieldName = newTermName("CREATOR")

    private lazy val AndroidParcelableInterface = definitions.getClassIfDefined("android.os.Parcelable")
    private lazy val AndroidCreatorClass        = definitions.getClassIfDefined("android.os.Parcelable$Creator")

    def isAndroidParcelableClass(sym: Symbol) =
      (AndroidParcelableInterface != NoSymbol) &&
      (sym.parentSymbols contains AndroidParcelableInterface)

    /* Typestate: should be called before emitting fields (because it adds an IField to the current IClass). */
    def addCreatorCode(block: BasicBlock) {
      val fieldSymbol = (
        clasz.symbol.newValue(newTermName(androidFieldName), NoPosition, Flags.STATIC | Flags.FINAL)
          setInfo AndroidCreatorClass.tpe
      )
      val methodSymbol = definitions.getMember(clasz.symbol.companionModule, androidFieldName)
      clasz addField new IField(fieldSymbol)
      block emit CALL_METHOD(methodSymbol, Static(false))
      block emit STORE_FIELD(fieldSymbol, true)
    }

    def legacyAddCreatorCode(clinit: JExtendedCode) {
      val creatorType = javaType(AndroidCreatorClass)
      jclass.addNewField(PublicStaticFinal,
                         androidFieldName,
                         creatorType)
      val moduleName = javaName(clasz.symbol)+"$"
      clinit.emitGETSTATIC(moduleName,
                           nme.MODULE_INSTANCE_FIELD.toString,
                           new JObjectType(moduleName))
      clinit.emitINVOKEVIRTUAL(moduleName, androidFieldName,
                               new JMethodType(creatorType, Array()))
      clinit.emitPUTSTATIC(jclass.getName(), androidFieldName, creatorType)
    }

  } // end of trait JAndroidBuilder

  /** builder of plain classes */
  class JPlainBuilder(bytecodeWriter: BytecodeWriter)
    extends JCommonBuilder(bytecodeWriter)
    with    JAndroidBuilder {

    val MIN_SWITCH_DENSITY = 0.7

    val StringBuilderClassName = javaName(definitions.StringBuilderClass)
    val BoxesRunTime = "scala.runtime.BoxesRunTime"

    val StringBuilderType = new JObjectType(StringBuilderClassName)               // TODO use ASMType.getObjectType
    val toStringType      = new JMethodType(JAVA_LANG_STRING, JType.EMPTY_ARRAY)  // TODO use ASMType.getMethodType
    val arrayCloneType    = new JMethodType(JAVA_LANG_OBJECT, JType.EMPTY_ARRAY)

    /** Map from type kinds to the Java reference types. It is used for
     *  loading class constants. @see Predef.classOf.
     */
    private val classLiteral = immutable.Map[TypeKind, JObjectType](
      UNIT   -> new JObjectType("java.lang.Void"),
      BOOL   -> new JObjectType("java.lang.Boolean"),
      BYTE   -> new JObjectType("java.lang.Byte"),
      SHORT  -> new JObjectType("java.lang.Short"),
      CHAR   -> new JObjectType("java.lang.Character"),
      INT    -> new JObjectType("java.lang.Integer"),
      LONG   -> new JObjectType("java.lang.Long"),
      FLOAT  -> new JObjectType("java.lang.Float"),
      DOUBLE -> new JObjectType("java.lang.Double")
    )

    /** used only from genCode(), i.e. only when emitting plain classes. */
    private val jBoxTo: Map[TypeKind, Tuple2[String, JMethodType]] = {
      Map(
        BOOL   -> Pair("boxToBoolean",   new JMethodType(classLiteral(BOOL),   Array(JType.BOOLEAN))) ,
        BYTE   -> Pair("boxToByte",      new JMethodType(classLiteral(BYTE),   Array(JType.BYTE)))    ,
        CHAR   -> Pair("boxToCharacter", new JMethodType(classLiteral(CHAR),   Array(JType.CHAR)))    ,
        SHORT  -> Pair("boxToShort",     new JMethodType(classLiteral(SHORT),  Array(JType.SHORT)))   ,
        INT    -> Pair("boxToInteger",   new JMethodType(classLiteral(INT),    Array(JType.INT)))     ,
        LONG   -> Pair("boxToLong",      new JMethodType(classLiteral(LONG),   Array(JType.LONG)))    ,
        FLOAT  -> Pair("boxToFloat",     new JMethodType(classLiteral(FLOAT),  Array(JType.FLOAT)))   ,
        DOUBLE -> Pair("boxToDouble",    new JMethodType(classLiteral(DOUBLE), Array(JType.DOUBLE)))
      )
    }

    /** used only from genCode(), i.e. only when emitting plain classes. */
    private val jUnboxTo: Map[TypeKind, Tuple2[String, JMethodType]] = {
      Map(
        BOOL   -> Pair("unboxToBoolean", new JMethodType(JType.BOOLEAN, Array(JAVA_LANG_OBJECT))) ,
        BYTE   -> Pair("unboxToByte",    new JMethodType(JType.BYTE,    Array(JAVA_LANG_OBJECT))) ,
        CHAR   -> Pair("unboxToChar",    new JMethodType(JType.CHAR,    Array(JAVA_LANG_OBJECT))) ,
        SHORT  -> Pair("unboxToShort",   new JMethodType(JType.SHORT,   Array(JAVA_LANG_OBJECT))) ,
        INT    -> Pair("unboxToInt",     new JMethodType(JType.INT,     Array(JAVA_LANG_OBJECT))) ,
        LONG   -> Pair("unboxToLong",    new JMethodType(JType.LONG,    Array(JAVA_LANG_OBJECT))) ,
        FLOAT  -> Pair("unboxToFloat",   new JMethodType(JType.FLOAT,   Array(JAVA_LANG_OBJECT))) ,
        DOUBLE -> Pair("unboxToDouble",  new JMethodType(JType.DOUBLE,  Array(JAVA_LANG_OBJECT)))
      )
    }

    def isParcelableClass = isAndroidParcelableClass(clasz.symbol)

    def serialVUID = clasz.symbol getAnnotation SerialVersionUIDAttr collect {
      case AnnotationInfo(_, Literal(const) :: _, _) => const.longValue
    }

    private def getSuperInterfaces(c: IClass): Array[String] = {

        // Additional interface parents based on annotations and other cues
        def newParentForAttr(attr: Symbol): Option[Symbol] = attr match {
          case SerializableAttr => Some(SerializableClass)
          case CloneableAttr    => Some(JavaCloneableClass)
          case RemoteAttr       => Some(RemoteInterfaceClass)
          case _                => None
        }

        /** Drop redundant interfaces (ones which are implemented by some other parent) from the immediate parents.
         *  This is important on Android because there is otherwise an interface explosion.
         */
        def minimizeInterfaces(lstIfaces: List[Symbol]): List[Symbol] = {
          var rest   = lstIfaces
          var leaves = List.empty[Symbol]
          while(!rest.isEmpty) {
            val candidate = rest.head
            val nonLeaf = leaves exists { lsym => lsym isSubClass candidate }
            if(!nonLeaf) {
              leaves = candidate :: (leaves filterNot { lsym => candidate isSubClass lsym })
            }
            rest = rest.tail
          }

          leaves
        }

      val ps = c.symbol.info.parents
      val superInterfaces0: List[Symbol] = if(ps.isEmpty) Nil else c.symbol.mixinClasses;
      val superInterfaces = superInterfaces0 ++ c.symbol.annotations.flatMap(ann => newParentForAttr(ann.symbol)) distinct

      if(superInterfaces.isEmpty) JClass.NO_INTERFACES
      else mkArray(minimizeInterfaces(superInterfaces) map javaName)
    }

    var clasz:  IClass = _   // this var must be assigned only by genClass()
    var jclass: JClass = _

    def getCurrentCUnit(): CompilationUnit = { clasz.cunit }

    def genClass(c: IClass) {
      clasz = c
      innerClassBuffer.clear()

      val name = javaName(c.symbol)

      val ps = c.symbol.info.parents
      val superClass: Symbol = if(ps.isEmpty) ObjectClass else ps.head.typeSymbol;

      val ifaces = getSuperInterfaces(c)

      val sig = getGenericSignature(c.symbol, c.symbol.owner)
      jclass = fjbgContext.JClass(javaFlags(c.symbol),
                                  name,
                                  javaName(superClass),
                                  ifaces,
                                  c.cunit.source.toString)

      // typestate: entering mode with valid call sequences:
      //   [ visitSource ] [ visitOuterClass ] ( visitAnnotation | visitAttribute )*

      addEnclosingMethodAttribute()

      val ssa = scalaSignatureAddingMarker(jclass, c.symbol)

      addGenericSignature(jclass, sig)

      addAnnotations(jclass, c.symbol.annotations ++ ssa)

      // typestate: entering mode with valid call sequences:
      //   ( visitInnerClass | visitField | visitMethod )* visitEnd

      if (isStaticModule(c.symbol) || serialVUID != None || isParcelableClass) {

        if (isStaticModule(c.symbol)) { addModuleInstanceField }
        addStaticInit(jclass, c.lookupStaticCtor)

      } else {

        for (constructor <- c.lookupStaticCtor) {
          addStaticInit(jclass, Some(constructor))
        }
        val skipStaticForwarders = (c.symbol.isInterface || settings.noForwarders.value)
        if (!skipStaticForwarders) {
          val lmoc = c.symbol.companionModule
          // add static forwarders if there are no name conflicts; see bugs #363 and #1735
          if (lmoc != NoSymbol) {
            // it must be a top level class (name contains no $s)
            val isCandidateForForwarders = {
              afterPickler { !(lmoc.name.toString contains '$') && lmoc.hasModuleFlag && !lmoc.isImplClass && !lmoc.isNestedClass }
            }
            if (isCandidateForForwarders) {
              log("Adding static forwarders from '%s' to implementations in '%s'".format(c.symbol, lmoc))
              val isRemoteClass = (clasz.symbol hasAnnotation RemoteAttr)
              addForwarders(isRemoteClass, jclass, lmoc.moduleClass)
            }
          }
        }

      }

      clasz.fields  foreach genField
      clasz.methods foreach genMethod

      addInnerClasses(clasz.symbol, jclass)
      bytecodeWriter.writeClass("" + c.symbol.name, jclass, c.symbol)

    }

    private def addEnclosingMethodAttribute() { // JVMS 4.7.7
      val clazz = clasz.symbol
      val sym = clazz.originalEnclosingMethod
      if (sym.isMethod) {
        debuglog("enclosing method for %s is %s (in %s)".format(clazz, sym, sym.enclClass))
        jclass addAttribute fjbgContext.JEnclosingMethodAttribute(
          jclass,
          javaName(sym.enclClass),
          javaName(sym),
          javaType(sym)
        )
      } else if (clazz.isAnonymousClass) {
        val enclClass = clazz.rawowner
        assert(enclClass.isClass, enclClass)
        val sym = enclClass.primaryConstructor
        if (sym == NoSymbol) {
          log("Ran out of room looking for an enclosing method for %s: no constructor here.".format(enclClass, clazz))
        } else {
          debuglog("enclosing method for %s is %s (in %s)".format(clazz, sym, enclClass))
          jclass addAttribute fjbgContext.JEnclosingMethodAttribute(
            jclass,
            javaName(enclClass),
            javaName(sym),
            javaType(sym).asInstanceOf[JMethodType]
          )
        }
      }
    }

    def genField(f: IField) {
      debuglog("Adding field: " + f.symbol.fullName)

      val sig = getGenericSignature(f.symbol, clasz.symbol)
      val jfield = jclass.addNewField(
        javaFlags(f.symbol) | javaFieldFlags(f.symbol),
        javaName(f.symbol),
        javaType(f.symbol.tpe)
      )

      addGenericSignature(jfield, sig)

      addAnnotations(jfield, f.symbol.annotations)
    }

    def debugLevel = settings.debuginfo.indexOfChoice

    // val emitSource = debugLevel >= 1
    // val emitLines  = debugLevel >= 2
    val emitVars   = debugLevel >= 3

    var method:  IMethod = _
    var jmethod: JMethod = _

    def genMethod(m: IMethod) {

        def isClosureApply(sym: Symbol): Boolean = {
          (sym.name == nme.apply) &&
          sym.owner.isSynthetic &&
          sym.owner.tpe.parents.exists { t =>
            val TypeRef(_, sym, _) = t
            FunctionClass contains sym
          }
        }

      if (m.symbol.isStaticConstructor || definitions.isGetClass(m.symbol)) return

      debuglog("Generating method " + m.symbol.fullName)
      method = m
      endPC.clear
      computeLocalVarsIndex(m)

      var resTpe = javaType(m.symbol.tpe.resultType)
      if (m.symbol.isClassConstructor)
        resTpe = JType.VOID

      var flags = javaFlags(m.symbol)
      if (jclass.isInterface)  { flags |= ACC_ABSTRACT }
      if (m.symbol.isStrictFP) { flags |= ACC_STRICT   }
      if (method.native)       { flags |= ACC_NATIVE   } // native methods of objects are generated in mirror classes

      val sig = getGenericSignature(m.symbol, clasz.symbol)
      jmethod = jclass.addNewMethod(flags,
                                    javaName(m.symbol),
                                    resTpe,
                                    mkArray(m.params map (p => javaType(p.kind))),
                                    mkArray(m.params map (p => javaName(p.sym))))

      val isRemoteClass = (clasz.symbol hasAnnotation RemoteAttr)
      addRemoteExceptionAnnot(isRemoteClass, jmethod.isPublic, m.symbol)

      // typestate: entering mode with valid call sequences:
      //   [ visitAnnotationDefault ] ( visitAnnotation | visitParameterAnnotation | visitAttribute )*

      addGenericSignature(jmethod, sig)

      val (excs, others) = m.symbol.annotations partition (_.symbol == ThrowsClass)
      addExceptionsAttribute(jmethod, excs)
      addAnnotations(jmethod, others)
      addParamAnnotations(jmethod, m.params.map(_.sym.annotations))

      // typestate: entering mode with valid call sequences:
      //   visitCode ( visitFrame | visitXInsn | visitLabel | visitTryCatchBlock | visitLocalVariable | visitLineNumber )* visitMaxs ] visitEnd
      // In addition, the visitXInsn and visitLabel methods must be called in the sequential order of the bytecode instructions of the visited code,
      // visitTryCatchBlock must be called before the labels passed as arguments have been visited, and
      // the visitLocalVariable and visitLineNumber methods must be called after the labels passed as arguments have been visited.

      val hasCodeAttribute = (!jmethod.isAbstract() && !method.native)
      if (hasCodeAttribute) {
        val jcode = jmethod.getCode().asInstanceOf[JExtendedCode]

        // add a fake local for debugging purposes
        if (emitVars && isClosureApply(method.symbol)) {
          val outerField = clasz.symbol.info.decl(nme.OUTER_LOCAL)
          if (outerField != NoSymbol) {
            log("Adding fake local to represent outer 'this' for closure " + clasz)
            val _this =
              new Local(method.symbol.newVariable(nme.FAKE_LOCAL_THIS),
                        toTypeKind(outerField.tpe),
                        false)
            m.locals = m.locals ::: List(_this)
            computeLocalVarsIndex(m) // since we added a new local, we need to recompute indexes

            jcode.emitALOAD_0()
            jcode.emitGETFIELD(javaName(clasz.symbol),
                               javaName(outerField),
                               javaType(outerField))
            jcode.emitSTORE(indexOf(_this), javaType(_this.kind))
          }
        }

        for (local <- m.locals if ! m.params.contains(local)) {
          debuglog("add local var: " + local)
          jmethod.addNewLocalVariable(javaType(local.kind), javaName(local.sym))
        }

        genCode(m)
        if (emitVars) { genLocalVariableTable(m, jcode) }

      }

      // check for code size
      try jmethod.freeze()
      catch {
        case e: JCode.CodeSizeTooBigException =>
          clasz.cunit.error(m.symbol.pos, "Code size exceeds JVM limits: %d".format(e.codeSize))
          throw e
      }
    }

    def addModuleInstanceField() {
      jclass.addNewField(PublicStaticFinal,
                         nme.MODULE_INSTANCE_FIELD.toString,
                         jclass.getType())
    }

    /* Typestate: should be called before emitting fields (because it invokes addCreatorCode() which adds an IField to the current IClass). */
    def addStaticInit(cls: JClass, mopt: Option[IMethod]) {
      val clinitMethod = cls.addNewMethod(PublicStatic,
                                          "<clinit>",
                                          JType.VOID,
                                          JType.EMPTY_ARRAY,
                                          new Array[String](0))
      val clinit = clinitMethod.getCode().asInstanceOf[JExtendedCode]

      mopt match {

       	case Some(m) =>

          val oldLastBlock = m.lastBlock
          val lastBlock = m.newBlock()
          oldLastBlock.replaceInstruction(oldLastBlock.length - 1, JUMP(lastBlock))

          if (isStaticModule(clasz.symbol)) {
            // call object's private ctor from static ctor
            lastBlock emit NEW(REFERENCE(m.symbol.enclClass))
            lastBlock emit CALL_METHOD(m.symbol.enclClass.primaryConstructor, Static(true))
          }

          // add serialVUID code
          serialVUID foreach { value =>
            val fieldName = "serialVersionUID"
            val fieldSymbol = clasz.symbol.newValue(newTermName(fieldName), NoPosition, Flags.STATIC | Flags.FINAL) setInfo longType
            clasz addField new IField(fieldSymbol)
            lastBlock emit CONSTANT(Constant(value))
            lastBlock emit STORE_FIELD(fieldSymbol, true)
          }

          if (isParcelableClass) { addCreatorCode(lastBlock) }

          lastBlock emit RETURN(UNIT)
          lastBlock.close

       	  method = m
       	  jmethod = clinitMethod
       	  genCode(m)

       	case None =>
          legacyStaticInitializer(cls, clinit)
      }
    }

    /* used only from addStaticInit() */
    private def legacyStaticInitializer(cls: JClass, clinit: JExtendedCode) {
      if (isStaticModule(clasz.symbol)) {
        clinit emitNEW cls.getName()
        clinit.emitINVOKESPECIAL(cls.getName(),
                                 JMethod.INSTANCE_CONSTRUCTOR_NAME,
                                 JMethodType.ARGLESS_VOID_FUNCTION)
      }

      serialVUID foreach { value =>
        val fieldName = "serialVersionUID"
        jclass.addNewField(PublicStaticFinal, fieldName, JType.LONG)
        clinit emitPUSH value
        clinit.emitPUSH(value)
        clinit.emitPUTSTATIC(jclass.getName(), fieldName, JType.LONG)
      }

      if (isParcelableClass) { legacyAddCreatorCode(clinit) }

      clinit.emitRETURN()
    }

    // -----------------------------------------------------------------------------------------
    // Emitting bytecode instructions.
    // -----------------------------------------------------------------------------------------

    var linearization: List[BasicBlock] = Nil
    var isModuleInitialized = false

    private val conds = immutable.Map[TestOp, Int](
      EQ -> JExtendedCode.COND_EQ,
      NE -> JExtendedCode.COND_NE,
      LT -> JExtendedCode.COND_LT,
      GT -> JExtendedCode.COND_GT,
      LE -> JExtendedCode.COND_LE,
      GE -> JExtendedCode.COND_GE
    )

    private def genConstant(jcode: JExtendedCode, const: Constant) {
      const.tag match {
        case UnitTag    => ()
        case BooleanTag => jcode emitPUSH const.booleanValue
        case ByteTag    => jcode emitPUSH const.byteValue
        case ShortTag   => jcode emitPUSH const.shortValue
        case CharTag    => jcode emitPUSH const.charValue
        case IntTag     => jcode emitPUSH const.intValue
        case LongTag    => jcode emitPUSH const.longValue
        case FloatTag   => jcode emitPUSH const.floatValue
        case DoubleTag  => jcode emitPUSH const.doubleValue
        case StringTag  => jcode emitPUSH const.stringValue
        case NullTag    => jcode.emitACONST_NULL()
        case ClassTag   =>
          val kind = toTypeKind(const.typeValue)
          val toPush =
            if (kind.isValueType) classLiteral(kind)
            else javaType(kind).asInstanceOf[JReferenceType]

          jcode emitPUSH toPush

        case EnumTag   =>
          val sym = const.symbolValue
          jcode.emitGETSTATIC(javaName(sym.owner),
                              javaName(sym),
                              javaType(sym.tpe.underlying))
        case _         =>
          abort("Unknown constant value: " + const)
      }
    }


    /** Invoked from genMethod() and addStaticInit() */
    def genCode(m: IMethod) {
      val jcode = jmethod.getCode.asInstanceOf[JExtendedCode]

      def makeLabels(bs: List[BasicBlock]) = {
        debuglog("Making labels for: " + method)

        mutable.HashMap(bs map (_ -> jcode.newLabel) : _*)
      }

      isModuleInitialized = false

      linearization = linearizer.linearize(m)
      val labels = makeLabels(linearization)

      var nextBlock: BasicBlock = linearization.head

      def genBlocks(l: List[BasicBlock]): Unit = l match {
        case Nil => ()
        case x :: Nil => nextBlock = null; genBlock(x)
        case x :: y :: ys => nextBlock = y; genBlock(x); genBlocks(y :: ys)
      }

      /**Generate exception handlers for the current method. */
      def genExceptionHandlers() {

        /** Return a list of pairs of intervals where the handler is active.
         *  The intervals in the list have to be inclusive in the beginning and
         *  exclusive in the end: [start, end).
         */
        def ranges(e: ExceptionHandler): List[(Int, Int)] = {
          var covered = e.covered
          var ranges: List[(Int, Int)] = Nil
          var start = -1
          var end = -1

          linearization foreach { b =>
            if (! (covered contains b) ) {
              if (start >= 0) { // we're inside a handler range
                end = labels(b).getAnchor()
                ranges ::= ((start, end))
                start = -1
              }
            } else {
              if (start < 0)  // we're not inside a handler range
                start = labels(b).getAnchor()

              end = endPC(b)
              covered -= b
            }
          }

          /* Add the last interval. Note that since the intervals are
           * open-ended to the right, we have to give a number past the actual
           * code!
           */
          if (start >= 0) {
            ranges ::= ((start, jcode.getPC()))
          }

          if (!covered.isEmpty) {
            debuglog("Some covered blocks were not found in method: " + method +
                     " covered: " + covered + " not in " + linearization)
          }

          ranges
        }

        for (e <- this.method.exh ; p <- ranges(e).sortBy(_._1)) {
          if (p._1 < p._2) {
            debuglog("Adding exception handler " + e + "at block: " + e.startBlock + " for " + method +
                  " from: " + p._1 + " to: " + p._2 + " catching: " + e.cls);
            val cls = if (e.cls == NoSymbol || e.cls == ThrowableClass) null
                      else javaName(e.cls)
            jcode.addExceptionHandler(p._1, p._2,
                                      labels(e.startBlock).getAnchor(),
                                      cls)
          } else
            log("Empty exception range: " + p)
        }
      } // end of genCode()'s genExceptionHandlers()

      def isAccessibleFrom(target: Symbol, site: Symbol): Boolean = {
        target.isPublic || target.isProtected && {
          (site.enclClass isSubClass target.enclClass) ||
          (site.enclosingPackage == target.privateWithin)
        }
      } // end of genCode()'s isAccessibleFrom()

      def genCallMethod(call: CALL_METHOD) {
        val CALL_METHOD(method, style) = call
        val siteSymbol  = clasz.symbol
        val hostSymbol  = call.hostClass
        val methodOwner = method.owner
        // info calls so that types are up to date; erasure may add lateINTERFACE to traits
        hostSymbol.info ; methodOwner.info

        def isInterfaceCall(sym: Symbol) = (
             sym.isInterface && methodOwner != ObjectClass
          || sym.isJavaDefined && sym.isNonBottomSubClass(ClassfileAnnotationClass)
        )
        // whether to reference the type of the receiver or
        // the type of the method owner (if not an interface!)
        val useMethodOwner = (
             style != Dynamic
          || !isInterfaceCall(hostSymbol) && isAccessibleFrom(methodOwner, siteSymbol)
          || hostSymbol.isBottomClass
        )
        val receiver = if (useMethodOwner) methodOwner else hostSymbol
        val jowner   = javaName(receiver)
        val jname    = javaName(method)
        val jtype    = javaType(method).asInstanceOf[JMethodType]

        def debugMsg(invoke: String) {
          debuglog("%s %s %s.%s:%s".format(invoke, receiver.accessString, jowner, jname, jtype))
        }

        def initModule() {
          // we initialize the MODULE$ field immediately after the super ctor
          if (isStaticModule(siteSymbol) && !isModuleInitialized &&
              jmethod.getName() == JMethod.INSTANCE_CONSTRUCTOR_NAME &&
              jname == JMethod.INSTANCE_CONSTRUCTOR_NAME) {
            isModuleInitialized = true
            jcode.emitALOAD_0()
            jcode.emitPUTSTATIC(jclass.getName(),
                                nme.MODULE_INSTANCE_FIELD.toString,
                                jclass.getType())
          }
        }

        style match {
          case Static(true)                         => jcode.emitINVOKESPECIAL  (jowner, jname, jtype) ; debugMsg("invokespecial")
          case Static(false)                        => jcode.emitINVOKESTATIC   (jowner, jname, jtype) ; debugMsg("invokestatic")
          case Dynamic if isInterfaceCall(receiver) => jcode.emitINVOKEINTERFACE(jowner, jname, jtype) ; debugMsg("invokinterface")
          case Dynamic                              => jcode.emitINVOKEVIRTUAL  (jowner, jname, jtype) ; debugMsg("invokevirtual")
          case SuperCall(_)                         =>
            jcode.emitINVOKESPECIAL(jowner, jname, jtype)
            initModule()
            debugMsg("invokespecial")
        }
      } // end of genCode()'s genCallMethod()

      def genBlock(b: BasicBlock) {
        labels(b).anchorToNext()

        debuglog("Generating code for block: " + b + " at pc: " + labels(b).getAnchor())
        var lastMappedPC = 0
        var lastLineNr = 0
        var crtPC = 0

        /** local variables whose scope appears in this block. */
        val varsInBlock: mutable.Set[Local] = new mutable.HashSet
        val lastInstr = b.lastInstruction

        for (instr <- b) {

          instr match {
            case THIS(_)           => jcode.emitALOAD_0()

            case CONSTANT(const)       => genConstant(jcode, const)

            case LOAD_ARRAY_ITEM(kind) =>
              if(kind.isRefOrArrayType) { jcode.emitAALOAD() }
              else {
                (kind: @unchecked) match {
                  case UNIT            => throw new IllegalArgumentException("invalid type for aload " + kind)
                  case BOOL | BYTE     => jcode.emitBALOAD()
                  case SHORT           => jcode.emitSALOAD()
                  case CHAR            => jcode.emitCALOAD()
                  case INT             => jcode.emitIALOAD()
                  case LONG            => jcode.emitLALOAD()
                  case FLOAT           => jcode.emitFALOAD()
                  case DOUBLE          => jcode.emitDALOAD()
                }
              }

            case LOAD_LOCAL(local)     => jcode.emitLOAD(indexOf(local), javaType(local.kind))

            case lf @ LOAD_FIELD(field, isStatic) =>
              var owner = javaName(lf.hostClass)
              debuglog("LOAD_FIELD with owner: " + owner +
                    " flags: " + Flags.flagsToString(field.owner.flags))
              val fieldJName = javaName(field)
              val fieldJType = javaType(field)
              if (isStatic) jcode.emitGETSTATIC(owner, fieldJName, fieldJType)
              else          jcode.emitGETFIELD( owner, fieldJName, fieldJType)

            case LOAD_MODULE(module) =>
              // assert(module.isModule, "Expected module: " + module)
              debuglog("generating LOAD_MODULE for: " + module + " flags: " + Flags.flagsToString(module.flags));
              if (clasz.symbol == module.moduleClass && jmethod.getName() != nme.readResolve.toString)
                jcode.emitALOAD_0()
              else
                jcode.emitGETSTATIC(javaName(module) /* + "$" */ ,
                                    nme.MODULE_INSTANCE_FIELD.toString,
                                    javaType(module))

            case STORE_ARRAY_ITEM(kind) =>
              if(kind.isRefOrArrayType) { jcode.emitAASTORE() }
              else {
                (kind: @unchecked) match {
                  case UNIT            => throw new IllegalArgumentException("invalid type for astore " + kind)
                  case BOOL | BYTE     => jcode.emitBASTORE()
                  case SHORT           => jcode.emitSASTORE()
                  case CHAR            => jcode.emitCASTORE()
                  case INT             => jcode.emitIASTORE()
                  case LONG            => jcode.emitLASTORE()
                  case FLOAT           => jcode.emitFASTORE()
                  case DOUBLE          => jcode.emitDASTORE()
                }
              }

            case STORE_LOCAL(local) =>
              jcode.emitSTORE(indexOf(local), javaType(local.kind))

            case STORE_THIS(_) =>
              // this only works for impl classes because the self parameter comes first
              // in the method signature. If that changes, this code has to be revisited.
              jcode.emitASTORE_0()

            case STORE_FIELD(field, isStatic) =>
              val owner = javaName(field.owner)
              val fieldJName = javaName(field)
              val fieldJType = javaType(field)
              if (isStatic) jcode.emitPUTSTATIC(owner, fieldJName, fieldJType)
              else          jcode.emitPUTFIELD( owner, fieldJName, fieldJType)

            case CALL_PRIMITIVE(primitive) => genPrimitive(primitive, instr.pos)

            /** Special handling to access native Array.clone() */
            case call @ CALL_METHOD(definitions.Array_clone, Dynamic) =>
              val target: String = javaType(call.targetTypeKind).getSignature()
              jcode.emitINVOKEVIRTUAL(target, "clone", arrayCloneType)

            case call @ CALL_METHOD(method, style) => genCallMethod(call)

            case BOX(kind) =>
              val Pair(mname, mtype) = jBoxTo(kind)
              jcode.emitINVOKESTATIC(BoxesRunTime, mname, mtype)

            case UNBOX(kind) =>
              val Pair(mname, mtype) = jUnboxTo(kind)
              jcode.emitINVOKESTATIC(BoxesRunTime, mname, mtype)

            case NEW(REFERENCE(cls)) =>
              val className = javaName(cls)
              jcode emitNEW className

            case CREATE_ARRAY(elem, 1) =>
              if(elem.isRefOrArrayType) { jcode emitANEWARRAY javaType(elem).asInstanceOf[JReferenceType] }
              else                      { jcode emitNEWARRAY  javaType(elem) }

            case CREATE_ARRAY(elem, dims) =>
              jcode.emitMULTIANEWARRAY(javaType(ArrayN(elem, dims)).asInstanceOf[JReferenceType], dims)

            case IS_INSTANCE(tpe) =>
              tpe match {
                case REFERENCE(cls) => jcode emitINSTANCEOF new JObjectType(javaName(cls))
                case ARRAY(elem)    => jcode emitINSTANCEOF new JArrayType(javaType(elem))
                case _              => abort("Unknown reference type in IS_INSTANCE: " + tpe)
              }

            case CHECK_CAST(tpe) =>
              tpe match {
                case REFERENCE(cls) => if (cls != ObjectClass) { jcode emitCHECKCAST new JObjectType(javaName(cls)) } // No need to checkcast for Objects
                case ARRAY(elem)    => jcode emitCHECKCAST new JArrayType(javaType(elem))
                case _              => abort("Unknown reference type in IS_INSTANCE: " + tpe)
              }

            case SWITCH(tags, branches) =>
              val tagArray = new Array[Array[Int]](tags.length)
              var caze = tags
              var i = 0

              while (i < tagArray.length) {
                tagArray(i) = new Array[Int](caze.head.length)
                caze.head.copyToArray(tagArray(i), 0)
                i += 1
                caze = caze.tail
              }
              val branchArray = jcode.newLabels(tagArray.length)
              i = 0
              while (i < branchArray.length) {
                branchArray(i) = labels(branches(i))
                i += 1
              }
              debuglog("Emitting SWITCH:\ntags: " + tags + "\nbranches: " + branches)
              jcode.emitSWITCH(tagArray,
                               branchArray,
                               labels(branches.last),
                               MIN_SWITCH_DENSITY)
              ()

            case JUMP(whereto) =>
              if (nextBlock != whereto)
                jcode.emitGOTO_maybe_W(labels(whereto), false) // default to short jumps

            case CJUMP(success, failure, cond, kind) =>
              if(kind.isIntSizedType) { // BOOL, BYTE, CHAR, SHORT, or INT
                if (nextBlock == success) {
                  jcode.emitIF_ICMP(conds(cond.negate()), labels(failure))
                  // .. and fall through to success label
                } else {
                  jcode.emitIF_ICMP(conds(cond), labels(success))
                  if (nextBlock != failure)
                    jcode.emitGOTO_maybe_W(labels(failure), false)
                }
              } else if(kind.isRefOrArrayType) { // REFERENCE(_) | ARRAY(_)
                if (nextBlock == success) {
                  jcode.emitIF_ACMP(conds(cond.negate()), labels(failure))
                  // .. and fall through to success label
                } else {
                  jcode.emitIF_ACMP(conds(cond), labels(success))
                  if (nextBlock != failure)
                    jcode.emitGOTO_maybe_W(labels(failure), false)
                }
              } else {
                (kind: @unchecked) match {
                  case LONG   => jcode.emitLCMP()
                  case FLOAT  =>
                    if (cond == LT || cond == LE) jcode.emitFCMPG()
                    else jcode.emitFCMPL()
                  case DOUBLE =>
                    if (cond == LT || cond == LE) jcode.emitDCMPG()
                    else jcode.emitDCMPL()
                }
                if (nextBlock == success) {
                  jcode.emitIF(conds(cond.negate()), labels(failure))
                  // .. and fall through to success label
                } else {
                  jcode.emitIF(conds(cond), labels(success));
                  if (nextBlock != failure)
                    jcode.emitGOTO_maybe_W(labels(failure), false)
                }
              }

            case CZJUMP(success, failure, cond, kind) =>
              if(kind.isIntSizedType) { // BOOL, BYTE, CHAR, SHORT, or INT
                if (nextBlock == success) {
                  jcode.emitIF(conds(cond.negate()), labels(failure))
                } else {
                  jcode.emitIF(conds(cond), labels(success))
                  if (nextBlock != failure)
                    jcode.emitGOTO_maybe_W(labels(failure), false)
                }
              } else if(kind.isRefOrArrayType) { // REFERENCE(_) | ARRAY(_)
                val Success = success
                val Failure = failure
                (cond, nextBlock) match {
                  case (EQ, Success) => jcode emitIFNONNULL labels(failure)
                  case (NE, Failure) => jcode emitIFNONNULL labels(success)
                  case (EQ, Failure) => jcode emitIFNULL    labels(success)
                  case (NE, Success) => jcode emitIFNULL    labels(failure)
                  case (EQ, _) =>
                    jcode emitIFNULL labels(success)
                    jcode.emitGOTO_maybe_W(labels(failure), false)
                  case (NE, _) =>
                    jcode emitIFNONNULL labels(success)
                    jcode.emitGOTO_maybe_W(labels(failure), false)
                }
              } else {
                (kind: @unchecked) match {
                  case LONG   =>
                    jcode.emitLCONST_0()
                    jcode.emitLCMP()
                  case FLOAT  =>
                    jcode.emitFCONST_0()
                    if (cond == LT || cond == LE) jcode.emitFCMPG()
                    else jcode.emitFCMPL()
                  case DOUBLE =>
                    jcode.emitDCONST_0()
                    if (cond == LT || cond == LE) jcode.emitDCMPG()
                    else jcode.emitDCMPL()
                }
                if (nextBlock == success) {
                  jcode.emitIF(conds(cond.negate()), labels(failure))
                } else {
                  jcode.emitIF(conds(cond), labels(success))
                  if (nextBlock != failure)
                    jcode.emitGOTO_maybe_W(labels(failure), false)
                }
              }

            case RETURN(kind) => jcode emitRETURN javaType(kind)

            case THROW(_)     => jcode.emitATHROW()

            case DROP(kind) =>
              if(kind.isWideType) jcode.emitPOP2()
              else                jcode.emitPOP()

            case DUP(kind) =>
              if(kind.isWideType) jcode.emitDUP2()
              else                jcode.emitDUP()

            case MONITOR_ENTER() => jcode.emitMONITORENTER()

            case MONITOR_EXIT()  => jcode.emitMONITOREXIT()

            case SCOPE_ENTER(lv) =>
              varsInBlock += lv
              lv.start = jcode.getPC()

            case SCOPE_EXIT(lv) =>
              if (varsInBlock(lv)) {
                lv.ranges = (lv.start, jcode.getPC()) :: lv.ranges
                varsInBlock -= lv
              }
              else if (b.varsInScope(lv)) {
                lv.ranges = (labels(b).getAnchor(), jcode.getPC()) :: lv.ranges
                b.varsInScope -= lv
              }
              else dumpMethodAndAbort(method, "Illegal local var nesting")

            case LOAD_EXCEPTION(_) =>
              ()
          }

          crtPC = jcode.getPC()

          // assert(instr.pos.source.isEmpty || instr.pos.source.get == (clasz.cunit.source), "sources don't match")
          // val crtLine = instr.pos.line.get(lastLineNr);

          val crtLine = try {
            if (instr.pos == NoPosition) lastLineNr else (instr.pos).line // check NoPosition to avoid costly exception
          } catch {
            case _: UnsupportedOperationException =>
              log("Warning: wrong position in: " + method)
              lastLineNr
          }

          if (instr eq lastInstr) { endPC(b) = jcode.getPC() }

          //System.err.println("CRTLINE: " + instr.pos + " " +
          //           /* (if (instr.pos < clasz.cunit.source.content.length) clasz.cunit.source.content(instr.pos) else '*') + */ " " + crtLine);

          if (crtPC > lastMappedPC) {
            jcode.completeLineNumber(lastMappedPC, crtPC, crtLine)
            lastMappedPC = crtPC
            lastLineNr   = crtLine
          }
        }

        // local vars that survived this basic block
        for (lv <- varsInBlock) {
          lv.ranges = (lv.start, jcode.getPC()) :: lv.ranges
        }
        for (lv <- b.varsInScope) {
          lv.ranges = (labels(b).getAnchor(), jcode.getPC()) :: lv.ranges
        }
      } // end of genCode()'s genBlock()


      def genPrimitive(primitive: Primitive, pos: Position) {
        primitive match {
          case Negation(kind) =>
            if(kind.isIntSizedType) { jcode.emitINEG() }
            else {
              kind match {
                case LONG   => jcode.emitLNEG()
                case FLOAT  => jcode.emitFNEG()
                case DOUBLE => jcode.emitDNEG()
                case _ => abort("Impossible to negate a " + kind)
              }
            }

          case Arithmetic(op, kind) =>
            op match {
              case ADD =>
                if(kind.isIntSizedType) { jcode.emitIADD() }
                else {
                  (kind: @unchecked) match {
                    case LONG   => jcode.emitLADD()
                    case FLOAT  => jcode.emitFADD()
                    case DOUBLE => jcode.emitDADD()
                  }
                }

              case SUB =>
                if(kind.isIntSizedType) { jcode.emitISUB() }
                else {
                  (kind: @unchecked) match {
                    case LONG   => jcode.emitLSUB()
                    case FLOAT  => jcode.emitFSUB()
                    case DOUBLE => jcode.emitDSUB()
                  }
                }

              case MUL =>
                if(kind.isIntSizedType) { jcode.emitIMUL() }
                else {
                  (kind: @unchecked) match {
                    case LONG   => jcode.emitLMUL()
                    case FLOAT  => jcode.emitFMUL()
                    case DOUBLE => jcode.emitDMUL()
                  }
                }

              case DIV =>
                if(kind.isIntSizedType) { jcode.emitIDIV() }
                else {
                  (kind: @unchecked) match {
                    case LONG   => jcode.emitLDIV()
                    case FLOAT  => jcode.emitFDIV()
                    case DOUBLE => jcode.emitDDIV()
                  }
                }

              case REM =>
                if(kind.isIntSizedType) { jcode.emitIREM() }
                else {
                  (kind: @unchecked) match {
                    case LONG   => jcode.emitLREM()
                    case FLOAT  => jcode.emitFREM()
                    case DOUBLE => jcode.emitDREM()
                  }
                }

              case NOT =>
                if(kind.isIntSizedType) {
                  jcode.emitPUSH(-1)
                  jcode.emitIXOR()
                } else if(kind == LONG) {
                  jcode.emitPUSH(-1l)
                  jcode.emitLXOR()
                } else {
                  abort("Impossible to negate an " + kind)
                }

              case _ =>
                abort("Unknown arithmetic primitive " + primitive)
            }

          case Logical(op, kind) => (op, kind) match {
            case (AND, LONG) => jcode.emitLAND()
            case (AND, INT)  => jcode.emitIAND()
            case (AND, _)    =>
              jcode.emitIAND()
              if (kind != BOOL)
                jcode.emitT2T(javaType(INT), javaType(kind));

            case (OR, LONG) => jcode.emitLOR()
            case (OR, INT)  => jcode.emitIOR()
            case (OR, _) =>
              jcode.emitIOR()
              if (kind != BOOL)
                jcode.emitT2T(javaType(INT), javaType(kind));

            case (XOR, LONG) => jcode.emitLXOR()
            case (XOR, INT)  => jcode.emitIXOR()
            case (XOR, _) =>
              jcode.emitIXOR()
              if (kind != BOOL)
                jcode.emitT2T(javaType(INT), javaType(kind));
          }

          case Shift(op, kind) => (op, kind) match {
            case (LSL, LONG) => jcode.emitLSHL()
            case (LSL, INT)  => jcode.emitISHL()
            case (LSL, _) =>
              jcode.emitISHL()
              jcode.emitT2T(javaType(INT), javaType(kind))

            case (ASR, LONG) => jcode.emitLSHR()
            case (ASR, INT)  => jcode.emitISHR()
            case (ASR, _) =>
              jcode.emitISHR()
              jcode.emitT2T(javaType(INT), javaType(kind))

            case (LSR, LONG) => jcode.emitLUSHR()
            case (LSR, INT)  => jcode.emitIUSHR()
            case (LSR, _) =>
              jcode.emitIUSHR()
              jcode.emitT2T(javaType(INT), javaType(kind))
          }

          case Comparison(op, kind) => ((op, kind): @unchecked) match {
            case (CMP, LONG)    => jcode.emitLCMP()
            case (CMPL, FLOAT)  => jcode.emitFCMPL()
            case (CMPG, FLOAT)  => jcode.emitFCMPG()
            case (CMPL, DOUBLE) => jcode.emitDCMPL()
            case (CMPG, DOUBLE) => jcode.emitDCMPL()
          }

          case Conversion(src, dst) =>
            debuglog("Converting from: " + src + " to: " + dst)
            if (dst == BOOL) {
              println("Illegal conversion at: " + clasz + " at: " + pos.source + ":" + pos.line)
            } else
              jcode.emitT2T(javaType(src), javaType(dst))

          case ArrayLength(_) =>
            jcode.emitARRAYLENGTH()

          case StartConcat =>
            jcode emitNEW StringBuilderClassName
            jcode.emitDUP()
            jcode.emitINVOKESPECIAL(StringBuilderClassName,
                                    JMethod.INSTANCE_CONSTRUCTOR_NAME,
                                    JMethodType.ARGLESS_VOID_FUNCTION)

          case StringConcat(el) =>
            val jtype = el match {
              case REFERENCE(_) | ARRAY(_) => JAVA_LANG_OBJECT
              case _ => javaType(el)
            }
            jcode.emitINVOKEVIRTUAL(StringBuilderClassName,
                                    "append",
                                    new JMethodType(StringBuilderType,
                                    Array(jtype)))
          case EndConcat =>
            jcode.emitINVOKEVIRTUAL(StringBuilderClassName,
                                    "toString",
                                    toStringType)

          case _ =>
            abort("Unimplemented primitive " + primitive)
        }
      } // end of genCode()'s genPrimitive()

      // genCode starts here
      genBlocks(linearization)

      if (this.method.exh != Nil) { genExceptionHandlers() }

    } // end of BytecodeGenerator.genCode()


    /** Emit a Local variable table for debugging purposes.
     *  Synthetic locals are skipped. All variables are method-scoped.
     *
     *  Invoked only from genMethod(), ie used only when emitting plain classes.
     *
     */
    private def genLocalVariableTable(m: IMethod, jcode: JCode) {

        /** Merge adjacent ranges. */
        def mergeEntries(ranges: List[(Int, Int)]): List[(Int, Int)] = {
          (ranges.foldLeft(Nil: List[(Int, Int)]) { (collapsed: List[(Int, Int)], p: (Int, Int)) => (collapsed, p) match {
            case (Nil, _) => List(p)
            case ((s1, e1) :: rest, (s2, e2)) if (e1 == s2) => (s1, e2) :: rest
            case _ => p :: collapsed
          }}).reverse
        }

      val vars = m.locals filterNot (_.sym.isSynthetic)
      if (vars.isEmpty) return

      val pool = jclass.getConstantPool
      val pc = jcode.getPC()
      var anonCounter = 0
      var entries = 0
      vars.foreach { lv =>
        lv.ranges = mergeEntries(lv.ranges.reverse);
        entries += lv.ranges.length
      }
      if (!jmethod.isStatic()) entries += 1

      val lvTab = ByteBuffer.allocate(2 + 10 * entries)
      def emitEntry(name: String, signature: String, idx: Short, start: Short, end: Short) {
        lvTab putShort start
        lvTab putShort end
        lvTab putShort pool.addUtf8(name).toShort
        lvTab putShort pool.addUtf8(signature).toShort
        lvTab putShort idx
      }

      lvTab.putShort(entries.toShort)

      if (!jmethod.isStatic()) {
        emitEntry("this", jclass.getType().getSignature(), 0, 0.toShort, pc.toShort)
      }

      for (lv <- vars) {
        val name = if (javaName(lv.sym) eq null) {
          anonCounter += 1
          "<anon" + anonCounter + ">"
        } else javaName(lv.sym)

        val index = indexOf(lv).toShort
        val tpe   = javaType(lv.kind).getSignature()
        for ((start, end) <- lv.ranges) {
          emitEntry(name, tpe, index, start.toShort, (end - start).toShort)
        }
      }
      val attr =
        fjbgContext.JOtherAttribute(jclass,
                                    jcode,
                                    tpnme.LocalVariableTableATTR.toString,
                                    lvTab.array())
      jcode addAttribute attr
    }


    /** For each basic block, the first PC address following it. */
    val endPC = new mutable.HashMap[BasicBlock, Int]

    ////////////////////// local vars ///////////////////////

    // def sizeOf(sym: Symbol): Int = sizeOf(toTypeKind(sym.tpe))

    def sizeOf(k: TypeKind): Int = if(k.isWideType) 2 else 1

    // def indexOf(m: IMethod, sym: Symbol): Int = {
    //   val Some(local) = m lookupLocal sym
    //   indexOf(local)
    // }

    def indexOf(local: Local): Int = {
      assert(local.index >= 0, "Invalid index for: " + local + "{" + local.## + "}: ")
      local.index
    }

    /**
     * Compute the indexes of each local variable of the given
     * method. *Does not assume the parameters come first!*
     *
     * Invoked only from genMethod().
     *
     */
    def computeLocalVarsIndex(m: IMethod) {
      var idx = if (m.symbol.isStaticMember) 0 else 1;

      for (l <- m.params) {
        debuglog("Index value for " + l + "{" + l.## + "}: " + idx)
        l.index = idx
        idx += sizeOf(l.kind)
      }

      for (l <- m.locals if !(m.params contains l)) {
        debuglog("Index value for " + l + "{" + l.## + "}: " + idx)
        l.index = idx
        idx += sizeOf(l.kind)
      }
    }

  } // end of class JPlainBuilder


  /** builder of mirror classes */
  class JMirrorBuilder(bytecodeWriter: BytecodeWriter) extends JCommonBuilder(bytecodeWriter) {

    private var cunit: CompilationUnit = _
    def getCurrentCUnit(): CompilationUnit = cunit;

    /** Generate a mirror class for a top-level module. A mirror class is a class
     *  containing only static methods that forward to the corresponding method
     *  on the MODULE instance of the given Scala object.  It will only be
     *  generated if there is no companion class: if there is, an attempt will
     *  instead be made to add the forwarder methods to the companion class.
     */
    def genMirrorClass(modsym: Symbol, cunit: CompilationUnit) {
      assert(modsym.companionClass == NoSymbol, modsym)
      innerClassBuffer.clear()
      this.cunit = cunit
      import JAccessFlags._
      val moduleName = javaName(modsym) // + "$"
      val mirrorName = moduleName.substring(0, moduleName.length() - 1)
      val mirrorClass = fjbgContext.JClass(ACC_SUPER | ACC_PUBLIC | ACC_FINAL,
                                           mirrorName,
                                           JAVA_LANG_OBJECT.getName,
                                           JClass.NO_INTERFACES,
                                           "" + cunit.source)

      log("Dumping mirror class for '%s'".format(mirrorClass.getName))

      val ssa = scalaSignatureAddingMarker(mirrorClass, modsym.companionSymbol)
      addAnnotations(mirrorClass, modsym.annotations ++ ssa)

      val isRemoteClass = (modsym hasAnnotation RemoteAttr)
      addForwarders(isRemoteClass, mirrorClass, modsym)

      addInnerClasses(modsym, mirrorClass)
      bytecodeWriter.writeClass("" + modsym.name, mirrorClass, modsym)
    }


  } // end of class JMirrorBuilder


  /** builder of bean info classes */
  class JBeanInfoBuilder(bytecodeWriter: BytecodeWriter) extends JBuilder(bytecodeWriter) {

    /**
     * Generate a bean info class that describes the given class.
     *
     * @author Ross Judson (ross.judson@soletta.com)
     */
    def genBeanInfoClass(clasz: IClass) {

      // val BeanInfoSkipAttr    = definitions.getRequiredClass("scala.beans.BeanInfoSkip")
      // val BeanDisplayNameAttr = definitions.getRequiredClass("scala.beans.BeanDisplayName")
      // val BeanDescriptionAttr = definitions.getRequiredClass("scala.beans.BeanDescription")
      // val description = c.symbol getAnnotation BeanDescriptionAttr
      // informProgress(description.toString)
      innerClassBuffer.clear()

      val beanInfoClass = fjbgContext.JClass(javaFlags(clasz.symbol),
            javaName(clasz.symbol) + "BeanInfo",
            "scala/beans/ScalaBeanInfo",
            JClass.NO_INTERFACES,
            clasz.cunit.source.toString)

      var fieldList = List[String]()

      for (f <- clasz.fields if f.symbol.hasGetter;
	         g = f.symbol.getter(clasz.symbol);
	         s = f.symbol.setter(clasz.symbol);
	         if g.isPublic && !(f.symbol.name startsWith "$")
          ) {
             // inserting $outer breaks the bean
             fieldList = javaName(f.symbol) :: javaName(g) :: (if (s != NoSymbol) javaName(s) else null) :: fieldList
      }

      val methodList: List[String] =
	     for (m <- clasz.methods
	          if !m.symbol.isConstructor &&
	          m.symbol.isPublic &&
	          !(m.symbol.name startsWith "$") &&
	          !m.symbol.isGetter &&
	          !m.symbol.isSetter)
       yield javaName(m.symbol)

      val constructor = beanInfoClass.addNewMethod(ACC_PUBLIC, "<init>", JType.VOID, new Array[JType](0), new Array[String](0))
      val jcode = constructor.getCode().asInstanceOf[JExtendedCode]
      val strKind = new JObjectType(javaName(StringClass))
      val stringArrayKind = new JArrayType(strKind)
      val conType = new JMethodType(JType.VOID, Array(javaType(ClassClass), stringArrayKind, stringArrayKind))

      def push(lst: List[String]) {
        var fi = 0
        for (f <- lst) {
          jcode.emitDUP()
          jcode emitPUSH fi
          if (f == null) { jcode.emitACONST_NULL() }
          else           { jcode emitPUSH f        }
          jcode emitASTORE strKind
          fi += 1
        }
      }

      jcode.emitALOAD_0()
      // push the class
      jcode emitPUSH javaType(clasz.symbol).asInstanceOf[JReferenceType]

      // push the string array of field information
      jcode emitPUSH fieldList.length
      jcode emitANEWARRAY strKind
      push(fieldList)

      // push the string array of method information
      jcode emitPUSH methodList.length
      jcode emitANEWARRAY strKind
      push(methodList)

      // invoke the superclass constructor, which will do the
      // necessary java reflection and create Method objects.
      jcode.emitINVOKESPECIAL("scala/beans/ScalaBeanInfo", "<init>", conType)
      jcode.emitRETURN()

      // TODO no inner classes attribute is written. Confirm intent.
      assert(innerClassBuffer.isEmpty, innerClassBuffer)

      bytecodeWriter.writeClass("BeanInfo ", beanInfoClass, clasz.symbol)
    }

  } // end of class JBeanInfoBuilder

}
