/* NSC -- new Scala compiler
 * Copyright 2005-2012 LAMP/EPFL
 * @author  Martin Odersky
 */

package scala.tools.nsc
package backend.jvm

import scala.tools.asm
import scala.annotation.switch
import scala.collection.immutable

/**
 *  Utilities to mediate between types as represented in Scala ASTs and ASM trees.
 *
 *  @author  Miguel Garcia, http://lamp.epfl.ch/~magarcia/ScalaCompilerCornerReloaded
 *
 */
trait BCodeTypes { _: GenBCode =>

  import global._

  // due to keyboard economy only
  val UNIT   = asm.Type.VOID_TYPE
  val BOOL   = asm.Type.BOOLEAN_TYPE
  val CHAR   = asm.Type.CHAR_TYPE
  val BYTE   = asm.Type.BYTE_TYPE
  val SHORT  = asm.Type.SHORT_TYPE
  val INT    = asm.Type.INT_TYPE
  val LONG   = asm.Type.LONG_TYPE
  val FLOAT  = asm.Type.FLOAT_TYPE
  val DOUBLE = asm.Type.DOUBLE_TYPE

  /*
   * RT_NOTHING and RT_NULL exist at run-time only.
   * They are the bytecode-level manifestation (in method signatures only) of what shows up as NothingClass resp. NullClass in Scala ASTs.
   * Therefore, when RT_NOTHING or RT_NULL are to be emitted,
   * a mapping is needed: the internal names of NothingClass and NullClass can't be emitted as-is.
   */
  val RT_NOTHING    = asm.Type.getObjectType("scala/runtime/Nothing$")
  val RT_NULL       = asm.Type.getObjectType("scala/runtime/Null$")
  val CT_NOTHING    = asm.Type.getObjectType("scala.Nothing") // TODO needed?
  val CT_NULL       = asm.Type.getObjectType("scala.Null")    // TODO needed?

  val ObjectReference    = asm.Type.getObjectType("java/lang/Object")
  val AnyRefReference    = ObjectReference // In tandem, javaName(definitions.AnyRefClass) == ObjectReference. Otherwise every `t1 == t2` requires special-casing.
  val StringReference    = asm.Type.getObjectType("java/lang/String")
  val ThrowableReference = asm.Type.getObjectType("java/lang/Throwable")

  // TODO rather than lazy, have an init() method that populates mutable collections. That would speed up accesses from then on.

  /** A map from scala primitive Types to asm.Type */
  lazy val primitiveTypeMap: Map[Symbol, asm.Type] = {
    import definitions._
    Map(
      UnitClass     -> UNIT,
      BooleanClass  -> BOOL,
      CharClass     -> CHAR,
      ByteClass     -> BYTE,
      ShortClass    -> SHORT,
      IntClass      -> INT,
      LongClass     -> LONG,
      FloatClass    -> FLOAT,
      DoubleClass   -> DOUBLE
    )
  }

  lazy val phantomTypeMap: Map[Symbol, asm.Type] = {
    import definitions._
    Map(
      NothingClass -> RT_NOTHING,
      NullClass    -> RT_NULL,
      NothingClass -> RT_NOTHING, // we map on purpose to RT_NOTHING, getting rid of the distinction compile-time vs. runtime for NullClass.
      NullClass    -> RT_NULL     // ditto.
    )
  }

  /** Maps the method symbol for a box method to the boxed type of the result.
   *  For example, the method symbol for `Byte.box()`) is mapped to the asm.Type `Ljava/lang/Integer;`. */
  lazy val boxResultType: Map[Symbol, asm.Type] = {
    for(Pair(csym, msym) <- definitions.boxMethod)
    yield (msym -> primitiveTypeMap(msym.tpe.resultType.typeSymbol))
  }

  /** Maps the method symbol for an unbox method to the primitive type of the result.
   *  For example, the method symbol for `Byte.unbox()`) is mapped to the asm.Type BYTE. */
  lazy val unboxResultType: Map[Symbol, asm.Type] = {
    for(Pair(csym, msym) <- definitions.unboxMethod)
    yield (msym -> primitiveTypeMap(csym))
  }

  // in keeping with ICode's tradition of calling out boxed types.
  val BOXED_UNIT    = asm.Type.getObjectType("java/lang/Void")
  val BOXED_BOOLEAN = asm.Type.getObjectType("java/lang/Boolean")
  val BOXED_BYTE    = asm.Type.getObjectType("java/lang/Byte")
  val BOXED_SHORT   = asm.Type.getObjectType("java/lang/Short")
  val BOXED_CHAR    = asm.Type.getObjectType("java/lang/Character")
  val BOXED_INT     = asm.Type.getObjectType("java/lang/Integer")
  val BOXED_LONG    = asm.Type.getObjectType("java/lang/Long")
  val BOXED_FLOAT   = asm.Type.getObjectType("java/lang/Float")
  val BOXED_DOUBLE  = asm.Type.getObjectType("java/lang/Double")

  val phantomRefTypes: Map[asm.Type, Type] = scala.collection.immutable.Map(
    RT_NOTHING -> definitions.NothingClass.tpe,
    CT_NOTHING -> definitions.NothingClass.tpe
    // RT_NULL    -> definitions.NullClass.tpe,
    // CT_NULL    -> definitions.NullClass.tpe
  )

  lazy val seenRefTypes = scala.collection.mutable.Map.empty[asm.Type, Type] ++= phantomRefTypes

  val classLiteral = immutable.Map[asm.Type, asm.Type](
    UNIT   -> BOXED_UNIT,
    BOOL   -> BOXED_BOOLEAN,
    BYTE   -> BOXED_BYTE,
    SHORT  -> BOXED_SHORT,
    CHAR   -> BOXED_CHAR,
    INT    -> BOXED_INT,
    LONG   -> BOXED_LONG,
    FLOAT  -> BOXED_FLOAT,
    DOUBLE -> BOXED_DOUBLE
  )

  val asmBoxTo: Map[asm.Type, MethodNameAndType] = {
    Map(
      BOOL   -> MethodNameAndType("boxToBoolean",   "(Z)Ljava/lang/Boolean;"  ) ,
      BYTE   -> MethodNameAndType("boxToByte",      "(B)Ljava/lang/Byte;"     ) ,
      CHAR   -> MethodNameAndType("boxToCharacter", "(C)Ljava/lang/Character;") ,
      SHORT  -> MethodNameAndType("boxToShort",     "(S)Ljava/lang/Short;"    ) ,
      INT    -> MethodNameAndType("boxToInteger",   "(I)Ljava/lang/Integer;"  ) ,
      LONG   -> MethodNameAndType("boxToLong",      "(J)Ljava/lang/Long;"     ) ,
      FLOAT  -> MethodNameAndType("boxToFloat",     "(F)Ljava/lang/Float;"    ) ,
      DOUBLE -> MethodNameAndType("boxToDouble",    "(D)Ljava/lang/Double;"   )
    )
  }

  val asmUnboxTo: Map[asm.Type, MethodNameAndType] = {
    Map(
      BOOL   -> MethodNameAndType("unboxToBoolean", "(Ljava/lang/Object;)Z") ,
      BYTE   -> MethodNameAndType("unboxToByte",    "(Ljava/lang/Object;)B") ,
      CHAR   -> MethodNameAndType("unboxToChar",    "(Ljava/lang/Object;)C") ,
      SHORT  -> MethodNameAndType("unboxToShort",   "(Ljava/lang/Object;)S") ,
      INT    -> MethodNameAndType("unboxToInt",     "(Ljava/lang/Object;)I") ,
      LONG   -> MethodNameAndType("unboxToLong",    "(Ljava/lang/Object;)J") ,
      FLOAT  -> MethodNameAndType("unboxToFloat",   "(Ljava/lang/Object;)F") ,
      DOUBLE -> MethodNameAndType("unboxToDouble",  "(Ljava/lang/Object;)D")
    )
  }

  /** Reverse map for toType */
  private lazy val reversePrimitiveMap: Map[asm.Type, Type] =
    (primitiveTypeMap map { case (s, pt) => (s.tpe, pt) } map (_.swap)).toMap

  final def hasInternalName(sym: Symbol) = { sym.isClass || (sym.isModule && !sym.isMethod) }

  // ---------------- inspector methods on asm.Type  ----------------

  /*
   * Unlike for ICode's REFERENCE, isBoxedType(t) implies isReferenceType(t)
   * Also, `isReferenceType(RT_NOTHING) == true` , similarly for RT_NULL.
   * Use isNullType() , isNothingType() to detect Nothing and Null.
   */
  final def isReferenceType(t: asm.Type) = (t.getSort == asm.Type.OBJECT)

  final def isNonBoxedReferenceType(t: asm.Type) = isReferenceType(t) && !isBoxedType(t)

  final def isArrayType(t: asm.Type) = (t.getSort == asm.Type.ARRAY)

  final def isValueType(t: asm.Type) = {
    (t.getSort : @switch) match {
      case asm.Type.VOID  | asm.Type.BOOLEAN | asm.Type.CHAR   |
           asm.Type.BYTE  | asm.Type.SHORT   | asm.Type.INT    |
           asm.Type.FLOAT | asm.Type.LONG    | asm.Type.DOUBLE
        => true
      case _
        => false
    }
  }

  final def isNonUnitValueType(t: asm.Type): Boolean = { isValueType(t) && !isUnitType(t) }

  final def isBoxedType(t: asm.Type) = {
    t match {
      case BOXED_UNIT  | BOXED_BOOLEAN | BOXED_CHAR   |
           BOXED_BYTE  | BOXED_SHORT   | BOXED_INT    |
           BOXED_FLOAT | BOXED_LONG    | BOXED_DOUBLE
        => true
      case _
        => false
    }
  }


  final def isRefOrArrayType(t: asm.Type) = isReferenceType(t)  || isArrayType(t)

  final def isNothingType(t: asm.Type) = { (t == RT_NOTHING) || (t == CT_NOTHING) }
  final def isNullType   (t: asm.Type) = { (t == RT_NULL)    || (t == CT_NULL)    }
  final def isUnitType   (t: asm.Type) = { t == UNIT }

  final def asmMethodType(s: Symbol): asm.Type = {
    assert(s.isMethod, "not a method-symbol: " + s)
    val resT: asm.Type = if (s.isClassConstructor) asm.Type.VOID_TYPE else toTypeKind(s.tpe.resultType);
    asm.Type.getMethodType( resT, (s.tpe.paramTypes map toTypeKind): _* )
  }

  /** On the JVM,
   *    BOOL, BYTE, CHAR, SHORT, and INT
   *  are like Ints for the purpose of lub calculation.
   **/
  final def isIntSizedType(t: asm.Type): Boolean = {
    (t.getSort : @switch) match {
      case asm.Type.BOOLEAN | asm.Type.CHAR  |
           asm.Type.BYTE    | asm.Type.SHORT | asm.Type.INT
        => true
      case _
        => false
    }
  }

  /** On the JVM, similar to isIntSizedType except that BOOL isn't integral while LONG is. */
  final def isIntegralType(t: asm.Type): Boolean = {
    (t.getSort : @switch) match {
      case asm.Type.CHAR  |
           asm.Type.BYTE  | asm.Type.SHORT | asm.Type.INT |
           asm.Type.LONG
        => true
      case _
        => false
    }
  }

  /** On the JVM, FLOAT and DOUBLE. */
  final def isRealType(t: asm.Type): Boolean = {
    (t.getSort == asm.Type.FLOAT ) ||
    (t.getSort == asm.Type.DOUBLE)
  }

  final def isNumericType(t: asm.Type) = isIntegralType(t) | isRealType(t)

  /** Is this type a category 2 type in JVM terms? (ie, is it LONG or DOUBLE?) */
  final def isWideType(t: asm.Type) = (t.getSize == 2)

  /*
   * Quoting from the JVMS, Sec. 2.4 "Reference Types and Values"
   *
   *   An array type consists of a component type with a single dimension (whose
   *   length is not given by the type). The component type of an array type may itself be
   *   an array type. If, starting from any array type, one considers its component type,
   *   and then (if that is also an array type) the component type of that type, and so on,
   *   eventually one must reach a component type that is not an array type; this is called
   *   the element type of the array type. The element type of an array type is necessarily
   *   either a primitive type, or a class type, or an interface type.
   *
   **/

  /** The (ultimate) element type of this array. */
  final def elementType(t: asm.Type): asm.Type = {
    assert(isArrayType(t), "Asked for the element type of a non-array type: " + t)
    t.getElementType
  }

  /** The type of items this array holds. */
  final def componentType(t: asm.Type): asm.Type = {
    assert(isArrayType(t), "Asked for the component type of a non-array type: " + t)
    val reduced = t.getDimensions - 1
    if(reduced == 0) t.getElementType
    else arrayN(t.getElementType, reduced)
  }

  /** The number of dimensions for array types. */
  final def dimensions(t: asm.Type): Int = {
    assert(isArrayType(t), "Asked for the number of dimensions of a non-array type: " + t.toString)
    t.getDimensions()
  }

  /* the type of 1-dimensional arrays of `elem` type. */
  final def arrayOf(elem: asm.Type): asm.Type = {
    assert(!isUnitType(elem), "The element type of an array type is necessarily either a primitive type, or a class type, or an interface type.")
    asm.Type.getObjectType("[" + elem.getDescriptor)
  }

  /* the type of N-dimensional arrays of `elem` type. */
  final def arrayN(elem: asm.Type, dims: Int): asm.Type = {
    assert(dims > 0)
    assert(!isUnitType(elem), "The element type of an array type is necessarily either a primitive type, or a class type, or an interface type.")
    val desc = ("[" * dims) + elem.getDescriptor
    asm.Type.getObjectType(desc)
  }

  /** Returns the asm.Type for the given type
   **/
  final def toTypeKind(t: Type): asm.Type = {

        /** Interfaces have to be handled delicately to avoid introducing spurious errors,
         *  but if we treat them all as AnyRef we lose too much information.
         **/
        def newReference(sym: Symbol): asm.Type = {
          assert(!primitiveTypeMap.contains(sym), "Use primitiveTypeMap instead.")
          assert(sym != definitions.ArrayClass,   "Use arrayOf() instead.")

          if(sym == definitions.NullClass)    return RT_NULL;
          if(sym == definitions.NothingClass) return RT_NOTHING;

          // Can't call .toInterface (at this phase) or we trip an assertion.
          // See PackratParser#grow for a method which fails with an apparent mismatch
          // between "object PackratParsers$class" and "trait PackratParsers"
          if (sym.isImplClass) {
            // pos/spec-List.scala is the sole failure if we don't check for NoSymbol
            val traitSym = sym.owner.info.decl(tpnme.interfaceName(sym.name))
            if (traitSym != NoSymbol)
              return asm.Type.getObjectType(traitSym.javaBinaryName.toString)
          }

          assert(hasInternalName(sym), "Invoked for a symbol lacking JVM internal name: " + sym.fullName)
          asm.Type.getObjectType(sym.javaBinaryName.toString)

        }

        def primitiveOrRefType(sym: Symbol): asm.Type = {
          assert(sym != definitions.ArrayClass, "Use primitiveOrArrayOrRefType() instead.")

          primitiveTypeMap.getOrElse(sym, newReference(sym))
        }

        def primitiveOrRefType2(sym: Symbol): asm.Type = {
          primitiveTypeMap.get(sym) match {
            case Some(pt) => pt
            case None =>
              sym match {
                case definitions.NullClass    => RT_NULL
                case definitions.NothingClass => RT_NOTHING
                case _ if sym.isClass         => newReference(sym)
                case _ =>
                  assert(sym.isType, sym) // it must be compiling Array[a]
                  ObjectReference
              }
          }
        }

    import definitions.ArrayClass

    // Call to .normalize fixes #3003 (follow type aliases). Otherwise, primitiveOrArrayOrRefType() would return ObjectReference.
    t.normalize match {

      case ThisType(sym) =>
        if(sym == ArrayClass) ObjectReference
        else                  phantomTypeMap.getOrElse(sym, asm.Type.getObjectType(sym.javaBinaryName.toString))

      case SingleType(_, sym) => primitiveOrRefType(sym)

      case _: ConstantType    => toTypeKind(t.underlying)

      case TypeRef(_, sym, args) =>
        if(sym == ArrayClass) arrayOf(toTypeKind(args.head))
        else                  primitiveOrRefType2(sym)

      case ClassInfoType(_, _, sym) =>
        assert(sym != ArrayClass, "ClassInfoType to ArrayClass!")
        primitiveOrRefType(sym)

      // !!! Iulian says types which make no sense after erasure should not reach here, which includes the ExistentialType, AnnotatedType, RefinedType.
      // I don't know if the first two cases exist because they do or as a defensive measure, but at the time I added it, RefinedTypes were indeed reaching here.
      case _: ExistentialType => abort("ExistentialType reached GenBCode: " + t)
      case _: AnnotatedType   => abort("AnnotatedType reached GenBCode: "   + t)
      case _: RefinedType     => abort("RefinedType reached GenBCode: "     + t) // defensive: parents map toTypeKind reduceLeft lub

      // For sure WildcardTypes shouldn't reach here either, but when debugging such situations this may come in handy.
      // case WildcardType    => REFERENCE(ObjectClass)
      case norm => abort(
        "Unknown type: %s, %s [%s, %s] TypeRef? %s".format(
          t, norm, t.getClass, norm.getClass, t.isInstanceOf[TypeRef]
        )
      )
    }

  } // end of method toTypeKind()

  /** Subtype check `a <:< b` on asm.Types. It used to be called TypeKind.<:<() */
  final def conforms(a: asm.Type, b: asm.Type): Boolean = {
    if(isArrayType(a)) { // may be null
      /* Array subtyping is covariant here, as in Java. Necessary for checking code that interacts with Java. */
      if(isArrayType(b))            { conforms(componentType(a), componentType(b)) }
      else if(b == AnyRefReference) { true  }
      else                          { false }
    }
    else if(isBoxedType(a)) { // may be null
      if(isBoxedType(b))            { a == b }
      else if(b == AnyRefReference) { true  }
      else                          { false }
    }
    else if(isNullType(a)) { // known to be null
      if(isNothingType(b))          { false }
      else if(isValueType(b))       { false }
      else                          { true  }
    }
    else if(isNothingType(a)) { // known to be Nothing
      true
    }
    else if(isUnitType(a)) {
      isUnitType(b)
    }
    else if(isReferenceType(a)) { // may be null
      if(isNothingType(a))        { true  }
      else if(isReferenceType(b)) { ??? }
      else if(isArrayType(b))     { isNullType(a) }
      else                        { false }
    }
    else {

        def msg = "(a: " + a + ", b: " + b + ")"

      assert(isNonUnitValueType(a), "a is !isNonUnitValueType. " + msg)
      assert(isNonUnitValueType(b), "a is !isNonUnitValueType. " + msg)

      (a eq b) || (a match {
        case BOOL | BYTE | SHORT | CHAR => b == INT || b == LONG // TODO Actually, does BOOL conform to LONG ? Even with adapt() it's a type error, right?.
        case _                          => a == b
      })
    }
  }

  /** The maxValueType of (Char, Byte) and of (Char, Short) is Int, to encompass the negative values of Byte and Short. See ticket #2087. */
  private def maxValueType(a: asm.Type, other: asm.Type): asm.Type = {
    assert(isValueType(a), "maxValueType() is defined only for 1st arg valuetypes (2nd arg doesn't matter).")

        def uncomparable: Nothing = {
          abort("Uncomparable asm.Types: " + a.toString + " with " + other.toString)
        }

    if(isNothingType(a))     return other;
    if(isNothingType(other)) return a;
    if(a == other)           return a;

    a match {

      case UNIT => uncomparable
      case BOOL => uncomparable

      case BYTE =>
        if (other == CHAR)            INT
        else if(isNumericType(other)) other
        else                          uncomparable

      case SHORT =>
        other match {
          case BYTE                          => SHORT
          case CHAR                          => INT
          case INT  | LONG  | FLOAT | DOUBLE => other
          case _                             => uncomparable
        }

      case CHAR =>
        other match {
          case BYTE | SHORT                 => INT
          case INT  | LONG | FLOAT | DOUBLE => other
          case _                            => uncomparable
        }

      case INT =>
        other match {
          case BYTE | SHORT | CHAR   => INT
          case LONG | FLOAT | DOUBLE => other
          case _                     => uncomparable
        }

      case LONG =>
        if(isIntegralType(other))  LONG
        else if(isRealType(other)) DOUBLE
        else                       uncomparable

      case FLOAT =>
        if (other == DOUBLE)          DOUBLE
        else if(isNumericType(other)) FLOAT
        else                          uncomparable

      case DOUBLE =>
        if(isNumericType(other)) DOUBLE
        else                     uncomparable

      case _ => uncomparable
    }
  }

  /* Takes promotions of numeric primitives into account. */
  final def maxType(a: asm.Type, other: asm.Type): asm.Type = {
    if(isValueType(a)) { maxValueType(a, other) }
    else {
      if(isNothingType(a))     return other;
      if(isNothingType(other)) return a;
      if(a == other)           return a;
       // Approximate `lub`. The common type of two references is always AnyRef.
       // For 'real' least upper bound wrt to subclassing use method 'lub'.
      assert(isArrayType(a) || isBoxedType(a) || isReferenceType(a), "This is not a valuetype and it's not something else, what is it? " + a)
      // TODO For some reason, ICode thinks `REFERENCE(...).maxType(BOXED(whatever))` is `uncomparable`. Here, that has maxType AnyRefReference.
      //      BTW, when swapping arguments, ICode says BOXED(whatever).maxType(REFERENCE(...)) == AnyRefReference, so I guess the above was an oversight in REFERENCE.maxType()
      if(isRefOrArrayType(other)) { AnyRefReference }
      else                        { abort("Uncomparable asm.Types: " + a.toString + " with " + other.toString) }
    }
  }


  /** Just a namespace for utilities that encapsulate MethodVisitor idioms.
   *  In the ASM world, org.objectweb.asm.commons.InstructionAdapter plays a similar role,
   *  but the methods here allow choosing when to transition from ICode to ASM types
   *  (including not at all, e.g. for performance).
   */
  abstract class JCodeMethodN extends BCInnerClassGen {

    def jmethod: asm.MethodVisitor

    import asm.Opcodes;
    import icodes.opcodes.{ InvokeStyle, Static, Dynamic,  SuperCall }

    val StringBuilderClassName = definitions.StringBuilderClass.javaBinaryName.toString
    val StringBuilderType      = asm.Type.getObjectType(StringBuilderClassName)
    val mdesc_toString         = "()Ljava/lang/String;"

    @inline final def emit(opc: Int) { jmethod.visitInsn(opc) }

    final def genCallMethod(method:      Symbol, style: InvokeStyle,
                      jMethodName: String,
                      siteSymbol:  Symbol, hostSymbol: Symbol,
                      thisName:    String, isModuleInitialized0: Boolean): Boolean = {

      var isModuleInitialized = isModuleInitialized0
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
      val jowner   = javaName(receiver)
      val jname    = method.javaSimpleName.toString
      val jtype    = asmMethodType(method).getDescriptor()

          def dbg(invoke: String) {
            debuglog("%s %s %s.%s:%s".format(invoke, receiver.accessString, jowner, jname, jtype))
          }

          def initModule() {
            // we initialize the MODULE$ field immediately after the super ctor
            if (isStaticModule(siteSymbol) && !isModuleInitialized &&
                jMethodName == INSTANCE_CONSTRUCTOR_NAME &&
                jname == INSTANCE_CONSTRUCTOR_NAME) {
              isModuleInitialized = true
              jmethod.visitVarInsn(asm.Opcodes.ALOAD, 0)
              jmethod.visitFieldInsn(
                asm.Opcodes.PUTSTATIC,
                thisName,
                strMODULE_INSTANCE_FIELD,
                asm.Type.getObjectType(thisName).getDescriptor
              )
            }
          }

      style match {
        case Static(true)                         => dbg("invokespecial");  invokespecial  (jowner, jname, jtype)
        case Static(false)                        => dbg("invokestatic");   invokestatic   (jowner, jname, jtype)
        case Dynamic if isInterfaceCall(receiver) => dbg("invokinterface"); invokeinterface(jowner, jname, jtype)
        case Dynamic                              => dbg("invokevirtual");  invokevirtual  (jowner, jname, jtype)
        case SuperCall(_)                         =>
          dbg("invokespecial")
          invokespecial(jowner, jname, jtype)
          initModule()
      }

      isModuleInitialized

    } // end of genCallMethod

    final def genPrimitiveNegation(kind: asm.Type) {
      neg(kind)
    }
    final def genPrimitiveArithmetic(op: icodes.ArithmeticOp, kind: asm.Type) {

      import icodes.{ ADD, SUB, MUL, DIV, REM, NOT }

      op match {

        case ADD => add(kind)
        case SUB => sub(kind)
        case MUL => mul(kind)
        case DIV => div(kind)
        case REM => rem(kind)

        case NOT =>
          if(isIntSizedType(kind)) {
            emit(Opcodes.ICONST_M1)
            emit(Opcodes.IXOR)
          } else if(kind == LONG) {
            jmethod.visitLdcInsn(new java.lang.Long(-1))
            jmethod.visitInsn(Opcodes.LXOR)
          } else {
            abort("Impossible to negate an " + kind)
          }

        case _ =>
          abort("Unknown arithmetic primitive " + op)
      }

    } // end of method genPrimitiveArithmetic()

    final def genPrimitiveLogical(op: icodes.LogicalOp, kind: asm.Type) {

      import icodes.{ AND, OR, XOR }

      ((op, kind): @unchecked) match {
        case (AND, LONG) => emit(Opcodes.LAND)
        case (AND, INT)  => emit(Opcodes.IAND)
        case (AND, _)    =>
          emit(Opcodes.IAND)
          if (kind != BOOL) { emitT2T(INT, kind) }

        case (OR, LONG) => emit(Opcodes.LOR)
        case (OR, INT)  => emit(Opcodes.IOR)
        case (OR, _) =>
          emit(Opcodes.IOR)
          if (kind != BOOL) { emitT2T(INT, kind) }

        case (XOR, LONG) => emit(Opcodes.LXOR)
        case (XOR, INT)  => emit(Opcodes.IXOR)
        case (XOR, _) =>
          emit(Opcodes.IXOR)
          if (kind != BOOL) { emitT2T(INT, kind) }
      }

    } // end of method genPrimitiveLogical()

    final def genPrimitiveShift(op: icodes.ShiftOp, kind: asm.Type) {

      import icodes.{ LSL, ASR, LSR }

      ((op, kind): @unchecked) match {
        case (LSL, LONG) => emit(Opcodes.LSHL)
        case (LSL, INT)  => emit(Opcodes.ISHL)
        case (LSL, _) =>
          emit(Opcodes.ISHL)
          emitT2T(INT, kind)

        case (ASR, LONG) => emit(Opcodes.LSHR)
        case (ASR, INT)  => emit(Opcodes.ISHR)
        case (ASR, _) =>
          emit(Opcodes.ISHR)
          emitT2T(INT, kind)

        case (LSR, LONG) => emit(Opcodes.LUSHR)
        case (LSR, INT)  => emit(Opcodes.IUSHR)
        case (LSR, _) =>
          emit(Opcodes.IUSHR)
          emitT2T(INT, kind)
      }

    } // end of method genPrimitiveShift()

    final def genPrimitiveComparison(op: icodes.ComparisonOp, kind: asm.Type) {

      import icodes.{ CMPL, CMP, CMPG }

      ((op, kind): @unchecked) match {
        case (CMP,  LONG)   => emit(Opcodes.LCMP)
        case (CMPL, FLOAT)  => emit(Opcodes.FCMPL)
        case (CMPG, FLOAT)  => emit(Opcodes.FCMPG)
        case (CMPL, DOUBLE) => emit(Opcodes.DCMPL)
        case (CMPG, DOUBLE) => emit(Opcodes.DCMPL) // http://docs.oracle.com/javase/specs/jvms/se5.0/html/Instructions2.doc3.html
      }

    } // end of method genPrimitiveComparison()

    final def genPrimitiveConversion(src: asm.Type, dst: asm.Type, pos: Position) {
      if (dst == BOOL) { println("Illegal conversion at: " + pos.source + ":" + pos.line) }
      else { emitT2T(src, dst) }
    }

    final def genStartConcat {
      jmethod.visitTypeInsn(Opcodes.NEW, StringBuilderClassName)
      jmethod.visitInsn(Opcodes.DUP)
      invokespecial(
        StringBuilderClassName,
        INSTANCE_CONSTRUCTOR_NAME,
        mdesc_arglessvoid
      )
    }

    final def genStringConcat(el: asm.Type) {
      val jtype =
        if(isArrayType(el) || isNonBoxedReferenceType(el)) JAVA_LANG_OBJECT
        else el;

      invokevirtual(
        StringBuilderClassName,
        "append",
        asm.Type.getMethodDescriptor(StringBuilderType, Array(jtype): _*)
      )
    }

    final def genEndConcat {
      invokevirtual(StringBuilderClassName, "toString", mdesc_toString)
    }

    /**
     * Emits one or more conversion instructions based on the types given as arguments.
     *
     * @param from The type of the value to be converted into another type.
     * @param to   The type the value will be converted into.
     */
    final def emitT2T(from: asm.Type, to: asm.Type) {

          def msg = "(from: " + from + ", to: " + to + ")"

      assert(isNonUnitValueType(from), "from is !isNonUnitValueType. " + msg)
      assert(isNonUnitValueType(to),   "to is !isNonUnitValueType. " + msg)

          def pickOne(opcs: Array[Int]) { // TODO index on to.getSort
            val chosen = (to: @unchecked) match {
              case BYTE   => opcs(0)
              case SHORT  => opcs(1)
              case CHAR   => opcs(2)
              case INT    => opcs(3)
              case LONG   => opcs(4)
              case FLOAT  => opcs(5)
              case DOUBLE => opcs(6)
            }
            if(chosen != -1) { emit(chosen) }
          }

      if(from == to) { return }
      if((from == BOOL) || (to == BOOL)) {
        // the only conversion involving BOOL that is allowed is (BOOL -> BOOL)
        throw new Error("inconvertible types : " + from.toString() + " -> " + to.toString())
      }

      if(isIntSizedType(from)) { // BYTE, CHAR, SHORT, and INT. (we're done with BOOL already)

        val fromByte  = { import asm.Opcodes._; Array( -1,  -1, I2C,  -1, I2L, I2F, I2D) } // do nothing for (BYTE -> SHORT) and for (BYTE -> INT)
        val fromChar  = { import asm.Opcodes._; Array(I2B, I2S,  -1,  -1, I2L, I2F, I2D) } // for (CHAR  -> INT) do nothing
        val fromShort = { import asm.Opcodes._; Array(I2B,  -1, I2C,  -1, I2L, I2F, I2D) } // for (SHORT -> INT) do nothing
        val fromInt   = { import asm.Opcodes._; Array(I2B, I2S, I2C,  -1, I2L, I2F, I2D) }

        (from: @unchecked) match {
          case BYTE  => pickOne(fromByte)
          case SHORT => pickOne(fromShort)
          case CHAR  => pickOne(fromChar)
          case INT   => pickOne(fromInt)
        }

      } else { // FLOAT, LONG, DOUBLE

        (from: @unchecked) match {
          case FLOAT           =>
            import asm.Opcodes.{ F2L, F2D, F2I }
            (to: @unchecked) match {
              case LONG    => emit(F2L)
              case DOUBLE  => emit(F2D)
              case _       => emit(F2I); emitT2T(INT, to)
            }

          case LONG            =>
            import asm.Opcodes.{ L2F, L2D, L2I }
            (to: @unchecked) match {
              case FLOAT   => emit(L2F)
              case DOUBLE  => emit(L2D)
              case _       => emit(L2I); emitT2T(INT, to)
            }

          case DOUBLE          =>
            import asm.Opcodes.{ D2L, D2F, D2I }
            (to: @unchecked) match {
              case FLOAT   => emit(D2F)
              case LONG    => emit(D2L)
              case _       => emit(D2I); emitT2T(INT, to)
            }
        }
      }
    } // end of emitT2T()

    final def genConstant(const: Constant) {
      const.tag match {

        case BooleanTag => boolconst(const.booleanValue)

        case ByteTag    => iconst(const.byteValue)
        case ShortTag   => iconst(const.shortValue)
        case CharTag    => iconst(const.charValue)
        case IntTag     => iconst(const.intValue)

        case LongTag    => lconst(const.longValue)
        case FloatTag   => fconst(const.floatValue)
        case DoubleTag  => dconst(const.doubleValue)

        case UnitTag    => ()

        case StringTag  =>
          assert(const.value != null, const) // TODO this invariant isn't documented in `case class Constant`
          jmethod.visitLdcInsn(const.stringValue) // `stringValue` special-cases null, but not for a const with StringTag

        case NullTag    => emit(asm.Opcodes.ACONST_NULL)

        case ClazzTag   =>
          val kind = toTypeKind(const.typeValue)
          val toPush: asm.Type =
            if (isValueType(kind)) classLiteral(kind)
            else kind;
          jmethod.visitLdcInsn(toPush)

        case EnumTag   =>
          val sym = const.symbolValue
          jmethod.visitFieldInsn(
            asm.Opcodes.GETSTATIC,
            javaName(sym.owner),
            sym.javaSimpleName.toString,
            toTypeKind(sym.tpe.underlying).getDescriptor()
          )

        case _ => abort("Unknown constant value: " + const)
      }
    }

    final def aconst(cst: AnyRef) {
      if (cst == null) { emit(Opcodes.ACONST_NULL) }
      else             { jmethod.visitLdcInsn(cst) }
    }

    final def boolconst(b: Boolean) { iconst(if(b) 1 else 0) }

    final def iconst(cst: Int) {
      if (cst >= -1 && cst <= 5) {
        emit(Opcodes.ICONST_0 + cst)
      } else if (cst >= java.lang.Byte.MIN_VALUE && cst <= java.lang.Byte.MAX_VALUE) {
        jmethod.visitIntInsn(Opcodes.BIPUSH, cst)
      } else if (cst >= java.lang.Short.MIN_VALUE && cst <= java.lang.Short.MAX_VALUE) {
        jmethod.visitIntInsn(Opcodes.SIPUSH, cst)
      } else {
        jmethod.visitLdcInsn(new Integer(cst))
      }
    }

    final def lconst(cst: Long) {
      if (cst == 0L || cst == 1L) {
        emit(Opcodes.LCONST_0 + cst.asInstanceOf[Int])
      } else {
        jmethod.visitLdcInsn(new java.lang.Long(cst))
      }
    }

    final def fconst(cst: Float) {
      val bits: Int = java.lang.Float.floatToIntBits(cst)
      if (bits == 0L || bits == 0x3f800000 || bits == 0x40000000) { // 0..2
        emit(Opcodes.FCONST_0 + cst.asInstanceOf[Int])
      } else {
        jmethod.visitLdcInsn(new java.lang.Float(cst))
      }
    }

    final def dconst(cst: Double) {
      val bits: Long = java.lang.Double.doubleToLongBits(cst)
      if (bits == 0L || bits == 0x3ff0000000000000L) { // +0.0d and 1.0d
        emit(Opcodes.DCONST_0 + cst.asInstanceOf[Int])
      } else {
        jmethod.visitLdcInsn(new java.lang.Double(cst))
      }
    }

    final def newarray(elem: asm.Type) { // TODO switch on elem.getSort
      if(isRefOrArrayType(elem)) {
        jmethod.visitTypeInsn(Opcodes.ANEWARRAY, elem.getInternalName)
      } else {
        val rand = {
          if(isIntSizedType(elem)) {
            (elem: @unchecked) match {
              case BOOL   => Opcodes.T_BOOLEAN
              case BYTE   => Opcodes.T_BYTE
              case SHORT  => Opcodes.T_SHORT
              case CHAR   => Opcodes.T_CHAR
              case INT    => Opcodes.T_INT
            }
          } else {
            (elem: @unchecked) match {
              case LONG   => Opcodes.T_LONG
              case FLOAT  => Opcodes.T_FLOAT
              case DOUBLE => Opcodes.T_DOUBLE
            }
          }
        }
        jmethod.visitIntInsn(Opcodes.NEWARRAY, rand)
      }
    }


    final def load( idx: Int, tk: asm.Type) { emitVarInsn(Opcodes.ILOAD,  idx, tk) }
    final def store(idx: Int, tk: asm.Type) { emitVarInsn(Opcodes.ISTORE, idx, tk) }

    final def aload( tk: asm.Type) { emitTypeBased(aloadOpcodes,  tk) }
    final def astore(tk: asm.Type) { emitTypeBased(astoreOpcodes, tk) }

    final def neg(tk: asm.Type) { emitPrimitive(negOpcodes, tk) }
    final def add(tk: asm.Type) { emitPrimitive(addOpcodes, tk) }
    final def sub(tk: asm.Type) { emitPrimitive(subOpcodes, tk) }
    final def mul(tk: asm.Type) { emitPrimitive(mulOpcodes, tk) }
    final def div(tk: asm.Type) { emitPrimitive(divOpcodes, tk) }
    final def rem(tk: asm.Type) { emitPrimitive(remOpcodes, tk) }

    final def invokespecial(owner: String, name: String, desc: String) {
      jmethod.visitMethodInsn(Opcodes.INVOKESPECIAL, owner, name, desc)
    }
    final def invokestatic(owner: String, name: String, desc: String) {
      jmethod.visitMethodInsn(Opcodes.INVOKESTATIC, owner, name, desc)
    }
    final def invokeinterface(owner: String, name: String, desc: String) {
      jmethod.visitMethodInsn(Opcodes.INVOKEINTERFACE, owner, name, desc)
    }
    final def invokevirtual(owner: String, name: String, desc: String) {
      jmethod.visitMethodInsn(Opcodes.INVOKEVIRTUAL, owner, name, desc)
    }

    final def goTo(label: asm.Label) { jmethod.visitJumpInsn(Opcodes.GOTO, label) }
    final def emitIF(cond: icodes.TestOp, label: asm.Label)      { jmethod.visitJumpInsn(cond.opcodeIF,     label) }
    final def emitIF_ICMP(cond: icodes.TestOp, label: asm.Label) { jmethod.visitJumpInsn(cond.opcodeIFICMP, label) }
    final def emitIF_ACMP(cond: icodes.TestOp, label: asm.Label) {
      assert((cond == icodes.EQ) || (cond == icodes.NE), cond)
      val opc = (if(cond == icodes.EQ) Opcodes.IF_ACMPEQ else Opcodes.IF_ACMPNE)
      jmethod.visitJumpInsn(opc, label)
    }
    final def emitIFNONNULL(label: asm.Label) { jmethod.visitJumpInsn(Opcodes.IFNONNULL, label) }
    final def emitIFNULL   (label: asm.Label) { jmethod.visitJumpInsn(Opcodes.IFNULL,    label) }

    final def emitRETURN(tk: asm.Type) {
      if(tk == UNIT) { emit(Opcodes.RETURN) }
      else           { emitTypeBased(returnOpcodes, tk)      }
    }

    /** Emits one of tableswitch or lookoupswitch. */
    final def emitSWITCH(keys: Array[Int], branches: Array[asm.Label], defaultBranch: asm.Label, minDensity: Double) {
      assert(keys.length == branches.length)

      // For empty keys, it makes sense emitting LOOKUPSWITCH with defaultBranch only.
      // Similar to what javac emits for a switch statement consisting only of a default case.
      if (keys.length == 0) {
        jmethod.visitLookupSwitchInsn(defaultBranch, keys, branches)
        return
      }

      // sort `keys` by increasing key, keeping `branches` in sync. TODO FIXME use quicksort
      var i = 1
      while (i < keys.length) {
        var j = 1
        while (j <= keys.length - i) {
          if (keys(j) < keys(j - 1)) {
            val tmp     = keys(j)
            keys(j)     = keys(j - 1)
            keys(j - 1) = tmp
            val tmpL        = branches(j)
            branches(j)     = branches(j - 1)
            branches(j - 1) = tmpL
          }
          j += 1
        }
        i += 1
      }

      // check for duplicate keys to avoid "VerifyError: unsorted lookupswitch" (SI-6011)
      i = 1
      while (i < keys.length) {
        if(keys(i-1) == keys(i)) {
          abort("duplicate keys in SWITCH, can't pick arbitrarily one of them to evict, see SI-6011.")
        }
        i += 1
      }

      val keyMin = keys(0)
      val keyMax = keys(keys.length - 1)

      val isDenseEnough: Boolean = {
        /** Calculate in long to guard against overflow. TODO what overflow? */
        val keyRangeD: Double = (keyMax.asInstanceOf[Long] - keyMin + 1).asInstanceOf[Double]
        val klenD:     Double = keys.length
        val kdensity:  Double = (klenD / keyRangeD)

        kdensity >= minDensity
      }

      if (isDenseEnough) {
        // use a table in which holes are filled with defaultBranch.
        val keyRange    = (keyMax - keyMin + 1)
        val newBranches = new Array[asm.Label](keyRange)
        var oldPos = 0;
        var i = 0
        while(i < keyRange) {
          val key = keyMin + i;
          if (keys(oldPos) == key) {
            newBranches(i) = branches(oldPos)
            oldPos += 1
          } else {
            newBranches(i) = defaultBranch
          }
          i += 1
        }
        assert(oldPos == keys.length, "emitSWITCH")
        jmethod.visitTableSwitchInsn(keyMin, keyMax, defaultBranch, newBranches: _*)
      } else {
        jmethod.visitLookupSwitchInsn(defaultBranch, keys, branches)
      }
    }

    // internal helpers -- not part of the public API of `jcode`
    // don't make private otherwise inlining will suffer

    final def emitVarInsn(opc: Int, idx: Int, tk: asm.Type) {
      assert((opc == Opcodes.ILOAD) || (opc == Opcodes.ISTORE), opc)
      jmethod.visitVarInsn(tk.getOpcode(opc), idx)
    }

    // ---------------- array load and store ----------------

    val aloadOpcodes  = { import Opcodes._; Array(AALOAD,  BALOAD,  SALOAD,  CALOAD,  IALOAD,  LALOAD,  FALOAD,  DALOAD)  }
    val astoreOpcodes = { import Opcodes._; Array(AASTORE, BASTORE, SASTORE, CASTORE, IASTORE, LASTORE, FASTORE, DASTORE) }

    val returnOpcodes = { import Opcodes._; Array(ARETURN, IRETURN, IRETURN, IRETURN, IRETURN, LRETURN, FRETURN, DRETURN) }

    final def emitTypeBased(opcs: Array[Int], tk: asm.Type) { // TODO switch on tk.getSort
      assert(tk != UNIT, tk)
      val opc = {
        if(isRefOrArrayType(tk)) {  opcs(0) }
        else if(isIntSizedType(tk)) {
          (tk: @unchecked) match {
            case BOOL | BYTE     => opcs(1)
            case SHORT           => opcs(2)
            case CHAR            => opcs(3)
            case INT             => opcs(4)
          }
        } else {
          (tk: @unchecked) match {
            case LONG            => opcs(5)
            case FLOAT           => opcs(6)
            case DOUBLE          => opcs(7)
          }
        }
      }
      emit(opc)
    }

    // ---------------- primitive operations ----------------

    val negOpcodes: Array[Int] = { import Opcodes._; Array(INEG, LNEG, FNEG, DNEG) }
    val addOpcodes: Array[Int] = { import Opcodes._; Array(IADD, LADD, FADD, DADD) }
    val subOpcodes: Array[Int] = { import Opcodes._; Array(ISUB, LSUB, FSUB, DSUB) }
    val mulOpcodes: Array[Int] = { import Opcodes._; Array(IMUL, LMUL, FMUL, DMUL) }
    val divOpcodes: Array[Int] = { import Opcodes._; Array(IDIV, LDIV, FDIV, DDIV) }
    val remOpcodes: Array[Int] = { import Opcodes._; Array(IREM, LREM, FREM, DREM) }

    final def emitPrimitive(opcs: Array[Int], tk: asm.Type) { // TODO index on tk.getSort
      val opc = {
        if(isIntSizedType(tk)) { opcs(0) }
        else {
          (tk: @unchecked) match {
            case LONG   => opcs(1)
            case FLOAT  => opcs(2)
            case DOUBLE => opcs(3)
          }
        }
      }
      emit(opc)
    }

    final def drop(tk: asm.Type) { emit(if(isWideType(tk)) Opcodes.POP2 else Opcodes.POP) }

    final def dup(tk: asm.Type)  { emit(if(isWideType(tk)) Opcodes.DUP2 else Opcodes.DUP) }

    // ---------------- field load and store ----------------

    final def fieldLoad( field: Symbol, hostClass: Symbol = null) { // TODO GenASM could use this method
      fieldOp(field, isLoad = true,  hostClass)
    }
    final def fieldStore(field: Symbol, hostClass: Symbol = null) { // TODO GenASM could use this method
      fieldOp(field, isLoad = false, hostClass)
    }

    private def fieldOp(field: Symbol, isLoad: Boolean, hostClass: Symbol = null) {
      // LOAD_FIELD.hostClass , CALL_METHOD.hostClass , and #4283
      val owner      =
        if(hostClass == null) javaName(field.owner)
        else                  javaName(hostClass)
      val fieldJName = field.javaSimpleName.toString
      val fieldDescr = toTypeKind(field.tpe).getDescriptor
      val isStatic   = field.isStaticMember
      val opc =
        if(isLoad) { if (isStatic) Opcodes.GETSTATIC else Opcodes.GETFIELD }
        else       { if (isStatic) Opcodes.PUTSTATIC else Opcodes.PUTFIELD }
      jmethod.visitFieldInsn(opc, owner, fieldJName, fieldDescr)

    }

    // ---------------- type checks and casts ----------------

    final def isInstance(tk: asm.Type) {
      jmethod.visitTypeInsn(Opcodes.INSTANCEOF, tk.getInternalName)
    }

    final def checkCast(tk: asm.Type) { // TODO GenASM could use this method
      assert(isRefOrArrayType(tk), "checkcast on primitive type: " + tk)
      assert(!isBoxedType(tk),     "checkcast on boxed type: " + tk) // TODO this is backwards compatible with ICode, but is it correct?
      jmethod.visitTypeInsn(Opcodes.CHECKCAST, tk.getInternalName)
    }

  } // end of class JCodeMethodN

    // ---------------- adapted from scalaPrimitives ----------------

    /* Given `code` reports the src TypeKind of the coercion indicated by `code`.
     * To find the dst TypeKind, `ScalaPrimitives.generatedKind(code)` can be used. */
    final def coercionFrom(code: Int): asm.Type = {
      import scalaPrimitives._
      (code: @switch) match {
        case B2B | B2C | B2S | B2I | B2L | B2F | B2D => BYTE
        case S2B | S2S | S2C | S2I | S2L | S2F | S2D => SHORT
        case C2B | C2S | C2C | C2I | C2L | C2F | C2D => CHAR
        case I2B | I2S | I2C | I2I | I2L | I2F | I2D => INT
        case L2B | L2S | L2C | L2I | L2L | L2F | L2D => LONG
        case F2B | F2S | F2C | F2I | F2L | F2F | F2D => FLOAT
        case D2B | D2S | D2C | D2I | D2L | D2F | D2D => DOUBLE
      }
    }

    /** If code is a coercion primitive, the result type */
    final def coercionTo(code: Int): asm.Type = {
      import scalaPrimitives._
      (code: @scala.annotation.switch) match {
        case B2B | C2B | S2B | I2B | L2B | F2B | D2B => BYTE
        case B2C | C2C | S2C | I2C | L2C | F2C | D2C => CHAR
        case B2S | C2S | S2S | I2S | L2S | F2S | D2S => SHORT
        case B2I | C2I | S2I | I2I | L2I | F2I | D2I => INT
        case B2L | C2L | S2L | I2L | L2L | F2L | D2L => LONG
        case B2F | C2F | S2F | I2F | L2F | F2F | D2F => FLOAT
        case B2D | C2D | S2D | I2D | L2D | F2D | D2D => DOUBLE
      }
    }

    final val typeOfArrayOp: Map[Int, asm.Type] = {
      import scalaPrimitives._
      Map(
        (List(ZARRAY_LENGTH, ZARRAY_GET, ZARRAY_SET) map (_ -> BOOL)) ++
        (List(BARRAY_LENGTH, BARRAY_GET, BARRAY_SET) map (_ -> BYTE)) ++
        (List(SARRAY_LENGTH, SARRAY_GET, SARRAY_SET) map (_ -> SHORT)) ++
        (List(CARRAY_LENGTH, CARRAY_GET, CARRAY_SET) map (_ -> CHAR)) ++
        (List(IARRAY_LENGTH, IARRAY_GET, IARRAY_SET) map (_ -> INT)) ++
        (List(LARRAY_LENGTH, LARRAY_GET, LARRAY_SET) map (_ -> LONG)) ++
        (List(FARRAY_LENGTH, FARRAY_GET, FARRAY_SET) map (_ -> FLOAT)) ++
        (List(DARRAY_LENGTH, DARRAY_GET, DARRAY_SET) map (_ -> DOUBLE)) ++
        (List(OARRAY_LENGTH, OARRAY_GET, OARRAY_SET) map (_ -> ObjectReference)) : _*
      )
    }

}
