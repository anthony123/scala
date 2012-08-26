/* NSC -- new Scala compiler
 * Copyright 2005-2012 LAMP/EPFL
 * @author  Martin Odersky
 */

package scala.tools.nsc
package backend.jvm

import scala.tools.asm
import scala.annotation.switch
import scala.collection.{ immutable, mutable }

/**
 *  Utilities to mediate between types as represented in Scala ASTs and ASM trees.
 *
 *  @author  Miguel Garcia, http://lamp.epfl.ch/~magarcia/ScalaCompilerCornerReloaded
 *
 */
abstract class BCodeTypes extends SubComponent with BytecodeWriters {

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
  val RT_NOTHING = asm.Type.getObjectType("scala/runtime/Nothing$")
  val RT_NULL    = asm.Type.getObjectType("scala/runtime/Null$")
  val CT_NOTHING = asm.Type.getObjectType("scala/Nothing") // TODO needed?
  val CT_NULL    = asm.Type.getObjectType("scala/Null")    // TODO needed?

  val ObjectReference = asm.Type.getObjectType("java/lang/Object")
  val AnyRefReference = ObjectReference // In tandem, javaNameASM(definitions.AnyRefClass) == ObjectReference. Otherwise every `t1 == t2` requires special-casing.
  // special names
  val StringReference          = asm.Type.getObjectType("java/lang/String")
  val ThrowableReference       = asm.Type.getObjectType("java/lang/Throwable")
  val jlCloneableReference     = asm.Type.getObjectType("java/lang/Cloneable")
  val jioSerializableReference = asm.Type.getObjectType("java/io/Serializable")

  // TODO rather than lazy, have an init() method that populates mutable collections. That would speed up accesses from then on.

  /** A map from scala primitive type-symbols to asm.Types */
  var primitiveTypeMap: Map[Symbol, asm.Type] = null

  var phantomTypeMap:   Map[Symbol, asm.Type] = null

  /** Maps the method symbol for a box method to the boxed type of the result.
   *  For example, the method symbol for `Byte.box()`) is mapped to the asm.Type `Ljava/lang/Integer;`. */
  var boxResultType:    Map[Symbol, asm.Type] = null
  /** Maps the method symbol for an unbox method to the primitive type of the result.
   *  For example, the method symbol for `Byte.unbox()`) is mapped to the asm.Type BYTE. */
  var unboxResultType:  Map[Symbol, asm.Type] = null

  def initBCodeTypes() {

    import definitions._

    primitiveTypeMap =
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

    phantomTypeMap =
      Map(
        NothingClass -> RT_NOTHING,
        NullClass    -> RT_NULL,
        NothingClass -> RT_NOTHING, // we map on purpose to RT_NOTHING, getting rid of the distinction compile-time vs. runtime for NullClass.
        NullClass    -> RT_NULL     // ditto.
      )

    boxResultType =
      for(Pair(csym, msym) <- definitions.boxMethod)
      yield (msym -> classLiteral(primitiveTypeMap(csym)))

    unboxResultType =
      for(Pair(csym, msym) <- definitions.unboxMethod)
      yield (msym -> primitiveTypeMap(csym))

    // boxed classes are looked up in the `exemplars` map by jvmWiseLUB().
    // Other than that, they aren't needed there (e.g., `isSubtypeOf()` special-cases boxed classes, similarly for others).
    val boxedClasses = List(BoxedBooleanClass, BoxedCharacterClass, BoxedByteClass, BoxedShortClass, BoxedIntClass, BoxedLongClass, BoxedFloatClass, BoxedDoubleClass)
    for(csym <- boxedClasses) {
      val key = asm.Type.getObjectType(csym.javaBinaryName.toString)
      val tr  = buildExemplar(key, csym)
      exemplars.put(tr.c, tr)
    }

    // reversePrimitiveMap = (primitiveTypeMap map { case (s, pt) => (s.tpe, pt) } map (_.swap)).toMap

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

  /** Map from type kinds to the Java reference types.
   *  It is used to push class literals onto the operand stack.
   *  @see Predef.classOf
   *  @see genConstant()
   */
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

  case class MethodNameAndType(mname: String, mdesc: String)

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

  final def hasInternalName(sym: Symbol) = { sym.isClass || (sym.isModule && !sym.isMethod) }

   // ------------------------------------------------
   // accessory maps tracking the isInterface, innerClasses, superClass, and supportedInterfaces relations,
   // allowing answering `conforms()` resorting to typer.
   // ------------------------------------------------

  val exemplars = mutable.Map.empty[asm.Type, Tracked]

  case class Tracked(c: asm.Type, flags: Int, sc: Tracked, ifaces: Array[Tracked]) {

    assert(
      !isSpecialType(c) &&
      ( if(sc == null) { (c == ObjectReference) || isInterface     }
        else           { (c != ObjectReference) && !sc.isInterface }
      ) &&
      (ifaces.forall(i => !isSpecialType(i.c) && i.isInterface)),
      "non well-formed plain-type: " + this
    )

    import asm.Opcodes._
    def hasFlags(mask: Int) = (flags & mask) != 0
    def isPrivate    = hasFlags(ACC_PRIVATE)
    def isPublic     = hasFlags(ACC_PUBLIC)
    def isAbstract   = hasFlags(ACC_ABSTRACT)
    def isInterface  = hasFlags(ACC_INTERFACE)
    def isFinal      = hasFlags(ACC_FINAL)
    def isSynthetic  = hasFlags(ACC_SYNTHETIC)
    def isSuper      = hasFlags(ACC_SUPER)
    def isDeprecated = hasFlags(ACC_DEPRECATED)

    def superClasses: List[Tracked] = {
      if(sc == null) Nil else sc :: sc.superClasses
    }

    def isSubtypeOf(other: asm.Type): Boolean = {
      assert(!isSpecialType(other), "so called special cases have to be handled in BCodeTypes.conforms()")

      if(c == other) return true;

      val otherIsIface = exemplars(other).isInterface

      if(this.isInterface) {
        if(other == ObjectReference) return true;
        if(!otherIsIface) return false;
      }
      else {
        if(sc != null && sc.isSubtypeOf(other)) return true;
        if(!otherIsIface) return false;
      }

      var idx = 0
      while(idx < ifaces.length) {
        if(ifaces(idx).isSubtypeOf(other)) return true;
        idx += 1
      }

      false

    }

  }

  def isDeprecated(sym: Symbol): Boolean = { sym.annotations exists (_ matches definitions.DeprecatedAttr) }

  private def getSuperInterfaces(csym: Symbol): List[Symbol] = {

      // Additional interface parents based on annotations and other cues
      def newParentForAttr(attr: Symbol): Option[Symbol] = attr match {
        case definitions.SerializableAttr => Some(definitions.SerializableClass)
        case definitions.CloneableAttr    => Some(definitions.CloneableClass)
        case definitions.RemoteAttr       => Some(definitions.RemoteInterfaceClass)
        case _ => None
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

    val superInterfaces0: List[Symbol] = csym.mixinClasses
    val superInterfaces:  List[Symbol] = superInterfaces0 ++ csym.annotations.flatMap(ann => newParentForAttr(ann.symbol)) distinct;

    assert(!superInterfaces.contains(NoSymbol), "found NoSymbol among: " + superInterfaces.mkString)
    assert(superInterfaces.forall(s => s.isInterface || s.isTrait), "found non-interface among: " + superInterfaces.mkString)

    minimizeInterfaces(superInterfaces)
  }

  /**
   * Records in accessory maps the superClass and supportedInterfaces relations,
   * so that afterwards queries can be answered without resorting to typer.
   * This method does not add to `innerClassesBuffer`, use `asmType()` or `toTypeKind()` for that.
   */
  final def exemplar(csym0: Symbol): Tracked = {
    assert(csym0 != NoSymbol, "NoSymbol can't be tracked")

        def trackedSymbol(sym: Symbol): Symbol = {
          if(sym.isJavaDefined && sym.isModuleClass) sym.linkedClassOfClass
          else if(sym.isModule) sym.moduleClass
          else sym // we track only module-classes and plain-classes
        }

    val csym = trackedSymbol(csym0)
    if(csym0 != csym) {
      // Console.println("[BCodeTypes.exemplar()] Tracking different symbol. \n\tWas: " + csym0.fullName.toString + "\n\tNow: " + csym.fullName.toString)
    }
    assert(!primitiveTypeMap.contains(csym), "primitive types not tracked here: " + csym.fullName)
    assert(!phantomTypeMap.contains(csym),   "phantom types not tracked here: " + csym.fullName)

    val key = asm.Type.getObjectType(csym.javaBinaryName.toString)
    assert(!isSpecialType(key), "Not a class to track: " + csym.fullName)

    exemplars.get(key) match {
      case Some(tr) => tr
      case _ =>
        val tr = buildExemplar(key, csym)
        exemplars.put(tr.c, tr) // tr.c is the hash-consed, internalized, canonical representative for csym's key.
        tr
    }
  }

  private val EMPTY_TRACKED_ARRAY  = Array.empty[Tracked]

  private def buildExemplar(key: asm.Type, csym: Symbol): Tracked = {
    val sc =
     if(csym.isImplClass) definitions.ObjectClass
     else csym.superClass
    assert(
      if(csym == definitions.ObjectClass)
        sc == NoSymbol
      else if(csym.isInterface)
        sc == definitions.ObjectClass
      else
        (sc != NoSymbol) && !sc.isInterface,
      "superClass out of order"
    )
    val ifaces    = getSuperInterfaces(csym) map exemplar;
    val ifacesArr =
     if(ifaces.isEmpty) EMPTY_TRACKED_ARRAY
     else {
      val arr = new Array[Tracked](ifaces.size)
      ifaces.copyToArray(arr)
      arr
     }

    val flags = mkFlags(
      javaFlags(csym),
      if(isDeprecated(csym)) asm.Opcodes.ACC_DEPRECATED else 0 // ASM pseudo access flag
    )

    val tsc = if(sc == NoSymbol) null else exemplar(sc)
    Tracked(key, flags, tsc, ifacesArr)
  }

  // ---------------- inspector methods on asm.Type  ----------------

  /*
   * Unlike for ICode's REFERENCE, isBoxedType(t) implies isReferenceType(t)
   * Also, `isReferenceType(RT_NOTHING) == true` , similarly for RT_NULL.
   * Use isNullType() , isNothingType() to detect Nothing and Null.
   */
  final def hasObjectSort(t: asm.Type) = (t.getSort == asm.Type.OBJECT)

  final def isNonBoxedReferenceType(t: asm.Type) = hasObjectSort(t) && !isBoxedType(t)

  final def isSpecialType(t: asm.Type): Boolean = {
    isValueType(t)   ||
    isArrayType(t)   ||
    isPhantomType(t)
  }

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

  final def isRefOrArrayType(t: asm.Type) = hasObjectSort(t) || isArrayType(t)

  final def isNothingType(t: asm.Type) = { (t == RT_NOTHING) || (t == CT_NOTHING) }
  final def isNullType   (t: asm.Type) = { (t == RT_NULL)    || (t == CT_NULL)    }
  final def isPhantomType(t: asm.Type) = { isNothingType(t)  || isNullType(t)     }
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

  final def isNumericType(t: asm.Type) = isIntegralType(t) || isRealType(t)

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
    assert(!isUnitType(elem) && !isPhantomType(elem),
           "The element type of an array type is necessarily either a primitive type, or a class type, or an interface type.")
    asm.Type.getObjectType("[" + elem.getDescriptor)
  }

  /* the type of N-dimensional arrays of `elem` type. */
  final def arrayN(elem: asm.Type, dims: Int): asm.Type = {
    assert(dims > 0)
    assert(!isUnitType(elem) && !isPhantomType(elem),
           "The element type of an array type is necessarily either a primitive type, or a class type, or an interface type.")
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
              return asmClassType(traitSym)
          }

          assert(hasInternalName(sym), "Invoked for a symbol lacking JVM internal name: " + sym.fullName)
          assert(!phantomTypeMap.contains(sym), "phantom types not supposed to reach here.")

          bufferIfInner(sym)

          exemplar(sym).c

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
        else                  phantomTypeMap.getOrElse(sym, exemplar(sym).c)

      case SingleType(_, sym) => primitiveOrRefType(sym)

      case _: ConstantType    => toTypeKind(t.underlying)

      case TypeRef(_, sym, args)    =>
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

  /**
   * Subtype check `a <:< b` on asm.Types that takes into account the JVM built-in numeric promotions (e.g. BYTE to INT).
   * Its operation can be visualized more easily in terms of the Java bytecode type hierarchy.
   * This method used to be called, in the ICode world, TypeKind.<:<()
   **/
  final def conforms(a: asm.Type, b: asm.Type): Boolean = {
    if(isArrayType(a)) { // may be null
      /* Array subtyping is covariant here, as in Java bytecode. Also necessary for Java interop. */
      if((b == jlCloneableReference)     ||
         (b == jioSerializableReference) ||
         (b == AnyRefReference))    { true  }
      else if(isArrayType(b))       { conforms(componentType(a), componentType(b)) }
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
    else if(hasObjectSort(a)) { // may be null
      if(isNothingType(a))        { true  }
      else if(hasObjectSort(b))   { exemplars(a).isSubtypeOf(b) }
      else if(isArrayType(b))     { isNullType(a) }
      else                        { false }
    }
    else {

        def msg = "(a: " + a + ", b: " + b + ")"

      assert(isNonUnitValueType(a), "a isn't a non-Unit value type. " + msg)
      assert(isValueType(b), "b isn't a value type. " + msg)

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
      assert(isArrayType(a) || isBoxedType(a) || hasObjectSort(a), "This is not a valuetype and it's not something else, what is it? " + a)
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
      val jowner   = internalName(receiver)
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

    final def genPrimitiveLogical(op: /* LogicalOp */ Int, kind: asm.Type) {

      import scalaPrimitives.{ AND, OR, XOR }

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

    final def genPrimitiveShift(op: /* ShiftOp */ Int, kind: asm.Type) {

      import scalaPrimitives.{ LSL, ASR, LSR }

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
      (const.tag: @switch) match {

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
            internalName(sym.owner),
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
        if(hostClass == null) internalName(field.owner)
        else                  internalName(hostClass)
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
      // TODO ICode also requires: but that's too much, right? assert(!isBoxedType(tk),     "checkcast on boxed type: " + tk)
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
      (List(ZARRAY_LENGTH, ZARRAY_GET, ZARRAY_SET) map (_ -> BOOL))   ++
      (List(BARRAY_LENGTH, BARRAY_GET, BARRAY_SET) map (_ -> BYTE))   ++
      (List(SARRAY_LENGTH, SARRAY_GET, SARRAY_SET) map (_ -> SHORT))  ++
      (List(CARRAY_LENGTH, CARRAY_GET, CARRAY_SET) map (_ -> CHAR))   ++
      (List(IARRAY_LENGTH, IARRAY_GET, IARRAY_SET) map (_ -> INT))    ++
      (List(LARRAY_LENGTH, LARRAY_GET, LARRAY_SET) map (_ -> LONG))   ++
      (List(FARRAY_LENGTH, FARRAY_GET, FARRAY_SET) map (_ -> FLOAT))  ++
      (List(DARRAY_LENGTH, DARRAY_GET, DARRAY_SET) map (_ -> DOUBLE)) ++
      (List(OARRAY_LENGTH, OARRAY_GET, OARRAY_SET) map (_ -> ObjectReference)) : _*
    )
  }

  val INNER_CLASSES_FLAGS =
    (asm.Opcodes.ACC_PUBLIC | asm.Opcodes.ACC_PRIVATE   | asm.Opcodes.ACC_PROTECTED |
     asm.Opcodes.ACC_STATIC | asm.Opcodes.ACC_INTERFACE | asm.Opcodes.ACC_ABSTRACT)

  // ---------------- InnerClasses attribute (JVMS 4.7.6) ----------------

  /**
   *
   * Checks if given symbol corresponds to inner class/object.
   *   If so, add it to the result, along with all other inner classes over the owner-chain for that symbol
   *   Otherwise returns Nil.
   *
   * This method also adds as member classes those inner classes that have been declared, but otherwise not referred in instructions.
   *
   * TODO the invoker is responsible to sort them so inner classes succeed their enclosing class to satisfy the Eclipse Java compiler
   * TODO the invoker is responsible to add member classes not referred in instructions.
   * TODO remove duplicate entries.
   *
   * TODO: some beforeFlatten { ... } which accounts for being nested in parameterized classes (if we're going to selectively flatten.)
   *
   * TODO assert (JVMS 4.7.6 The InnerClasses attribute)
   * If a class file has a version number that is greater than or equal to 51.0, and has an InnerClasses attribute in its attributes table,
   * then for all entries in the classes array of the InnerClasses attribute,
   * the value of the outer_class_info_index item must be zero if the value of the inner_name_index item is zero.
   */

  case class InnerClassEntry(name: Name, outerName: Name, innerName: String, access: Int) {
    assert(name != null, "Null isn't good as class name in an InnerClassEntry.")
  }

  /** For given symbol return a symbol corresponding to a class that should be declared as inner class.
   *
   *  For example:
   *  class A {
   *    class B
   *    object C
   *  }
   *
   *  then method will return:
   *    NoSymbol for A,
   *    the same symbol for A.B (corresponding to A$B class), and
   *    A$C$ symbol for A.C.
   */
  private def innerClassSymbolFor(s: Symbol): Symbol =
    if (s.isClass) s else if (s.isModule) s.moduleClass else NoSymbol

  private val EMPTY_INNERCLASSENTRY_ARRAY = Array.empty[InnerClassEntry]

  private val innerChainsMap = mutable.Map.empty[/* class */ Symbol, Array[InnerClassEntry]]

  final def innerClassesChain(csym: Symbol): Array[InnerClassEntry] = {
    val ics = innerClassSymbolFor(csym)
    if(ics == NoSymbol) return EMPTY_INNERCLASSENTRY_ARRAY

        def buildInnerClassesChain: Array[InnerClassEntry] = {
          var chain: List[Symbol] = Nil

          var x = ics
          while(x ne NoSymbol) {
            assert(x.isClass, "not an inner-class symbol")
            val isInner = !x.rawowner.isPackageClass
            if (isInner) {
              chain ::= x
              x = innerClassSymbolFor(x.rawowner)
            } else {
              x = NoSymbol
            }
          }

          if(chain.isEmpty) EMPTY_INNERCLASSENTRY_ARRAY
          else {
            val arr = new Array[InnerClassEntry](chain.size)
            (chain map toInnerClassEntry).copyToArray(arr)
            arr
          }
        }

    innerChainsMap.getOrElseUpdate(ics, buildInnerClassesChain)
  }

  private def toInnerClassEntry(innerSym: Symbol): InnerClassEntry = {

        /** The outer name for this inner class. Note that it returns null
         *  when the inner class should not get an index in the constant pool.
         *  That means non-member classes (anonymous). See Section 4.7.5 in the JVMS.
         */
        def outerName(innerSym: Symbol): Name = {
          if (innerSym.originalEnclosingMethod != NoSymbol)
            null
          else {
            val outerName = innerSym.rawowner.javaBinaryName
            if (isTopLevelModule(innerSym.rawowner)) nme.stripModuleSuffix(outerName)
            else outerName
          }
        }

        def innerName(innerSym: Symbol): String = {
          if (innerSym.isAnonymousClass || innerSym.isAnonymousFunction)
            null
          else
            innerSym.rawname + innerSym.moduleSuffix
        }

    val access = mkFlags(
      if (innerSym.rawowner.hasModuleFlag) asm.Opcodes.ACC_STATIC else 0,
      javaFlags(innerSym),
      if(isDeprecated(innerSym)) asm.Opcodes.ACC_DEPRECATED else 0 // ASM pseudo-access flag
    ) & (INNER_CLASSES_FLAGS | asm.Opcodes.ACC_DEPRECATED)

    val jname = innerSym.javaBinaryName // never null
    val oname = outerName(innerSym)     // null when method-enclosed
    val iname = innerName(innerSym)     // null for anonymous inner class

    InnerClassEntry(jname, oname, iname, access)
  }

  val innerClassBufferASM = mutable.LinkedHashSet[Symbol]()

  final def javaSimpleName(sym: Symbol): String = { sym.javaSimpleName.toString }

  final def internalName(sym: Symbol): String = { asmClassType(sym).getInternalName }

  final def asmClassType(sym: Symbol): asm.Type = {
    assert(hasInternalName(sym), "doesn't have internal name: " + sym.fullName)
    bufferIfInner(sym)
    phantomTypeMap.getOrElse(sym, exemplar(sym).c)
  }

  def bufferIfInner(sym: Symbol) {
    val ics = innerClassSymbolFor(sym)
    if(ics != NoSymbol) {
      innerClassBufferASM += ics
    }
  }

  def addInnerClassesASM(csym: Symbol, jclass: asm.ClassVisitor) {
    // used to detect duplicates.
    val seen = mutable.Map.empty[Name, Name]
    // result without duplicates, not yet sorted.
    val result = mutable.Set.empty[InnerClassEntry]

    // add inner classes which might not have been referenced yet TODO this should be done in genPlainClass()
    afterErasure {
      for (sym <- List(csym, csym.linkedClassOfClass); memberc <- sym.info.decls.map(innerClassSymbolFor) if memberc.isClass) {
        innerClassBufferASM += memberc
      }
    }

    for(s <- innerClassBufferASM; e <- innerClassesChain(s)) {

      assert(e.name != null, "javaName is broken.") // documentation
      val doAdd = seen.get(e.name) match {
        // TODO is it ok for prevOName to be null? (Someone should really document the invariants of the InnerClasses bytecode attribute)
        case Some(prevOName) =>
          // this occurs e.g. when innerClassBuffer contains both class Thread$State, object Thread$State,
          // i.e. for them it must be the case that oname == java/lang/Thread
          assert(prevOName == e.outerName, "duplicate")
          false
        case None => true
      }

      if(doAdd) {
        seen   += (e.name -> e.outerName)
        result += e
      }

    }
    // sort them so inner classes succeed their enclosing class to satisfy the Eclipse Java compiler
    for(e <- result.toList sortBy (_.name.length)) {
      jclass.visitInnerClass(
        e.name.toString,
        if(e.outerName != null) e.outerName.toString else null,
        e.innerName,
        e.access)
    }

  }

  // what follows used to live in BCodeUtils

  var pickledBytes = 0 // statistics

  def mkFlags(args: Int*) = args.foldLeft(0)(_ | _)

  @inline final def hasPublicBitSet(flags: Int) = ((flags & asm.Opcodes.ACC_PUBLIC) != 0)

  @inline final def isRemote(s: Symbol) = (s hasAnnotation definitions.RemoteAttr)

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

    // Final: the only fields which can receive ACC_FINAL are eager vals.
    // Neither vars nor lazy vals can, because:
    //
    // Source: http://docs.oracle.com/javase/specs/jls/se7/html/jls-17.html#jls-17.5.3
    // "Another problem is that the specification allows aggressive
    // optimization of final fields. Within a thread, it is permissible to
    // reorder reads of a final field with those modifications of a final
    // field that do not take place in the constructor."
    //
    // A var or lazy val which is marked final still has meaning to the
    // scala compiler. The word final is heavily overloaded unfortunately;
    // for us it means "not overridable". At present you can't override
    // vars regardless; this may change.
    //
    // The logic does not check .isFinal (which checks flags for the FINAL flag,
    // and includes symbols marked lateFINAL) instead inspecting rawflags so
    // we can exclude lateFINAL. Such symbols are eligible for inlining, but to
    // avoid breaking proxy software which depends on subclassing, we do not
    // emit ACC_FINAL.
    // Nested objects won't receive ACC_FINAL in order to allow for their overriding.

    val finalFlag = (
         (((sym.rawflags & symtab.Flags.FINAL) != 0) || isTopLevelModule(sym))
      && !sym.enclClass.isInterface
      && !sym.isClassConstructor
      && !sym.isMutable // lazy vals and vars both
    )

    // Primitives are "abstract final" to prohibit instantiation
    // without having to provide any implementations, but that is an
    // illegal combination of modifiers at the bytecode level so
    // suppress final if abstract if present.
    import asm.Opcodes._
    mkFlags(
      if (privateFlag) ACC_PRIVATE else ACC_PUBLIC,
      if (sym.isDeferred || sym.hasAbstractFlag) ACC_ABSTRACT else 0,
      if (sym.isInterface) ACC_INTERFACE else 0,
      if (finalFlag && !sym.hasAbstractFlag) ACC_FINAL else 0,
      if (sym.isStaticMember) ACC_STATIC else 0,
      if (sym.isBridge) ACC_BRIDGE | ACC_SYNTHETIC else 0,
      if (sym.isArtifact) ACC_SYNTHETIC else 0,
      if (sym.isClass && !sym.isInterface) ACC_SUPER else 0,
      if (sym.isVarargsMethod) ACC_VARARGS else 0,
      if (sym.hasFlag(symtab.Flags.SYNCHRONIZED)) ACC_SYNCHRONIZED else 0
    )
  }

  def javaFieldFlags(sym: Symbol) = {
    javaFlags(sym) | mkFlags(
      if (sym hasAnnotation definitions.TransientAttr) asm.Opcodes.ACC_TRANSIENT else 0,
      if (sym hasAnnotation definitions.VolatileAttr)  asm.Opcodes.ACC_VOLATILE  else 0,
      if (sym.isMutable) 0 else asm.Opcodes.ACC_FINAL
    )
  }

  def isTopLevelModule(sym: Symbol): Boolean =
    afterPickler { sym.isModuleClass && !sym.isImplClass && !sym.isNestedClass }

  def isStaticModule(sym: Symbol): Boolean = {
    sym.isModuleClass && !sym.isImplClass && !sym.isLifted
  }

  // -----------------------------------------------------------------------------------------
  // finding the least upper bound in agreement with the bytecode verifier (given two internal names handed by ASM)
  // Background:
  //  http://gallium.inria.fr/~xleroy/publi/bytecode-verification-JAR.pdf
  //  http://comments.gmane.org/gmane.comp.java.vm.languages/2293
  //  https://issues.scala-lang.org/browse/SI-3872
  // -----------------------------------------------------------------------------------------

  def firstCommonSuffix(as: List[Tracked], bs: List[Tracked]): asm.Type = {
    var chainA = as
    var chainB = bs
    var fcs: Tracked = null
    do {
      if      (chainB contains chainA.head) fcs = chainA.head
      else if (chainA contains chainB.head) fcs = chainB.head
      else {
        chainA = chainA.tail
        chainB = chainB.tail
      }
    } while(fcs == null)
    fcs.c
  }

  @inline final def jvmWiseLUB(a: asm.Type, b: asm.Type): asm.Type = {

    assert(!isSpecialType(a), "jvmWiseLUB() received a non-plain-class " + a)
    assert(!isSpecialType(b), "jvmWiseLUB() received a non-plain-class " + b)

    val ta = exemplars(a)
    val tb = exemplars(b)

    val res = Pair(ta.isInterface, tb.isInterface) match {
      case (true, true) =>
        ???
      case (true, false) =>
        if(tb.isSubtypeOf(a)) a else ObjectReference
      case (false, true) =>
        if(ta.isSubtypeOf(b)) b else ObjectReference
      case _ =>
        firstCommonSuffix(ta :: ta.superClasses, tb :: tb.superClasses)
    }
    assert(!isSpecialType(res), "jvmWiseLUB() returned a non-plain-class.")
    res
  }

  /* The internal name of the least common ancestor of the types given by inameA and inameB.
     It's what ASM needs to know in order to compute stack map frames, http://asm.ow2.org/doc/developer-guide.html#controlflow */
  def getCommonSuperClass(inameA: String, inameB: String): String = {
    val a   = asm.Type.getObjectType(inameA)
    val b = asm.Type.getObjectType(inameB)
    val lca = jvmWiseLUB(a, b)
    val lcaName = lca.getInternalName // don't call javaName because that side-effects innerClassBuffer.
    assert(lcaName != "scala/Any")

    lcaName // TODO ASM caches the answer during the lifetime of a ClassWriter. We outlive that. Do some caching.
  }

  /** An `asm.ClassWriter` that uses `jvmWiseLUB()`  */
  class CClassWriter(flags: Int) extends asm.ClassWriter(flags) {
    override def getCommonSuperClass(iname1: String, iname2: String): String = {
      BCodeTypes.this.getCommonSuperClass(iname1, iname2)
    }
  }

  // -----------------------------------------------------------------------------------------
  // constants
  // -----------------------------------------------------------------------------------------

  val classfileVersion: Int = settings.target.value match {
    case "jvm-1.5"     => asm.Opcodes.V1_5
    case "jvm-1.5-asm" => asm.Opcodes.V1_5
    case "jvm-1.6"     => asm.Opcodes.V1_6
    case "jvm-1.7"     => asm.Opcodes.V1_7
  }

  val majorVersion: Int = (classfileVersion & 0xFF)
  val emitStackMapFrame = (majorVersion >= 50)

  val extraProc: Int = mkFlags(
    asm.ClassWriter.COMPUTE_MAXS,
    if(emitStackMapFrame) asm.ClassWriter.COMPUTE_FRAMES else 0
  )

  val JAVA_LANG_OBJECT = asm.Type.getObjectType("java/lang/Object")
  val JAVA_LANG_STRING = asm.Type.getObjectType("java/lang/String")

  object isJavaEntryPoint {

    def apply(sym: Symbol, csymCompUnit: CompilationUnit): Boolean = {
      def fail(msg: String, pos: Position = sym.pos) = {
        csymCompUnit.warning(sym.pos,
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
          case MethodType(p :: Nil, _) => p.tpe.typeSymbol == definitions.ArrayClass
          case _                       => false
        }
      }
      // At this point it's a module with a main-looking method, so either succeed or warn that it isn't.
      hasApproximate && {
        // Before erasure so we can identify generic mains.
        beforeErasure {
          val companion     = sym.linkedClassOfClass
          val companionMain = companion.tpe.member(nme.main)

          if (definitions.hasJavaMainMethod(companion))
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
                  definitions.isJavaMainMethod(m) || fail("main method must have exact signature (Array[String])Unit", m.pos)
              case tp =>
                fail("don't know what this is: " + tp, m.pos)
            }
          }
        }
      }
    }

  }

  trait BCCommonPhase extends global.GlobalPhase {

    val BeanInfoAttr = rootMirror.getRequiredClass("scala.beans.BeanInfo")

    def initBytecodeWriter(entryPoints: List[Symbol]): BytecodeWriter = {
      settings.outputDirs.getSingleOutput match {
        case Some(f) if f hasExtension "jar" =>
          // If no main class was specified, see if there's only one
          // entry point among the classes going into the jar.
          if (settings.mainClass.isDefault) {
            entryPoints map (_.fullName('.')) match {
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

          // TODO A ScalapBytecodeWriter could take asm.util.Textifier as starting point.
          //      Three areas where javap ouput is less than ideal (e.g. when comparing versions of the same classfile) are:
          //        (a) unreadable pickle;
          //        (b) two constant pools, while having identical contents, are displayed differently due to physical layout.
          //        (c) stack maps (classfile version 50 and up) are displayed in encoded form by javap, their expansion makes more sense instead.
      }
    }

  } // end of trait BCCommonPhase

  /*
   * Custom attribute (JVMS 4.7.1) "ScalaSig" used as marker only
   * i.e., the pickle is contained in a custom annotation, see:
   *   (1) `addAnnotations()`,
   *   (2) SID # 10 (draft) - Storage of pickled Scala signatures in class files, http://www.scala-lang.org/sid/10
   *   (3) SID # 5 - Internals of Scala Annotations, http://www.scala-lang.org/sid/5
   * That annotation in turn is not related to the "java-generic-signature" (JVMS 4.7.9)
   * other than both ending up encoded as attributes (JVMS 4.7)
   * (with the caveat that the "ScalaSig" attribute is associated to some classes,
   * while the "Signature" attribute can be associated to classes, methods, and fields.)
   *
   **/
  trait BCPickles {

    import scala.reflect.internal.pickling.{ PickleFormat, PickleBuffer }

    val versionPickle = {
      val vp = new PickleBuffer(new Array[Byte](16), -1, 0)
      assert(vp.writeIndex == 0, vp)
      vp writeNat PickleFormat.MajorVersion
      vp writeNat PickleFormat.MinorVersion
      vp writeNat 0
      vp
    }

    def createJAttribute(name: String, b: Array[Byte], offset: Int, len: Int): asm.Attribute = {
      val dest = new Array[Byte](len);
      System.arraycopy(b, offset, dest, 0, len);
      new asm.CustomAttr(name, dest)
    }

    def pickleMarkerLocal = {
      createJAttribute(tpnme.ScalaSignatureATTR.toString, versionPickle.bytes, 0, versionPickle.writeIndex)
    }

    def pickleMarkerForeign = {
      createJAttribute(tpnme.ScalaATTR.toString, new Array[Byte](0), 0, 0)
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
     *  @param jclassName The class file that is being readied.
     *  @param sym    The symbol for which the signature has been entered in the symData map.
     *                This is different than the symbol
     *                that is being generated in the case of a mirror class.
     *  @return       An option that is:
     *                - defined and contains an AnnotationInfo of the ScalaSignature type,
     *                  instantiated with the pickle signature for sym.
     *                - empty if the jclass/sym pair must not contain a pickle.
     *
     */
    def getAnnotPickle(jclassName: String, sym: Symbol): Option[AnnotationInfo] = {
      currentRun.symData get sym match {
        case Some(pickle) if !nme.isModuleName(newTermName(jclassName)) =>
          val scalaAnnot = {
            val sigBytes = ScalaSigBytes(pickle.bytes.take(pickle.writeIndex))
            AnnotationInfo(sigBytes.sigAnnot, Nil, List((nme.bytes, sigBytes)))
          }
          pickledBytes += pickle.writeIndex
          currentRun.symData -= sym
          currentRun.symData -= sym.companionSymbol
          Some(scalaAnnot)
        case _ =>
          None
      }
    }

  } // end of trait BCPickles

  trait BCInnerClassGen {

    val EMPTY_JTYPE_ARRAY  = Array.empty[asm.Type]
    val EMPTY_STRING_ARRAY = Array.empty[String]

    val mdesc_arglessvoid = "()V"

    val CLASS_CONSTRUCTOR_NAME    = "<clinit>"
    val INSTANCE_CONSTRUCTOR_NAME = "<init>"

    val PublicStatic      = asm.Opcodes.ACC_PUBLIC | asm.Opcodes.ACC_STATIC
    val PublicStaticFinal = asm.Opcodes.ACC_PUBLIC | asm.Opcodes.ACC_STATIC | asm.Opcodes.ACC_FINAL

    val strMODULE_INSTANCE_FIELD = nme.MODULE_INSTANCE_FIELD.toString

    def debugLevel = settings.debuginfo.indexOfChoice

    val emitSource = debugLevel >= 1
    val emitLines  = debugLevel >= 2
    val emitVars   = debugLevel >= 3

    // TODO here's where innerClasses-related stuff should go , as well as javaName , and the helpers they invoke.

    /** Specialized array conversion to prevent calling
     *  java.lang.reflect.Array.newInstance via TraversableOnce.toArray
     */
    def mkArray(xs: Traversable[asm.Type]):  Array[asm.Type]  = { val a = new Array[asm.Type](xs.size); xs.copyToArray(a); a }
    def mkArray(xs: Traversable[String]):    Array[String]    = { val a = new Array[String](xs.size);   xs.copyToArray(a); a }

    def descriptor(t: Type):     String = { toTypeKind(t).getDescriptor }
    def descriptor(s: Symbol):   String = { asmClassType(s).getDescriptor }

    /**
     * Returns a new ClassWriter for the class given by arguments.
     *
     * @param access the class's access flags. This parameter also indicates if the class is deprecated.
     *
     * @param name the internal name of the class.
     *
     * @param signature the signature of this class. May be <tt>null</tt> if
     *        the class is not a generic one, and does not extend or implement
     *        generic classes or interfaces.
     *
     * @param superName the internal of name of the super class. For interfaces,
     *        the super class is {@link Object}. May be <tt>null</tt>, but
     *        only for the {@link Object} class.
     *
     * @param interfaces the internal names of the class's interfaces (see
     *        {@link Type#getInternalName() getInternalName}). May be
     *        <tt>null</tt>.
     */
    def createJClass(access: Int, name: String, signature: String, superName: String, interfaces: Array[String]): asm.ClassWriter = {
      val cw = new CClassWriter(extraProc)
      cw.visit(classfileVersion,
               access, name, signature,
               superName, interfaces)

      cw
    }

  } // end of trait BCInnerClassGen

  trait BCAnnotGen extends BCInnerClassGen {

    def ubytesToCharArray(bytes: Array[Byte]): Array[Char] = {
      val ca = new Array[Char](bytes.size)
      var idx = 0
      while(idx < bytes.size) {
        val b: Byte = bytes(idx)
        assert((b & ~0x7f) == 0)
        ca(idx) = b.asInstanceOf[Char]
        idx += 1
      }

      ca
    }

    private def arrEncode(sb: ScalaSigBytes): Array[String] = {
      var strs: List[String]  = Nil
      val bSeven: Array[Byte] = sb.sevenBitsMayBeZero
      // chop into slices of at most 65535 bytes, counting 0x00 as taking two bytes (as per JVMS 4.4.7 The CONSTANT_Utf8_info Structure)
      var prevOffset = 0
      var offset     = 0
      var encLength  = 0
      while(offset < bSeven.size) {
        val deltaEncLength = (if(bSeven(offset) == 0) 2 else 1)
        val newEncLength = encLength.toLong + deltaEncLength
        if(newEncLength >= 65535) {
          val ba     = bSeven.slice(prevOffset, offset)
          strs     ::= new java.lang.String(ubytesToCharArray(ba))
          encLength  = 0
          prevOffset = offset
        } else {
          encLength += deltaEncLength
          offset    += 1
        }
      }
      if(prevOffset < offset) {
        assert(offset == bSeven.length)
        val ba = bSeven.slice(prevOffset, offset)
        strs ::= new java.lang.String(ubytesToCharArray(ba))
      }
      assert(strs.size > 1, "encode instead as one String via strEncode()") // TODO too strict?
      strs.reverse.toArray
    }

    private def strEncode(sb: ScalaSigBytes): String = {
      val ca = ubytesToCharArray(sb.sevenBitsMayBeZero)
      new java.lang.String(ca)
      // debug val bvA = new asm.ByteVector; bvA.putUTF8(s)
      // debug val enc: Array[Byte] = scala.reflect.internal.pickling.ByteCodecs.encode(bytes)
      // debug assert(enc(idx) == bvA.getByte(idx + 2))
      // debug assert(bvA.getLength == enc.size + 2)
    }

    def emitArgument(av:   asm.AnnotationVisitor,
                     name: String,
                     arg:  ClassfileAnnotArg) {
      arg match {

        case LiteralAnnotArg(const) =>
          if(const.isNonUnitAnyVal) { av.visit(name, const.value) }
          else {
            const.tag match {
              case StringTag  =>
                assert(const.value != null, const) // TODO this invariant isn't documented in `case class Constant`
                av.visit(name, const.stringValue)  // `stringValue` special-cases null, but that execution path isn't exercised for a const with StringTag
              case ClazzTag   => av.visit(name, toTypeKind(const.typeValue))
              case EnumTag =>
                val edesc  = descriptor(const.tpe) // the class descriptor of the enumeration class.
                val evalue = const.symbolValue.name.toString // value the actual enumeration value.
                av.visitEnum(name, edesc, evalue)
            }
          }

        case sb@ScalaSigBytes(bytes) =>
          // see http://www.scala-lang.org/sid/10 (Storage of pickled Scala signatures in class files)
          // also JVMS Sec. 4.7.16.1 The element_value structure and JVMS Sec. 4.4.7 The CONSTANT_Utf8_info Structure.
          if (sb.fitsInOneString) {
            av.visit(name, strEncode(sb))
          } else {
            val arrAnnotV: asm.AnnotationVisitor = av.visitArray(name)
            for(arg <- arrEncode(sb)) { arrAnnotV.visit(name, arg) }
            arrAnnotV.visitEnd()
          }          // for the lazy val in ScalaSigBytes to be GC'ed, the invoker of emitAnnotations() should hold the ScalaSigBytes in a method-local var that doesn't escape.

        case ArrayAnnotArg(args) =>
          val arrAnnotV: asm.AnnotationVisitor = av.visitArray(name)
          for(arg <- args) { emitArgument(arrAnnotV, null, arg) }
          arrAnnotV.visitEnd()

        case NestedAnnotArg(annInfo) =>
          val AnnotationInfo(typ, args, assocs) = annInfo
          assert(args.isEmpty, args)
          val desc = descriptor(typ) // the class descriptor of the nested annotation class
          val nestedVisitor = av.visitAnnotation(name, desc)
          emitAssocs(nestedVisitor, assocs)
      }
    }

    /** Whether an annotation should be emitted as a Java annotation
     *   .initialize: if 'annot' is read from pickle, atp might be un-initialized
     */
    private def shouldEmitAnnotation(annot: AnnotationInfo) =
      annot.symbol.initialize.isJavaDefined &&
      annot.matches(definitions.ClassfileAnnotationClass) &&
      annot.args.isEmpty &&
      !annot.matches(definitions.DeprecatedAttr)

    def emitAssocs(av: asm.AnnotationVisitor, assocs: List[(Name, ClassfileAnnotArg)]) {
      for ((name, value) <- assocs) {
        emitArgument(av, name.toString(), value)
      }
      av.visitEnd()
    }

    def emitAnnotations(cw: asm.ClassVisitor, annotations: List[AnnotationInfo]) {
      for(annot <- annotations; if shouldEmitAnnotation(annot)) {
        val AnnotationInfo(typ, args, assocs) = annot
        assert(args.isEmpty, args)
        val av = cw.visitAnnotation(descriptor(typ), true)
        emitAssocs(av, assocs)
      }
    }

    def emitAnnotations(mw: asm.MethodVisitor, annotations: List[AnnotationInfo]) {
      for(annot <- annotations; if shouldEmitAnnotation(annot)) {
        val AnnotationInfo(typ, args, assocs) = annot
        assert(args.isEmpty, args)
        val av = mw.visitAnnotation(descriptor(typ), true)
        emitAssocs(av, assocs)
      }
    }

    def emitAnnotations(fw: asm.FieldVisitor, annotations: List[AnnotationInfo]) {
      for(annot <- annotations; if shouldEmitAnnotation(annot)) {
        val AnnotationInfo(typ, args, assocs) = annot
        assert(args.isEmpty, args)
        val av = fw.visitAnnotation(descriptor(typ), true)
        emitAssocs(av, assocs)
      }
    }

    def emitParamAnnotations(jmethod: asm.MethodVisitor, pannotss: List[List[AnnotationInfo]]) {
      val annotationss = pannotss map (_ filter shouldEmitAnnotation)
      if (annotationss forall (_.isEmpty)) return
      for (Pair(annots, idx) <- annotationss.zipWithIndex;
           annot <- annots) {
        val AnnotationInfo(typ, args, assocs) = annot
        assert(args.isEmpty, args)
        val pannVisitor: asm.AnnotationVisitor = jmethod.visitParameterAnnotation(idx, descriptor(typ), true)
        emitAssocs(pannVisitor, assocs)
      }
    }

  } // end of trait BCAnnotGen

  trait BCJGenSigGen {

    // @M don't generate java generics sigs for (members of) implementation
    // classes, as they are monomorphic (TODO: ok?)
    private def needsGenericSignature(sym: Symbol) = !(
      // PP: This condition used to include sym.hasExpandedName, but this leads
      // to the total loss of generic information if a private member is
      // accessed from a closure: both the field and the accessor were generated
      // without it.  This is particularly bad because the availability of
      // generic information could disappear as a consequence of a seemingly
      // unrelated change.
         settings.Ynogenericsig.value
      || sym.isArtifact
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

      val jsOpt: Option[String] = erasure.javaSig(sym, memberTpe)
      if (jsOpt.isEmpty) { return null }

      val sig = jsOpt.get
      log(sig) // This seems useful enough in the general case.

          def wrap(op: => Unit) = {
            try   { op; true }
            catch { case _: Throwable => false }
          }

      if (settings.Xverify.value) {
        // Run the signature parser to catch bogus signatures.
        val isValidSignature = wrap {
          // Alternative: scala.tools.reflect.SigParser (frontend to sun.reflect.generics.parser.SignatureParser)
          import scala.tools.asm.util.SignatureChecker
          if (sym.isMethod)    { SignatureChecker checkMethodSignature sig } // requires asm-util.jar
          else if (sym.isTerm) { SignatureChecker checkFieldSignature  sig }
          else                 { SignatureChecker checkClassSignature  sig }
        }

        if(!isValidSignature) {
          getCurrentCUnit().warning(sym.pos,
              """|compiler bug: created invalid generic signature for %s in %s
                 |signature: %s
                 |if this is reproducible, please report bug at https://issues.scala-lang.org/
              """.trim.stripMargin.format(sym, sym.owner.skipPackageObject.fullName, sig))
          return null
        }
      }

      if ((settings.check containsName phaseName)) {
        val normalizedTpe = beforeErasure(erasure.prepareSigMap(memberTpe))
        val bytecodeTpe = owner.thisType.memberInfo(sym)
        if (!sym.isType && !sym.isConstructor && !(erasure.erasure(sym)(normalizedTpe) =:= bytecodeTpe)) {
          getCurrentCUnit().warning(sym.pos,
              """|compiler bug: created generic signature for %s in %s that does not conform to its erasure
                 |signature: %s
                 |original type: %s
                 |normalized type: %s
                 |erasure type: %s
                 |if this is reproducible, please report bug at http://issues.scala-lang.org/
              """.trim.stripMargin.format(sym, sym.owner.skipPackageObject.fullName, sig, memberTpe, normalizedTpe, bytecodeTpe))
           return null
        }
      }

      sig
    }

  } // end of trait BCJGenSigGen

  trait BCForwardersGen extends BCAnnotGen with BCJGenSigGen {

    // -----------------------------------------------------------------------------------------
    // Static forwarders (related to mirror classes but also present in
    // a plain class lacking companion module, for details see `isCandidateForForwarders`).
    // -----------------------------------------------------------------------------------------

    val ExcludedForwarderFlags = {
      import symtab.Flags._
      // Should include DEFERRED but this breaks findMember.
      ( CASE | SPECIALIZED | LIFTED | PROTECTED | STATIC | EXPANDEDNAME | BridgeAndPrivateFlags )
    }

    /** Adds a @remote annotation, actual use unknown.
     *
     * Invoked from genMethod() and addForwarder().
     */
    def addRemoteExceptionAnnot(isRemoteClass: Boolean, isJMethodPublic: Boolean, meth: Symbol) {
      val needsAnnotation = (
        (  isRemoteClass ||
           isRemote(meth) && isJMethodPublic
        ) && !(meth.throwsAnnotations contains definitions.RemoteExceptionClass)
      )
      if (needsAnnotation) {
        val c   = Constant(definitions.RemoteExceptionClass.tpe)
        val arg = Literal(c) setType c.tpe
        meth.addAnnotation(definitions.ThrowsClass, arg)
      }
    }

    /** Add a forwarder for method m. Used only from addForwarders(). */
    private def addForwarder(isRemoteClass: Boolean, jclass: asm.ClassVisitor, module: Symbol, m: Symbol) {
      val moduleName     = internalName(module)
      val methodInfo     = module.thisType.memberInfo(m)
      val paramJavaTypes: List[asm.Type] = methodInfo.paramTypes map toTypeKind
      // val paramNames     = 0 until paramJavaTypes.length map ("x_" + _)

      /** Forwarders must not be marked final,
       *  as the JVM will not allow redefinition of a final static method,
       *  and we don't know what classes might be subclassing the companion class.  See SI-4827.
       */
      // TODO: evaluate the other flags we might be dropping on the floor here.
      // TODO: ACC_SYNTHETIC ?
      val flags = PublicStatic | (
        if (m.isVarargsMethod) asm.Opcodes.ACC_VARARGS else 0
      )

      // TODO needed? for(ann <- m.annotations) { ann.symbol.initialize }
      val jgensig = if (m.isDeferred) null else getGenericSignature(m, module); // only add generic signature if method concrete; bug #1745
      addRemoteExceptionAnnot(isRemoteClass, hasPublicBitSet(flags), m)
      val (throws, others) = m.annotations partition (_.symbol == definitions.ThrowsClass)
      val thrownExceptions: List[String] = getExceptions(throws)

      val jReturnType = toTypeKind(methodInfo.resultType)
      val mdesc = asm.Type.getMethodDescriptor(jReturnType, paramJavaTypes: _*)
      val mirrorMethodName = m.javaSimpleName.toString
      val mirrorMethod: asm.MethodVisitor = jclass.visitMethod(
        flags,
        mirrorMethodName,
        mdesc,
        jgensig,
        mkArray(thrownExceptions)
      )

      // typestate: entering mode with valid call sequences:
      //   [ visitAnnotationDefault ] ( visitAnnotation | visitParameterAnnotation | visitAttribute )*

      emitAnnotations(mirrorMethod, others)
      emitParamAnnotations(mirrorMethod, m.info.params.map(_.annotations))

      // typestate: entering mode with valid call sequences:
      //   visitCode ( visitFrame | visitXInsn | visitLabel | visitTryCatchBlock | visitLocalVariable | visitLineNumber )* visitMaxs ] visitEnd

      mirrorMethod.visitCode()

      mirrorMethod.visitFieldInsn(asm.Opcodes.GETSTATIC, moduleName, strMODULE_INSTANCE_FIELD, descriptor(module))

      var index = 0
      for(jparamType <- paramJavaTypes) {
        mirrorMethod.visitVarInsn(jparamType.getOpcode(asm.Opcodes.ILOAD), index)
        assert(jparamType.getSort() != asm.Type.METHOD, jparamType)
        index += jparamType.getSize()
      }

      mirrorMethod.visitMethodInsn(asm.Opcodes.INVOKEVIRTUAL, moduleName, mirrorMethodName, asmMethodType(m).getDescriptor)
      mirrorMethod.visitInsn(jReturnType.getOpcode(asm.Opcodes.IRETURN))

      mirrorMethod.visitMaxs(0, 0) // just to follow protocol, dummy arguments
      mirrorMethod.visitEnd()

    }

    /** Add forwarders for all methods defined in `module` that don't conflict
     *  with methods in the companion class of `module`. A conflict arises when
     *  a method with the same name is defined both in a class and its companion object:
     *  method signature is not taken into account.
     */
    def addForwarders(isRemoteClass: Boolean, jclass: asm.ClassVisitor, jclassName: String, moduleClass: Symbol) {
      assert(moduleClass.isModuleClass, moduleClass)
      debuglog("Dumping mirror class for object: " + moduleClass)

      val linkedClass  = moduleClass.companionClass
      val linkedModule = linkedClass.companionSymbol
      lazy val conflictingNames: Set[Name] = {
        (linkedClass.info.members collect { case sym if sym.name.isTermName => sym.name }).toSet
      }
      debuglog("Potentially conflicting names for forwarders: " + conflictingNames)

      for (m <- moduleClass.info.membersBasedOnFlags(ExcludedForwarderFlags, symtab.Flags.METHOD)) {
        if (m.isType || m.isDeferred || (m.owner eq definitions.ObjectClass) || m.isConstructor)
          debuglog("No forwarder for '%s' from %s to '%s'".format(m, jclassName, moduleClass))
        else if (conflictingNames(m.name))
          log("No forwarder for " + m + " due to conflict with " + linkedClass.info.member(m.name))
        else if (m.hasAccessBoundary)
          log(s"No forwarder for non-public member $m")
        else {
          log("Adding static forwarder for '%s' from %s to '%s'".format(m, jclassName, moduleClass))
          if (m.isAccessor && m.accessed.hasStaticAnnotation) {
            log("@static: accessor " + m + ", accessed: " + m.accessed)
          } else addForwarder(isRemoteClass, jclass, moduleClass, m)
        }
      }
    }

    /**
     * Quoting from JVMS 4.7.5 The Exceptions Attribute
     *   "The Exceptions attribute indicates which checked exceptions a method may throw.
     *    There may be at most one Exceptions attribute in each method_info structure."
     *
     * The contents of that attribute are determined by the `String[] exceptions` argument to ASM's ClassVisitor.visitMethod()
     * This method returns such list of internal names.
     *
     */
    def getExceptions(excs: List[AnnotationInfo]): List[String] = {
      for (AnnotationInfo(tp, List(exc), _) <- excs.distinct if tp.typeSymbol == definitions.ThrowsClass)
      yield {
        val Literal(const) = exc
        internalName(const.typeValue.typeSymbol)
      }
    }

  } // end of trait BCForwardersGen

  trait BCClassGen extends BCInnerClassGen {

    val MIN_SWITCH_DENSITY = 0.7

    val StringBuilderClassName = definitions.StringBuilderClass.javaBinaryName.toString
    val BoxesRunTime = "scala/runtime/BoxesRunTime"

    val mdesc_arrayClone  = "()Ljava/lang/Object;"

    val tdesc_long        = asm.Type.LONG_TYPE.getDescriptor // ie. "J"

    private def serialVUID(csym: Symbol): Option[Long] = csym getAnnotation definitions.SerialVersionUIDAttr collect {
      case AnnotationInfo(_, Literal(const) :: _, _) => const.longValue
    }

    def addSerialVUID(csym: Symbol, jclass: asm.ClassVisitor) {
      // add static serialVersionUID field if `clasz` annotated with `@SerialVersionUID(uid: Long)`
      serialVUID(csym) foreach { value =>
        val fieldName = "serialVersionUID"
        jclass.visitField(
          PublicStaticFinal,
          fieldName,
          tdesc_long,
          null, // no java-generic-signature
          value
        ).visitEnd()
      }
    }

    /**
     * @param owner internal name of the enclosing class of the class.
     *
     * @param name the name of the method that contains the class.

     * @param methodType the method that contains the class.
     */
    case class EnclMethodEntry(owner: String, name: String, methodType: asm.Type)

    /**
     * @return null if the current class is not internal to a method
     *
     * Quoting from JVMS 4.7.7 The EnclosingMethod Attribute
     *   A class must have an EnclosingMethod attribute if and only if it is a local class or an anonymous class.
     *   A class may have no more than one EnclosingMethod attribute.
     *
     */
    def getEnclosingMethodAttribute(clazz: Symbol): EnclMethodEntry = { // JVMS 4.7.7

          def newEEE(eClass: Symbol, m: Symbol) = {
            EnclMethodEntry(
              internalName(eClass),
              m.javaSimpleName.toString,
              asmMethodType(m)
            )
          }

      var res: EnclMethodEntry = null
      val sym = clazz.originalEnclosingMethod
      if (sym.isMethod) {
        debuglog("enclosing method for %s is %s (in %s)".format(clazz, sym, sym.enclClass))
        res = newEEE(sym.enclClass, sym)
      } else if (clazz.isAnonymousClass) {
        val enclClass = clazz.rawowner
        assert(enclClass.isClass, enclClass)
        val sym = enclClass.primaryConstructor
        if (sym == NoSymbol) {
          log("Ran out of room looking for an enclosing method for %s: no constructor here.".format(enclClass, clazz))
        } else {
          debuglog("enclosing method for %s is %s (in %s)".format(clazz, sym, enclClass))
          res = newEEE(enclClass, sym)
        }
      }

      res
    }

  } // end of trait BCClassGen

  trait BCInitGen
    extends BCClassGen
    with    BCAnnotGen
    with    BCInnerClassGen
    with    JAndroidBuilder
    with    BCForwardersGen
    with    BCPickles {

    def methodSymbols(cd: ClassDef): List[Symbol] = {
      cd.impl.body collect { case dd: DefDef => dd.symbol }
    }

    def initJClass(jclass:        asm.ClassVisitor,
                   csym:          Symbol,
                   thisName:      String,
                   thisSignature: String,
                   cunit:         CompilationUnit) {

      val ps = csym.info.parents
      val superClass: String = if(ps.isEmpty) JAVA_LANG_OBJECT.getInternalName else internalName(ps.head.typeSymbol);
      val ifaces = getSuperInterfaces(csym) map internalName // `internalName()` tracks inner classes.

      val flags = mkFlags(
        javaFlags(csym),
        if(isDeprecated(csym)) asm.Opcodes.ACC_DEPRECATED else 0 // ASM pseudo access flag
      )

      jclass.visit(classfileVersion, flags,
                   thisName, thisSignature,
                   superClass, ifaces.toArray)
      // typestate: entering mode with valid call sequences:
      //   [ visitSource ] [ visitOuterClass ] ( visitAnnotation | visitAttribute )*

      if(emitSource) {
        jclass.visitSource(cunit.source.toString, null /* SourceDebugExtension */)
      }

      val enclM = getEnclosingMethodAttribute(csym)
      if(enclM != null) {
        val EnclMethodEntry(className, methodName, methodType) = enclM
        jclass.visitOuterClass(className, methodName, methodType.getDescriptor)
      }

      // typestate: entering mode with valid call sequences:
      //   ( visitAnnotation | visitAttribute )*

      val ssa = getAnnotPickle(thisName, csym)
      jclass.visitAttribute(if(ssa.isDefined) pickleMarkerLocal else pickleMarkerForeign)
      emitAnnotations(jclass, csym.annotations ++ ssa)

      // typestate: entering mode with valid call sequences:
      //   ( visitInnerClass | visitField | visitMethod )* visitEnd

      if (isStaticModule(csym) || isAndroidParcelableClass(csym)) {

        if (isStaticModule(csym)) { addModuleInstanceField(jclass, thisName) }

      } else {

        val skipStaticForwarders = (csym.isInterface || settings.noForwarders.value)
        if (!skipStaticForwarders) {
          val lmoc = csym.companionModule
          // add static forwarders if there are no name conflicts; see bugs #363 and #1735
          if (lmoc != NoSymbol) {
            // it must be a top level class (name contains no $s)
            val isCandidateForForwarders = {
              afterPickler { !(lmoc.name.toString contains '$') && lmoc.hasModuleFlag && !lmoc.isImplClass && !lmoc.isNestedClass }
            }
            if (isCandidateForForwarders) {
              log("Adding static forwarders from '%s' to implementations in '%s'".format(csym, lmoc))
              addForwarders(isRemote(csym), jclass, thisName, lmoc.moduleClass)
            }
          }
        }

      }

      // the invoker is responsible for adding a class-static constructor.

    } // end of method initJClass

    def addModuleInstanceField(jclass: asm.ClassVisitor, thisName: String) {
      val fv =
        jclass.visitField(PublicStaticFinal, // TODO confirm whether we really don't want ACC_SYNTHETIC nor ACC_DEPRECATED
                          strMODULE_INSTANCE_FIELD,
                          thisDescr(thisName),
                          null, // no java-generic-signature
                          null  // no initial value
        )

      // typestate: entering mode with valid call sequences:
      //   ( visitAnnotation | visitAttribute )* visitEnd.

      fv.visitEnd()
    }

    def thisDescr(thisName: String): String = {
      assert(thisName != null, "thisDescr invoked too soon.")
      asm.Type.getObjectType(thisName).getDescriptor
    }

    def initJMethod(jclass:           asm.ClassVisitor,
                    msym:             Symbol,
                    isNative:         Boolean,
                    csym:             Symbol,
                    isJInterface:     Boolean,
                    paramTypes:       List[asm.Type],
                    paramAnnotations: List[List[AnnotationInfo]]
    ): Pair[Int, asm.MethodVisitor] = {

      var resTpe: asm.Type = toTypeKind(msym.info.resultType) // TODO confirm: was msym.tpe.resultType
      if (msym.isClassConstructor)
        resTpe = asm.Type.VOID_TYPE

      val flags = mkFlags(
        javaFlags(msym),
        if (isJInterface)      asm.Opcodes.ACC_ABSTRACT   else 0,
        if (msym.isStrictFP)   asm.Opcodes.ACC_STRICT     else 0,
        if (isNative)          asm.Opcodes.ACC_NATIVE     else 0, // native methods of objects are generated in mirror classes
        if(isDeprecated(msym)) asm.Opcodes.ACC_DEPRECATED else 0  // ASM pseudo access flag
      )

      // TODO needed? for(ann <- m.symbol.annotations) { ann.symbol.initialize }
      val jgensig = getGenericSignature(msym, csym)
      addRemoteExceptionAnnot(isRemote(csym), hasPublicBitSet(flags), msym)
      val (excs, others) = msym.annotations partition (_.symbol == definitions.ThrowsClass)
      val thrownExceptions: List[String] = getExceptions(excs)

      val jMethodName =
        if(msym.isStaticConstructor) CLASS_CONSTRUCTOR_NAME
        else javaSimpleName(msym)
      val mdesc = asm.Type.getMethodDescriptor(resTpe, paramTypes: _*)
      val jmethod = jclass.visitMethod(
        flags,
        jMethodName,
        mdesc,
        jgensig,
        mkArray(thrownExceptions)
      )

      // TODO param names: (m.params map (p => javaName(p.sym)))

      // typestate: entering mode with valid call sequences:
      //   [ visitAnnotationDefault ] ( visitAnnotation | visitParameterAnnotation | visitAttribute )*

      emitAnnotations(jmethod, others)
      emitParamAnnotations(jmethod, paramAnnotations)

      Pair(flags, jmethod)
    } // end of method initJMethod

  }

  /** basic functionality for class file building of plain, mirror, and beaninfo classes. */
  abstract class JBuilder(bytecodeWriter: BytecodeWriter) extends BCInnerClassGen {

    def writeIfNotTooBig(label: String, jclassName: String, jclass: asm.ClassWriter, sym: Symbol) {
      try {
        val arr = jclass.toByteArray()
        bytecodeWriter.writeClass(label, jclassName, arr, sym)
      } catch {
        case e: java.lang.RuntimeException if(e.getMessage() == "Class file too large!") =>
          // TODO check where ASM throws the equivalent of CodeSizeTooBigException
          log("Skipped class "+jclassName+" because it exceeds JVM limits (it's too big or has methods that are too long).")
      }
    }

  } // end of class JBuilder

  /** functionality for building plain and mirror classes */
  abstract class JCommonBuilder(bytecodeWriter: BytecodeWriter)
    extends JBuilder(bytecodeWriter)
    with    BCAnnotGen
    with    BCForwardersGen
    with    BCPickles { }

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
      innerClassBufferASM.clear()
      this.cunit = cunit
      val moduleName = internalName(modsym) // + "$"
      val mirrorName = moduleName.substring(0, moduleName.length() - 1)

      val flags = (asm.Opcodes.ACC_SUPER | asm.Opcodes.ACC_PUBLIC | asm.Opcodes.ACC_FINAL)
      val mirrorClass = createJClass(flags,
                                     mirrorName,
                                     null /* no java-generic-signature */,
                                     JAVA_LANG_OBJECT.getInternalName,
                                     EMPTY_STRING_ARRAY)

      // typestate: entering mode with valid call sequences:
      //   [ visitSource ] [ visitOuterClass ] ( visitAnnotation | visitAttribute )*

      if(emitSource) {
        mirrorClass.visitSource("" + cunit.source,
                                null /* SourceDebugExtension */)
      }

      val ssa = getAnnotPickle(mirrorName, modsym.companionSymbol)
      mirrorClass.visitAttribute(if(ssa.isDefined) pickleMarkerLocal else pickleMarkerForeign)
      emitAnnotations(mirrorClass, modsym.annotations ++ ssa)

      // typestate: entering mode with valid call sequences:
      //   ( visitInnerClass | visitField | visitMethod )* visitEnd

      addForwarders(isRemote(modsym), mirrorClass, mirrorName, modsym)

      addInnerClassesASM(modsym, mirrorClass)
      mirrorClass.visitEnd()
      writeIfNotTooBig("" + modsym.name, mirrorName, mirrorClass, modsym)
    }

  } // end of class JMirrorBuilder

  /** builder of bean info classes */
  class JBeanInfoBuilder(bytecodeWriter: BytecodeWriter) extends JBuilder(bytecodeWriter) {

    /**
     * Generate a bean info class that describes the given class.
     *
     * @author Ross Judson (ross.judson@soletta.com)
     */
    def genBeanInfoClass(cls: Symbol, cunit: CompilationUnit, fieldSymbols: List[Symbol], methodSymbols: List[Symbol]) {

      // val BeanInfoSkipAttr    = definitions.getRequiredClass("scala.beans.BeanInfoSkip")
      // val BeanDisplayNameAttr = definitions.getRequiredClass("scala.beans.BeanDisplayName")
      // val BeanDescriptionAttr = definitions.getRequiredClass("scala.beans.BeanDescription")
      // val description = c.symbol getAnnotation BeanDescriptionAttr
      // informProgress(description.toString)
      innerClassBufferASM.clear()

      val flags = mkFlags(
        javaFlags(cls),
        if(isDeprecated(cls)) asm.Opcodes.ACC_DEPRECATED else 0 // ASM pseudo access flag
      )

      val beanInfoName = (internalName(cls) + "BeanInfo")
      val beanInfoClass = createJClass(
            flags,
            beanInfoName,
            null, // no java-generic-signature
            "scala/beans/ScalaBeanInfo",
            EMPTY_STRING_ARRAY
      )

      // beanInfoClass typestate: entering mode with valid call sequences:
      //   [ visitSource ] [ visitOuterClass ] ( visitAnnotation | visitAttribute )*

      beanInfoClass.visitSource(
        cunit.source.toString,
        null /* SourceDebugExtension */
      )

      var fieldList = List[String]()

      for (f <- fieldSymbols if f.hasGetter;
	         g = f.getter(cls);
	         s = f.setter(cls);
	         if g.isPublic && !(f.name startsWith "$")
          ) {
             // inserting $outer breaks the bean
             fieldList = javaSimpleName(f) :: javaSimpleName(g) :: (if (s != NoSymbol) javaSimpleName(s) else null) :: fieldList
      }

      val methodList: List[String] =
	     for (m <- methodSymbols
	          if !m.isConstructor &&
	          m.isPublic &&
	          !(m.name startsWith "$") &&
	          !m.isGetter &&
	          !m.isSetter)
       yield javaSimpleName(m)

      // beanInfoClass typestate: entering mode with valid call sequences:
      //   ( visitInnerClass | visitField | visitMethod )* visitEnd

      val constructor = beanInfoClass.visitMethod(
        asm.Opcodes.ACC_PUBLIC,
        INSTANCE_CONSTRUCTOR_NAME,
        mdesc_arglessvoid,
        null, // no java-generic-signature
        EMPTY_STRING_ARRAY // no throwable exceptions
      )

      // constructor typestate: entering mode with valid call sequences:
      //   [ visitAnnotationDefault ] ( visitAnnotation | visitParameterAnnotation | visitAttribute )*

      val stringArrayJType: asm.Type = arrayOf(JAVA_LANG_STRING)
      val conJType: asm.Type =
        asm.Type.getMethodType(
          asm.Type.VOID_TYPE,
          Array(exemplar(definitions.ClassClass).c, stringArrayJType, stringArrayJType): _*
        )

      def push(lst: List[String]) {
        var fi = 0
        for (f <- lst) {
          constructor.visitInsn(asm.Opcodes.DUP)
          constructor.visitLdcInsn(new java.lang.Integer(fi))
          if (f == null) { constructor.visitInsn(asm.Opcodes.ACONST_NULL) }
          else           { constructor.visitLdcInsn(f) }
          constructor.visitInsn(JAVA_LANG_STRING.getOpcode(asm.Opcodes.IASTORE))
          fi += 1
        }
      }

      // constructor typestate: entering mode with valid call sequences:
      //   [ visitCode ( visitFrame | visitXInsn | visitLabel | visitTryCatchBlock | visitLocalVariable | visitLineNumber )* visitMaxs ] visitEnd

      constructor.visitCode()

      constructor.visitVarInsn(asm.Opcodes.ALOAD, 0)
      // push the class
      constructor.visitLdcInsn(exemplar(cls).c)

      // push the string array of field information
      constructor.visitLdcInsn(new java.lang.Integer(fieldList.length))
      constructor.visitTypeInsn(asm.Opcodes.ANEWARRAY, JAVA_LANG_STRING.getInternalName)
      push(fieldList)

      // push the string array of method information
      constructor.visitLdcInsn(new java.lang.Integer(methodList.length))
      constructor.visitTypeInsn(asm.Opcodes.ANEWARRAY, JAVA_LANG_STRING.getInternalName)
      push(methodList)

      // invoke the superclass constructor, which will do the
      // necessary java reflection and create Method objects.
      constructor.visitMethodInsn(asm.Opcodes.INVOKESPECIAL, "scala/beans/ScalaBeanInfo", INSTANCE_CONSTRUCTOR_NAME, conJType.getDescriptor)
      constructor.visitInsn(asm.Opcodes.RETURN)

      constructor.visitMaxs(0, 0) // just to follow protocol, dummy arguments
      constructor.visitEnd()

      addInnerClassesASM(cls, beanInfoClass)
      beanInfoClass.visitEnd()

      writeIfNotTooBig("BeanInfo ", beanInfoName, beanInfoClass, cls)
    }

  } // end of class JBeanInfoBuilder

  trait JAndroidBuilder {
    self: BCInnerClassGen =>

    /** From the reference documentation of the Android SDK:
     *  The `Parcelable` interface identifies classes whose instances can be written to and restored from a `Parcel`.
     *  Classes implementing the `Parcelable` interface must also have a static field called `CREATOR`,
     *  which is an object implementing the `Parcelable.Creator` interface.
     */
    val androidFieldName = newTermName("CREATOR")

    private lazy val AndroidParcelableInterface = rootMirror.getClassIfDefined("android.os.Parcelable")
    lazy val AndroidCreatorClass        = rootMirror.getClassIfDefined("android.os.Parcelable$Creator")

    def isAndroidParcelableClass(sym: Symbol) =
      (AndroidParcelableInterface != NoSymbol) &&
      (sym.parentSymbols contains AndroidParcelableInterface)

    // TODO see JPlainBuilder.addAndroidCreatorCode()

    def legacyAddCreatorCode(clinit: asm.MethodVisitor, jclass: asm.ClassVisitor, csym: Symbol, thisName: String) {
      val creatorType: asm.Type = asmClassType(AndroidCreatorClass)
      val tdesc_creator = creatorType.getDescriptor

      jclass.visitField(
        PublicStaticFinal,
        androidFieldName,
        tdesc_creator,
        null, // no java-generic-signature
        null  // no initial value
      ).visitEnd()

      val moduleName = internalName(csym)+"$"

      // GETSTATIC `moduleName`.MODULE$ : `moduleName`;
      clinit.visitFieldInsn(
        asm.Opcodes.GETSTATIC,
        moduleName,
        strMODULE_INSTANCE_FIELD,
        asm.Type.getObjectType(moduleName).getDescriptor
      )

      // INVOKEVIRTUAL `moduleName`.CREATOR() : android.os.Parcelable$Creator;
      clinit.visitMethodInsn(
        asm.Opcodes.INVOKEVIRTUAL,
        moduleName,
        androidFieldName,
        asm.Type.getMethodDescriptor(creatorType, Array.empty[asm.Type]: _*)
      )

      // PUTSTATIC `thisName`.CREATOR;
      clinit.visitFieldInsn(
        asm.Opcodes.PUTSTATIC,
        thisName,
        androidFieldName,
        tdesc_creator
      )
    }

  } // end of trait JAndroidBuilder

  /**
   * Collects (in `result`) all LabelDef nodes enclosed (directly or not) by each node it visits.
   *
   * In other words, this traverser prepares a map giving
   * all labelDefs (the entry-value) having a Tree node (the entry-key) as ancestor.
   * The entry-value for a LabelDef entry-key always contains the entry-key.
   *
   * */
  class LabelDefsFinder extends Traverser {
    val result = mutable.Map.empty[Tree, List[LabelDef]]
    var acc: List[LabelDef] = Nil
    override def traverse(tree: Tree) {
      val saved = acc
      acc = Nil
      super.traverse(tree)
      // acc contains all LabelDefs found under (but not at) `tree`
      tree match {
        case lblDf: LabelDef => acc ::= lblDf
        case _               => ()
      }
      if(acc.isEmpty) {
        acc = saved
      } else {
        result += (tree -> acc)
        acc = acc ::: saved
      }
    }
  }

}
