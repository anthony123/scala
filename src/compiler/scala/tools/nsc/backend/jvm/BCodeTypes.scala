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
trait BCodeTypes extends GenBCode {

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

  /** Reverse map for toType */
  private lazy val reversePrimitiveMap: Map[asm.Type, Symbol] =
    (primitiveTypeMap map (_.swap)).toMap

  /** Defined for reference types (ie non-array non-primitive types; boxed ones are fine).
   *
   *  See also:
   *    def primitiveOrArrayOrRefType(sym: Symbol, arrtarg: Type = null): asm.Type
   *    def toTypeKind(t: Type): asm.Type
   *
   * */
  def classSymbol(reft: asm.Type): Symbol = {
    assert(!isArrayType(reft), "Invoked for an array type.")
    assert(!isValueType(reft), "Invoked for a primitive type.")

    ???
  }

  def toType(t: asm.Type): Type = {
    reversePrimitiveMap get t map (_.tpe) getOrElse {
      if(isReferenceType(t))  classSymbol(t).tpe
      else if(isArrayType(t)) definitions.arrayType(toType(componentType(t)))
      else abort("Unknown asm.Type.")
    }
  }

  /* Unlike for ICode's REFERENCE, isBoxedType(t) implies isReferenceType(t) */
  final def isReferenceType(t: asm.Type) = (t.getSort == asm.Type.OBJECT) && !isNothingType(t)

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

  final def isUnitType(t: asm.Type): Boolean = { t.getSort == asm.Type.VOID }

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

  /*
   * For use only within BCodeTypes trait.
   *
   *   (1) The canonical way to obtain an asm.Type from GenBCode is via `toTypeKind()`.
   *
   *   (2) From within `BCodeTypes`, two other helpers should be preferred (`primitiveOrRefType()` and `primitiveOrClassType`)
   *       because they handle primitives and arrays, which `asmType()` doesn't.
   *       `asmType()` is just a shortcut for `asm.Type.getObjectType()`, as the preconditions listed below make clear.
   **/
  private def asmType(sym: Symbol): asm.Type = {
    assert(!primitiveTypeMap.contains(sym), "Use primitiveTypeMap instead.")
    assert(sym != definitions.ArrayClass,   "Use primitiveOrArrayOrRefType() instead.")
    assert(sym.isClass || (sym.isModule && !sym.isMethod), "Invoked for a symbol lacking JVM internal name: " + sym.fullName)

    asm.Type.getObjectType(sym.javaBinaryName.toString)
  }

  val ObjectReference    = asmType(definitions.ObjectClass)
  val AnyRefReference    = ObjectReference // In tandem, javaName(definitions.AnyRefClass) == ObjectReference. Otherwise every `t1 == t2` requires special-casing.
  val NothingReference   = asmType(definitions.NothingClass) // different from binarynme.RuntimeNothing
  val NullReference      = asmType(definitions.NullClass)    // different from binarynme.RuntimeNull
  val StringReference    = asmType(definitions.StringClass)
  val ThrowableReference = asmType(definitions.ThrowableClass)
  // This is problematic, because there's also BOXED_UNIT. Besides, it's not in use: val BoxedUnitReference = asmType(definitions.BoxedUnitClass)

  final def isRefOrArrayType(t: asm.Type) = isReferenceType(t)  || isArrayType(t)

  final def isNothingType(t: asm.Type) = (t == NothingReference)
  final def isNullType   (t: asm.Type) = (t == NullReference)

  final def isInterfaceType(t: asm.Type) = {
    isReferenceType(t) &&
    !isBoxedType(t)    && {
      val cls = classSymbol(t)

      cls.isInterface || cls.isTrait // cls.isImplClass not true for isTrait class symbols at this point (after mixin)
    }
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

  /** The ultimate element type of this array. */
  def elementType(t: asm.Type): asm.Type = {
    assert(isArrayType(t), "Asked for the element type of a non-array type: " + t)
    t.getElementType
  }

  /** The type of items this array holds. */
  def componentType(t: asm.Type): asm.Type = {
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
   *
   *  Call to .normalize fixes #3003 (follow type aliases).
   *  Otherwise, primitiveOrArrayOrRefType() would return ObjectReference.
   **/
  def toTypeKind(t: Type): asm.Type = {
    t.normalize match {
      case ThisType(sym)            =>
        if(sym == definitions.ArrayClass) ObjectReference
        else asmType(sym)
      case SingleType(_, sym)       => primitiveOrRefType(sym)
      case ConstantType(_)          => toTypeKind(t.underlying)
      case TypeRef(_, sym, args)    => primitiveOrArrayOrRefType(sym, args.head)
      case ClassInfoType(_, _, sym) =>
        if(sym == definitions.ArrayClass) abort("ClassInfoType to ArrayClass!")
        else primitiveOrRefType(sym)

      // !!! Iulian says types which make no sense after erasure should not reach here,
      // which includes the ExistentialType, AnnotatedType, RefinedType.  I don't know
      // if the first two cases exist because they do or as a defensive measure, but
      // at the time I added it, RefinedTypes were indeed reaching here.
      case ExistentialType(_, t1)  => abort("ExistentialType reached GenBCode: " + t)
      case AnnotatedType(_, t1, _) => abort("AnnotatedType reached GenBCode: "   + t)
      case RefinedType(parents, _) => abort("RefinedType reached GenBCode: "     + t) // defensive: parents map toTypeKind reduceLeft lub

      // For sure WildcardTypes shouldn't reach here either, but when
      // debugging such situations this may come in handy.
      // case WildcardType                    => REFERENCE(ObjectClass)
      case norm => abort(
        "Unknown type: %s, %s [%s, %s] TypeRef? %s".format(
          t, norm, t.getClass, norm.getClass, t.isInstanceOf[TypeRef]
        )
      )
    }
  }

  /** Interfaces have to be handled delicately to avoid introducing spurious errors,
   *  but if we treat them all as AnyRef we lose too much information.
   **/
  private def newReference(sym: Symbol): asm.Type = {
    assert(!primitiveTypeMap.contains(sym), "Use primitiveTypeMap instead.")
    assert(sym != definitions.ArrayClass,   "Use primitiveOrArrayOrRefType() instead.")

    // Can't call .toInterface (at this phase) or we trip an assertion.
    // See PackratParser#grow for a method which fails with an apparent mismatch
    // between "object PackratParsers$class" and "trait PackratParsers"
    if (sym.isImplClass) {
      // pos/spec-List.scala is the sole failure if we don't check for NoSymbol
      val traitSym = sym.owner.info.decl(tpnme.interfaceName(sym.name))
      if (traitSym != NoSymbol)
        return asmType(traitSym)
    }
    asmType(sym)
  }

  private def primitiveOrRefType(sym: Symbol): asm.Type = {
    assert(sym != definitions.ArrayClass, "Use primitiveOrArrayOrRefType() instead.")

    primitiveTypeMap.getOrElse(sym, newReference(sym))
  }

  private def primitiveOrArrayOrRefType(sym: Symbol, arrtarg: Type = null): asm.Type = {
    primitiveTypeMap.get(sym) match {
      case Some(pt) => pt
      case None =>
        sym match {
          case definitions.ArrayClass => arrayOf(toTypeKind(arrtarg))
          case _ if sym.isClass       => newReference(sym)
          case _ =>
            assert(sym.isType, sym) // it must be compiling Array[a]
            ObjectReference
        }
    }
  }

  /** A simple, very very conservative, subtyping check. */
  def <:<(a: asm.Type, b: asm.Type): Boolean = {
    if(isArrayType(a)) {

      /** Array subtyping is covariant here, as in Java. Necessary for checking code that interacts with Java. */
      if(isArrayType(b))            { <:<(componentType(a), componentType(b)) }
      else if(b == AnyRefReference) { true  } // TODO: platform dependent!
      else                          { false }

    } else if(isBoxedType(a)) {

      if(isBoxedType(b))            { a == b }
      else if(b == AnyRefReference) { true   } // TODO: platform dependent!
      else                          { false  }

    } else if(isReferenceType(a)) {

      if(isNothingType(a))        { true  }
      else if(isReferenceType(b)) { classSymbol(a).tpe <:< classSymbol(b).tpe }
      else if(isArrayType(b))     { componentType(a) == NullReference }
      else                        { false }

    } else {
      (a eq b) || (a match {
        case BOOL | BYTE | SHORT | CHAR => b == INT || b == LONG
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
  def maxType(a: asm.Type, other: asm.Type): asm.Type = {
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

}
