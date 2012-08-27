package scala.tools.nsc
package backend.jvm

object BType {
  var global: scala.tools.nsc.Global = null

  def chrs = global.chrs

  // ------------- sorts -------------

  val VOID   : Int =  0
  val BOOLEAN: Int =  1
  val CHAR   : Int =  2
  val BYTE   : Int =  3
  val SHORT  : Int =  4
  val INT    : Int =  5
  val FLOAT  : Int =  6
  val LONG   : Int =  7
  val DOUBLE : Int =  8
  val ARRAY  : Int =  9
  val OBJECT : Int = 10
  val METHOD : Int = 11

  // ------------- primitive types -------------

  val VOID_TYPE    = new BType(VOID,    ('V' << 24) | (5 << 16) | (0 << 8) | 0, 1)
  val BOOLEAN_TYPE = new BType(BOOLEAN, ('Z' << 24) | (0 << 16) | (5 << 8) | 1, 1)
  val CHAR_TYPE    = new BType(CHAR,    ('C' << 24) | (0 << 16) | (6 << 8) | 1, 1)
  val BYTE_TYPE    = new BType(BYTE,    ('B' << 24) | (0 << 16) | (5 << 8) | 1, 1)
  val SHORT_TYPE   = new BType(SHORT,   ('S' << 24) | (0 << 16) | (7 << 8) | 1, 1)
  val INT_TYPE     = new BType(INT,     ('I' << 24) | (0 << 16) | (0 << 8) | 1, 1)
  val FLOAT_TYPE   = new BType(FLOAT,   ('F' << 24) | (2 << 16) | (2 << 8) | 1, 1)
  val LONG_TYPE    = new BType(LONG,    ('J' << 24) | (1 << 16) | (1 << 8) | 2, 1)
  val DOUBLE_TYPE  = new BType(DOUBLE,  ('D' << 24) | (3 << 16) | (3 << 8) | 2, 1)

  /**
   * Returns the Java type corresponding to the given type descriptor. For
   * method descriptors, buf is supposed to contain nothing more than the
   * descriptor itself.
   *
   * @param chrs a buffer containing a type descriptor.
   * @param off the offset of this descriptor in the previous buffer.
   * @return the Java type corresponding to the given type descriptor.
   */
  private def getType(off: Int): BType = {
    var len = 0
    chrs(off) match {
      case 'V' => VOID_TYPE
      case 'Z' => BOOLEAN_TYPE
      case 'C' => CHAR_TYPE
      case 'B' => BYTE_TYPE
      case 'S' => SHORT_TYPE
      case 'I' => INT_TYPE
      case 'F' => FLOAT_TYPE
      case 'J' => LONG_TYPE
      case 'D' => DOUBLE_TYPE
      case '[' =>
        len = 1
        while (chrs(off + len) == '[') {
          len += 1
        }
        if (chrs(off + len) == 'L') {
          len += 1
          while (chrs(off + len) != ';') {
            len += 1
          }
        }
        new BType(ARRAY, off, len + 1)
      case 'L' =>
        len = 1
        while (chrs(off + len) != ';') {
          len += 1
        }
        new BType(OBJECT, off + 1, len - 1)
      // case '(':
      case _ =>
        assert(chrs(off) == '(')
        var resPos = off + 1
        while(resPos != ')') { resPos += 1 }
        val resType = getType(resPos + 1)
        new BType(METHOD, off, resPos + resType.len)
    }
  }

  /** Params denote an internal name. */
  def getObjectType(index: Int, length: Int): BType = {
    val sort = if(chrs(index) == '[') ARRAY else OBJECT;
    new BType(sort, index, length)
  }

  /**
   * @param typeDescriptor a field or method type descriptor.
   */
  def getType(typeDescriptor: String): BType = {
    val n = global.newTypeName(typeDescriptor)
    getType(n.start)
  }

  /**
   * @param methodDescriptor a method descriptor.
   */
  def getMethodType(methodDescriptor: String): BType = {
    val n = global.newTypeName(methodDescriptor)
    new BType(BType.METHOD, n.start, n.length) // TODO assert isValidMethodDescriptor
  }

  /**
   * Returns the Java method type corresponding to the given argument and
   * return types.
   *
   * @param returnType the return type of the method.
   * @param argumentTypes the argument types of the method.
   * @return the Java type corresponding to the given argument and return types.
   */
  def getMethodType(returnType: BType, argumentTypes: Array[BType]): BType = {
    val n = global.newTypeName(getMethodDescriptor(returnType, argumentTypes))
    new BType(BType.METHOD, n.start, n.length)
  }

  /**
   * Returns the Java types corresponding to the argument types of method descriptor whose first argument starts at idx0.
   *
   * @param idx0 index into chrs of the first argument.
   * @return the Java types corresponding to the argument types of the given method descriptor.
   */
  def getArgumentTypes(idx0: Int): Array[BType] = {
    assert(chrs(idx0 - 1) == '(')
    var off  = idx0
    var size = 0
    var keepGoing = true
    while (keepGoing) {
      val car = chrs(off)
      off += 1
      if (car == ')') {
        keepGoing = false
      } else if (car == 'L') {
        while (chrs(off) != ';') {
          off += 1
        }
        size += 1
      } else if (car != '[') {
        size += 1;
      }
    }
    val args = new Array[BType](size)
    off = idx0
    size = 0;
    while (chrs(off) != ')') {
      args(size) = getType(off)
      off += args(size).len + (if(args(size).sort == OBJECT) 2 else 0)
      size += 1;
    }
    args
  }

  /**
   * Returns the Java types corresponding to the argument types of the given
   * method descriptor.
   *
   * @param methodDescriptor a method descriptor.
   * @return the Java types corresponding to the argument types of the given method descriptor.
   */
  def getArgumentTypes(methodDescriptor: String): Array[BType] = {
    val n = global.newTypeName(methodDescriptor)
    getArgumentTypes(n.start + 1)
  }

  /**
   * Returns the Java type corresponding to the return type of the given
   * method descriptor.
   *
   * @param methodDescriptor a method descriptor.
   * @return the Java type corresponding to the return type of the given
   *         method descriptor.
   */
  def getReturnType(methodDescriptor: String): BType = {
    val n     = global.newTypeName(methodDescriptor)
    val delta = n.pos(')') // `delta` is relative to the Name's zero-based start position, not a valid index into chrs.
    assert(delta < n.length, "not a valid method descriptor: " + methodDescriptor)
    getType(n.start + delta + 1)
  }

  /**
   * Returns the descriptor corresponding to the given argument and return
   * types.
   *
   * @param returnType the return type of the method.
   * @param argumentTypes the argument types of the method.
   * @return the descriptor corresponding to the given argument and return
   *         types.
   */
  def getMethodDescriptor(
      returnType: BType,
      argumentTypes: Array[BType]): String =
  {
    val buf = new StringBuffer()
    buf.append('(')
    var i = 0
    while(i < argumentTypes.length) {
      argumentTypes(i).getDescriptor(buf)
      i += 1
    }
    buf.append(')')
    returnType.getDescriptor(buf)
    buf.toString()
  }

}

/**
 * Based on ASM's Type class. Namer's chrs is used in this class for the same purposes as the `buf` char array in asm.Type.
 */
class BType(val sort: Int, val off: Int, val len: Int) {

  def toASMType: scala.tools.asm.Type = {
    import scala.tools.asm
    sort match {
      case BType.VOID    => asm.Type.VOID_TYPE
      case BType.BOOLEAN => asm.Type.BOOLEAN_TYPE
      case BType.CHAR    => asm.Type.CHAR_TYPE
      case BType.BYTE    => asm.Type.BYTE_TYPE
      case BType.SHORT   => asm.Type.SHORT_TYPE
      case BType.INT     => asm.Type.INT_TYPE
      case BType.FLOAT   => asm.Type.FLOAT_TYPE
      case BType.LONG    => asm.Type.LONG_TYPE
      case BType.DOUBLE  => asm.Type.DOUBLE_TYPE
      case BType.ARRAY   |
           BType.OBJECT  => asm.Type.getObjectType(getInternalName)
      case BType.METHOD  => asm.Type.getMethodType(getDescriptor)
    }
  }

    /**
     * Returns the number of dimensions of this array type. This method should
     * only be used for an array type.
     *
     * @return the number of dimensions of this array type.
     */
    def getDimensions: Int = { // TODO rename to `dimensions`
      var i = 1;
      while (BType.chrs(off + i) == '[') {
        i += 1;
      }
      i
    }

    /**
     * Returns the type of the elements of this array type. This method should
     * only be used for an array type.
     *
     * @return Returns the type of the elements of this array type.
     */
    def getElementType(): BType = {
      BType.getType(off + getDimensions)
    }

    /**
     * Returns the internal name of the class corresponding to this object or
     * array type. The internal name of a class is its fully qualified name (as
     * returned by Class.getName(), where '.' are replaced by '/'. This method
     * should only be used for an object or array type.
     *
     * @return the internal name of the class corresponding to this object type.
     */
    def getInternalName: String = {
      new String(BType.chrs, off, len)
    }

    /**
     * Returns the argument types of methods of this type. This method should
     * only be used for method types.
     *
     * @return the argument types of methods of this type.
     */
    def getArgumentTypes: Array[BType] = {
      BType.getArgumentTypes(getDescriptor) // TODO access idx directly
    }

    /**
     * Returns the return type of methods of this type. This method should only
     * be used for method types.
     *
     * @return the return type of methods of this type.
     */
    def getReturnType: BType = {
      BType.getReturnType(getDescriptor) // TODO access idx directly
    }

    // ------------------------------------------------------------------------
    // Conversion to type descriptors
    // ------------------------------------------------------------------------

    /**
     * Returns the descriptor corresponding to this Java type.
     *
     * @return the descriptor corresponding to this Java type.
     */
    def getDescriptor: String = {
      val buf = new StringBuffer()
      getDescriptor(buf)
      buf.toString()
    }

    def isPrimitiveOrVoid(): Boolean = {
      sort < BType.ARRAY;
    }

    /**
     * Appends the descriptor corresponding to this Java type to the given
     * string buffer.
     *
     * @param buf the string buffer to which the descriptor must be appended.
     */
    private def getDescriptor(buf: StringBuffer) {
        if (isPrimitiveOrVoid) {
            // descriptor is in byte 3 of 'off' for primitive types (buf == null)
            buf.append(((off & 0xFF000000) >>> 24).asInstanceOf[Char])
        } else if (sort == BType.OBJECT) {
            buf.append('L')
            buf.append(BType.chrs, off, len)
            buf.append(';')
        } else { // sort == ARRAY || sort == METHOD
            buf.append(BType.chrs, off, len)
        }
    }

    // ------------------------------------------------------------------------
    // Corresponding size and opcodes
    // ------------------------------------------------------------------------

    /**
     * Returns the size of values of this type. This method must not be used for
     * method types.
     *
     * @return the size of values of this type, i.e., 2 for <tt>long</tt> and
     *         <tt>double</tt>, 0 for <tt>void</tt> and 1 otherwise.
     */
    def getSize: Int = {
        // the size is in byte 0 of 'off' for primitive types (buf == null)
        if(isPrimitiveOrVoid) (off & 0xFF) else 1
    }

    /**
     * Returns a JVM instruction opcode adapted to this Java type. This method
     * must not be used for method types.
     *
     * @param opcode a JVM instruction opcode. This opcode must be one of ILOAD,
     *        ISTORE, IALOAD, IASTORE, IADD, ISUB, IMUL, IDIV, IREM, INEG, ISHL,
     *        ISHR, IUSHR, IAND, IOR, IXOR and IRETURN.
     * @return an opcode that is similar to the given opcode, but adapted to
     *         this Java type. For example, if this type is <tt>float</tt> and
     *         <tt>opcode</tt> is IRETURN, this method returns FRETURN.
     */
    def getOpcode(opcode: Int): Int = {
      import scala.tools.asm.Opcodes
      if (opcode == Opcodes.IALOAD || opcode == Opcodes.IASTORE) {
        // the offset for IALOAD or IASTORE is in byte 1 of 'off' for
        // primitive types (buf == null)
        opcode + (if(isPrimitiveOrVoid) (off & 0xFF00) >> 8 else 4)
      } else {
        // the offset for other instructions is in byte 2 of 'off' for
        // primitive types (buf == null)
        opcode + (if (isPrimitiveOrVoid) (off & 0xFF0000) >> 16 else 4)
      }
    }

    // ------------------------------------------------------------------------
    // Equals, hashCode and toString
    // ------------------------------------------------------------------------

    /**
     * Tests if the given object is equal to this type.
     *
     * @param o the object to be compared to this type.
     * @return <tt>true</tt> if the given object is equal to this type.
     */
    override def equals(o: Any): Boolean = {
      if (!(o.isInstanceOf[BType])) {
        return false
      }
      val t = o.asInstanceOf[BType]
      if (this eq t) {
        return true
      }
      if (sort != t.sort) {
        return false
      }
      if (sort >= BType.ARRAY) {
        if (len != t.len) {
          return false
        }
        // sort checked already
        if (off == t.off) {
          return true
        }
        var i = 0
        while(i < len) {
          if (BType.chrs(off + i) != BType.chrs(t.off + i)) {
            return false
          }
          i += 1
        }
        // If we reach here, we could update the largest of (this.off, t.off) to match the other, so as to simplify future == comparisons.
        // But that would require a var rather than val.
      }
      true
    }

    /**
     * Returns a hash code value for this type.
     *
     * @return a hash code value for this type.
     */
    override def hashCode(): Int = {
      var hc = 13 * sort;
      if (sort >= BType.ARRAY) {
        var i = off
        val end = i + len
        while (i < end) {
          hc = 17 * (hc + BType.chrs(i))
          i += 1
        }
      }
      hc
    }

    /**
     * Returns a string representation of this type.
     *
     * @return the descriptor of this type.
     */
    override def toString: String = { getDescriptor }

}
