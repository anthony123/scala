/* NSC -- new Scala compiler
 * Copyright 2005-2012 LAMP/EPFL
 * @author  Martin Odersky
 */

package scala.tools.asm.optimiz;

import java.util.List;

import scala.tools.asm.Opcodes;
import scala.tools.asm.Type;
import scala.tools.asm.tree.MethodNode;
import scala.tools.asm.tree.AbstractInsnNode;
import scala.tools.asm.tree.InvokeDynamicInsnNode;
import scala.tools.asm.tree.MethodInsnNode;
import scala.tools.asm.tree.JumpInsnNode;
import scala.tools.asm.tree.LabelNode;
import scala.tools.asm.tree.InsnNode;
import scala.tools.asm.tree.VarInsnNode;
import scala.tools.asm.tree.InsnList;
import scala.tools.asm.tree.IntInsnNode;
import scala.tools.asm.tree.LdcInsnNode;

import scala.tools.asm.tree.analysis.AnalyzerException;
import scala.tools.asm.tree.analysis.Analyzer;
import scala.tools.asm.tree.analysis.Frame;
import scala.tools.asm.tree.analysis.Value;
import scala.tools.asm.tree.analysis.Interpreter;

/**
 *  This method transformer uses a custom interpreter that propagates primitive constants (over copy operations).
 *  With that information, this transformer:
 *    (a) replaces an operation taking constant inputs by a load of the result (the inputs are dropped).
 *    (b) simplifies control flow when possible.
 *
 *  Information about nullness is not propagated. For that, use NullnessPropagator.
 *
 *  @author  Miguel Garcia, http://lamp.epfl.ch/~magarcia/ScalaCompilerCornerReloaded/
 *  @version 1.0
 */
public class ConstantFolder {

    /** after transform() has run, this field records whether
     *  at least one pass of this transformer modified something. */
    public boolean changed = false;

    private UnreachableCode unreachCodeRemover = new UnreachableCode();

    public void transform(final String owner, final MethodNode mnode) throws AnalyzerException {

        Analyzer<CFValue> propag = new Analyzer<CFValue>(new ConstantInterpreter());
        propag.analyze(owner, mnode);

        Frame<CFValue>[] frames = propag.getFrames();
        AbstractInsnNode[] insns = mnode.instructions.toArray();

        changed = false;

        int i = 0;
        while(i < insns.length) {

            Frame<CFValue>   frame = frames[i];
            AbstractInsnNode insn  = insns[i];

            CFValue value1   = null;
            CFValue value2   = null;
            boolean succeeds = false;

            int opc = insns[i].getOpcode();
            switch (opc) {

                case Opcodes.IFEQ:
                case Opcodes.IFNE:
                case Opcodes.IFLT:
                case Opcodes.IFGE:
                case Opcodes.IFGT:
                case Opcodes.IFLE:
                    if(frame.getStackTop().isConstant()) {
                        ICst ic = (ICst) frame.getStackTop();
                        switch (opc) {
                            case Opcodes.IFEQ: succeeds = ic.v == 0; break;
                            case Opcodes.IFNE: succeeds = ic.v != 0; break;
                            case Opcodes.IFLT: succeeds = ic.v  < 0; break;
                            case Opcodes.IFGE: succeeds = ic.v >= 0; break;
                            case Opcodes.IFGT: succeeds = ic.v  > 0; break;
                            case Opcodes.IFLE: succeeds = ic.v <= 0; break;
                        }
                        InsnList is = dropAndJump(1, succeeds, ((JumpInsnNode) insn).label);
                        mnode.instructions.insert(insn, is);
                        mnode.instructions.remove(insn);
                        changed = true;
                    }
                    break;

                case Opcodes.IF_ICMPEQ:
                case Opcodes.IF_ICMPNE:
                case Opcodes.IF_ICMPLT:
                case Opcodes.IF_ICMPGE:
                case Opcodes.IF_ICMPGT:
                case Opcodes.IF_ICMPLE:
                    value2 = frame.getStackTop();
                    value1 = frame.peekDown(1);
                    if(value1.isConstant() && value2.isConstant()) {
                        ICst i1 = (ICst) value1;
                        ICst i2 = (ICst) value2;
                        switch (opc) {
                            case Opcodes.IF_ICMPEQ: succeeds = i1.v == i2.v; break;
                            case Opcodes.IF_ICMPNE: succeeds = i1.v != i2.v; break;
                            case Opcodes.IF_ICMPLT: succeeds = i1.v  < i2.v; break;
                            case Opcodes.IF_ICMPGE: succeeds = i1.v >= i2.v; break;
                            case Opcodes.IF_ICMPGT: succeeds = i1.v  > i2.v; break;
                            case Opcodes.IF_ICMPLE: succeeds = i1.v <= i2.v; break;
                        }
                        InsnList is = dropAndJump(2, succeeds, ((JumpInsnNode) insn).label);
                        mnode.instructions.insert(insn, is);
                        mnode.instructions.remove(insn);
                        changed = true;
                    }
                    break;

                case Opcodes.TABLESWITCH:
                case Opcodes.LOOKUPSWITCH:
                    if(frame.getStackTop().isConstant()) {
                        ICst ic = (ICst) frame.getStackTop();
                        switch (opc) {
                            case Opcodes.TABLESWITCH:  break;
                            case Opcodes.LOOKUPSWITCH: break;
                        }
                        // TODO pop and jump or just pop, changed = true;
                    }
                    break;

                default:
                    ;

            }

            i += 1;
        }

        if(changed) {
            // UnreachableCode eliminates null frames (which complicate further analyses).
            unreachCodeRemover.transform(owner, mnode);
        }

    }

    private InsnList dropAndJump(final int drops, final boolean takeTheJump, LabelNode label) {
        assert drops == 1 || drops == 2;
        InsnNode d  = new InsnNode(Opcodes.POP);
        InsnList is = new InsnList();
        is.add(d);
        if(drops == 2) {
           is.add(new InsnNode(Opcodes.POP));
        }
        if(takeTheJump) {
            is.add(new JumpInsnNode(Opcodes.GOTO, label));
        }
        return is;
    }

    static private abstract class CFValue implements Value {

        protected final int size;

        public CFValue(int size) {
            this.size = size;
        }

        @Override
        final public int getSize() { return size; }

        public boolean isConstant() { return false; }

        final public boolean isUnknown() { return !isConstant(); } // we have just one class of "unknowns" (as opposed to e.g. LessThanZero, etc.)

        public abstract CFValue convI();
        public abstract CFValue convF();
        public abstract CFValue convJ();
        public abstract CFValue convD();

        public abstract CFValue iinc();
        public abstract CFValue neg();

        public abstract CFValue add(CFValue value2);
        public abstract CFValue sub(CFValue value2);
        public abstract CFValue mul(CFValue value2);
        public abstract CFValue div(CFValue value2);

        public abstract CFValue and(CFValue value2);
        public abstract CFValue or (CFValue value2);

        public abstract boolean equals(final Object value);
        public abstract int hashCode();

    } // end of nested class CFValue

    final static private class Unknown extends CFValue {

        static public Unknown UNKNOWN_1 = new Unknown(1);

        static public Unknown UNKNOWN_2 = new Unknown(2);

        public Unknown(int size) {
            super(size);
        }

        @Override public Unknown convI() { return Unknown.UNKNOWN_1; }
        @Override public Unknown convF() { return Unknown.UNKNOWN_1; }
        @Override public Unknown convJ() { return Unknown.UNKNOWN_2; }
        @Override public Unknown convD() { return Unknown.UNKNOWN_2; }

        @Override public Unknown iinc() { return this; }
        @Override public Unknown neg()  { return this; }

        @Override public Unknown add(CFValue value2) { assert size == value2.size; return this; }
        @Override public Unknown sub(CFValue value2) { assert size == value2.size; return this; }
        @Override public Unknown mul(CFValue value2) { assert size == value2.size; return this; } // TODO times integral zero return a zero of that size
        @Override public Unknown div(CFValue value2) { assert size == value2.size; return this; }

        @Override public CFValue and(CFValue value2) {
            assert size == value2.size;
            CFValue result = this;
            if(value2.isConstant()) {
                if(value2 instanceof ICst) {
                    ICst that = (ICst)value2;
                    if(that.v == 0) {
                        result = that;
                    }
                } else if(value2 instanceof JCst) {
                    JCst that = (JCst)value2;
                    if(that.v == 0L) {
                        result = that;
                    }
                }
            }
            return result;
        }
        @Override public CFValue or (CFValue value2) {
            assert size == value2.size;
            CFValue result = this;
            if(value2.isConstant()) {
                if(value2 instanceof ICst) {
                    ICst that = (ICst)value2;
                    if(that.v == 0xFFFFFFFF) {
                        result = that;
                    }
                } else if(value2 instanceof JCst) {
                    JCst that = (JCst)value2;
                    if(that.v == 0xFFFFFFFFFFFFFFFFL) {
                        result = that;
                    }
                }
            }
            return result;
        }

        @Override public boolean equals(final Object value) { return this == value; }
        @Override public int hashCode() { return size; }

    } // end of nested class Unknown

    static private abstract class Constant extends CFValue {

        public Constant(int size) {
            super(size);
        }

        @Override
        public boolean isConstant() { return true; }

    } // end of nested class Constant


    final static private class ICst extends Constant {

        private final int sort;
        private final int v;

        public ICst(final char c) {
            super(1);
            this.sort = Type.CHAR;
            this.v    = c;
        }

        public ICst(final byte b) {
            super(1);
            this.sort = Type.BYTE;
            this.v    = b;
        }

        public ICst(final short s) {
            super(1);
            this.sort = Type.SHORT;
            this.v    = s;
        }

        public ICst(final int i) {
            super(1);
            this.sort = Type.INT;
            this.v    = i;
        }

        @Override public ICst convI() { return this;                      }
        @Override public FCst convF() { return new FCst((float)  this.v); }
        @Override public JCst convJ() { return new JCst((long)   this.v); }
        @Override public DCst convD() { return new DCst((double) this.v); }

        @Override public ICst iinc()  { return new ICst(v + 1); }
        @Override public ICst neg()   { return new ICst(-v); }

        @Override public CFValue add(CFValue value2) {
            assert size == value2.size;
            if(v == 0) {
                return value2;
            } else if(value2.isUnknown()) {
                return value2;
            } else {
                ICst that = (ICst) value2;
                return new ICst(v + that.v);
            }
        }
        @Override public CFValue sub(CFValue value2) {
            assert size == value2.size;
            if(value2.isUnknown()) {
                return value2;
            } else {
                ICst that = (ICst) value2;
                return new ICst(v - that.v);
            }
        }
        @Override public CFValue mul(CFValue value2) {
            assert size == value2.size;
            if(v == 0) {
                return this;
            } else if(v == 1) {
                return value2;
            } else if(value2.isUnknown()) {
                return value2;
            } else {
                ICst that = (ICst) value2;
                return new ICst(v * that.v);
            }
        }
        @Override public CFValue div(CFValue value2) {
            assert size == value2.size;
            if(value2.isUnknown()) {
                return value2;
            } else {
                ICst that = (ICst) value2;
                if(that.v == 0) { return Unknown.UNKNOWN_1; }
                else { return new ICst(v / that.v); }
            }
        }

        @Override public CFValue and(CFValue value2) {
            assert size == value2.size;
            CFValue result = Unknown.UNKNOWN_1;
            if(v == 0) {
                result = this;
            } else if(value2.isConstant()) {
                ICst that = (ICst)value2;
                result = new ICst(v & that.v);
            }
            return result;
        }
        @Override public CFValue or(CFValue value2) {
            assert size == value2.size;
            CFValue result = Unknown.UNKNOWN_1;
            if(v == 0xFFFFFFFF) {
                result = this;
            } else if(value2.isConstant()) {
                ICst that = (ICst)value2;
                result = new ICst(v | that.v);
            }
            return result;
        }

        @Override
        public boolean equals(final Object value) {
            if (!(value instanceof ICst)) {
                return false;
            }
            ICst that = (ICst) value;
            // basing ICst equality con comparing v's means we have to keep v's representing booleans, bytes, shorts, and chars in "canonical form"
            // for example, for sort == Type.CHAR, IINC shouldn't increase v past 0xffff (otherwise equals() with another ICst representing the same Char might fail).
            return (sort == that.sort) && (v == that.v);
        }

        @Override
        public int hashCode() {
            return sort + v;
        }

    } // end of nested class ICst

    final static private class FCst extends Constant {

        private final int   sort;
        private final float v;

        public FCst(final float f) {
            super(1);
            this.sort = Type.FLOAT;
            this.v    = f;
        }

        @Override public ICst convI() { return new ICst((int)    this.v); }
        @Override public FCst convF() { return this;                      }
        @Override public JCst convJ() { return new JCst((long)   this.v); }
        @Override public DCst convD() { return new DCst((double) this.v); }

        @Override public FCst iinc()  { throw new UnsupportedOperationException(); }
        @Override public FCst neg()   { return new FCst(-v); }

        @Override public CFValue add(CFValue value2) {
            assert size == value2.size;
            // we don't try to guess addition of positive vs negative zero and unknown, just return unknown.
            if(value2.isUnknown()) {
                return value2;
            } else {
                FCst that = (FCst) value2;
                return new FCst(v + that.v);
            }
        }
        @Override public CFValue sub(CFValue value2) {
            assert size == value2.size;
            // we don't try to guess subtraction of positive vs negative zero and unknown, just return unknown.
            if(value2.isUnknown()) {
                return value2;
            } else {
                FCst that = (FCst) value2;
                return new FCst(v - that.v);
            }
        }
        @Override public CFValue mul(CFValue value2) {
            assert size == value2.size;
            if(v == 0f) {
                return this;
            } else if(v == 1f) {
                return value2;
            } else if(value2.isUnknown()) {
                return value2;
            } else {
                FCst that = (FCst) value2;
                return new FCst(v * that.v);
            }
        }
        /**
         * Quoting from the JVMS:
         *   Despite the fact that overflow, underflow, division by zero, or loss of precision may occur,
         *   execution of an fdiv instruction never throws a runtime exception.
         */
        @Override public CFValue div(CFValue value2) {
            assert size == value2.size;
            if(value2.isUnknown()) {
                return value2;
            } else {
                FCst that = (FCst) value2;
                return new FCst(v / that.v);
            }
        }

        @Override public CFValue and(CFValue value2) { throw new UnsupportedOperationException(); }
        @Override public CFValue or(CFValue value2)  { throw new UnsupportedOperationException(); }

        @Override
        public boolean equals(final Object value) {
            if (!(value instanceof FCst)) {
                return false;
            }
            FCst that = (FCst) value;
            return (sort == that.sort) && (v == that.v);
        }

        @Override
        public int hashCode() {
            return java.lang.Float.floatToIntBits(v);
        }

    } // end of nested class FCst

    final static private class JCst extends Constant {

        private final int   sort;
        private final long  v;

        public JCst(final long j) {
            super(2);
            this.sort = Type.LONG;
            this.v    = j;
        }

        @Override public ICst convI() { return new ICst((int)    this.v); }
        @Override public FCst convF() { return new FCst((float)  this.v); }
        @Override public JCst convJ() { return this;                      }
        @Override public DCst convD() { return new DCst((double) this.v); }

        @Override public JCst iinc()  { throw new UnsupportedOperationException(); }
        @Override public JCst neg()   { return new JCst(-v); }

        @Override public CFValue add(CFValue value2) {
            assert size == value2.size;
            if(v == 0L) {
                return value2;
            } else if(value2.isUnknown()) {
                return value2;
            } else {
                JCst that = (JCst) value2;
                return new JCst(v + that.v);
            }
        }
        @Override public CFValue sub(CFValue value2) {
            assert size == value2.size;
            if(value2.isUnknown()) {
                return value2;
            } else {
                JCst that = (JCst) value2;
                return new JCst(v - that.v);
            }
        }
        @Override public CFValue mul(CFValue value2) {
            assert size == value2.size;
            if(v == 0L) {
                return this;
            } else if(v == 1L) {
                return value2;
            } else if(value2.isUnknown()) {
                return value2;
            } else {
                JCst that = (JCst) value2;
                return new JCst(v * that.v);
            }
        }
        @Override public CFValue div(CFValue value2) {
            assert size == value2.size;
            if(value2.isUnknown()) {
                return value2;
            } else {
                JCst that = (JCst) value2;
                if(that.v == 0L) { return Unknown.UNKNOWN_2; }
                else { return new JCst(v / that.v); }
            }
        }

        @Override public CFValue and(CFValue value2) {
            assert size == value2.size;
            CFValue result = Unknown.UNKNOWN_2;
            if(v == 0) {
                result = this;
            } else if(value2.isConstant()) {
                JCst that = (JCst)value2;
                result = new JCst(v & that.v);
            }
            return result;
        }
        @Override public CFValue or(CFValue value2) {
            assert size == value2.size;
            CFValue result = Unknown.UNKNOWN_2;
            if(v == 0xFFFFFFFFFFFFFFFFL) {
                result = this;
            } else if(value2.isConstant()) {
                JCst that = (JCst)value2;
                result = new JCst(v | that.v);
            }
            return result;
        }

        @Override
        public boolean equals(final Object value) {
            if (!(value instanceof JCst)) {
                return false;
            }
            JCst that = (JCst) value;
            return (sort == that.sort) && (v == that.v);
        }

        @Override
        public int hashCode() {
            return (int)v;
        }

    } // end of nested class JCst

    static private class DCst extends Constant {

        private final int    sort;
        private final double v;

        public DCst(final double d) {
            super(2);
            this.sort = Type.DOUBLE;
            this.v    = d;
        }

        @Override public ICst convI() { return new ICst((int)    this.v); }
        @Override public FCst convF() { return new FCst((float)  this.v); }
        @Override public JCst convJ() { return new JCst((long)   this.v); }
        @Override public DCst convD() { return this;                      }

        @Override public DCst iinc()  { throw new UnsupportedOperationException(); }
        @Override public DCst neg()   { return new DCst(-v); }

        @Override public CFValue add(CFValue value2) {
            assert size == value2.size;
            // we don't try to guess addition of positive vs negative zero and unknown, just return unknown.
            if(value2.isUnknown()) {
                return value2;
            } else {
                DCst that = (DCst) value2;
                return new DCst(v + that.v);
            }
        }
        @Override public CFValue sub(CFValue value2) {
            assert size == value2.size;
            // we don't try to guess subtraction of positive vs negative zero and unknown, just return unknown.
            if(value2.isUnknown()) {
                return value2;
            } else {
                DCst that = (DCst) value2;
                return new DCst(v - that.v);
            }
        }
        @Override public CFValue mul(CFValue value2) {
            assert size == value2.size;
            if(v == 0d) {
                return this;
            } else if(v == 1d) {
                return value2;
            } else if(value2.isUnknown()) {
                return value2;
            } else {
                DCst that = (DCst) value2;
                return new DCst(v * that.v);
            }
        }
        /**
         * Quoting from the JVMS:
         *   Despite the fact that overflow, underflow, division by zero, or loss of precision may occur,
         *   execution of an fdiv instruction never throws a runtime exception.
         */
        @Override public CFValue div(CFValue value2) {
            assert size == value2.size;
            if(value2.isUnknown()) {
                return value2;
            } else {
                DCst that = (DCst) value2;
                return new DCst(v / that.v);
            }
        }

        @Override public CFValue and(CFValue value2) { throw new UnsupportedOperationException(); }
        @Override public CFValue or(CFValue value2)  { throw new UnsupportedOperationException(); }

        @Override
        public boolean equals(final Object value) {
            if (!(value instanceof DCst)) {
                return false;
            }
            DCst that = (DCst) value;
            return (sort == that.sort) && (v == that.v);
        }

        @Override
        public int hashCode() {
            return (int)java.lang.Double.doubleToLongBits(v);
        }

    } // end of nested class DCst

    static public class ConstantInterpreter extends SizingInterpreter<CFValue> {

        public ConstantInterpreter() {
            super(ASM4);
        }

        protected ConstantInterpreter(final int api) {
            super(api);
        }

        private CFValue dunno(int size) {
            if(size == 0) {
                return null;
            }
            return (size == 1) ? Unknown.UNKNOWN_1 : Unknown.UNKNOWN_2;
        }

        @Override
        public CFValue newValue(final Type type) {
            if (type == Type.VOID_TYPE) {
                return null;
            }
            return dunno(type == null ? 1 : type.getSize());
        }

        static public ICst bconst(int b)     { return new ICst((byte)  b); }
        static public ICst sconst(int s)     { return new ICst((short) s); }
        static public ICst iconst(int i)     { return new ICst(i);         }

        static public FCst fconst(float  f)  { return new FCst(f); }
        static public JCst jconst(long   j)  { return new JCst(j); }
        static public DCst dconst(double d)  { return new DCst(d); }

        /**
         * ACONST_NULL,
         * ICONST_M1, ICONST_0, ICONST_1, ICONST_2, ICONST_3, ICONST_4, ICONST_5,
         * LCONST_0, LCONST_1,
         * FCONST_0, FCONST_1, FCONST_2,
         * DCONST_0, DCONST_1,
         * BIPUSH,
         * SIPUSH,
         * LDC
         */
        @Override
        public CFValue newOperation(final AbstractInsnNode insn) throws AnalyzerException {
            int opc = insn.getOpcode();
            switch (opc) {

                case ACONST_NULL:
                    return Unknown.UNKNOWN_1; // use NullnessPropagator instead

                case ICONST_M1:
                    return iconst(-1);

                case ICONST_0:
                case ICONST_1:
                case ICONST_2:
                case ICONST_3:
                case ICONST_4:
                case ICONST_5:
                    return iconst(opc - ICONST_0);

                case LCONST_0:
                case LCONST_1:
                    return jconst(opc - LCONST_0);

                case FCONST_0:
                case FCONST_1:
                case FCONST_2:
                    return fconst(opc - FCONST_0);

                case DCONST_0:
                case DCONST_1:
                    return dconst(opc - DCONST_0);

                case BIPUSH:
                    return bconst(((IntInsnNode) insn).operand);

                case SIPUSH:
                    return sconst(((IntInsnNode) insn).operand);

                case LDC:
                    Object cst = ((LdcInsnNode) insn).cst;
                    if (cst instanceof Integer) {
                        return iconst(((Integer) cst).intValue());
                    } else if (cst instanceof Float) {
                        return fconst(((Float) cst).floatValue());
                    } else if (cst instanceof Long) {
                        return jconst(((Long) cst).longValue());
                    } else if (cst instanceof Double) {
                        return dconst(((Double) cst).doubleValue());
                    } else {
                        return dunno(getResultSize(insn));
                    }

                default:
                    return dunno(getResultSize(insn));
            }
        }

        /**
         * Propagates the input value through LOAD, STORE, DUP, and SWAP instructions.
         */
        @Override
        public CFValue copyOperation(final AbstractInsnNode insn, final CFValue value) {
            return value;
        }

        /**
         *  INEG, LNEG, FNEG, DNEG,
         *  IINC,
         *       I2L, I2F, I2D,
         *  L2I,      L2F, L2D,
         *  F2I, F2L,      F2D,
         *  D2I, D2L, D2F,
         *  I2B, I2C, I2S
         */
        @Override
        public CFValue unaryOperation(final AbstractInsnNode insn, final CFValue value) throws AnalyzerException {
            switch (insn.getOpcode()) {
                case INEG:
                case FNEG:
                case LNEG:
                case DNEG:
                    return value.neg();

                case IINC:
                    return value.iinc();

                case I2B:
                case I2C:
                case I2S:
                    if(value instanceof ICst) {
                        ICst ic = (ICst)value;
                        switch (insn.getOpcode()) {
                            case I2B: return new ICst((byte)  ic.v);
                            case I2C: return new ICst((char)  ic.v);
                            case I2S: return new ICst((short) ic.v);
                        }
                    } else {
                        return dunno(getResultSize(insn));
                    }

                case F2I:
                case L2I:
                case D2I:
                    return value.convI();

                case I2F:
                case L2F:
                case D2F:
                    return value.convF();

                case I2L:
                case F2L:
                case D2L:
                    return value.convJ();

                case I2D:
                case F2D:
                case L2D:
                    return value.convD();

                default:
                    return dunno(getResultSize(insn));
            }
        }

        /**
         * IADD, LADD, FADD, DADD,
         * ISUB, LSUB, FSUB, DSUB,
         * IMUL, LMUL, FMUL, DMUL,
         * IDIV, LDIV, FDIV, DDIV,
         * IREM, LREM, FREM, DREM,
         * ISHL, LSHL,
         * ISHR, LSHR,
         * IUSHR, LUSHR,
         * IAND, LAND,
         * IOR, LOR,
         * IXOR, LXOR,
         * LCMP,
         * FCMPL, FCMPG,
         * DCMPL, DCMPG,
         */
        @Override
        public CFValue binaryOperation(
            final AbstractInsnNode insn,
            final CFValue value1,
            final CFValue value2) throws AnalyzerException {
            switch (insn.getOpcode()) {
                case IADD:
                case FADD:
                case LADD:
                case DADD:
                    return value1.add(value2);

                case ISUB:
                case FSUB:
                case LSUB:
                case DSUB:
                    return value1.sub(value2);

                case IMUL:
                case FMUL:
                case LMUL:
                case DMUL:
                    return value1.mul(value2);

                case IDIV:
                case FDIV:
                case LDIV:
                case DDIV:
                    return value1.div(value2);

                case IREM:
                case FREM:
                case LREM:
                case DREM:
                    return dunno(getResultSize(insn)); // TODO return value1.REM(value2);

                case IAND:
                case LAND:
                    return value1.and(value2);

                case IOR:
                case LOR:
                    return value1.or(value2);

                case IXOR:
                case LXOR:
                    return dunno(getResultSize(insn)); // TODO return value1.XOR(value2);

                case ISHL:
                case LSHL:
                    return dunno(getResultSize(insn)); // TODO return value1.SHL(value2);

                case ISHR:
                case LSHR:
                    return dunno(getResultSize(insn)); // TODO return value1.SHR(value2);

                case IUSHR:
                case LUSHR:
                    return dunno(getResultSize(insn)); // TODO return value1.USHR(value2);

                case LCMP:
                    if(value1.isUnknown() || value2.isUnknown()) {
                        return Unknown.UNKNOWN_1;
                    } else {
                        JCst j1 = (JCst)value1;
                        JCst j2 = (JCst)value2;
                             if(j1.v >  j2.v) { return new ICst( 1); }
                        else if(j1.v == j2.v) { return new ICst( 0); }
                        else                  { return new ICst(-1); }
                    }

                case FCMPL:
                case DCMPL:
                    return dunno(getResultSize(insn)); // TODO return value1.CMPL(value2);

                case FCMPG:
                case DCMPG:
                    return dunno(getResultSize(insn)); // TODO return value1.CMPG(value2);

                default:
                    return dunno(getResultSize(insn));
            }
        }

        @Override
        public CFValue ternaryOperation(
            final AbstractInsnNode insn,
            final CFValue value1,
            final CFValue value2,
            final CFValue value3) throws AnalyzerException {
            return dunno(getResultSize(insn));
        }

        @Override
        public CFValue naryOperation(final AbstractInsnNode insn, final List<? extends CFValue> values) throws AnalyzerException {
            // TODO any calls to the Scala runtime for which we know it returns a primitive constant, given its arguments?
            return dunno(getResultSize(insn));
        }

        @Override
        public void returnOperation(AbstractInsnNode insn, CFValue value, CFValue expected) throws AnalyzerException {
        }

        @Override
        public CFValue merge(final CFValue d, final CFValue w) {
            if(d == w) { return d; }
            assert d.size == w.size;
            if(d.isUnknown() || w.isUnknown()) {
                return dunno(d.size);
            }
            if (d.equals(w)) { return d; }
            else { return dunno(d.size); }
        }

    } // end of nested class ConstantInterpreter


} // end of class ConstantPropagator