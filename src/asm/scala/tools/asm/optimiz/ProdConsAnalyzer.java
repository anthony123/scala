/* NSC -- new Scala compiler
 * Copyright 2005-2012 LAMP/EPFL
 * @author  Martin Odersky
 */


package scala.tools.asm.optimiz;

import java.util.*;

import scala.tools.asm.Opcodes;
import scala.tools.asm.tree.*;

import scala.tools.asm.tree.analysis.Analyzer;
import scala.tools.asm.tree.analysis.AnalyzerException;
import scala.tools.asm.tree.analysis.SourceValue;
import scala.tools.asm.tree.analysis.Frame;

/**
 *  A SourceInterpreter can be used in conjunction with an Analyzer
 *  to find out, for each instruction, a Frame containing for each location P
 *  (local-var or stack-slot) the instructions that may produce the value in P.
 *
 *  Oftentimes, we want to invert that map
 *  ie we want to find all the possible consumers of values that a given instruction produces.
 *
 *  After `analyze()` has run:
 *    - consumers(insn) returns the set of instructions that may consume at least one value produced by `insn`.
 *                      "at least" because DUP produces two values.
 *    - producers(insn) returns the set of instructions that may produce at least one value consumed by `insn`.
 *
 *  Alternative terminology:
 *     - those definitions reaching insn are given by `producers(insn)`
 *
 *  This in turn allows computing:
 *      - du-chains (definition-use chains)
 *      - ud-chains (use-definition chains)
 *      - webs
 *      as covered in Sec. 8.10 of
 *        Steven S. Muchnick. Advanced compiler design and implementation.
 *        Morgan Kaufmann Publishers Inc., San Francisco, CA, USA, 1997.
 *
 *  @author  Miguel Garcia, http://lamp.epfl.ch/~magarcia/ScalaCompilerCornerReloaded/
 *  @version 1.0
 *
 */
public class ProdConsAnalyzer extends Analyzer<SourceValue> {

    public static ProdConsAnalyzer create() {
        return new ProdConsAnalyzer(new ProdConsInterpreter());
    }

    private final ProdConsInterpreter pt;

    private ProdConsAnalyzer(ProdConsInterpreter pt) {
        super(pt);
        this.pt = pt;
    }

    MethodNode mnode = null;
    Frame<SourceValue>[] frames = null;

    // ------------------------------------------------------------------------
    // utilities made available to clients
    // ------------------------------------------------------------------------

    public Frame<SourceValue>[] analyze(final String owner, final MethodNode mnode) throws AnalyzerException {
        this.mnode = mnode;
        frames = super.analyze(owner, mnode);
        return frames;
    }

    public Frame<SourceValue> frameAt(AbstractInsnNode insn) {
        int idx = mnode.instructions.indexOf(insn);
        return frames[idx];
    }

        // ------------------------------------------------------------------------
        // functionality used by DeadStoreElim
        // ------------------------------------------------------------------------

    /**
     *  The value produced by insn (if any) is "dropped" in case no non-trivial instruction consumes it.
     *  Examples of dropping are:
     *      - returning from a method with non-empty operand stack
     *      - POP
     *      - POP2
     *  This method returns whether insn has non-trivial consumers, ie those using the value for "real" computation.
     * */
    public boolean hasConsumers(final AbstractInsnNode insn) {
        Set<AbstractInsnNode> cs = pt.consumers(insn);
        Iterator<AbstractInsnNode> iter = cs.iterator();
        while(iter.hasNext()) {
            AbstractInsnNode c = iter.next();
            if(c.getOpcode() != Opcodes.POP &&
               c.getOpcode() != Opcodes.POP2) {
                return true;
            }
        }
        return false;
    }

        // ------------------------------------------------------------------------
        // functionality used by PushPopCollapser
        // ------------------------------------------------------------------------

    public boolean isSoleConsumerForItsProducers(AbstractInsnNode consumer) {
        Set<AbstractInsnNode> ps = pt.producers(consumer);
        if(ps.isEmpty()) {
            // a POP as firs instruction of an exception handler should be left as-is
            // (its distinctive feature being a lack of explicit producers, ie the exception on the stack is loaded implicitly).
            return false;
        }
        Iterator<AbstractInsnNode> iter = ps.iterator();
        while (iter.hasNext()) {
            AbstractInsnNode prod = iter.next();
            if(!hasAsSingleConsumer(prod, consumer)) {
                return false;
            }
        }
        return true;
    }

    public boolean hasAsSingleConsumer(AbstractInsnNode producer, AbstractInsnNode consumer) {
        Set<AbstractInsnNode> cs = pt.consumers(producer);
        boolean result = (cs.size() == 1) && (cs.iterator().next().equals(consumer));
        return result;
    }

    public void neutralizeStackPush(AbstractInsnNode consumer, int size) {
        Set<AbstractInsnNode> ps = pt.producers(consumer);
        assert !ps.isEmpty() : "There can't be a POP or POP2 without some other instruction pushing a value for it on the stack.";

        Iterator<AbstractInsnNode> iter = ps.iterator();
        while (iter.hasNext()) {
            AbstractInsnNode prod = iter.next();
            if(hasStackEffectOnly(prod)) {
                mnode.instructions.remove(prod);
            } else {
                mnode.instructions.insert(prod, Util.getDrop(size));
            }
        }
    }

    public boolean hasStackEffectOnly(AbstractInsnNode producer) {
        boolean result = Util.isLOAD(producer);
        result |= Util.isPrimitiveConstant(producer) || Util.isStringConstant(producer); // we leave out LDC <type> on purpose.
        result |= producer.getOpcode() == Opcodes.NEWARRAY; // array creation with primitive element type.
        // TODO check whether a NEW has no side-effects (via constructors).
        return result;
    }

    // ------------------------------------------------------------------------
    // internal methods
    // ------------------------------------------------------------------------

}
