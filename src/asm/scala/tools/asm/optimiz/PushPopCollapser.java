/* NSC -- new Scala compiler
 * Copyright 2005-2012 LAMP/EPFL
 * @author  Martin Odersky
 */


package scala.tools.asm.optimiz;

import scala.tools.asm.*;
import scala.tools.asm.tree.*;

import scala.tools.asm.tree.analysis.AnalyzerException;

import java.util.*;

/**
 *  Some transformations (eg DeadStoreElim) mark computations as redundant by inserting DROP instructions to discard computed values.
 *
 *  This transformation starts from there by removing those (producer, consumer) pairs where
 *  the consumer is a DROP and the producer has its value consumed only by the DROP in question.
 *  (More general cases are possible, but the above covers the inlining scenario).
 *
 *  @author  Miguel Garcia, http://lamp.epfl.ch/~magarcia/ScalaCompilerCornerReloaded/
 *  @version 1.0
 *
 */
public class PushPopCollapser {

    private ProdConsAnalyzer cp = null;
    private MethodNode mnode = null;

    /** after transform() has run, this field records whether
     *  at least one pass of this transformer modified something. */
    public boolean changed = false;

    public void transform(final String owner, final MethodNode mnode) throws AnalyzerException {

        this.mnode = mnode;

        changed = false;
        boolean keepGoing = false;

        final Set<AbstractInsnNode> skipExam = new HashSet<AbstractInsnNode>();

        do {

            keepGoing = false;

            // compute the produce-consume relation (ie values flow from "producer" instructions to "consumer" instructions).
            this.cp = ProdConsAnalyzer.create();
            this.cp.analyze(owner, mnode);

            final Iterator<AbstractInsnNode> iter = mnode.instructions.iterator();

            while(iter.hasNext()) {
                final AbstractInsnNode current = iter.next();
                if(current != null && Util.isDROP(current) && !skipExam.contains(current)) {
                    final InsnNode drop = (InsnNode) current;
                    final Set<AbstractInsnNode> producers = cp.producers(drop);
                    final boolean isElidable = (
                        cp.isSoleConsumerForItsProducers(drop) &&
                        !isAlreadyMinimized(producers, drop)
                    );
                    if (isElidable) {
                        int size = (drop.getOpcode() == Opcodes.POP ? 1 : 2);
                        neutralizeStackPush(producers, size);
                        mnode.instructions.remove(drop);
                        keepGoing = true;
                    } else {
                        skipExam.add(drop);
                    }
                }
            }

            changed = (changed || keepGoing);

        } while(keepGoing);

    }

    private boolean isAlreadyMinimized(final Set<AbstractInsnNode> producers, InsnNode drop) {
        if(producers.size() == 1) {
            AbstractInsnNode singleProd = producers.iterator().next();
            if(singleProd.getNext() == drop && !canSimplify(singleProd)) {
                return true;
            }
        }
        return false;
    }

    /**
     *  All we know about the "producer" instructions is each pushes a value we don't need onto the stack,
     *  while we still need any side-effects producers might have.
     *
     *  A blanket way to "neutralize stack push" of an instruction involves inserting a POP or POP2 right after it.
     *
     *  That's what we do unless a special case is detected. For example, for IADD shorter code is emitted
     *  by replacing IADD with two POP instructions (with the added benefit that
     *  follow-up passes will in turn neutralize their producers, and so on).
     *
     */
    private void neutralizeStackPush(final Set<AbstractInsnNode> producers, final int size) {
        assert !producers.isEmpty() : "There can't be a POP or POP2 without some other instruction pushing a value for it on the stack.";

        final Iterator<AbstractInsnNode> iter = producers.iterator();
        while (iter.hasNext()) {

            final AbstractInsnNode prod = iter.next();
            final int opc = prod.getOpcode();

            if(Util.hasPushEffectOnly(prod) || SSLUtil.isSideEffectFreeGETSTATIC(prod)) {

                // remove altogether the instruction that pushes.
                mnode.instructions.remove(prod);

            } else if(SSLUtil.isSideEffectFreeCall(prod)) {

                // replace the call-instruction that pushes with as many DROPs as arguments it expects on the stack.
                MethodInsnNode mi = (MethodInsnNode) prod;
                Type[] argTs = Type.getArgumentTypes(mi.desc);
                for(int argIdx = 0; argIdx < argTs.length; argIdx++) {
                    mnode.instructions.insert(prod, Util.getDrop(argTs[argIdx].getSize()));
                }
                switch (opc) {
                    case Opcodes.INVOKEINTERFACE:
                    case Opcodes.INVOKESPECIAL:
                    case Opcodes.INVOKEVIRTUAL:
                        mnode.instructions.insert(prod, Util.getDrop(1));
                        break;
                    default:
                        break;
                }
                mnode.instructions.remove(prod);

            } else {

                // leave in place the instruction that pushes, add a DROP right after it.
                mnode.instructions.insert(prod, Util.getDrop(size));

            }
        }
    }

    private boolean canSimplify(AbstractInsnNode producer) {
        return Util.hasPushEffectOnly(producer) || SSLUtil.isSideEffectFree(producer);
    }

}
