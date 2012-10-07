/* NSC -- new Scala compiler
 * Copyright 2005-2012 LAMP/EPFL
 * @author  Martin Odersky
 */

package scala.tools.asm.optimiz;

import static scala.tools.asm.Opcodes.ATHROW;
import static scala.tools.asm.Opcodes.GOTO;
import static scala.tools.asm.Opcodes.IRETURN;
import static scala.tools.asm.Opcodes.RETURN;

import java.util.*;

import scala.tools.asm.tree.AbstractInsnNode;
import scala.tools.asm.tree.InsnList;
import scala.tools.asm.tree.JumpInsnNode;
import scala.tools.asm.tree.LabelNode;
import scala.tools.asm.tree.MethodNode;

/**
 *  Replaces:
 *    (1) a jump to a GOTO label instruction with a jump to label, and
 *    (2) a GOTO to a method-return instruction (whether IRETURN, ..., RETURN, or ATHROW)
 *        with a clone of that method-return instruction.
 *
 *  For example, the following chain of "jump-only" blocks:
 *
 *          JUMP b1;
 *      b1: JUMP b2;
 *      b2: JUMP ... etc.
 *
 *  In particular, it handles "lassos"
 *
 *          JUMP b1;
 *      b1: JUMP b2;
 *      b2: JUMP b1;
 *
 *  is collapsed by making the start of the chain target directly the "final destination".
 *  Even if covered by an exception handler, a "non-self-loop jump-only block" can always be removed.
 *
 *  @author  Miguel Garcia, http://lamp.epfl.ch/~magarcia/ScalaCompilerCornerReloaded/
 */
public class JumpChainsCollapser extends MethodTransformer {

    public JumpChainsCollapser(final MethodTransformer mt) {
        super(mt);
    }

    public void transform(final MethodNode mn) {
        InsnList insns = mn.instructions;
        Iterator<AbstractInsnNode> i = insns.iterator();
        while (i.hasNext()) {
            AbstractInsnNode insn = i.next();
            if (insn instanceof JumpInsnNode) {
                JumpInsnNode source = (JumpInsnNode) insn;
                LabelNode finalDest = finalDestLabel(source);
                source.label = finalDest;
                if (source.getOpcode() == GOTO) {
                    AbstractInsnNode target = insnLabelledBy(finalDest);
                    int op = target.getOpcode();
                    if ((op >= IRETURN && op <= RETURN) || op == ATHROW) {
                        insns.set(source, target.clone(null));
                    }
                }
            }
        }
        super.transform(mn);
    }

    /**
     *  Returns the executable instruction (if any) denoted by the argument, null otherwise.
     */
    private AbstractInsnNode insnLabelledBy(final LabelNode label) {
        assert label != null;
        AbstractInsnNode labelled = label;
        while (labelled != null && labelled.getOpcode() < 0) {
            labelled = labelled.getNext();
        }
        return labelled;
    }

    private LabelNode finalDestLabel(final JumpInsnNode source) {
        assert source != null;

        HashSet<LabelNode> seenLabels = new HashSet<LabelNode>();
        seenLabels.add(source.label);

        LabelNode label = source.label;

        do {
            AbstractInsnNode dest = insnLabelledBy(label);
            if(dest.getOpcode() != GOTO) {
                return label;
            }
            JumpInsnNode detour = (JumpInsnNode) dest;
            if(seenLabels.contains(detour.label)) {
                // we've found a loop (or lasso) from source to the instruction denoted by detour.label
                return detour.label;
            }
            seenLabels.add(detour.label);
            label = detour.label;
        } while (true);

    }
}
