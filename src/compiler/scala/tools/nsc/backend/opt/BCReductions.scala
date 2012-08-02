/* NSC -- new Scala compiler
 * Copyright 2005-2011 LAMP/EPFL
 * @author  Martin Odersky
 */

package scala.tools.nsc
package backend.opt

import scala.tools.asm
import scala.tools.asm.tree._
import scala.annotation.switch
import collection.JavaConversions

/** Straightforward in-place reductions on the bytecode content of a method body.
 *  These reduction require no iterative dataflow analysis.
 *
 *  @author  Miguel Garcia, http://lamp.epfl.ch/~magarcia/ScalaCompilerCornerReloaded/
 *  @version 1.0
 */
trait BCReductions {



  /////////////////////////////////////////////////////
  /* ---------------- query methods ---------------- */
  /////////////////////////////////////////////////////

  def hasCode(m: MethodNode): Boolean = { (m.access & (asm.Opcodes.ACC_ABSTRACT | asm.Opcodes.ACC_NATIVE)) != 0 }

  def finishesBBlock(insnNode: AbstractInsnNode): Boolean = {
    val insnOpcode = insnNode.getOpcode()
    val insnType   = insnNode.getType()

    (insnType: @switch) match {
      case AbstractInsnNode.JUMP_INSN         => true
      case AbstractInsnNode.LOOKUPSWITCH_INSN => true
      case AbstractInsnNode.TABLESWITCH_INSN  => true
      case AbstractInsnNode.VAR_INSN if insnOpcode == asm.Opcodes.RET => ??? /* on purpose */
      case AbstractInsnNode.INSN =>
        import asm.Opcodes
        (insnOpcode: @switch) match {
          case Opcodes.ATHROW => true
          case Opcodes.IRETURN | Opcodes.LRETURN | Opcodes.FRETURN |
               Opcodes.DRETURN | Opcodes.ARETURN | Opcodes.RETURN => true
          case _ => false
        }
    }
  }

  def possibleSuccessors(insnNode: AbstractInsnNode): List[AbstractInsnNode] = {
    val insnOpcode = insnNode.getOpcode()
    val insnType   = insnNode.getType()

    insnNode match {

      case jmp: JumpInsnNode =>
        (insnOpcode: @switch) match {
          case asm.Opcodes.JSR  => ??? // this is on purpose.
          case asm.Opcodes.GOTO => List(jmp.label)
          case _                => List(jmp.label, insnNode.getNext)
        }

      case lw: LookupSwitchInsnNode =>
        lw.dflt :: JavaConversions.iterableAsScalaIterable(lw.labels).toList

      case ts: TableSwitchInsnNode  =>
        ts.dflt :: JavaConversions.iterableAsScalaIterable(ts.labels).toList

      case _ =>

        (insnType: @switch) match {
          case AbstractInsnNode.VAR_INSN if insnOpcode == asm.Opcodes.RET => ??? /* on purpose */
          case AbstractInsnNode.INSN =>
            import asm.Opcodes
            (insnOpcode: @switch) match {
              case Opcodes.ATHROW  |
                   Opcodes.IRETURN | Opcodes.LRETURN | Opcodes.FRETURN |
                   Opcodes.DRETURN | Opcodes.ARETURN | Opcodes.RETURN => Nil
              case _ => List(insnNode.getNext)
            }
          case _ => List(insnNode.getNext)
        }

    }

  }



  ////////////////////////////////////////////////
  /* ---------------- analyses ---------------- */
  ////////////////////////////////////////////////

  /** Both ends are inclusive. */
  case class BBlock(from: AbstractInsnNode, to: AbstractInsnNode)

  /** Computes the basic blocks (TODO and succs preds, normal vs exceptional control flow)
   *
   *  Preconds:
   *   (1) does not require visitMaxs() to have been called on the MethodNode argument.
   *   (2) doesn't handle methods with JSR instruction.
   */
  class CFG(m: MethodNode) {

    var basicBlocks: List[BBlock] = Nil

    // instructions starting a basic block reachable over normal control flow.
    private val isStartBB = collection.mutable.Set.empty[AbstractInsnNode]
    private def markBegin(i: AbstractInsnNode) { isStartBB += i }

    import asm.Opcodes
    if(hasCode(m)) {
      // determine basic blocks reachable over normal control flow in two passes.

      // Pass 1: mark those instructions starting a basic block (not an EH) by adding them to `isStart`
      var idx       = 0
      val insns     = m.instructions
      markBegin(insns.getFirst)
      while(idx < insns.size) {
        val insnNode   = insns.get(idx) // first call to insns.get() makes sure all insns are numbered consecutively. isRepOK()
        val insnOpcode = insnNode.getOpcode()
        val insnType   = insnNode.getType()

        insnNode match {

          case jmp: JumpInsnNode =>
            (insnOpcode: @switch) match {
              case Opcodes.JSR  => ??? // this is on purpose.
              case Opcodes.GOTO => markBegin(jmp.label) // not scheduling "the instruction following insnNode" because it could be an EH start
              case _            => markBegin(jmp.label); markBegin(insnNode.getNext)
            }

          case lw: LookupSwitchInsnNode => possibleSuccessors(lw) foreach markBegin

          case ts: TableSwitchInsnNode  => possibleSuccessors(ts) foreach markBegin

          case _ => ()
        }

        idx += 1
      }

      // Pass 2: find the last instruction in each basic block

      val isStartEH = JavaConversions.iterableAsScalaIterable(m.tryCatchBlocks).map(tcb => tcb.handler).toSet
      assert(isStartEH forall { eh => !isStartBB(eh) }, "The start of an exception handler is being tracked twice.")

          def idxOf(i: AbstractInsnNode) = { insns indexOf i }
          def isEHStart(i: AbstractInsnNode) = {
            i match {
              case ln: LabelNode => isStartEH(ln)
              case _             => false
            }
          }

      for(h <- isStartBB ++ isStartEH) {
        val iter = insns.iterator(idxOf(h) + 1)
        if(!iter.hasNext) {
          basicBlocks ::= BBlock(h, h)
          // TODO possibleSuccessors
        } else {

          var keepGoing = true
          while(iter.hasNext && keepGoing) {
            val curr = iter.next()
            if(finishesBBlock(curr)) {
              basicBlocks ::= BBlock(h, curr)
              // TODO possibleSuccessors
              keepGoing = false
            }
            else if(isStartBB(curr)) {
              basicBlocks ::= BBlock(h, iter.previous())
              // TODO fall-through case, add normal-control-flow edge: (iter.previous -> curr)
              keepGoing = false
            }
            else {
              assert(!isEHStart(curr), "We're not supposed to fall-off into an exception handler.")
              assert(iter.hasNext,     "Must fall-through somewhere, but there's no somewhere.")
            }
          }

        }

      }
    }

  }



  ////////////////////////////////////////////////////////////////////////////
  /* ---------------- semantics-preserving transformations ---------------- */
  ////////////////////////////////////////////////////////////////////////////

  /** Collapses a multi-hop jump chain into its final destination, and eliminate an unconditional jump when fall through accomplishes the same.
   *  May leave behind unreachable code, use `elimUnreach()` to deal with it.
   *  Preconds:
   *   (1) does not require visitMaxs() to have been called on the MethodNode argument.
   *   (2) doesn't handle methods with JSR instruction.
   */
  def collapseJumps(m: MethodNode) {
    ??? // TODO
  }

  /** Removes back-to-back instructions (usually two of them) that have no effect on the execution state.
   *  May leave behind unreachable code, use `elimUnreach()` to deal with it.
   *  Preconds:
   *   (1) does not require visitMaxs() to have been called on the MethodNode argument.
   *   (2) doesn't handle methods with JSR instruction.
   */
  def peephole(m: MethodNode) {
    ??? // TODO
  }

  /** Eliminate unreachable basic blocks from a method.
   *  Takes care of removing exception handlers protecting no reachable instructions.
   */
  def elimUnreach(m: MethodNode) {
    ??? // TODO
  }

}