/* NSC -- new Scala compiler
 * Copyright 2005-2012 LAMP/EPFL
 * @author  Martin Odersky
 */


package scala.tools.nsc
package backend
package jvm

import scala.tools.asm
import asm.Opcodes
import asm.tree.{MethodInsnNode, MethodNode}


/**
 *  Optimize and tidy-up bytecode before it's emitted for good.
 *
 *  @author  Miguel Garcia, http://lamp.epfl.ch/~magarcia/ScalaCompilerCornerReloaded/
 *  @version 1.0
 *
 *  TODO Improving the Precision and Correctness of Exception Analysis in Soot, http://www.sable.mcgill.ca/publications/techreports/#report2003-3
 *
 *  TODO https://github.com/retronym/scala/compare/topic/closure-sharing
 *       Why not constrain isSafeToUseConstantFunction to just Function whose apply()'s body has constant type?
 *       Useful e.g. with assert(cond, msg) when msg is string literal
 *       (otherwise, the anon-closure-class refers to the enclosing method, which refers to inner classes chain, not to mention the ConstantPool grows, etc.)
 */
abstract class BCodeOpt extends BCodeTypes {

  /**
   *  Intra-method optimizations. Upon visiting each method in an asm.tree.ClassNode,
   *  optimizations are applied iteratively until a fixpoint is reached.
   *
   *  All optimizations implemented here can do based solely on information local to the method
   *  (in particular, no lookups on `exemplars` are performed).
   *  That way, intra-method optimizations can be performed in parallel (in pipeline-2)
   *  while GenBCode's pipeline-1 keeps building more `asm.tree.ClassNode`s.
   *  Moreover, pipeline-2 is realized by a thread-pool.
   *
   *  The entry point is `cleanseClass()`.
   */
  class BCodeCleanser(cnode: asm.tree.ClassNode) {

    val jumpsCollapser      = new asm.optimiz.JumpChainsCollapser(null)
    val unreachCodeRemover  = new asm.optimiz.UnreachableCode
    val labelsCleanup       = new asm.optimiz.LabelsCleanup(null)
    val danglingExcHandlers = new asm.optimiz.DanglingExcHandlers(null)

    val copyPropagator      = new asm.optimiz.CopyPropagator
    val deadStoreElim       = new asm.optimiz.DeadStoreElim
    val ppCollapser         = new asm.optimiz.PushPopCollapser
    val unboxElider         = new asm.optimiz.UnBoxElider
    val jumpReducer         = new asm.optimiz.JumpReducer(null)
    val nullnessPropagator  = new asm.optimiz.NullnessPropagator
    val constantFolder      = new asm.optimiz.ConstantFolder

    val lvCompacter         = new asm.optimiz.LocalVarCompact(null)

    cleanseClass();

    /**
     *  The (intra-method) optimizations below are performed until a fixpoint is reached.
     *  They are grouped somewhat arbitrarily into:
     *    - those performed by `cleanseMethod()`
     *    - those performed by `elimRedundandtCode()`
     *    - nullness propagation
     *    - constant folding
     *
     *  After the fixpoint has been reached, two more optimizations are performed just once
     *  (further applications wouldn't reduce any further):
     *    - eliding box/unbox pairs
     *    - eliding redundant local vars.
     *
     *  An introduction to ASM bytecode rewriting can be found in Ch. 8. "Method Analysis" in
     *  the ASM User Guide, http://download.forge.objectweb.org/asm/asm4-guide.pdf
     */
    def cleanseClass() {
      // find out maxLocals and maxStack (maxLocals is given by nxtIdx in PlainClassBuilder, but maxStack hasn't been computed yet).
      val cw = new asm.ClassWriter(asm.ClassWriter.COMPUTE_MAXS)
      cnode.accept(cw)

      val mwIter = cw.getMethodWriters().iterator
      val mnIter = cnode.methods.iterator()

      while(mnIter.hasNext) {
        val mnode = mnIter.next()
        val mw    = mwIter.next()
        mnode.visitMaxs(mw.getMaxStack, mw.getMaxLocals)
        val isConcrete = ((mnode.access & (asm.Opcodes.ACC_ABSTRACT | asm.Opcodes.ACC_NATIVE)) == 0)
        if(isConcrete) {
          val cName = cnode.name

          var keepGoing = false
          do {
            keepGoing = false

            keepGoing |= cleanseMethod(cName, mnode)
            keepGoing |= elimRedundantCode(cName, mnode)

            nullnessPropagator.transform(cName, mnode);   // infers null resp. non-null reaching certain program points, simplifying control-flow based on that.
            keepGoing |= nullnessPropagator.changed

            constantFolder.transform(cName, mnode);       // propagates primitive constants, performs ops and simplifies control-flow based on that.
            keepGoing |= constantFolder.changed

          } while(keepGoing)

          // cacheRepeatableReads(cName, mnode)

          unboxElider.transform(cName, mnode)   // remove box/unbox pairs (this transformer is more expensive than most)
          lvCompacter.transform(mnode)          // compact local vars, remove dangling LocalVariableNodes.

          runTypeFlowAnalysis(cName, mnode) // debug
        }
      }
    }

    //--------------------------------------------------------------------
    // First optimization pack
    //--------------------------------------------------------------------

    /**
     *  This method performs a few intra-method optimizations:
     *    - collapse a multi-jump chain to target its final destination via a single jump
     *    - remove unreachable code
     *    - remove those LabelNodes and LineNumbers that aren't in use
     *
     *  Some of the above are applied repeatedly until no further reductions occur.
     *
     *  Node: what ICode calls reaching-defs is available as asm.tree.analysis.SourceInterpreter, but isn't used here.
     *
     */
    def cleanseMethod(cName: String, mnode: asm.tree.MethodNode): Boolean = {

      var changed = false
      var keepGoing = false

      do {
        keepGoing = false

        jumpsCollapser.transform(mnode)            // collapse a multi-jump chain to target its final destination via a single jump
        keepGoing |= jumpsCollapser.changed
        repOK(mnode)

        unreachCodeRemover.transform(cName, mnode) // remove unreachable code
        keepGoing |= unreachCodeRemover.changed
        repOK(mnode)

        labelsCleanup.transform(mnode)             // remove those LabelNodes and LineNumbers that aren't in use
        keepGoing |= labelsCleanup.changed
        repOK(mnode)

        danglingExcHandlers.transform(mnode)
        keepGoing |= danglingExcHandlers.changed
        repOK(mnode)

        changed |= keepGoing

      } while (keepGoing)

      changed

    }

    //--------------------------------------------------------------------
    // Second optimization pack
    //--------------------------------------------------------------------

    /**
     *  This method performs a few intra-method optimizations,
     *  aimed at reverting the extra copying introduced by inlining:
     *    - replace the last link in a chain of data accesses by a direct access to the chain-start.
     *    - dead-store elimination
     *    - remove those (producer, consumer) pairs where the consumer is a DROP and
     *      the producer has its value consumed only by the DROP in question.
     *
     * */
    def elimRedundantCode(cName: String, mnode: asm.tree.MethodNode): Boolean = {
      var changed   = false
      var keepGoing = false

      do {

        keepGoing = false

        copyPropagator.transform(cName, mnode) // replace the last link in a chain of data accesses by a direct access to the chain-start.
        keepGoing |= copyPropagator.changed

        deadStoreElim.transform(cName, mnode)  // replace STOREs to non-live local-vars with DROP instructions.
        keepGoing |= deadStoreElim.changed

        ppCollapser.transform(cName, mnode)    // propagate a DROP to the instruction(s) that produce the value in question, drop the DROP.
        keepGoing |= ppCollapser.changed

        jumpReducer.transform(mnode)           // simplifies branches that need not be taken to get to their destination.
        keepGoing |= jumpReducer.changed

        changed = (changed || keepGoing)

      } while (keepGoing)

      changed
    }

    //--------------------------------------------------------------------
    // Third optimization pack: Repeatable reads
    //--------------------------------------------------------------------

    /**
     *  A common idiom emitted by explicitouter and lambdalift involves
     *  dot navigation rooted at a local (for example, LOAD 0)
     *  followed by invocations of isStable (getters or GETFIELD)
     *  that result in a value that depends only on the access path described above.
     *
     *  Rather than duplicating the access path each time the value in question is required,
     *  that value can be stored after its first access in a local-var added for that purpose.
     *  This way, any side-effects required upon first access (e.g. lazy-val initialization)
     *  are preserved, while successive accesses load the local directly (shorter code size, faster).
     *
     */
    def cacheRepeatableReads(cName: String, mnode: asm.tree.MethodNode) {

      // (1) Those params never assigned qualify as "stable-roots" for "stable-access-paths"
      //     Code that has been tail-call-transformed contains assignments to formals.
      val stableLocals = new Array[Boolean](descrToBType(mnode.desc).getArgumentCount)
      var idx = 0
      while(idx < stableLocals.length) {
        stableLocals(idx) = true
        idx += 1
      }
      val insns = mnode.instructions.toArray
      for (insn <- insns) {
        if (asm.optimiz.Util.isSTORE(insn)) {
          val st = insn.asInstanceOf[asm.tree.VarInsnNode]
          if (st.`var` < stableLocals.length) {
            stableLocals(st.`var`) = false
          }
        }
      }

      // (2)
      import asm.tree.analysis.{ Analyzer, Frame }
      import asm.tree.AbstractInsnNode
      val tfa = new Analyzer[StableValue](new StableChainInterpreter)
      tfa.analyze(cName, mnode)

    }

    /**
     *  Represents *an individual link* in an access-path all whose links are stable.
     *  Such access-path is a lattice element in the StableChainInterpreter dataflow-analysis.
     *
     *  @param index TODO
     *  @param vsize TODO
     */
    case class StableValue(index: Int, vsize: Int) extends asm.tree.analysis.Value {
      override def getSize() = vsize
      def isStable = (index != -1)
    }

    class StableChainInterpreter extends asm.tree.analysis.Interpreter[StableValue](asm.Opcodes.ASM4) {

      private val UNKNOWN_1 = StableValue(-1, 1)
      private val UNKNOWN_2 = StableValue(-1, 2)

      private def dunno(size: Int): StableValue = {
        (size: @unchecked) match {
          case 0 => null
          case 1 => UNKNOWN_1
          case 2 => UNKNOWN_2
        }
      }

      private def dunno(producer: asm.tree.AbstractInsnNode): StableValue = {
        dunno(asm.optimiz.SizingUtil.getResultSize(producer))
      }

      override def newValue(t: asm.Type) = {
        if (t == asm.Type.VOID_TYPE) null
        else dunno(t.getSize())
      }

      /**
       * ACONST_NULL,
       * ICONST_M1, ICONST_0, ICONST_1, ICONST_2, ICONST_3, ICONST_4, ICONST_5,
       * LCONST_0, LCONST_1,
       * FCONST_0, FCONST_1, FCONST_2,
       * DCONST_0, DCONST_1,
       * BIPUSH,   SIPUSH,
       * LDC,
       * JSR,
       * GETSTATIC, // TODO
       * NEW
       */
      override def newOperation(insn: asm.tree.AbstractInsnNode) = { dunno(insn) }

      /**
       * Propagates the input value through LOAD, STORE, DUP, and SWAP instructions.
       */
      override def copyOperation(insn: asm.tree.AbstractInsnNode, value: StableValue) = { value }

      /**
       * INEG, LNEG, FNEG, DNEG,
       * IINC,
       *       I2L, I2F, I2D,
       * L2I,      L2F, L2D,
       * F2I, F2L,      F2D,
       * D2I, D2L, D2F,
       * I2B, I2C, I2S
       *
       * IFEQ, IFNE, IFLT, IFGE, IFGT, IFLE,
       * IFNULL, IFNONNULL
       * TABLESWITCH, LOOKUPSWITCH,
       * IRETURN, LRETURN, FRETURN, DRETURN, ARETURN,
       * PUTSTATIC,
       * GETFIELD, // TODO
       * NEWARRAY, ANEWARRAY, ARRAYLENGTH,
       * ATHROW,
       * CHECKCAST, INSTANCEOF,
       * MONITORENTER, MONITOREXIT,
       */
      override def unaryOperation(insn: asm.tree.AbstractInsnNode, value: StableValue) = {
        // Actually some unaryOperation on a stable-value results in another stable-value,
        // but to keep things simple this operation is considered to finish a stable-access-path
        // ("to keep things simple" means: the only way to extend an stable-access-path is via a "stable" INVOKE or GETFIELD)
        dunno(insn)
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
       * IALOAD, LALOAD, FALOAD, DALOAD, AALOAD, BALOAD, CALOAD, SALOAD,
       * IF_ICMPEQ, IF_ICMPNE, IF_ICMPLT, IF_ICMPGE, IF_ICMPGT, IF_ICMPLE,
       * IF_ACMPEQ, IF_ACMPNE,
       * PUTFIELD
       */
      override def binaryOperation(insn: asm.tree.AbstractInsnNode, value1: StableValue, value2: StableValue) = {
        // Actually some binaryOperations on two stable-values results in another stable-value,
        // but to keep things simple this operation is considered to finish a stable-access-path
        // ("to keep things simple" means: the only way to extend an stable-access-path is via a "stable" INVOKE or GETFIELD)
        dunno(insn)
      }

      /**
       * IASTORE, LASTORE, FASTORE, DASTORE, AASTORE, BASTORE, CASTORE, SASTORE
       */
      override def ternaryOperation(
        insn:   asm.tree.AbstractInsnNode,
        value1: StableValue,
        value2: StableValue,
        value3: StableValue) = {
        dunno(insn)
      }

      /**
       * INVOKEVIRTUAL, INVOKESPECIAL, INVOKESTATIC, INVOKEINTERFACE,
       * MULTIANEWARRAY and INVOKEDYNAMIC
       */
      override def naryOperation(insn: asm.tree.AbstractInsnNode, values: java.util.List[_ <: StableValue]): StableValue = {
        insn.getOpcode match {

          case Opcodes.INVOKEVIRTUAL
             | Opcodes.INVOKESPECIAL
             | Opcodes.INVOKEINTERFACE if values.size() == 1 && values.get(0).isStable =>
            val rcv      = values.get(0)
            val callsite = insn.asInstanceOf[MethodInsnNode]
            repeatableReads
            ???

          case Opcodes.INVOKESTATIC    => ???

          case Opcodes.INVOKEDYNAMIC   => dunno(insn)

          case _                       => dunno(insn)
        }
      }

      /**
       * IRETURN, LRETURN, FRETURN, DRETURN, ARETURN
       */
      override def returnOperation(insn: asm.tree.AbstractInsnNode, value: StableValue, expected: StableValue) { }

      /**
       * POP, POP2
       */
      override def drop(insn: asm.tree.AbstractInsnNode, value: StableValue) { }

      override def merge(d: StableValue, w: StableValue) = {
        assert(d.getSize() == w.getSize())
        if (d == w) d else dunno(d.getSize())
      }

    } // end of class StableChainInterpreter

    //--------------------------------------------------------------------
    // Type-flow analysis
    //--------------------------------------------------------------------

    def runTypeFlowAnalysis(owner: String, mnode: MethodNode) {

      import asm.tree.analysis.{ Analyzer, Frame }
      import asm.tree.AbstractInsnNode

      val tfa = new Analyzer[TFValue](new TypeFlowInterpreter)
      tfa.analyze(owner, mnode)
      val frames: Array[Frame[TFValue]]   = tfa.getFrames()
      val insns:  Array[AbstractInsnNode] = mnode.instructions.toArray()
      var i = 0
      while(i < insns.length) {
        if (frames(i) == null && insns(i) != null) {
          // TODO assert(false, "There should be no unreachable code left by now.")
        }
        i += 1
      }
    }

    //--------------------------------------------------------------------
    // Utilities for reuse by different optimizations
    //--------------------------------------------------------------------

    /**
     *  Well-formedness checks, useful after each fine-grained transformation step on a MethodNode.
     *
     *  Makes sure that exception-handler and local-variable entries are non-obviously wrong
     *  (e.g., the left and right brackets of instruction ranges are checked, right bracket should follow left bracket).
     */
    def repOK(mnode: asm.tree.MethodNode): Boolean = {
      if(!global.settings.debug.value) {
        return true;
      }

          def isInsn(insn: asm.tree.AbstractInsnNode) {
            assert(mnode.instructions.contains(insn))
          }

          def inSequence(fst: asm.tree.AbstractInsnNode, snd: asm.tree.AbstractInsnNode): Boolean = {
            var current = fst
            while(true) {
              current = current.getNext()
              if(current == null) { return false }
              if(current == snd)  { return true  }
            }
            false
          }

      val insnIter = mnode.instructions.iterator()
      while(insnIter.hasNext) {
        assert(insnIter.next() != null, "instruction stream shouldn't contain nulls.")
      }

      // exception-handler entries
      if(mnode.tryCatchBlocks != null) {
        val tryIter = mnode.tryCatchBlocks.iterator()
        while(tryIter.hasNext) {
          val tcb = tryIter.next
          assert(tcb.start   != null)
          assert(tcb.end     != null)
          assert(tcb.handler != null)
          isInsn(tcb.start)
          isInsn(tcb.end)
          isInsn(tcb.handler)
          inSequence(tcb.start, tcb.end)
        }
      }

      // local-vars entries
      if(mnode.localVariables != null) {
        val lvIter = mnode.localVariables.iterator()
        while(lvIter.hasNext) {
          val lv = lvIter.next
          isInsn(lv.start)
          isInsn(lv.end)
          inSequence(lv.start, lv.end)
        }
      }

      true
    }

  }

}