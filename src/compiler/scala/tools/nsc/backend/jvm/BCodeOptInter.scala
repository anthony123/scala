/* NSC -- new Scala compiler
 * Copyright 2005-2012 LAMP/EPFL
 * @author  Martin Odersky
 */


package scala.tools.nsc
package backend
package jvm

import scala.tools.asm
import asm.Opcodes
import asm.optimiz.UnBoxAnalyzer.FakeParamLoad
import asm.optimiz.{UnBoxAnalyzer, ProdConsAnalyzer, Util}
import asm.tree.analysis.SourceValue
import asm.tree._

import scala.collection.{ mutable, immutable }
import scala.Some
import collection.convert.Wrappers.JListWrapper
import collection.convert.Wrappers.JSetWrapper

/**
 *  Optimize and tidy-up bytecode before it's serialized for good.
 *  This class focuses on inter-procedural optimizations.
 *
 *  @author  Miguel Garcia, http://lamp.epfl.ch/~magarcia/ScalaCompilerCornerReloaded/
 *  @version 1.0
 *
 */
abstract class BCodeOptInter extends BCodeOptIntra {

  import global._

  val cgns = new mutable.PriorityQueue[CallGraphNode]()(cgnOrdering)

  // dclosure-endpoint -> BType-of-Late-Closure-Class
  val closuresForDelegates = mutable.Map.empty[MethodSymbol, BType]


  /**
   * must-single-thread
   **/
  override def clearBCodeOpt() {
    super.clearBCodeOpt()
    cgns.clear()
    codeRepo.clear()
    elidedClasses.clear()
    closuRepo.clear()
  }

  //--------------------------------------------------------
  // Tracking of delegating-closures
  //--------------------------------------------------------

  override def isDClosure(iname: String): Boolean = { closuRepo.isDelegatingClosure(iname)  }

  case class MethodRef(ownerClass: BType, mnode: MethodNode)

  /**
   *  @return the callee, for a MethodNodeInsn, represented as MethodRef. Otherwise null.
   * */
  def accessedMethodRef(insn: AbstractInsnNode): MethodRef = {
    insn match {
      case mi: MethodInsnNode =>
        val ownerBT = lookupRefBType(mi.owner)
        val mnode   = codeRepo.getMethod(ownerBT, mi.name, mi.desc).mnode
        MethodRef(ownerBT, mnode)
      case _ => null
    }
  }

  /**
   * Terminology for delegating closures
   * -----------------------------------
   *
   * "delegating closure": (dclosure for short) an anonymous-closure-class
   *                       created by UnCurry's `closureConversionModern()`.
   *
   * "dclosure endpoint":  method consisting of the closure's body, its name contains "dlgt$".
   *
   * "master class of a dclosure": non-dclosure class declaring one or more dclosure endpoints
   *                               (we say the master class "is responsible for" its dclosures).
   *
   * Invariants for delegating closures
   * ----------------------------------
   *
   * The items above exhibit invariants that a "traditional closure" doesn't necessarily guarantee,
   * invariants that can be exploited for optimization:
   *
   *   (a) the endpoint of a dclosure is the single entry point through which
   *       the dclosure may access functionality of its master class.
   *
   *   (b) Initially there's program wide a single callsite targeting any given dclosure-endpoint
   *       (that callsite is enclosed in one of the dclosure's apply() methods).
   *       This may change due to:
   *
   *         (b.1) dead-code elimination, which may remove the instantiation of the dclosure
   *               (just like any anonymous closure, a dclosure is instantiated at a single program-wide point).
   *
   *         (b.2) as part of `WholeProgramAnalysis.inlining()`, closure-inlining elides a dclosure-class.
   *               As a result, one or more callsites to the endpoint may occur now in the
   *               "static-HiO" method added to the master class (see `buildStaticHiO`).
   *               Still, all those occurrences can be found by inspecting the master class.
   *               Moreover, a static-HiO method, although public, is itself never inlined
   *               (callsites to it may well be inlined, e.g. in another class).
   *               Thus the following invariant holds:
   *
   *               Callsites to a dclosure endpoint may appear only:
   *                 - either in
   *                     the dclosure (just one callsite), if the dclosure hasn't been inlined;
   *                 - or
   *                     in the master class (one ore more callsites), if the dclosure has been inlined.
   *
   *               (This whole nit-pick about not losing track of callsites to endpoints is
   *               explained by our desire to optimize).
   *
   *   (c) a class C owning a closure-endpoint method isn't a delegating-closure itself
   *       (it's fine for C to be a traditional-closure or a non-closure).
   *
   * Beware
   * ------
   *
   *   (1) Not really an invariant but almost:
   *       "all instantiations of dclosure D are enclosed in a method of the master class of D"
   *       With inlining, "transplanting" a method's instructions to another class may break the condition above.
   *       Apparently few program points contradict the above right after GenBCode.
   *
   *
   *   (2) Care is needed to preserve Invariant (b.2) in the presence of closure-inlining and delayedInit,
   *       ie we want to preserve:
   *             static-HiO's declaring class == master class of the inlined dclosure
   *       See log entry starting with "Surprise surprise" in `inlineClosures()` along with workaround.
   *
   **/
  object closuRepo extends BCInnerClassGen {

    /**
     *  dclosure-class -> endpoint-as-methodRef-in-master-class
     *
     *  @see populateDClosureMaps() Before that method runs, this map is empty.
     */
    final val endpoint = mutable.Map.empty[BType, MethodRef]

    /**
     *  master-class -> dclosure-classes-it's-responsible-for
     *
     *  @see populateDClosureMaps() Before that method runs, this map is empty.
     */
    final val dclosures = mutable.Map.empty[BType, List[BType]]

    /**
     *  dclosure-class -> "classes other than its master-class referring to it, via NEW dclosure or INVOKE endpoint"
     *
     *  @see populateNonMasterUsers() Before that method runs, this map is empty.
     */
    final val nonMasterUsers = mutable.Map.empty[BType, mutable.Set[BType]].withDefaultValue(mutable.Set.empty)

    // --------------------- query methods ---------------------

    final def isDelegatingClosure( c:    BType):     Boolean = { endpoint.contains(c) }
    final def isDelegatingClosure(iname: String):    Boolean = { isDelegatingClosure(lookupRefBType(iname)) }
    final def isDelegatingClosure(cnode: ClassNode): Boolean = { isDelegatingClosure(cnode.name) }

    final def isTraditionalClosure(c: BType): Boolean = { c.isClosureClass && !isDelegatingClosure(c) }

    final def masterClass(dclosure: BType): BType = { endpoint(dclosure).ownerClass }

    final def isMasterClass(c:     BType ):    Boolean = { dclosures.contains(c) }
    final def isMasterClass(iname: String):    Boolean = { isMasterClass(lookupRefBType(iname)) }
    final def isMasterClass(cnode: ClassNode): Boolean = { isMasterClass(cnode.name) }

    /**
     * The set of delegating-closures created during UnCurry, represented as BTypes.
     * Some of these might not be emitted, e.g. as a result of dead-code elimination or closure inlining.
     * */
    final def allDClosures:     collection.Set[BType] = { endpoint.keySet  }
    final def allMasterClasses: collection.Set[BType] = { dclosures.keySet }

    /**
     * The set of delegating-closures used by no other class than the argument
     * (besides the trivial usage of each dclosure by itself).
     * */
    final def exclusiveDClosures(master: BType): List[BType] = {
      dclosures(master) filter { dc => nonMasterUsers(dc).isEmpty }
    }

    final def isDClosureExclusiveTo(d: BType, master: BType): Boolean = {
      exclusiveDClosures(master) contains d
    }

    /**
     * The set of delegating-closures used by no other class than the argument
     * (besides the trivial usage of each dclosure by itself)
     * and moreover not elided (as a consequence, endpoint is public).
     * */
    final def liveDClosures(masterCNode: ClassNode): List[BType] = {
      val master = lookupRefBType(masterCNode.name)
      assert(isMasterClass(master), "Not a master class for any dclosure: " + master.getInternalName)
      for(
        d <- exclusiveDClosures(master);
        if !elidedClasses.contains(d);
        dep = endpoint(d).mnode;
        // looking ahead, it's possible for an arg-less static endpoint to be pasted into the dclosure's apply().
        if masterCNode.methods.contains(dep)
      ) yield d
    }

    def closureInstantiations(mnode: MethodNode, dclosure: BType): List[AbstractInsnNode] = {
      assert(dclosure != null)
      mnode.instructions.toList filter { insn => instantiatedDClosure(insn) == dclosure }
    }

    def closureInvocations(mnode: MethodNode, dclosure: BType): List[AbstractInsnNode] = {
      assert(dclosure != null)
      mnode.instructions.toList filter { insn => invokedDClosure(insn) == dclosure }
    }

    def closureAccesses(mnode: MethodNode, dclosure: BType): List[AbstractInsnNode] = {
      assert(dclosure != null)
      mnode.instructions.toList filter { insn => accessedDClosure(insn) == dclosure }
    }

    // ------------------------------- yes/no inspectors and asserts ------------------------------

    /**
     *  A master-class of a non-elided dclosure contains:
     *    - a single instantiation of it, and
     *    - no invocations to the dclosure's endpoint.
     *  (the "non-elided" part is responsible for that property: a dclosure that was inlined
     *   has a callsite to the endpoint in the shio method that replaces the higher-order method invocation).
     * */
    def assertEndpointInvocationsIsEmpty(masterCNode: ClassNode, dclosure: BType) {
      for( /*debug*/
        masterMethod <- JListWrapper(masterCNode.methods);
        if !Util.isAbstractMethod(masterMethod)
      ) {
        assert(
          closuRepo.closureInvocations(masterMethod, dclosure).isEmpty,
          "A master class of a non-elided dclosure is supposed to contain a single instantiation of it, however " +
         s"${methodSignature(masterCNode, masterMethod)} invokes the endpoint of ${dclosure.getInternalName}"
        )
      }
    }

    // -------------- utilities to track dclosure usages in classes other than master --------------

    /**
     * Matches a "NEW dclosure" instruction returning the dclosure's BType in that case. Otherwise null.
     * */
    private def instantiatedDClosure(insn: AbstractInsnNode): BType = {
      if(insn.getOpcode == Opcodes.NEW) {
        val ti  = insn.asInstanceOf[TypeInsnNode]
        val dbt = lookupRefBType(ti.desc)
        if(isDelegatingClosure(dbt)) {
          return dbt
        }
      }

      null
    }

    /**
     * Matches a "INVOKE dclosure-endpoint" instruction returning the dclosure's BType in that case. Otherwise null.
     * */
    def invokedDClosure(insn: AbstractInsnNode): BType = {
      if(insn.getType == AbstractInsnNode.METHOD_INSN) {
        val mi     = insn.asInstanceOf[MethodInsnNode]
        val master = lookupRefBType(mi.owner)
        if(isMasterClass(master)) {
          for(
            dclosure <- dclosures(master);
            mnode: MethodNode = endpoint(dclosure).mnode;
            if (mnode.name == mi.name) && (mnode.desc == mi.desc)
          ) {
            return dclosure
          }
        }
      }

      null
    }

    /**
     * Matches a dclosure instantiation or endpoint invocation, returning the dclosure's BType in that case. Otherwise null.
     * */
    private def accessedDClosure(insn: AbstractInsnNode): BType = {
      instantiatedDClosure(insn) match {
        case null => invokedDClosure(insn)
        case dc   => dc
      }
    }

    /**
     *  In case dc is a dclosure being "used" in `enclClass` (for enclClass not the master class of dc),
     *  make note of this fact in `nonMasterUsers`.
     *
     *  For the purposes of forthcoming optimizations,
     *  a dclosure is "used" whenever an instantiation of it or an endpoint-invocation to it
     *  are lexically enclosed in the "user" class (ie `enclClass`).
     *
     *  @param insn      bytecode instruction that may access a dclosure
     *  @param enclClass enclosing class where the usage of the dclosure appears
     * */
    def trackClosureUsageIfAny(insn: AbstractInsnNode, enclClass: BType) {
      val dc = accessedDClosure(insn)
      if(dc == null || enclClass == dc || !isDelegatingClosure(dc)) { return }
      assert(
        !isDelegatingClosure(enclClass),
         "A dclosure D is used by a class C other than its master class, but C is a dclosure itself. " +
        s"Who plays each role: D by ${dc.getInternalName} , C by ${enclClass.getInternalName} "
      )
      if(enclClass != masterClass(dc)) {
        nonMasterUsers(dc) += enclClass
      }
    }

    // --------------------- closuRepo initializers ---------------------

    /**
     *  must-single-thread
     * */
    def populateDClosureMaps() {

      // all dclosure-endpoints accounted for (ie a dclosure created for each)
      {
            def locations(msyms: collection.Set[MethodSymbol]): String = {
              msyms map { m => m.fullLocationString } mkString(" , ")
            }

        val endpointsLackingDClosure = (uncurry.closureDelegates filterNot (closuresForDelegates.keySet))
        assert(
          endpointsLackingDClosure.isEmpty,
          s"The following dclosure-endpoints (created by UnCurry) got from genLateClosure() no dclosure-class: ${locations(endpointsLackingDClosure)}"
        )
        val endpointsFromNowhere = ((closuresForDelegates.keySet) filterNot uncurry.closureDelegates)
        assert(
          endpointsFromNowhere.isEmpty,
          s"The following dclosure-endpoints were not created by UnCurry's closureConversionModern(): ${locations(endpointsFromNowhere)}"
        )
      }

      assert(endpoint.isEmpty)
      assert(dclosures.isEmpty)
      assert(nonMasterUsers.isEmpty)

      for (Pair(delegateMethodSymbol, closureBT) <- closuresForDelegates) {
        val delegateMethodRef = {
          val delegateOwnerBT:    BType = exemplar(delegateMethodSymbol.owner).c
          val delegateMethodType: BType = asmMethodType(delegateMethodSymbol)
          val delegateName:      String = delegateMethodSymbol.javaSimpleName.toString
          assert(
            codeRepo.classes.containsKey(delegateOwnerBT),
            "A class being compiled can't be found via codeRepo: " + delegateOwnerBT.getInternalName
          )
          val delegateMethodNode = codeRepo.getMethod(delegateOwnerBT, delegateName, delegateMethodType.getDescriptor).mnode
          assert(
            delegateMethodNode != null,
            "A method being compiled can't be found via codeRepo: " + methodSignature(delegateOwnerBT, delegateName, delegateMethodType)
          )
          Util.makePublicMethod(delegateMethodNode)

          MethodRef(delegateOwnerBT, delegateMethodNode)
        }
        endpoint.put(closureBT, delegateMethodRef)
      }

      for(cep <- endpoint) {
        val endpointOwningClass: BType = cep._2.ownerClass
        assert(
          !isDelegatingClosure(endpointOwningClass),
          "A class owning a closure-endpoint method cannot be a delegating-closure itself: " + endpointOwningClass.getInternalName
        )
      }

      for(Pair(dclosure, endpointRef) <- endpoint) {
        val master = endpointRef.ownerClass
        val other  = dclosures.getOrElse(master, Nil)
        dclosures.put(master, dclosure :: other)
      }

    } // end of method populateDClosureMaps()

    /**
     * Right after GenBCode, 99% of all "NEW dclosure" instructions are found in masterClass(dclosure).
     * The exceptions (due to delayedInit) are found here.
     *
     * Additionally, non-master-class users of dclosures are also spotted during inlining
     * (those uses are tracked from then on, see `trackClosureUsageIfAny()`).
     *
     * As a result, after `WholeProgramAnalysis.optimize()` has run
     * we know where to look for usages of a given dclosure.
     * "All users of a dclosure" is needed to partition the set of dclosures
     * so that different Worker2 threads have exclusive access to different partitions.
     *
     * For example, as part of intra-class optimizations exclusive access is required to
     * the gropus of (master class, its dclosures) to decide whether a dclosure endpoint
     * can be made private or static. In the affirmative case, we'll need to adapt (all) its usages.
     *
     * */
    def populateNonMasterUsers() {
      val iterCompiledEntries = codeRepo.classes.entrySet().iterator()
      while(iterCompiledEntries.hasNext) {
        val e = iterCompiledEntries.next()
        val compiledClassBT: BType     = e.getKey
        val compiledClassCN: ClassNode = e.getValue
        for(
          mnode <- JListWrapper(compiledClassCN.methods);
          if !Util.isAbstractMethod(mnode)
        ) {
          mnode foreachInsn { insn => closuRepo.trackClosureUsageIfAny(insn, compiledClassBT) }
        }
      }
    }

    // --------------------- closuRepo post-initialization utilities ---------------------

    /**
     *  TODO documentation
     * */
    def retractAsDClosure(dc: BType) {
      assert(
        nonMasterUsers(dc).isEmpty,
        s"A dclosure can't be retracted unless used only by its master class, but ${dc.getInternalName} in use by ${nonMasterUsers(dc).mkString}"
      )
      val exMaster = masterClass(dc)
      endpoint.remove(dc)
      if(dclosures.contains(exMaster)) {
        val other = dclosures(exMaster) filterNot { _ == dc }
        if(other.isEmpty) { dclosures.remove(exMaster)     }
        else              { dclosures.put(exMaster, other) }
      }
    }

    def clear() {
      uncurry.closureDelegates.clear()
      closuresForDelegates.clear()
      mixer.detouredFinalTraitMethods.clear()
      endpoint.clear()
      dclosures.clear()
      nonMasterUsers.clear()
    }

  } // end of object closuRepo

  //--------------------------------------------------------
  // Optimization pack: Method-inlining and Closure-inlining
  //--------------------------------------------------------

  /**
   * During `GenBCode`, `PlainClassBuilder` inspects each MethodNode for a plain class,
   * detecting those callsites targeting @inline methods, and collecting them (the callsites) in a `CallGraphNode` instance,
   * classified into "higher-order callsites" (ie taking one or more functions as arguments) and the rest.
   * The callsites in question constitute "requests for inlining".
   *
   * During `WholeProgramAnalysis.inlining()` An attempt will be made to fulfill the inlining requests,
   * after detecting any attempts at cyclic inlining. Moreover a request may prove unfeasible afterwards too,
   * e.g. due to the callsite program point having a deeper operand-stack than the arguments the callee expects,
   * and the callee containing exception handlers.
   *
   * A description of the workflow for method-inlining and closure-inlining can be found in `WholeProgramAnalysis.inlining()`.
   *
   * @param hostOwner the JVM-level class defining method host
   * @param host      the method were inlining has been requested
   *
   */
  final class CallGraphNode(val hostOwner: ClassNode, val host: MethodNode) {

    var hiOs:  List[InlineTarget] = Nil
    var procs: List[InlineTarget] = Nil

    def isEmpty    = (hiOs.isEmpty && procs.isEmpty)
    def candidates = (hiOs ::: procs).sorted(inlineTargetOrdering)

    def directCallees: Set[MethodNode] = {
      hiOs.map(_.callee).toSet ++ procs.map(_.callee)
    }

    /**
     * Initially the invocation instructions (one for each InlineTarget)
     * haven't been resolved to the MethodNodes they target.
     * This method takes care of that, setting `InlineTarget.callee` and `InlineTarget.owner` as a side-effect.
     *
     * can-multi-thread, provided each callsite.owner has been entered as TypeName in Names.
     * */
    def populate() {
      if(!Util.isReadyForAnalyzer(host)) {
        Util.computeMaxLocalsMaxStack(host)
      }
      for(c <- candidates) {
        c.populate()
      }
      hiOs  = hiOs  filter { it => it.callee != null }
      procs = procs filter { it => it.callee != null }
    }

    def isRepOK: Boolean = {
      candidates forall { c => c.callee != host } // non-cyclic
    }

  }

  object cgnOrdering extends scala.math.Ordering[CallGraphNode] {
    def compare(x: CallGraphNode, y: CallGraphNode): Int = {
      var result = x.host.instructions.size().compare(y.host.instructions.size())
      if (result == 0) {
        result = x.hashCode().compare(y.hashCode())
      }
      result
    }
  }

  /**
   *  An inlining request, given by a callsite and items for error reporting.
   *
   *  @param callsite for which inlining has been requested
   *  @param cunit    for error reporting
   *  @param pos      for error reporting
   *
   * */
  final class InlineTarget(val callsite: MethodInsnNode, val cunit: CompilationUnit, val pos: Position) {

    var callee: MethodNode = null // the concrete callee denoted by the callsite
    var owner:  ClassNode  = null // the class declaring the callee

    def populate() {
      val ownerBT = lookupRefBType(callsite.owner)
      // `null` usually indicates classfile wasn't found and thus couldn't be parsed. TODO warning?
      val mnAndOwner = codeRepo.getMethodOrNull(ownerBT, callsite.name, callsite.desc)
      if(mnAndOwner != null) {
        callee = mnAndOwner.mnode
        owner  = mnAndOwner.owner
        if(!Util.isReadyForAnalyzer(callee)) {
          Util.computeMaxLocalsMaxStack(callee)
        }
      }
    }

    def calleeId: String = { owner.name + "::" + callee.name + callee.desc }

    def warn(msg: String) = cunit.inlinerWarning(pos, msg)

  }

  object inlineTargetOrdering extends scala.math.Ordering[InlineTarget] {
    def compare(x: InlineTarget, y: InlineTarget): Int = {
      x.hashCode().compare(y.hashCode())
    }
  }

  /**
   *  Single-access point for requests to parse bytecode for inlining purposes.
   *  Given the BType of a class with internal name,
   *  `codeRepo` allows obtaining its bytecode-level representation (ClassNode).
   *  It's possible to find out whether a ClassNode was compiled in this run, or parsed from an external library.
   * */
  object codeRepo {

    val parsed  = new java.util.concurrent.ConcurrentHashMap[BType, asm.tree.ClassNode]
    val classes = new java.util.concurrent.ConcurrentHashMap[BType, asm.tree.ClassNode]

    def containsKey(bt: BType): Boolean = { (classes.containsKey(bt) || parsed.containsKey(bt)) }

    /**
     *  must-single-thread
     */
    def getFieldOrNull(bt: BType, name: String, desc: String): FieldNode = {
      try { getField(bt, name, desc) }
      catch {
        case ex: MissingRequirementError =>
          null // TODO bytecode parsing shouldn't fail, otherwise how could the FieldInsnNode have compiled?
      }
    }

    /**
     *  must-single-thread
     */
    def getMethodOrNull(bt: BType, name: String, desc: String): MethodNodeAndOwner = {
      try { getMethod(bt, name, desc) }
      catch {
        case ex: MissingRequirementError =>
          null // TODO bytecode parsing shouldn't fail, otherwise how could the callsite have compiled?
      }
    }

    /**
     *  @return None if not found, the MethodNode's access field otherwise.
     *
     *  must-single-thread
     *
     * */
    def getMethodAccess(bt: BType, name: String, desc: String, isMultithread: Boolean): Option[Int] = {
      val cn =
        if(isMultithread) { getClassNodeOrNull(bt) }
        else              {       getClassNode(bt) }
      if(cn == null) { return None }
      val iter = cn.methods.iterator()
      while(iter.hasNext) {
        val mn = iter.next()
        if(mn.name == name && mn.desc == desc) {
          return Some(mn.access)
        }
      }
      for(ifaceIName <- JListWrapper(cn.interfaces)) {
        val outcome = getMethodAccess(lookupRefBType(ifaceIName), name, desc, isMultithread)
        if(outcome.nonEmpty) { return outcome }
      }
      if(cn.superName != null) {
        val outcome = getMethodAccess(lookupRefBType(cn.superName), name, desc, isMultithread)
        if(outcome.nonEmpty) { return outcome }
      }
      None
    }

    /**
     * Looks up (parsing from bytecode if needed) the field declared in `bt`
     * given by the combination of field-name and field-descriptor.
     *
     * must-single-thread
     */
    def getField(bt: BType, name: String, desc: String): FieldNode = {
      val cn = getClassNode(bt)
      val iter = cn.fields.iterator()
      while(iter.hasNext) {
        val fn = iter.next()
        if(fn.name == name && fn.desc == desc) {
          return fn
        }
      }

      MissingRequirementError.notFound(s"Could not find FieldNode: ${bt.getInternalName}.$name: ${desc}")
    }

    /**
     * Looks up (parsing from bytecode if needed) the method declared in `bt`
     * given by the combination of method-name and method-descriptor.
     * Keeps looking up over the superclass hierarchy, until reaching j.l.Object
     *
     * @return if found, the MethodNode and the ClassNode declaring it. Otherwise MissingRequirementError is thrown.
     *
     * must-single-thread
     */
    def getMethod(bt: BType, name: String, desc: String): MethodNodeAndOwner = {

      var current = bt

      while(current != null) {
        val cn = getClassNode(current)
        val iter = cn.methods.iterator()
        while(iter.hasNext) {
          val mn = iter.next()
          if(mn.name == name && mn.desc == desc) {
            return MethodNodeAndOwner(mn, cn)
          }
        }
        current = if(cn.superName == null) null else lookupRefBType(cn.superName)
      }

      MissingRequirementError.notFound(s"Could not find MethodNode: ${bt.getInternalName}.${name}${desc}")
    }

    /** must-single-thread */
    def getClassNode(owner: String): asm.tree.ClassNode = { getClassNode(brefType(owner)) }

    /**
     *  Returns the ASM ClassNode for a class that's being compiled or that's going to be parsed from external bytecode.
     *
     *  After this method has run, the following two post-conditions hold:
     *    - `exemplars.containsKey(bt)`
     *    - `codeRepo.containsKey(bt)`
     *
     *  must-single-thread
     */
    def getClassNode(bt: BType): asm.tree.ClassNode = {
      var res = classes.get(bt)
      if(res == null) {
        res = parsed.get(bt)
        if(res == null) {
          res = parseClassAndEnterExemplar(bt)
        }
      }
      assert(exemplars.containsKey(bt))
      res
    }

    /**
     *  can-multi-thread
     * */
    def getClassNodeOrNull(bt: BType): asm.tree.ClassNode = {
      try {
        var res = classes.get(bt)
        if(res == null) {
          res = parsed.get(bt)
          // we can't call parseClassAndEnterExemplar(bt) because in the time window from the checks above and
          // the time parseClassAndEnterExemplar() runs, Worker1 may have added to codeRepo.classes the class we didn't find.
        }
        res
      }
      catch {
        case ex: MissingRequirementError =>
          null // TODO bytecode parsing shouldn't fail, otherwise how could the callsite have compiled?
      }
    }

    /**
     *  A few analyses (e.g., Type-Flow Analysis) require `exemplars` to contain entries for all classes the analysis encounters.
     *  A class that is being compiled is already associated to a Tracked instance (GenBCode took care of that).
     *  For a class `bt` mentioned in external bytecode, this method takes care of creating the necessary entry in `exemplars`.
     *
     *  After this method has run the following two post-conditions hold:
     *    - `exemplars.containsKey(bt)`
     *    - `codeRepo.parsed.containsKey(bt)`
     *
     *  @param bt a "normal" class (see `BType.isNonSpecial`) for which an entry in `exemplars` should be added if not yet there.
     *
     *  @return   the ASM ClassNode after parsing the argument from external bytecode.
     *
     *  must-single-thread
     */
    def parseClassAndEnterExemplar(bt: BType): ClassNode = {
      assert(bt.isNonSpecial,  s"The `exemplars` map is supposed to hold ''normal'' classes only, not ${bt.getInternalName}")
      assert(!containsKey(bt), s"codeRepo already contains ${bt.getInternalName}")

          /** must-single-thread */
          def parseClass(): asm.tree.ClassNode = {
            assert(!containsKey(bt))
            val iname   = bt.getInternalName
            val dotName = iname.replace('/', '.')
            classPath.findSourceFile(dotName) match {
              case Some(classFile) =>
                val cn = new asm.tree.ClassNode()
                val cr = new asm.ClassReader(classFile.toByteArray)
                cr.accept(cn, asm.ClassReader.SKIP_FRAMES)
                parsed.put(bt, cn)
                cn
              case _ => MissingRequirementError.notFound(s"Could not find bytecode for $dotName")
            }
          }

      val cn = parseClass()

      if(exemplars.containsKey(bt)) {
        return cn // TODO check if superName, interfaces, etc agree btw cn and exemplar(bt)
      }

          def enterIfUnseen(iname: String): Tracked = {
            val bt = brefType(iname)
            var exempl = exemplars.get(bt)
            if(exempl == null) {
              parseClassAndEnterExemplar(bt)
              exempl = exemplars.get(bt)
            }
            exempl
          }

          def enterIfUnseens(inames: java.util.List[String]): Array[Tracked] = {
            var ifaces: List[Tracked] = Nil
            val iter = inames.iterator()
            while(iter.hasNext) {
              ifaces ::= enterIfUnseen(iter.next())
            }
            if(ifaces.isEmpty) { EMPTY_TRACKED_ARRAY }
            else {
              val arr = new Array[Tracked](ifaces.size)
              ifaces.copyToArray(arr)
              arr
            }
          }

      val tsc       = enterIfUnseen(cn.superName)
      val ifacesArr = enterIfUnseens(cn.interfaces)

      // ClassNode.innerClasses isn't indexed by InnerClassNode.name, this map accomplishes that feat.
      val innerClassNode: Map[String, InnerClassNode] = {
        JListWrapper(cn.innerClasses) map (icn => (icn.name -> icn)) toMap
      }

      val isInnerClass = innerClassNode.contains(cn.name)
      val innersChain: Array[InnerClassEntry] =
        if(!isInnerClass) null
        else {

              def toInnerClassEntry(icn: InnerClassNode): InnerClassEntry = {
                InnerClassEntry(icn.name, icn.outerName, icn.innerName, icn.access)
              }

          var chain: List[InnerClassEntry] = toInnerClassEntry(innerClassNode(cn.name)) :: Nil
          var keepGoing = true
          do {
            // is the enclosing class of the current class itself an inner class?
            val currentOuter = chain.head.outerName
            keepGoing = innerClassNode.contains(currentOuter)
            if(keepGoing) {
              chain ::= toInnerClassEntry(innerClassNode(currentOuter))
            }
          } while(keepGoing)

          chain.toArray
        }

      val tr = Tracked(bt, cn.access, tsc, ifacesArr, innersChain)
      exemplars.put(tr.c, tr) // no counterpart in symExemplars, that's life.

      cn
    }

    /**
     *  An invariant we want to maintain:
     *    "each internal name mentioned in an instruction that's part of this program
     *     should have a Tracked instance (which implies, a BType instance)"
     *  That invariant guarantees a Type-Flow Analysis can be run anytime, which might be useful.
     *
     *  This method goes over its argument looking for not-yet-seen TypeNames,
     *  fabricating a Tracked instance for them (if needed by parsing bytecode,
     *  thus the location of this method as utility in codeRepo).
     *
     *  Without a TypeName for an internal name or method descriptor, the following conversions can't be performed:
     *    from type-descriptor to BType, via `BCodeTypes.descrToBType()`
     *    from internal-name   to BType, via `BCodeTypes.lookupRefBType()`
     *  In turn, BTypes are indispensable as keys to the `exemplars` map.
     *
     *  must-single-thread
     */
    def enterExemplarsForUnseenTypeNames(insns: InsnList) {

        def enterInternalName(iname: String) {
          var bt = brefType(iname)
          if(bt.isArray) {
            bt = bt.getElementType
          }
          if(bt.isNonSpecial && !exemplars.containsKey(bt)) {
            codeRepo.parseClassAndEnterExemplar(bt)
          }
        }

        def enterDescr(desc: String) {
          val c: Char = desc(0)
          c match {
            case 'V' | 'Z' | 'C' | 'B' | 'S' | 'I' | 'F' | 'J' | 'D' => ()
            case 'L' =>
              val iname = desc.substring(1, desc.length() - 1)
              enterInternalName(iname)
            case '(' =>
              val mt = BType.getMethodType(desc)
              enterDescr(mt.getReturnType.getDescriptor)
              for(argt <- mt.getArgumentTypes) {
                enterDescr(argt.getDescriptor)
              }
            case '[' =>
              val arrt = BType.getType(desc)
              enterDescr(arrt.getComponentType.getDescriptor)
          }
        }

      val iter = insns.iterator()
      while(iter.hasNext) {
        val insn = iter.next()
        insn match {
          case ti: TypeInsnNode   => enterInternalName(ti.desc) // an intenal name, actually
          case fi: FieldInsnNode  => enterInternalName(fi.owner); enterDescr(fi.desc)
          case mi: MethodInsnNode => enterInternalName(mi.owner); enterDescr(mi.desc)
          case ivd: InvokeDynamicInsnNode => () // TODO
          case ci: LdcInsnNode =>
            ci.cst match {
              case t: asm.Type => enterDescr(t.getDescriptor)
              case _           => ()
            }
          case ma: MultiANewArrayInsnNode => enterDescr(ma.desc)
          case _ => ()
        }
      }

    } // end of method enterExemplarsForUnseenTypeNames()

    def clear() {
      parsed.clear()
      classes.clear()
    }

  } // end of object codeRepo

  /**
   * WholeProgramAnalysis needs ClassNodes to be available for all classes being compiled
   * (preparing those ClassNodes is the job of GenBCode's Worker1, with queue q2 being filled as a result).
   * However, `WholeProgramAnalysis.inlining()` does not consume ClassNodes from q2
   * but from a queue of CallGraphNodes (BCodeOptInter.cgns) that is populated during PlainClassBuilder's genDefDef().
   *
   * TODO break up into two or more classes
   */
  final class WholeProgramAnalysis(val isMultithread: Boolean) {

    import asm.tree.analysis.{Analyzer, BasicValue, BasicInterpreter}

    val unreachCodeRemover = new asm.optimiz.UnreachableCode

    /**
     *  TODO documentation
     *
     *  must-single-thread due to
     *    - `populateDClosureMaps()`
     *    - `inlining()`
     *
     **/
    def optimize() {

      closuRepo.populateDClosureMaps()
      closuRepo.populateNonMasterUsers()

      privatizables.clear()
      inlining()
      // println(s"About to privatize: ${privatizables.size} shio methods.") // debug
      for(priv <- privatizables; shioMethod <- priv._2) { Util.makePrivateMethod(shioMethod) }
      privatizables.clear()

      // val howManyDClosures: Float = closuRepo.endpoint.keySet.size
      // val howManyShared   : Float = closuRepo.nonMasterUsers.keySet.size
      // println("Proportion of dclosures in use by non-master to those used only from master:" howManyShared / howManyDClosures)

      if(settings.isSmallPrivateInlineOn) {
        val compiledClassesIter = codeRepo.classes.values().iterator()
        while(compiledClassesIter.hasNext) {
          percolateUpwards(compiledClassesIter.next())
        }
      }

    }

    /**
     * shio methods are collected as they are built in the `privatizables` map, grouped by their ownning class.
     * (That class also owns what used to be the endpoint of the delegating-closure that was inlined).
     *
     * shio methods spend most of their time as public methods, so as not to block method-inlining
     * (they're synthetically generated, thus it would come as a surprise if they required attention from the developer).
     * However, in case no method-inlining transplanted them to another class, they are made private as initially intended.
     * */
    private val privatizables = new MethodsPerClass

    private class MethodsPerClass extends mutable.HashMap[BType, List[MethodNode]] {

      def track(k: ClassNode, v: MethodNode) { track(lookupRefBType(k.name), v) }
      def track(k: BType,     v: MethodNode) { put(k, v :: getOrElse(k, Nil)) }

      /**
       *  It's ok trying to untrack a method that's not being tracked. If in doubt, call untrack()
       * */
      def untrack(k: BType, v: MethodNode) {
        val v2 = getOrElse(k, Nil) filterNot { _ eq v }
        if(v2.isEmpty) { remove(k)  }
        else           { put(k, v2) }
      }

      /**
       *  It's ok trying to untrack a method that's not being tracked. If in doubt, call untrack()
       * */
      def untrack(k: BType, methodName: String, methodDescr: String) {
        val v2 = getOrElse(k, Nil) filterNot { mn => (mn.name == methodName) && (mn.desc == methodDescr) }
        if(v2.isEmpty) { remove(k)  }
        else           { put(k, v2) }
      }

    } // end of class MethodsPerClass

    // -------------------------------------------------------------------------------
    // ------------------------------- inlining rounds -------------------------------
    // -------------------------------------------------------------------------------

    /**
     *  Performs closure-inlining and method-inlining, by first breaking any cycles
     *  over the "inlined-into" relation (see local method `isReachable()`).
     *  Afterwards,
     *    - `WholeProgramAnalysis.inlineMethod()`   takes care of method-inlining
     *    - `WholeProgramAnalysis.inlineClosures()` of closure-inlining
     *
     *  must-single-thread
     *
     **/
    private def inlining() {

      /*
       * The MethodNode for each callsite to an @inline method is found via `CallGraphNode.populate()`,
       * if necessary by parsing bytecode (ie the classfile given by a callsite's `owner` field is parsed).
       * This is safe because by the time `WholeProgramAnalysis.inlining()` is invoked
       * all classes being compiled have been put in `codeRepo.classes` already.
       * Not finding a class there means it has to be parsed.
       */
      val mn2cgn = mutable.Map.empty[MethodNode, CallGraphNode]
      for(cgn <- cgns) {
        cgn.populate()
        assert(cgn.isRepOK)
        mn2cgn += (cgn.host -> cgn)
      }

          /**
           * @return true iff there's a chain of inline-requests starting at `start` that contains `goal`
           * */
          def isReachable(start: MethodNode, goal: MethodNode, visited: Set[MethodNode]): Boolean = {
            (start eq goal) ||
            (visited contains goal) || {

              val directCallees: Set[MethodNode] = {
                mn2cgn.get(start) match {
                  case Some(startCGN) => startCGN.directCallees
                  case _              => Set.empty
                }
              }
              (directCallees contains goal) || {
                val visited2 = (visited ++ directCallees)

                directCallees exists { d => isReachable(d, goal, visited2) }
              }

            }
          }

      for(cgn <- cgns) {
        cgn.hiOs  = cgn.hiOs  filterNot { it: InlineTarget => isReachable(it.callee, cgn.host, Set.empty) }
        cgn.procs = cgn.procs filterNot { it: InlineTarget => isReachable(it.callee, cgn.host, Set.empty) }
      }

      /**
       *  It only remains to visit the elements of `cgns` in an order that ensures
       *  a CallGraphNode has stabilitzed by the time it's inlined into a host method.
       *  "A CallGraphNode has stabilized" means all inlinings have been performed inside it,
       *  where those inlinings were based on callees that were themselves already stabilized.
       */
      val remaining = mutable.Set.empty[CallGraphNode]
      remaining ++= cgns.toList
      while(remaining.nonEmpty) {
        val leaves = remaining.filter( cgn => cgn.candidates.forall( c => !mn2cgn.contains(c.callee) || !remaining.contains(mn2cgn(c.callee)) ) )
        assert(leaves.nonEmpty, "Otherwise loop forever")
        inliningRound(leaves)
        remaining --= leaves
      }

    } // end of method inlining()

    /**
     *  TODO documentation
     *
     *  TODO leaves are independent from each other, could be done in parallel.
     *
     *  @param leaves        TODO
     *
     * */
    private def inliningRound(leaves: collection.Set[CallGraphNode]) {

      leaves foreach { leaf => inlineCallees(leaf) }

    }

    /**
     *  Perform inlinings in a single method (given by `CallGraphNode.host`)
     *  of the callees given by `CallGraphNode.procs` and `CallGraphNode.hiOs`.
     *
     *  @param leaf         TODO
     *
     *  must-single-threadd
     */
    private def inlineCallees(leaf: CallGraphNode) {

      // debug: `Util.textify(leaf.host)` can be used to record (before and after) what the host-method looks like.

      //----------------------------------------------------------------------
      // Part 1 of 4: Dead-code elimination, reporting about callsites that are dead
      //----------------------------------------------------------------------

          def logDead(callsite: MethodInsnNode) {
            log(
              s"Dead-code elimination in method ${methodSignature(leaf.hostOwner, leaf.host)} " +
              s"has removed a callsite that was marked for inlining, callsite ${Util.textify(callsite)}"
            )
          }

      {
        // UnreachableCode eliminates null frames (which complicate further analyses).
        Util.computeMaxLocalsMaxStack(leaf.host)
        unreachCodeRemover.transform(leaf.hostOwner.name, leaf.host)
        val (remainingProcs, deadCodeProcs) = leaf.procs partition { proc => leaf.host.instructions.contains(proc.callsite) }
        for(proc <- deadCodeProcs) { logDead(proc.callsite) }
        leaf.procs = remainingProcs
        val (remainingHiOs, deadHiOs) = leaf.hiOs partition { hiO => leaf.host.instructions.contains(hiO.callsite) }
        for(hiO <- deadHiOs) { logDead(hiO.callsite) }
        leaf.hiOs = remainingHiOs
      }

      //----------------------------------------------------------------------
      // Part 2 of 4: Type-Flow Analysis to determine non-nullness of receiver
      //----------------------------------------------------------------------

      val tfa = new Analyzer[TFValue](new TypeFlowInterpreter)
      tfa.analyze(leaf.hostOwner.name, leaf.host)
      // looking up in array `frames` using the whatever-then-current index of `insn` would assume the instruction list hasn't changed.
      // while in general after adding or removing instructions an analysis should be re-run,
      // for the purposes of inlining it's ok to have at hand for a callsite its frame as it was when the analysis was computed.
      val tfaFrameAt: Map[MethodInsnNode, asm.tree.analysis.Frame[TFValue]] = {
         leaf.candidates
        .filter(it => leaf.host.instructions.contains(it.callsite))
        .map(it => it.callsite -> tfa.frameAt(it.callsite).asInstanceOf[asm.tree.analysis.Frame[TFValue]]).toMap
      }

      //-----------------------------
      // Part 3 of 4: method-inlining
      //-----------------------------

      leaf.procs foreach { proc =>

        val hostOwner = leaf.hostOwner.name
        val frame     = tfaFrameAt(proc.callsite)

        val inlineMethodOutcome = inlineMethod(
          hostOwner,
          leaf.host,
          proc.callsite,
          frame,
          proc.callee, proc.owner,
          doTrackClosureUsage = true
        )
        inlineMethodOutcome foreach proc.warn

        val success = inlineMethodOutcome.isEmpty
        logInlining(
          success, hostOwner, leaf.host, proc.callsite, isHiO = false,
          isReceiverKnownNonNull(frame, proc.callsite),
          proc.callee, proc.owner
        )

      }
      leaf.procs = Nil

      //------------------------------
      // Part 4 of 4: closure-inlining
      //------------------------------

      leaf.hiOs foreach { hiO =>

        val callsiteTypeFlow = tfaFrameAt(hiO.callsite)
        assert(callsiteTypeFlow != null,
          s"Most likely dead-code found in method ${methodSignature(leaf.hostOwner, leaf.host)} " +
          s"because at instruction ${Util.textify(hiO.callsite)} (at index ${leaf.host.instructions.indexOf(hiO.callsite)}}) " +
           "no frame is computed by type-flow analysis. Here's the complete bytecode of that method " + Util.textify(leaf.host)
        )

        val success = inlineClosures(
          leaf.hostOwner,
          leaf.host,
          callsiteTypeFlow,
          hiO
        )

        val hasNonNullReceiver = isReceiverKnownNonNull(callsiteTypeFlow, hiO.callsite)
        logInlining(
          success, leaf.hostOwner.name, leaf.host, hiO.callsite, isHiO = true,
          hasNonNullReceiver,
          hiO.callee, hiO.owner
        )

      }
      leaf.hiOs = Nil

      // debug
      val da = new Analyzer[BasicValue](new asm.tree.analysis.BasicVerifier)
      da.analyze(leaf.hostOwner.name, leaf.host)
    }

    /**
     * SI-5850: Inlined code shouldn't forget null-check on the original receiver
     */
    private def isReceiverKnownNonNull(frame: asm.tree.analysis.Frame[TFValue], callsite: MethodInsnNode): Boolean = {
      callsite.getOpcode match {
        case Opcodes.INVOKEDYNAMIC => false // TODO
        case Opcodes.INVOKESTATIC  => true
        case Opcodes.INVOKEVIRTUAL   |
             Opcodes.INVOKESPECIAL   |
             Opcodes.INVOKEINTERFACE =>
          val rcv:  TFValue = frame.getReceiver(callsite)
          assert(rcv.lca.hasObjectSort)
          rcv.isNonNull
      }
    }

    /**
     * This method takes care of all the little details around inlining the callee's instructions for a callsite located in a `host` method.
     * Those details boil down to:
     *   (a) checking whether inlining is feasible. If unfeasible, don't touch anything and return false.
     *   (b) replacing the callsite with:
     *       STORE instructions for expected arguments,
     *       callee instructions adapted to their new environment
     *         (accesses to local-vars shifted,
     *          RETURNs replaced by jumps to the single-exit of the inlined instructions,
     *          without forgetting to empty all the stack slots except stack-top right before jumping)
     *   (c) copying the debug info from the callee's over to the host method
     *   (d) re-computing the maxLocals and maxStack of the host method.
     *   (e) return None (this indicates success).
     *
     * Inlining is considered unfeasible in three cases, summarized below and described in more detail on the spot:
     *   (a.0) callee is a synchronized method
     *   (a.1) due to the possibility of the callee clearing the operand-stack when entering an exception-handler, as well as
     *   (a.2) inlining would lead to illegal access errors.
     *   (a.3) calee returns scala.runtime.Nothing$ , which means it'll throw an exception
     *         (s.r.Nothing$ looks like an object to the type-flow analysis).
     *
     * @param hostOwner   internal name of the class declaring the host method
     * @param host        method containing a callsite for which inlining has been requested
     * @param callsite    invocation whose inlining is requested.
     * @param frame       informs about stack depth at the callsite
     * @param callee      actual method-implementation that will be dispatched at runtime.
     * @param calleeOwner class that declares callee
     * @param doTrackClosureUsage TODO documentation
     *
     * @return None iff method-inlining was actually performed,
     *         Some(diagnostics) iff the inlining is unfeasible.
     *
     */
    def inlineMethod(hostOwner:     String,
                     host:          MethodNode,
                     callsite:      MethodInsnNode,
                     frame:         asm.tree.analysis.Frame[TFValue],
                     callee:        MethodNode,
                     calleeOwner:   ClassNode,
                     doTrackClosureUsage: Boolean): Option[String] = {

      assert(host.instructions.contains(callsite))
      assert(callee != null)
      assert(callsite.name == callee.name)
      assert(callsite.desc == callee.desc)
      assert(!Util.isConstructor(callee))

      val hostId   = hostOwner        + "::" + host.name   + host.desc
      val calleeId = calleeOwner.name + "::" + callee.name + callee.desc

      /*
       * Situation (a.0) under which method-inlining is unfeasible: synchronized callee.
       */
      if(Util.isSynchronizedMethod(callee)) {
        return Some(s"Closure-inlining failed because ${methodSignature(calleeOwner, callee)} is synchronized.")
      }

      /*
       * Situation (a.1) under which method-inlining is unfeasible: In case both conditions below hold:
       *   (a.1.i ) the operand stack may be cleared in the callee, and
       *   (a.1.ii) the stack at the callsite in host contains more values than args expected by the callee.
       *
       * Alternatively, additional STORE instructions could be inserted to park those extra values while the inlined body executes,
       * but the overhead doesn't make it worth the effort.
       */
      if(!callee.tryCatchBlocks.isEmpty) {
        val stackHeight       = frame.getStackSize
        val expectedArgs: Int = Util.expectedArgs(callsite)
        if(stackHeight > expectedArgs) {
          return Some(
            s"The operand stack may be cleared on entering an exception-handler in $calleeId , and " +
            s"the stack at the callsite in $hostId contains more values than args expected by the callee."
          )
        }
        assert(stackHeight == expectedArgs)
      }

      // instruction cloning requires the following map to consistently replace new for old LabelNodes.
      val labelMap = Util.clonedLabels(callee)

      /*
       * In general callee.instructions and bodyInsns aren't same size,
       * for example because calleeInsns may contain FrameNodes which weren't cloned into body.
       * Therefore, don't try to match up original and cloned instructions by position!
       * Instead, `insnMap` is a safe way to find a cloned instruction using the original as key.
       */
      val insnMap   = new java.util.HashMap[AbstractInsnNode, AbstractInsnNode]()
      val body      = Util.clonedInsns(callee.instructions, labelMap, insnMap)
      val bodyInsns = body.toArray

      /*
       * In case the callee has been parsed from bytecode,
       * its instructions may refer to type descriptors and internal names
       * that as of yet lack a corresponding TypeName in Names.chrs
       * (the GenBCode infrastructure standardizes on TypeNames for lookups.
       * The utility below takes care of creating TypeNames for those descriptors and internal names.
       * Even if inlining proves unfeasible, those TypeNames won't cause any harm.
       *
       * TODO why weren't those TypeNames entered as part of parsing callee from bytecode?
       *      After all, we might want to run e.g. Type-Flow Analysis on external methods before inlining them.
       */
      if(!isMultithread) {
        codeRepo.enterExemplarsForUnseenTypeNames(body) // must-single-thread
      }

      val hostOwnerBT = lookupRefBType(hostOwner)

      val illegalAccessInsn = allAccessesLegal(body, hostOwnerBT)
      if(illegalAccessInsn != null) {
        return Some(
          s"Callee $calleeId contains instruction \n${Util.textify(illegalAccessInsn)}that would cause IllegalAccessError from class $hostOwner"
        )
      }

      val calleeMethodType = BType.getMethodType(callee.desc) // must-single-thread

      /*
       * Situation (a.3) under which method-inlining is unfeasible: callee has Nothing type.
       */
      if(calleeMethodType.getReturnType.isNothingType) {
        return Some(s"Closure-inlining failed because ${methodSignature(calleeOwner, callee)} has Nothing type.")
      }

      // By now it's a done deal that method-inlining will be performed. There's no going back.

      // each local-var access in `body` is shifted host.maxLocals places
      for(bodyInsn <- bodyInsns; if bodyInsn.getType == AbstractInsnNode.VAR_INSN) {
        val lvi = bodyInsn.asInstanceOf[VarInsnNode]
        lvi.`var` += host.maxLocals
      }

      // add a STORE instruction for each expected argument, including for THIS instance if any.
      val argStores   = new InsnList
      var nxtLocalIdx = host.maxLocals
      if(Util.isInstanceMethod(callee)) {
        argStores.insert(new VarInsnNode(Opcodes.ASTORE, nxtLocalIdx))
        nxtLocalIdx    += 1
      }
      for(at <- calleeMethodType.getArgumentTypes) {
        val opc         = at.toASMType.getOpcode(Opcodes.ISTORE)
        argStores.insert(new VarInsnNode(opc, nxtLocalIdx))
        nxtLocalIdx    += at.getSize
      }
      body.insert(argStores)

      // body's last instruction is a LabelNode denoting the single-exit point
      val postCall   = new asm.Label
      val postCallLN = new asm.tree.LabelNode(postCall)
      postCall.info  = postCallLN
      body.add(postCallLN)

          /**
           * body may contain xRETURN instructions, each should be replaced at that program point
           * by DROPs (as needed) for all slots but stack-top.
           */
          def replaceRETURNs() {
            val retType        = calleeMethodType.getReturnType
            val hasReturnValue = !retType.isUnitType
            val retVarIdx      = host.maxLocals + callee.maxLocals
            nxtLocalIdx       += retType.getSize

            if(hasReturnValue) {
              val retVarLoad = {
                val opc = retType.toASMType.getOpcode(Opcodes.ILOAD)
                new VarInsnNode(opc, retVarIdx)
              }
              assert(body.getLast == postCallLN)
              body.insert(body.getLast, retVarLoad)
            }

                def retVarStore(retInsn: InsnNode) = {
                  val opc = retInsn.getOpcode match {
                    case Opcodes.IRETURN => Opcodes.ISTORE
                    case Opcodes.LRETURN => Opcodes.LSTORE
                    case Opcodes.FRETURN => Opcodes.FSTORE
                    case Opcodes.DRETURN => Opcodes.DSTORE
                    case Opcodes.ARETURN => Opcodes.ASTORE
                  }
                  new VarInsnNode(opc, retVarIdx)
                }

            val ca = new Analyzer[BasicValue](new BasicInterpreter)
            ca.analyze(callsite.owner, callee)
            val insnArr = callee.instructions.toArray // iterate this array while mutating callee.instructions at will
            for(calleeInsn <- insnArr;
                if calleeInsn.getOpcode >= Opcodes.IRETURN && calleeInsn.getOpcode <= Opcodes.RETURN)
            {
              val retInsn = calleeInsn.asInstanceOf[InsnNode]
              val frame   = ca.frameAt(retInsn) // NPE means dead-code wasn't removed from the callee before calling inlineMethod
              val height  = frame.getStackSize
              val counterpart = insnMap.get(retInsn)
              assert(counterpart.getOpcode == retInsn.getOpcode)
              assert(hasReturnValue == (retInsn.getOpcode != Opcodes.RETURN))
              val retRepl = new InsnList
              // deal with stack-top: either drop it or keep its value in retVar
              if(hasReturnValue)  { retRepl.add(retVarStore(retInsn)) }
              else if(height > 0) { retRepl.add(Util.getDrop(frame.peekDown(0).getSize)) }
              // deal with the rest of the stack
              for(slot <- 1 until height) {
                retRepl.add(Util.getDrop(frame.peekDown(slot).getSize))
              }
              retRepl.add(new JumpInsnNode(Opcodes.GOTO, postCallLN))
              body.insert(counterpart, retRepl)
              body.remove(counterpart)
            }
          }

      replaceRETURNs()

      if(doTrackClosureUsage) {
        checkTransplantedAccesses(body, hostOwnerBT)
      }

      host.instructions.insert(callsite, body) // after this point, body.isEmpty (an ASM instruction can be owned by a single InsnList)
      host.instructions.remove(callsite)

      // let the host know about the debug info of the callee
      host.localVariables.addAll(Util.clonedLocalVariableNodes(callee, labelMap, callee.name + "_"))
      host.tryCatchBlocks.addAll(Util.clonedTryCatchBlockNodes(callee, labelMap))

      // the host's local-var space grows by the local-var space of the callee, plus another local-var in case hasReturnValue
      Util.computeMaxLocalsMaxStack(host)
      assert(host.maxLocals >= nxtLocalIdx) // TODO why not == ? Likely because a RETURN in callee adds no extra var in host for result, while IRETURN etc do.

      None

    } // end of method inlineMethod()

    private def logInlining(success:   Boolean,
                            hostOwner: String,
                            host:      MethodNode,
                            callsite:  MethodInsnNode,
                            isHiO:     Boolean,
                            isReceiverKnownNonNull: Boolean,
                            hiO:       MethodNode,
                            hiOOwner:  ClassNode) {

      val remark  = if(isReceiverKnownNonNull) ""  else " (albeit null receiver couldn't be ruled out)"
      val kind    = if(isHiO)   "closure-inlining" else "method-inlining"
      val leading = if(success) "Successful " + kind + remark else "Failed " + kind

      log(
        leading +
        s". Callsite: ${callsite.owner}.${callsite.name}${callsite.desc} , occurring in method $hostOwner::${host.name}${host.desc}"
      )

      if(!success) {
        debuglog(s"Bytecode of callee, declared by ${hiOOwner.name} \n" + Util.textify(hiO))
      }

    } // end of method logInlining()

    /**
     * Situation (a.2) under which method-inlining is unfeasible:
     *   In case access control doesn't give green light.
     *   Otherwise a java.lang.IllegalAccessError would be thrown at runtime.
     *
     * Quoting from the JVMS (our terminology: `there` stands for `C`; `here` for `D`):
     *
     *  5.4.4 Access Control
     *
     *  A class or interface C is accessible to a class or interface D if and only if either of the following conditions is true:
     *    (cond A1) C is public.
     *    (cond A2) C and D are members of the same runtime package (Sec 5.3).
     *
     *  A field or method R is accessible to a class or interface D if and only if any of the following conditions are true:
     *    (cond B1) R is public.
     *    (cond B2) R is protected and is declared in a class C, and D is either a subclass of C or C itself.
     *              Furthermore, if R is not static, then the symbolic reference to R
     *              must contain a symbolic reference to a class T, such that T is either a subclass
     *              of D, a superclass of D or D itself.
     *    (cond B3) R is either protected or has default access (that is, neither public nor
     *              protected nor private), and is declared by a class in the same runtime package as D.
     *    (cond B4) R is private and is declared in D.
     *
     *  This discussion of access control omits a related restriction on the target of a
     *  protected field access or method invocation (the target must be of class D or a
     *  subtype of D). That requirement is checked as part of the verification process
     *  (Sec 5.4.1); it is not part of link-time access control.
     *
     *  @param body instructions that will be inlined in a method in class `here`
     *  @param here class from which accesses given by `body` will take place.
     *
     *  @return the first instruction found in `body`
     *          that would result in java.lang.IllegalAccessError if used from class `here`.
     *
     */
    private def allAccessesLegal(body: InsnList, here: BType): AbstractInsnNode = {

          /**
           * @return whether the first argument is a subtype of the second, or both are the same BType.
           */
          def isSubtypeOrSame(a: BType, b: BType): Boolean = {
            (a == b) || {
              val ax = exemplars.get(a)
              val bx = exemplars.get(b)

              (ax != null) && (bx != null) && ax.isSubtypeOf(b)
            }
          }

          /**
           * Furthermore, if R is not static, then the symbolic reference to R
           * must contain a symbolic reference to a class T, such that T is either a subclass
           * of D, a superclass of D or D itself.
           */
          def sameLineage(thereSymRef: BType): Boolean = {
            (thereSymRef == here) ||
            isSubtypeOrSame(thereSymRef, here) ||
            isSubtypeOrSame(here, thereSymRef)
          }

          def samePackageAsHere(there: BType): Boolean = { there.getRuntimePackage == here.getRuntimePackage }

          def memberAccess(flags: Int, thereOwner: BType): Boolean = {
            val key = { (Opcodes.ACC_PUBLIC | Opcodes.ACC_PROTECTED | Opcodes.ACC_PRIVATE) & flags }
            key match {

              case 0 /* default access */ => // (cond B3)
                samePackageAsHere(thereOwner)

              case Opcodes.ACC_PUBLIC     => // (cond B1)
                true

              case Opcodes.ACC_PROTECTED  =>
                // (cond B2)
                val condB2 = isSubtypeOrSame(here, thereOwner) && {
                  val isStatic = ((Opcodes.ACC_STATIC & flags) != 0)
                  isStatic || sameLineage(thereOwner)
                }
                condB2 || samePackageAsHere(thereOwner)

              case Opcodes.ACC_PRIVATE    => // (cond B4)
                (thereOwner == here)
            }
          }

      val iter = body.iterator()
      while(iter.hasNext) {
        val insn    = iter.next()
        val isLegal = insn match {

          case ti: TypeInsnNode  => isAccessible(lookupRefBType(ti.desc), here)

          case fi: FieldInsnNode =>
            val fowner: BType = lookupRefBType(fi.owner)
            val fn: FieldNode = codeRepo.getFieldOrNull(fowner, fi.name, fi.desc)
            (fn != null) && memberAccess(fn.access, fowner)

          case mi: MethodInsnNode =>
            val thereSymRef: BType  = lookupRefBType(mi.owner)
            val mAccess: Option[Int] = codeRepo.getMethodAccess(thereSymRef, mi.name, mi.desc, isMultithread)
            mAccess.nonEmpty && memberAccess(mAccess.get, thereSymRef)

          case ivd: InvokeDynamicInsnNode => false // TODO

          case ci: LdcInsnNode =>
            ci.cst match {
              case t: asm.Type => isAccessible(lookupRefBType(t.getInternalName), here)
              case _           => true
            }

          case ma: MultiANewArrayInsnNode =>
            val et = descrToBType(ma.desc).getElementType
            if(et.hasObjectSort) isAccessible(et, here)
            else true

          case _ => true
        }
        if(!isLegal) {
          return insn
        }
      }

      null // stands for "all accesses legal"

    } // end of method allAccessesLegal()

    /**
     * See also method `allAccessesLegal()`
     *
     * Quoting from the JVMS (our terminology: `there` stands for `C`; `here` for `D`):
     *
     *  5.4.4 Access Control
     *
     *  A class or interface C is accessible to a class or interface D if and only if either of the following conditions is true:
     *    (cond A1) C is public.
     *    (cond A2) C and D are members of the same runtime package (Sec 5.3).
     */
    private def isAccessible(there: BType, here: BType): Boolean = {
      if(!there.isNonSpecial) true
      else if (there.isArray) isAccessible(there.getElementType, here)
      else {
        assert(there.hasObjectSort, "not of object sort: " + there.getDescriptor)
        (there.getRuntimePackage == here.getRuntimePackage) || exemplars.get(there).isPublic
      }
    }

    private def allExceptionsAccessible(tcns: java.util.List[TryCatchBlockNode], here: BType): Boolean = {
      JListWrapper(tcns).forall( tcn => (tcn.`type` == null) || isAccessible(lookupRefBType(tcn.`type`), here) )
    }

    private def allLocalVarTypesAccessible(lvns: java.util.List[LocalVariableNode], here: BType): Boolean = {
      JListWrapper(lvns).forall( lvn => {
        val there = descrToBType(lvn.desc)

        there.isValueType || isAccessible(there, here)
      } )
    }

    /**
     * This method inlines the invocation of a "higher-order method" and
     * stack-allocates the anonymous closures received as arguments.
     *
     * "Stack-allocating" in the sense of "scalar replacement of aggregates" (see also "object fusion").
     * This can always be done for closures converted in UnCurry via `closureConversionModern()`
     * a conversion that has the added benefit of minimizing pointer-chasing (heap navigation).
     *
     *
     * Rationale
     * ---------
     *
     * Closure inlining results in faster code by specializing a higher-order method
     * to the particular anonymous closures given as arguments at a particular callsite
     * (at the cost of code duplication, namely of the Hi-O method, no other code gets duplicated).
     *
     * The "Hi-O" method usually applies the closure inside a loop (e.g., map and filter fit this description)
     * that's why a hi-O callsite can be regarded for most practical purposes as a loop-header.
     * "Regarded as a loop header" because we'd like the JIT compiler to pick that code section for compilation.
     * If actually a loop-header, and the instructions for the hi-O method were inlined,
     * then upon OnStackReplacement the whole method containing the hi-O invocation would have to be compiled
     * (which might well not be hot code itself).
     *
     * To minimize that wasted effort, `inlineClosures()` creates a dedicated (static, synthetic) method
     * for a given combination of hi-O and closures to inline
     * (not all closures might be amenable to inlining, details below).
     * In that method, closure-apply() invocations are inlined, thus cancelling out:
     *   - any redundant box-unbox pairs when passing arguments to closure-apply(); as well as
     *   - any unbox-box pair for its return value.
     *
     *
     * Terminology
     * -----------
     *
     * hi-O method:     the "higher-order" method taking one or more closure instances as argument. For example, Range.foreach()
     *
     * closure-state:   the values of fields of an anonymous-closure-class, all of them final.
     *                  In particular an $outer field is present whenever the closure "contains" inner classes (in particular, closures).
     *
     * closure-methods: apply() which possibly forwards to a specialized variant after unboxing some of its arguments.
     *                  For a closure converted in UnCurry:
     *                    - via `closureConversionModern()` there are no additional closure-methods.
     *                    - via `closureConversionTraditional()`  those methods that were local to the source-level apply()
     *                      also become closure-methods after lambdalift.
     *
     * closure-constructor: a sequence of assignments to initialize the (from then on immutable) closure-state by copying arguments' values.
     *                      The first such argument is always the THIS of the invoker,
     *                      which becomes the $outer value from the perspective of the closure-class.
     *
     *
     * Preconditions
     * -------------
     *
     * In order to stack-allocate a particular closure passed to Hi-O,
     * the closure in question should not escape from Hi-O (a necessary condition).
     * There's in fact a whole cascade of prerequisites to check,
     * desribed in detail in helper methods `survivors1()` to `survivors3()`,
     * with some yet more pre-conditions being check in `ClosureClassUtil.isRepOK()`.
     *
     * Rewriting mechanics
     * -------------------
     *
     * Provided all pre-conditions have been satisfied, `StaticHiOUtil.buildStaticHiO()` is tasked with
     * preparing a MethodNode that will be invoked instead of hi-O. That method is the last one to have veto power.
     * If successful, it only remains for `StaticHiOUtil.rewriteHost()` to patch `host` to changed the target of
     * the original callsite invocation, as well as adapt its arguments.
     *
     * @param hostOwner        the class declaring the host method.
     *                         Upon successful closure-inling, a "static-HiO" ("shio") method is added to hostOwner.
     * @param host             the method containing a callsite for which inlining has been requested
     * @param callsiteTypeFlow the type-stack reaching the callsite. Useful for knowing which args are closure-typed.
     * @param inlineTarget     inlining request (includes: callsite, callee, callee's owner, and error reporting)
     *
     * @return true iff inlining was actually performed.
     *
     * must-single-thread
     *
     */
    private def inlineClosures(hostOwner:        ClassNode,
                               host:             MethodNode,
                               callsiteTypeFlow: asm.tree.analysis.Frame[TFValue],
                               inlineTarget:     InlineTarget): Boolean = {

      // invocation of a higher-order method (taking one or more closures) whose inlining is requested.
      val callsite: MethodInsnNode = inlineTarget.callsite
      // the actual implementation of the higher-order method that will be dispatched at runtime
      val hiO:      MethodNode     = inlineTarget.callee
      // the Classnode where callee is declared.
      val hiOOwner: ClassNode      = inlineTarget.owner

      val callerId = hostOwner.name + "::" + host.name + host.desc

      assert(!isMultithread)
      codeRepo.enterExemplarsForUnseenTypeNames(hiO.instructions) // must-single-thread

      if(Util.isSynchronizedMethod(hiO)) {
        inlineTarget.warn(s"Closure-inlining failed because ${inlineTarget.calleeId} is synchronized.")
        return false
      }

      val illegalAccessInsn = allAccessesLegal(hiO.instructions, lookupRefBType(hostOwner.name))
      if(illegalAccessInsn != null) {
        inlineTarget.warn(
          s"Closure-inlining failed because ${inlineTarget.calleeId} contains instruction \n${Util.textify(illegalAccessInsn)}" +
          s"that would cause IllegalAccessError from class ${hostOwner.name}"
        )
        return false
      }

            /**
             *  Which params of the hiO method receive closure-typed arguments?
             *
             *  Param-positions are zero-based.
             *  The receiver (of an instance method) is ignored: "params" refers to those listed in a JVM-level method descriptor.
             *  There's a difference between formal-param-positions (as returned by this method) and local-var-indexes (as used in a moment).
             *  The latter take into account the JVM-type-size of previous locals, while param-positions are numbered consecutively.
             *
             *  @return the positions of those hiO method-params taking a closure-typed actual argument.
             */
            def survivors1(): collection.Set[Int] = {

              val actualsTypeFlow: Array[TFValue] = callsiteTypeFlow.getActualArguments(callsite) map (_.asInstanceOf[TFValue])
              var idx = 0
              var survivors = mutable.LinkedHashSet[Int]()
              while(idx < actualsTypeFlow.length) {
                val tf = actualsTypeFlow(idx)
                if(tf.lca.isClosureClass) {
                  survivors += idx
                }
                idx += 1
              }

              survivors
            }

      val closureTypedHiOArgs = survivors1()
      if(closureTypedHiOArgs.isEmpty) {
        /*
         * Example,
         *   callsite `global.log`
         *   in `def log(msg: => AnyRef) { global.log(msg) }`
         * will have empty closureTypedArgs because it receives a Function0, not a closure-class.
         * We try to overcome that by method-inlining (not closure-inlining) that callsite.
         * Doing so may unblock closure-inlining of the closure(s) passed to `host` (itself a higher-order method).
         *
         */
        val asMethodInlineOutcome =
          inlineMethod(
            hostOwner.name, host,
            callsite, callsiteTypeFlow,
            hiO, hiOOwner,
            doTrackClosureUsage = true
          )

        asMethodInlineOutcome match {

          case Some(diagnostics) =>
            inlineTarget.warn(diagnostics)
            return false

          case None =>
            val quickOptimizer = new BCodeCleanser(hostOwner)
            quickOptimizer.basicIntraMethodOpt(host)
            Util.computeMaxLocalsMaxStack(host)
            return true // not really "successful closure-inlining" (see comment above) but the closest we can get.

        }

      }

          /**
           * Pre-requisites on host method
           *
           * Given
           *   (1) a copy-propagating, params-aware, Consumers-Producers analysis of the host method,
           *   (2) the previous subset of params (ie those receiving closure-typed actual arguments)
           * determine those params that receive a unique closure, and look up the ClassNode for the closures in question.
           *
           * N.B.: Assuming the standard compiler transforms as of this writing, `survivors2()` isn't strictly necessary.
           * However it protects against any non-standard transform that messes up with preconds required for correctness.
           *
           * `survivors2()` goes over the formal params in `survivors1()`, picking those that have a single producer,
           * such that the value thus produced is the only actual for the param in question.
           *
           * Given that the type of the actual fulfills Tracked.isClosureClass,
           * the ClassNode of that type can be found in codeRepo.classes (it's being compiled in this run).
           *
           * @return a map with an entry for each hiO method-param that takes a closure,
           *         where an entry maps the position of the method-param to a closure class.
           */
          def survivors2(): Map[Int, ClassNode] = {

            // if cpHost where to be hoisted out of this method, cache `cpHost.frameAt()` before hiOs are inlined.
            val cpHost: UnBoxAnalyzer = UnBoxAnalyzer.create()
            cpHost.analyze(hostOwner.name, host)
            val callsiteCP: asm.tree.analysis.Frame[SourceValue] = cpHost.frameAt(callsite)
            val actualsProducers: Array[SourceValue] = callsiteCP.getActualArguments(callsite) map (_.asInstanceOf[SourceValue])
            val closureProducers: Map[SourceValue, Int] = closureTypedHiOArgs.map(idx => (actualsProducers(idx) -> idx)).toMap

            for(
              (prods, idx) <- closureProducers;
              if (prods.insns.size() == 1);
              singleProducer = prods.insns.iterator().next();
              if(singleProducer.getOpcode == Opcodes.NEW);
              closureBT = lookupRefBType(singleProducer.asInstanceOf[TypeInsnNode].desc)
              if(!isPartialFunctionType(closureBT))
            ) yield (idx, codeRepo.classes.get(closureBT))
          }

      val closureClassPerHiOFormal = survivors2()
      if(closureClassPerHiOFormal.isEmpty) {
        inlineTarget.warn(
          s"Can't perform closure-inlining because in $callerId different closures may arrive at the same argument position."
        )
        return false
      }

          /**
           * Pre-requisites on hiO method
           *
           * A closure `f` used in hiO method can be stack-allocated provided
           * all usages are of the form `f.apply(...)`, and only of that form.
           *
           * This is checked bytecode-level by looking up all usages of hiO's method-param conveying `f`
           * and checking whether they're of the form shown above.
           *
           * @return for each closure-conveying param in method hiO,
           *         information about that closure and its usages (see `ClosureUsages`).
           *
           */
          def survivors3(): Iterable[ClosureUsages] = {

            val cpHiO: ProdConsAnalyzer = ProdConsAnalyzer.create()
            cpHiO.analyze(hiOOwner.name, hiO)

            val mtHiO = BType.getMethodType(hiO.desc)
            val isInstanceMethod = Util.isInstanceMethod(hiO)

                /**
                 *  Checks whether all closure-usages (in hiO) are of the form `closure.apply(...)`
                 *  and if so return the MethodNode for that apply(). Otherwise null.
                 *
                 *  @param closureClass     class realizing the closure of interest
                 *  @param localVarIdxHiO   local-var in hiO (a formal param) whose value is the closure of interest
                 *  @param closureArgUsages instructions where the closure is used as input
                 */
                def areAllApplyCalls(closureClass:      ClassNode,
                                     localVarIdxHiO:    Int,
                                     closureArgUsages:  collection.Set[AbstractInsnNode],
                                     formalParamPosHiO: Int): MethodNode = {

                      def warn(reason: String) {
                        inlineTarget.warn(
                          s"Can't stack-allocate the closure passed at argument position $formalParamPosHiO because $reason"
                        )
                      }

                  // (1) all usages are invocations
                  if(closureArgUsages.exists(insn => insn.getType != AbstractInsnNode.METHOD_INSN)) {
                    warn(s"not all of its usages in ${inlineTarget.calleeId} are invocations of the closure's apply() method.")
                    return null
                  }

                  // (2) moreover invocations of one and the same method
                  if(closureArgUsages.isEmpty) {
                    warn(s"no invocations were found in ${inlineTarget.calleeId} of the closure's apply() method.")
                    return null
                  }
                  var iter: Iterator[AbstractInsnNode] = closureArgUsages.iterator
                  val fst = iter.next().asInstanceOf[MethodInsnNode]
                  while(iter.hasNext) {
                    val nxt = iter.next().asInstanceOf[MethodInsnNode]
                    if(
                      fst.getOpcode != nxt.getOpcode ||
                      fst.owner     != nxt.owner     ||
                      fst.name      != nxt.name      ||
                      fst.desc      != nxt.desc
                    ) {
                      warn(s"one or more methods other than apply() are called on it in ${inlineTarget.calleeId}")
                      return null
                    }
                  }

                  // (3) each invocation takes the closure instance as receiver, and only as receiver (ie not as argument)
                  iter = closureArgUsages.iterator
                  while(iter.hasNext) {

                        def isClosureLoad(sv: SourceValue) = {
                          (sv.insns.size() == 1) && {
                            sv.insns.iterator().next() match {
                              case lv: VarInsnNode => lv.`var` == localVarIdxHiO
                              case _ => false
                            }
                          }
                        }

                    val nxt = iter.next().asInstanceOf[MethodInsnNode]
                    val frame = cpHiO.frameAt(nxt)
                    val isDispatchedOnClosure = isClosureLoad(frame.getReceiver(nxt))
                    val passesClosureAsArgument = {
                      frame.getActualArguments(nxt).exists(v => isClosureLoad(v.asInstanceOf[SourceValue]))
                    }

                    if(passesClosureAsArgument) {
                      warn(s"${inlineTarget.calleeId} passes the closure as argument, thus letting it escape (to a method not marked @inline).")
                      return null
                    }
                    if(!isDispatchedOnClosure) {
                      warn(s"${inlineTarget.calleeId} contains a closure usage other than as receiver of apply().")
                      return null
                    }
                  }

                  // (4) whether it's actually an apply or specialized-apply invocation
                  val arity = BType.getMethodType(fst.desc).getArgumentCount
                  if(arity > definitions.MaxFunctionArity) {
                    warn("the callee invokes apply() on the closure with more than " + definitions.MaxFunctionArity + " arguments.")
                    return null
                  }

                  // all checks passed, look up applyMethod
                  val closureClassBType = lookupRefBType(closureClass.name)
                  val tentative = codeRepo.getMethodOrNull(closureClassBType, fst.name, fst.desc)
                  val applyMethod =
                    if(tentative == null) { null }
                    else { tentative.mnode }

                  if(applyMethod == null) {
                    warn(s"${inlineTarget.calleeId} invokes apply() on the closure, but the bytecode for that method couldn't be found.")
                  }

                  applyMethod
                }

            for (
              (formalParamPosHiO, closureClass) <- closureClassPerHiOFormal;
              localVarIdxHiO = mtHiO.convertFormalParamPosToLocalVarIdx(formalParamPosHiO, isInstanceMethod);
              closureArgUsages: Set[AbstractInsnNode] = JSetWrapper(cpHiO.consumersOfLocalVar(localVarIdxHiO)).toSet;
              applyMethod = areAllApplyCalls(closureClass, localVarIdxHiO, closureArgUsages, formalParamPosHiO);
              if applyMethod != null
            ) yield ClosureUsages(
              formalParamPosHiO,
              localVarIdxHiO,
              closureClass,
              applyMethod,
              closureArgUsages map (_.asInstanceOf[MethodInsnNode])
            )
          }

      val (closureClassUtils, failedAttempts) =
        (survivors3().toArray.map { cu => ClosureClassUtil(cu) }) partition { ccu => ccu.isRepOK }

      for(fa <- failedAttempts) { inlineTarget.warn(fa.diagnostics) }

      if(closureClassUtils.isEmpty) {
        return false
      }

      val shio = StaticHiOUtil(hiO, closureClassUtils)
      val staticHiO: MethodNode = shio.buildStaticHiO(hostOwner, callsite, inlineTarget)
      if(staticHiO == null) { return false }
      assert(Util.isPublicMethod(staticHiO), "Not a public method: " + methodSignature(hostOwner, staticHiO))
      if(!shio.rewriteHost(hostOwner, host, callsite, staticHiO, inlineTarget)) {
        return false
      }

      val enclClass = lookupRefBType(hostOwner.name)
      checkTransplantedAccesses(staticHiO.instructions, enclClass)

      hostOwner.methods.add(staticHiO)
      privatizables.track(hostOwner, staticHiO)
      for(ccu <- closureClassUtils) {
        val dclosure: BType = lookupRefBType(ccu.closureClass.name)
        if(closuRepo.isDelegatingClosure(dclosure)) {

          val mc = closuRepo.masterClass(dclosure)
          if(mc != enclClass) {
            log(
              s"DClosure usage in non-master: a static-HiO method added to class ${hostOwner.name} " +
              s"(resulting from inlining closure $dclosure) invokes that closure's endpoint method (which is declared in $mc)"
            )
            assert(closuRepo.nonMasterUsers(dclosure).contains(enclClass))
          }

          // once inlined, a dclosure used only by its master class loses its "dclosure" status
          if(closuRepo.nonMasterUsers(dclosure).isEmpty) {
            Util.makePrivateMethod(closuRepo.endpoint(dclosure).mnode)
            closuRepo.retractAsDClosure(dclosure)
          }

        }
      }

      true
    } // end of method inlineClosures

    /**
     *
     * */
    private def checkTransplantedAccesses(body: InsnList, enclClass: BType) {

      /*
       * An invocation to a shio method declared in a class other than the new home of the callsite (enclClass)
       * forces the shio method in question to remain public.
       * */
      body foreachInsn { insn =>
        insn match {
          case mi: MethodInsnNode =>
            val calleeOwnerBT = lookupRefBType(mi.owner)
            if(calleeOwnerBT != enclClass) {
              // it's ok to try to untrack a method that's not being tracked
              privatizables.untrack(calleeOwnerBT, mi.name, mi.desc)
            }
          case _ => ()
        }
      }

      /*
       * In case `insn` denotes a dclosure instantiation or endpoint invocation
       * and `enclClass` isn't the master class of that closure, note this fact `nonMasterUsers`.
       * */
      body foreachInsn { insn => closuRepo.trackClosureUsageIfAny(insn, enclClass) }

    }

    /**
     *  For a given pair (hiO method, closure-argument) an instance of ClosureUsages
     *  records the apply() invocations inside hiO for a particular closure-argument.
     *
     *  @param formalParamPosHiO zero-based position in the formal-params-list of hiO method
     *  @param localVarIdxHiO    corresponding index into the locals-array of hiO method
     *                           (in general different from formalParamPosHiO due to JVM-type-sizes)
     *  @param closureClass      final class of the closure (ie not e.g. Function1 but an anon-closure-class)
     *  @param applyMethod       the apply method invoked inside hiO (which in turn may invoke another).
     *  @param usages            invocations in hiO of closureClass' applyMethod.
     *                           Allows finding out the instruction producing receiver and arguments.
     */
    private case class ClosureUsages(
      formalParamPosHiO: Int,
      localVarIdxHiO:    Int,
      closureClass:      ClassNode,
      applyMethod:       MethodNode,
      usages:            Set[MethodInsnNode]
    )

    /**
     *  Query methods that dig out information hidden in the structure of a closure-class.
     */
    private case class ClosureClassUtil(closureUsages: ClosureUsages) {

      def closureClass: ClassNode = closureUsages.closureClass

      val constructor: MethodNode = {
        var result: MethodNode = null
        val iter = closureClass.methods.iterator()
        while(iter.hasNext) {
          val nxt = iter.next()
          if(nxt.name == "<init>") {
            assert(result == null, s"duplicate <init> method found in closure-class: ${closureClass.name}")
            result = nxt
          }
        }
        Util.computeMaxLocalsMaxStack(result)

        result
      }

      val constructorMethodType = BType.getMethodType(constructor.desc)

      /**
       *  The constructor of a closure-class has params for (a) the outer-instance; and (b) captured-locals.
       *  Those values are stored in final-fields of the closure-class (the so called "closure state")
       *  to serve later as actual arguments in a "delegate-invoking apply()".
       *
       *  From the perspective of `host` (which invokes `hiO`) the closure-state aliases the actuals
       *  to the closure instantiation. When the time comes to inline that apply
       *  (containing usages of closure-state fields) their correspondence with the values they alias is needed because:
       *    (a) `host` knowns only what actuals go to which closure-constructor-param-positions; and
       *    (b) there's no guarantee that those values appear in the same order in both
       *        - closure instantiation, and
       *        - delegate-invoking apply invocation.
       *
       *  This map tracks the aliasing of closure-state values, before and after the closure was instantiated.
       */
      val stateField2constrParam: Map[String, Int] = {

        val cpConstructor: ProdConsAnalyzer = ProdConsAnalyzer.create()
        cpConstructor.analyze(closureClass.name, constructor)

        /*
         * for each constructor-param-position:
         *   obtain its local-var index
         *   find the single consumer of a LOAD of that local-var (should be a PUTFIELD)
         *   add pair to map.
         **/
        val constructorBT = BType.getMethodType(constructor.desc)

            def findClosureStateField(localVarIdx: Int): String = {
              val consumers = cpConstructor.consumersOfLocalVar(localVarIdx)
              if(localVarIdx == 1) {
                // for outer-param, don't count IFNULL, or IFNONNULL, (in general any jump instruction) as consumer
                val consumerIter = consumers.iterator()
                var stop = false
                while(consumerIter.hasNext && !stop) {
                  val cnext = consumerIter.next
                  if(cnext.getType == AbstractInsnNode.JUMP_INSN) {
                    consumers.remove(cnext)
                    stop = true
                  }
                }
              }
              val consumer: AbstractInsnNode = cpConstructor.getSingleton(consumers)
              consumer match {
                case null => null
                case fi: FieldInsnNode
                  if (fi.getOpcode == Opcodes.PUTFIELD ) &&
                     (fi.owner     == closureClass.name)
                          => fi.name
                case _    => null
              }
            }

        val result =
          for(
            paramPos <- 0 until constructorBT.getArgumentCount;
            localVarIdx = constructorBT.convertFormalParamPosToLocalVarIdx(paramPos, isInstanceMethod = true);
            fieldName   = findClosureStateField(localVarIdx);
            if fieldName != null
          ) yield (fieldName -> (localVarIdx - 1))

        result.toMap
      }

      private def getClosureState(fieldName: String): FieldNode = {
        val fIter = closureClass.fields.iterator()
        while(fIter.hasNext) {
          val f = fIter.next()
          if(Util.isInstanceField(f) && (f.name == fieldName)) {
            return f
          }
        }

        null
      }

      val field: Map[String, FieldNode] = {
        val result =
          for(
            (fieldName, _) <- stateField2constrParam;
            fn = getClosureState(fieldName);
            if fn != null
          ) yield (fieldName -> fn)

        result.toMap
      }

      /**
       *  As part of building staticHiO, closure-usages in hiO are replaced by either:
       *    (a) self-contained code snippets; or
       *    (b) invocation to the delegate created during `closureConversionModern()`
       *
       *  In both cases the snippet of instructions to paste (let's call it "stub") should:
       *    (c) avoid using the closure's THIS; and
       *    (d) consume from the operand-stack what the `applyMethod` invocation used to consume, and
       *        leave on exit what `applyMethod()` used to return.
       *
       *  In order to implement the above, it's way easier if `staticHiO` doesn't have to
       *  chase invocation chains like:
       *
       *    (1) First into "bridge-style apply()"
       *
       *          final < bridge > < artifact > def apply(v1: Object): Object = {
       *            apply(scala.Int.unbox(v1));
       *            scala.runtime.BoxedUnit.UNIT
       *          };
       *
       *    (2) Which in turn invokes a "forwarding apply()"
       *
       *          final def apply(x$1: Int): Unit = apply$mcVI$sp(x$1);
       *
       *    (3) Which finally invokes a "delegate-invoking apply()"
       *
       *          < specialized > def apply$mcVI$sp(v1: Int): Unit = $outer.C$$dlgt1$1(v1);
       *
       *  This utility method returns a fabricated MethodNode, where invocation chains as above have been
       *  collapsed into a self-contained method. In case this is not possible, this method returns null.
       *
       *  For example, this method returns `null` for a closure converted by `closureConversionTraditional()`
       *  where the original closure-body contained local-methods that lambdalift turned into
       *  closure-methods. In general it's not always possible to "un-do" all the dependencies on the closure's THIS,
       *  and in the example we don't even try.
       *
       *  Starting from the known `applyMethod`, collapsing involves:
       *    (i)  checking whether THIS doesn't escape. If so, the current method is fine as is.
       *    (ii) in case THIS escapes only as receiver of a (non-recursive) invocation on this closure,
       *         then drill-down into the target. If that target can itself be collapsed,
       *         we collapse it with the current method being visited (as expected,
       *         collapsing a drilled-down method means inlining it into a clone of the current method).
       */
      private def helperStubTemplate(): Either[String, MethodNode] = {

          def escapingThis(mnodeOwner: String, mnode: MethodNode): collection.Set[AbstractInsnNode] = {

                def isClosureStateAccess(insn: AbstractInsnNode) = {
                  insn.getOpcode == Opcodes.GETFIELD && {
                    val fi = insn.asInstanceOf[FieldInsnNode]
                    stateField2constrParam.contains(fi.name)
                  }
                }

            Util.computeMaxLocalsMaxStack(mnode)
            val cpHiO: ProdConsAnalyzer = ProdConsAnalyzer.create()
            cpHiO.analyze(mnodeOwner, mnode)
            for(
              consumer <- JSetWrapper(cpHiO.consumersOfLocalVar(0))
              if !isClosureStateAccess(consumer)
            ) yield consumer
          }

        val closureClassName  = closureUsages.closureClass.name
        val closureClassBType = lookupRefBType(closureClass.name)

            /**
             *  @return Right[MethodNode] fabricated stub for use when building staticHiO
             *          Left[String]      diagnostics message why a stub can't be fabricated
             * */
            def getInnermostForwardee(current: MethodNode, visited0: Set[MethodNode]): Either[String, MethodNode] = {

              val currentId = closureClass.name + "." + current.name + current.desc

              if(!current.tryCatchBlocks.isEmpty) {
                // The instructions of the resulting MethodNode will serve as template to replace closure-usages.
                // TODO warn We can't rule out the possibility of an exception-handlers-table making such replacement non-well-formed.
                return Left(
                  s"Method $currentId contains excepion-handlers. Once inlined, " +
                   " the operand stack may contain more values at that program point than consumed by the closure-usage."
                )
              }
              val escaping = escapingThis(closureClassName, current)
              if(escaping.isEmpty) {
                return Right(current)
              }
              if(escaping.size == 1) {
                escaping.iterator.next() match {

                  case forwarder: MethodInsnNode if forwarder.owner == closureClassName =>
                    val forwardee = codeRepo.getMethod(closureClassBType, forwarder.name, forwarder.desc).mnode
                    val visited   = visited0 + current
                    if(visited.exists(v => v eq forwardee)) {
                      return null // TODO warn recursive invocation chain was detected, involving one or more closure-methods
                    }
                    getInnermostForwardee(forwardee, visited) match {

                      case Right(rewritten) =>
                        val cm: Util.ClonedMethod = Util.clonedMethodNode(current)
                        val clonedCurrent = cm.mnode
                        val tfa = new Analyzer[TFValue](new TypeFlowInterpreter)
                        tfa.analyze(closureClassName, current)
                        val clonedForwarder = cm.insnMap.get(forwarder).asInstanceOf[MethodInsnNode]
                        val frame   = tfa.frameAt(clonedForwarder).asInstanceOf[asm.tree.analysis.Frame[TFValue]]
                        val inlineMethodOutcome = inlineMethod(
                          closureClassName,
                          clonedCurrent,
                          clonedForwarder,
                          frame,
                          rewritten, closureUsages.closureClass,
                          doTrackClosureUsage = true
                        )
                        return inlineMethodOutcome match {
                          case None                => Right(clonedCurrent)
                          case Some(diagnosticMsg) => Left(diagnosticMsg)
                        }

                      case diagnostics =>
                        return diagnostics
                    }

                  case _ => ()
                }
              }

              Left(s"The closure's THIS value escapes $currentId method")

            } // end of method getInnermostForwardee()

        val result: MethodNode =
          getInnermostForwardee(closureUsages.applyMethod, Set.empty) match {
            case Right(mn)   => mn
            case diagnostics => return diagnostics
          }

        val quickOptimizer = new BCodeCleanser(closureClass)
        quickOptimizer.basicIntraMethodOpt(result)
        Util.computeMaxLocalsMaxStack(result)

        if(escapingThis(closureClassName, result).nonEmpty) {
          return Left(
             "In spite of our best efforts, the closure's THIS is used for something that can't be reduced later. " +
            s"In other words, it escapes the methods in class $closureClassName"
          )
        }

            def hasMultipleRETURNs: Boolean = {
              var returnSeen = false
              val iter = result.instructions.iterator
              while(iter.hasNext) {
                if(Util.isRETURN(iter.next())) {
                  if (returnSeen) { return true; }
                  returnSeen = true
                }
              }

              false
            }

        if(hasMultipleRETURNs) {
          return Left(s"The stub computed for class $closureClassName has multiple returns.")
        }

        assert(result.desc == closureUsages.applyMethod.desc)

        Right(result)
      } // end of method helperStubTemplate()

      val stubCreatorOutcome: Either[String, MethodNode] = helperStubTemplate()

      def stubTemplate: MethodNode = stubCreatorOutcome.right.get

      def diagnostics: String = {
        var diags: List[String] = Nil
        if(!areAllFiledsAccountedFor) {
          diags ::= s"Number of closure-state fields should be one less than number of fields in ${closureClass.name}" +
                     "(static field SerialVersionUID isn't part of closure-state)"
        }
        if(stubCreatorOutcome.isLeft) {
          diags ::= stubCreatorOutcome.left.get
        }

        diags.mkString(",\n")
      }

      /**
       * Number of closure-state fields should be one less than number of fields in closure-class
       * (static field SerialVersionUID isn't part of closure-state).
       */
      def areAllFiledsAccountedFor: Boolean = {
        (stateField2constrParam.size == (closureClass.fields.size() - 1)) &&
        (stateField2constrParam.size == field.size)
      }

      def isRepOK: Boolean = {
        areAllFiledsAccountedFor && stubCreatorOutcome.isRight
      }

    } // end of class ClosureClassUtil

    /**
     *  Query methods that help derive a "static hiO method" given a "hiO method".
     *  Most of the rewriting needed to realize closure-inlining is done by `buildStaticHiO()` and `rewriteHost()`.
     *
     *  @param hiO higher-order method for which the closures given by `closureClassUtils`
     *             (closures that `hiO` receives as arguments) are to be stack-allocated.
     *  @param closureClassUtils a subset of the closures that `hiO` expects,
     *                           ie the subset that has survived a plethora of checks about pre-conditions for inlining.
     */
    private case class StaticHiOUtil(hiO: MethodNode, closureClassUtils: Array[ClosureClassUtil]) {

      val howMany = closureClassUtils.size

      /**
       *  Which (zero-based) param-positions in hiO correspond to closures to be inlined.
       */
      val isInlinedParamPos: Set[Int] = {
        closureClassUtils.map( ccu => ccu.closureUsages.formalParamPosHiO ).toSet
      }

      /**
       *  Form param-positions in hiO corresponding to closures to be inlined, their local-variable index.
       */
      val isInlinedLocalIdx: Set[Int] = {
        closureClassUtils.map( ccu => ccu.closureUsages.localVarIdxHiO).toSet
      }

      /**
       *  The "slack of a closure-receiving method-param of hiO" has to do with the rewriting
       *  by which a staticHiO method is derived from a hiO method.
       *
       *  As part of that rewriting, those params receiving closures that are to be stack-allocated
       *  are replaced with params that receive the closure's state values.
       *  Usages of locals in the rewritten method will in general require shifting.
       *
       *  As a first step, the following map informs for each closure-receiving-param
       *  the accumulated sizes of closure-state params added so far (including those for that closure), minus 1
       *  (accounting for the fact the closure-param will be elided along with the closure-instance).
       *
       *  In the map, an entry has the form:
       *    (original-local-var-idx-in-HiO -> accumulated-sizes-inluding-constructorParams-for-this-closure)
       */
      val closureParamSlack: Array[Tuple2[Int, Int]] = {
        var acc = 0
        val result =
          for(cu <- closureClassUtils)
          yield {
            val constrParams: Array[BType] = cu.constructorMethodType.getArgumentTypes
            constrParams foreach { constrParamBT => acc += constrParamBT.getSize }
            acc -= 1
            // assert(acc >= -1). In other words, not every closure-constructor has at least an outer instance param.

            (cu.closureUsages.localVarIdxHiO -> acc)
          }

        result.sortBy(_._1)
      }

      /**
       *  Given a locaVarIdx valid in hiO, returns the localVarIdx (for the same value) in staticHiO.
       *
       *  In principle, this method isn't applicable to closure-receiving params themselves (they simply go away),
       *  but for uniformity in that case returns
       *  the local-var-idx in staticHiO of the param holding the first constructor-param.
       */
      def shiftedLocalIdx(original: Int): Int = {
        assert(original >= 0)
        var i = (closureParamSlack.length - 1)
        while (i >= 0) {
          val Pair(localVarIdx, acc) = closureParamSlack(i)
          if(localVarIdx < original) {
            val result = original + acc
            assert(result >= 0)

            return result
          }
          i -= 1
        }

        original
      }

      /**
       * Quoting from `inlineClosures()`:
       *
       *     Closure inlining results in faster code by specializing a higher-order method
       *     to the particular anonymous closures given as arguments at a particular callsite
       *     (at the cost of code duplication, namely of the Hi-O method, no other code gets duplicated).
       *
       *  The MethodNode built by `buildStaticHiO()` is the "specialized code" referred to above.
       *  The main difficulty is properly shifting local-var-indexes, so that they keep denoting the same values.
       *  Shifting is needed because:
       *    - some formal params have been removed (those for closure-instances), while
       *    - others (zero or more closure-state values) have taken their place, and also because
       *    - the code snippets pasted to replace closure-invocations use local-vars of their own.
       *
       *  The steps to build `staticHiO` are:
       *
       *    (1) pick unique method name
       *
       *    (2) visit `hiO` formal params,
       *        discarding those for stack-allocated closures, and
       *        splicing-in params for closure-state.
       *        Along the way staticHiO's maxLocals is updated. Its initial value was hiO's maxLocals.
       *
       *    (3) now comes putting together the body of staticHiO.
       *        The starting point is a verbatim copy of hiO's InsnList,
       *        ie source-line information will be present (if any).
       *        The exception-handlers table can be copied without changes,
       *        while the entries about visibility ranges of local-vars need shifting.
       *
       *    (4) Those closure-applications still present in the method body can't remain forever.
       *        The contract with `getStubsIterator()` is:
       *            for each closure to inline, give me an iterator of code snippets,
       *            where each code snippet has to be able to cope with the arguments (save for the receiver)
       *            of a usage of that closure (ie of a closure-application).
       *
       *  @return `staticHiO` if preconditions are satisfied. Otherwise null.
       */
      def buildStaticHiO(hostOwner: ClassNode, callsite: MethodInsnNode, inlineTarget: InlineTarget): MethodNode = {

        // val txtHiOBefore = Util.textify(hiO)

        // (1) method name
        val name = {
          var attempt = 1
          var candidate: String = null
          var duplicate = false
          do {
            candidate = "shio$" + attempt + "$" + hiO.name
            duplicate = JListWrapper(hostOwner.methods) exists { mn => mn.name == candidate }
            attempt += 1
          } while(duplicate)

          candidate
        }

        // (2) method descriptor, computing initial value of staticHiO's maxLocals (will be updated again once stubs are pasted)
        var formals: List[BType] = Nil
        if(Util.isInstanceMethod(hiO)) {
          formals ::= lookupRefBType(callsite.owner)
        }
        val hiOMethodType = BType.getMethodType(hiO.desc)
        var maxLocals = hiO.maxLocals
        foreachWithIndex(hiOMethodType.getArgumentTypes.toList) {
          (hiOParamType, hiOParamPos) =>
            if(isInlinedParamPos(hiOParamPos)) {
              // splice-in the closure's constructor's params, the original closure-receiving param goes away.
              maxLocals -= 1
              val ccu = closureClassUtils.find(_.closureUsages.formalParamPosHiO == hiOParamPos).get
              for(constrParamType <- ccu.constructorMethodType.getArgumentTypes) {
                formals ::= constrParamType
                maxLocals += constrParamType.getSize
              }
            } else {
              formals ::= hiOParamType
            }
        }
        val shiOMethodType = BType.getMethodType(hiOMethodType.getReturnType, formals.reverse.toArray)

        // (3) clone InsnList, get Label map
        val labelMap = Util.clonedLabels(hiO)
        val insnMap  = new java.util.HashMap[AbstractInsnNode, AbstractInsnNode]()
        val body     = Util.clonedInsns(hiO.instructions, labelMap, insnMap)

        // (4) Util.clone TryCatchNodes
        val tcns: java.util.List[TryCatchBlockNode] = Util.clonedTryCatchBlockNodes(hiO, labelMap)
        val here = lookupRefBType(hostOwner.name)
        if(!allExceptionsAccessible(tcns, here)) {
          inlineTarget.warn(
            "Couldn't perform closure-inlining because not all exceptions " +
            "declared by the callee are accessible from the class containing the caller."
          )
          return null
        }

        // (5) Util.clone LocalVarNodes, shift as per-oracle
        val lvns: java.util.List[LocalVariableNode] = Util.clonedLocalVariableNodes(hiO, labelMap, "")
        val lvnIter = lvns.iterator()
        while(lvnIter.hasNext) {
          val lvn: LocalVariableNode = lvnIter.next()
          if(isInlinedLocalIdx(lvn.index)) {
            lvnIter.remove()
          } else {
            lvn.index = shiftedLocalIdx(lvn.index)
          }
        }
        if(!allLocalVarTypesAccessible(lvns, here)) {
          inlineTarget.warn(
            "Couldn't perform closure-inlining because not all LocalVariableNode types " +
            "declared by the callee are accessible from the class containing the caller."
          )
          return null
        }

        // (6) Shift LOADs and STOREs: (a) remove all isInlined LOADs; (b) shift as per oracle
        //     (There are no usages of spliced-in params yet)
        val bodyIter = body.iterator()
        while(bodyIter.hasNext) {
          val insn = bodyIter.next
          if(insn.getType == AbstractInsnNode.VAR_INSN) {
            val vi = insn.asInstanceOf[VarInsnNode]
            assert(vi.getOpcode != Opcodes.RET)
            if(isInlinedLocalIdx(vi.`var`)) {
              bodyIter.remove()
            } else {
              vi.`var` = shiftedLocalIdx(vi.`var`)
            }
          }
        }

        // (7) put together the pieces above into a MethodNode
        val shio: MethodNode =
          new MethodNode(
            Opcodes.ASM4,
            Opcodes.ACC_PUBLIC | Opcodes.ACC_STATIC | Opcodes.ACC_SYNTHETIC,
            name,
            shiOMethodType.getDescriptor,
            null,
            null
          )
        shio.instructions   = body
        shio.tryCatchBlocks = tcns
        shio.localVariables = lvns
        shio.maxStack  = hiO.maxStack // will be updated in due time (not before stubs have been pasted)
        shio.maxLocals = maxLocals

        // (8) rewrite usages (closure-apply invocations)
        //     For each usage obtain the stub (it's the same stub for all usages of the same closure), clone and paste.
        for(ccu <- closureClassUtils) {
          val stubsIter = getStubsIterator(ccu, shio)
          assert(ccu.closureUsages.usages.nonEmpty)
          for(usage0 <- ccu.closureUsages.usages) {
            val usage = insnMap.get(usage0)
            assert(body.contains(usage))
            assert(stubsIter.hasNext)
            body.insert(usage, stubsIter.next())
            body.remove(usage)
          }
          assert(!stubsIter.hasNext)
        }

        // (9) update maxStack, run TFA for debug purposes
        Util.computeMaxLocalsMaxStack(shio)
        val quickOptimizer = new BCodeCleanser(hostOwner)
        quickOptimizer.basicIntraMethodOpt(shio)
        Util.computeMaxLocalsMaxStack(shio)
        // val txtShioAfter = Util.textify(shio)
        // val tfaDebug = new Analyzer[TFValue](new TypeFlowInterpreter)
        // tfaDebug.analyze(hostOwner.name, shio)

        shio
      } // end of method buildStaticHiO()

      /**
       * `host` is patched to:
       *   (1) convey closure-constructor-args instead of an instantiated closure; and
       *   (2) target `staticHiO` rather than `hiO`
       *
       * How `host` looks before rewriting
       * ---------------------------------
       *
       * In terms of bytecode, two code sections are relevant:
       *   - instantiation of AC (the "Anonymous Closure"); and
       *   - passing it as argument to Hi-O:
       *
       *     NEW AC
       *     DUP
       *     // load of closure-state args, the first of which is THIS
       *     INVOKESPECIAL < init >
       *
       * The above in turn prepares the i-th argument as part of this code section:
       *
       *     // instructions that load (i-1) args
       *     // here goes the snippet above (whose instructions load the closure instance we want to elide)
       *     // more args get loaded
       *     INVOKE Hi-O
       *
       * How `host` looks after rewriting
       * --------------------------------
       *
       *   (a) The NEW, DUP, and < init > instructions for closure instantiation have been removed.
       *   (b) INVOKE Hi-O has been replaced by INVOKE shio,
       *       which expects on the operand stack not closures but their closure-state instead.
       *       The closure-state of a closure may consist of zero, one, or more arguments
       *       (usually an outer instance is part of the closure-state, but empty closure state is also possible).
       *
       * @param hostOwner class declaring the host method
       * @param host      method containing a callsite for which inlining has been requested
       * @param callsite  invocation of a higher-order method (taking one or more closures) whose inlining is requested
       * @param staticHiO a static method added to hostOwner, specializes hiO by inlining the closures hiO used to be invoked with
       *
       * @return whether closure-inlining was actually performed (should always be the case unless wrong input bytecode).
       */
      def rewriteHost(hostOwner:    ClassNode,
                      host:         MethodNode,
                      callsite:     MethodInsnNode,
                      staticHiO:    MethodNode,
                      inlineTarget: InlineTarget): Boolean = {

        val cpHost = ProdConsAnalyzer.create()
        cpHost.analyze(hostOwner.name, host)
        val callsiteCP: asm.tree.analysis.Frame[SourceValue] = cpHost.frameAt(callsite)
        val actualsProducers: Array[SourceValue] = callsiteCP.getActualArguments(callsite) map (_.asInstanceOf[SourceValue])

        val newInsns: Array[AbstractInsnNode] =
          for(
            ccu <- closureClassUtils;
            closureParamPos = ccu.closureUsages.formalParamPosHiO;
            newInsnSV       = actualsProducers(closureParamPos)
          ) yield {
            assert(newInsnSV.insns.size() == 1)
            newInsnSV.insns.iterator().next()
          }

        val dupInsns: Array[InsnNode] =
          for(newInsn <- newInsns)
          yield {
            val newConsumers = (JSetWrapper(cpHost.consumers(newInsn)) filter (_ ne callsite))
            assert(newConsumers.size == 1)
            val dupInsn = newConsumers.iterator.next().asInstanceOf[InsnNode]
            assert(dupInsn.getOpcode == Opcodes.DUP)

            dupInsn
          }

        val initInsns: Array[MethodInsnNode] =
          for(dupInsn <- dupInsns)
          yield {
            val initInsn = cpHost.consumers(dupInsn).iterator.next().asInstanceOf[MethodInsnNode]
            assert(initInsn.getOpcode == Opcodes.INVOKESPECIAL && initInsn.name  == "<init>")

            initInsn
          }

        if ((newInsns.length != howMany) || (dupInsns.length != howMany) || (initInsns.length != howMany)) {
          inlineTarget.warn(
            "Couldn't perform closure-inlining because one or more closure instantiations couldn't be rewritten."
          )
          return false
        }

            def removeAll(ai: Array[_ <: AbstractInsnNode]) {
              ai foreach {i => host.instructions.remove(i) }
            }

        // This is the point of no return. Starting here, all closure-inlinings in `host` must succeed.

        removeAll(newInsns)
        removeAll(dupInsns)
        removeAll(initInsns)

        /*
         * No need to attempt eliding here those closure classes for which hostOwner is the only "master class".
         * Intra-class analysis `shakeAndMinimizeClosures()` will do that.
         * Actually, information on `nonMasterUsers` is complete by now
         * (because `populateNonMasterUsers()` runs before `inlining()`).
         * Thus in theory eliding could be done here. But that would add to the code to understand, unlike this comment, right? ;-)
         *
         * */

        val rewiredInvocation = new MethodInsnNode(Opcodes.INVOKESTATIC, hostOwner.name, staticHiO.name, staticHiO.desc)
        host.instructions.set(callsite, rewiredInvocation)
        Util.computeMaxLocalsMaxStack(host)

        true
      } // end of method rewriteHost()

      /**
       *  All of the usages of a closure in hiO are of the same shape: invocation of `applyMethod`
       *  whose receiver is LOAD of a closure-param.
       *
       *  The invoker of this method, `buildStaticHiO()`, will have an easier time if it just can replace
       *  those invocations without touching the instructions surrounding them.
       *
       *  To make that possible, this method returns copies (as many as closure usages) of a stub of instructions.
       *  The stub takes as starting point `stubTemplate` (a MethodNode where chains of apply-invocations
       *  have been collapsed into a self-contained method).
       *
       *  The stub is obtained by:
       *    (1) prefixing STORE instructions (whose locals are added here too) to consume the actual arguments
       *        the closure-usage used to consume.
       *    (2) reformulating GETFIELDs on closure-state, to use instead the spliced-in params in staticHiO
       *        (these params receive values that used to go to the closure's constructor)
       *    (3) properly shifting locals so that the resulting stub makes sense.
       */
      private def getStubsIterator(ccu: ClosureClassUtil, shio: MethodNode): Iterator[InsnList] = {
        val labelMap = Util.clonedLabels(ccu.stubTemplate)
        val stub = new InsnList

        val oldMaxLocals = shio.maxLocals
        val stores = new InsnList
        var accArgSizes = 0
        for(argT <- BType.getMethodType(ccu.stubTemplate.desc).getArgumentTypes) {
          val opcode = argT.getOpcode(Opcodes.ISTORE)
          stores.insert(new VarInsnNode(opcode, oldMaxLocals + accArgSizes))
          accArgSizes += argT.getSize
        }
        shio.maxLocals += ccu.stubTemplate.maxLocals

        val insnIter = ccu.stubTemplate.instructions.iterator()
        while(insnIter.hasNext) {
          val insn = insnIter.next()

          if(Util.isRETURN(insn)) {
            // elide
          } else if(insn.getType == AbstractInsnNode.VAR_INSN) {
            val vi = insn.asInstanceOf[VarInsnNode]
            if(vi.`var` == 0) {
              assert(vi.getOpcode == Opcodes.ALOAD)
              /*
               * case A: remove all `LOAD 0` instructions. THIS was to be consumed by a GETFIELD we'll also rewrite.
               */
            } else {
              /*
               * case B: rewrite LOADs for params of applyMethod.
               *         Past-maxLocals vars are fabricated (they are also used in the STOREs at the very beginning of the stub).
               *         Each `LOAD i` with 1 <= i is shifted
               */
              val updatedIdx = vi.`var` - 1 + oldMaxLocals
              assert(updatedIdx >= 0)
              val cloned = new VarInsnNode(vi.getOpcode, updatedIdx)
              stub.add(cloned)
            }
          } else if(
            (insn.getOpcode == Opcodes.GETFIELD) &&
            (insn.asInstanceOf[FieldInsnNode].owner == ccu.closureClass.name)
          ) {
            /*
             * case C: Given a GETFIELD in applyMethod, its localVarIdx in staticHiO is given by:
             *         shifted-localvaridx-of-closure-param + localvaridx-of-corresponding-constructor-param
             */
            val fa   = insn.asInstanceOf[FieldInsnNode]
            val base = shiftedLocalIdx(ccu.closureUsages.localVarIdxHiO)
            val dx   = ccu.stateField2constrParam(fa.name)
            val ft   = descrToBType(ccu.field(fa.name).desc)
            val opc  = ft.getOpcode(Opcodes.ILOAD)
            assert(base + dx >= 0)
            val load = new VarInsnNode(opc, base + dx)
            stub.add(load)
          } else {
            stub.add(insn.clone(labelMap))
          }

        }

        stub.insert(stores)

        var stubCopies: List[InsnList] = stub :: Nil
        for(i <- 2 to ccu.closureUsages.usages.size) {
          stubCopies ::=
            Util.clonedInsns(
              stub,
              Util.clonedLabels(stub),
              new java.util.HashMap[AbstractInsnNode, AbstractInsnNode]
            )
        }

        stubCopies.iterator
      } // end of method getStubsIterator()

    } // end of class StaticHiOUtil

    /**
     *  Inline those "small" private methods that are invoked from a single place.
     *
     * */
    private def percolateUpwards(cnode: ClassNode) {

      log(s"Attempting to inline small-private-methods-used-once (aka percolating), class ${cnode.name}")

      val candidates = {
        JListWrapper(cnode.methods)
       .filter(m => Util.isPrivateMethod(m) && !Util.isConstructor(m) && !Util.isAbstractMethod(m))
       .filter(m => m.tryCatchBlocks.isEmpty) /* considering only callees without exception handlers allows skipping type-flow analysis */
       .filter(m => m.name.contains('$'))
      }

          def invokes(insn: AbstractInsnNode, callee: MethodNode): Boolean = {
            (insn.getType == AbstractInsnNode.METHOD_INSN) && {
              val mi = insn.asInstanceOf[MethodInsnNode]

              (mi.owner == cnode.name) && (mi.name == callee.name) && (mi.desc == callee.desc)
            }
          }

          case class Invocation(caller: MethodNode, callsite: MethodInsnNode, callee: MethodNode)

      val invocations = mutable.Set.empty[Invocation] ++ {
        for(
          caller <- JListWrapper(cnode.methods);
          if !Util.isAbstractMethod(caller);
          i <- caller.instructions.toList;
          if i.getType == AbstractInsnNode.METHOD_INSN;
          callsite = i.asInstanceOf[MethodInsnNode];
          callee <- candidates;
          if invokes(callsite, callee)
        ) yield Invocation(caller, callsite, callee)
      }

        /**
         *  (1) Discard those tuples sharing the same candidate as callee
         *      (they stand for different invocations, either from different or the same method)
         *
         *  (2) Discard those tuples where caller == callee (they stand for direct recursive invocations)
         *
         */
          def pruneMultipleOrRecursive() {
            for(candidate <- candidates) {
              val callingContexts = invocations.filter(invoc => invoc.callee == candidate)
              val discard = (callingContexts.size  > 1) || {
                (callingContexts.size == 1) && { val tuple = callingContexts.head; tuple.caller == tuple.callee }
              }
              if(discard) {
                invocations --= callingContexts
              }
            }
          }

      pruneMultipleOrRecursive()

          def asCaller(callee: MethodNode): collection.Set[Invocation] = { invocations.filter(invoc => invoc.caller == callee) }

          def promotesSimplerCodeDownTheRoad(callee: MethodNode): Boolean = {

            Util.computeMaxLocalsMaxStack(callee)
            // UnreachableCode eliminates null frames (which complicate further analyses).
            unreachCodeRemover.transform(cnode.name, callee)

            promotesClosureRecycling(callee) || promotesDeCapture(callee)
          }

          /**
           *  A private callee "promotes closure recycling (after inlining)" whenever it contains
           *  a INVOKESPECIAL <init> for an anonymous-closure instruction
           *  taking one or more method parameters as constructor args.
           *
           * */
          def promotesClosureRecycling(callee: MethodNode): Boolean = {

              def isClosureInit(insn: AbstractInsnNode) = {
                insn.getType == AbstractInsnNode.METHOD_INSN && {
                  val init = insn.asInstanceOf[MethodInsnNode]
                  init.name == "<init>" && isDClosure(init.owner)
                }
              }

            val closureInits = callee.instructions.toList collect { case i if isClosureInit(i) => i.asInstanceOf[MethodInsnNode] }
            if(closureInits.isEmpty) { return false }

            val cp = UnBoxAnalyzer.create()
            cp.analyze(cnode.name , callee)
            closureInits exists { init: MethodInsnNode =>
              val frame: asm.tree.analysis.Frame[SourceValue] = cp.frameAt(init)
              val actualArgs: Array[SourceValue] = frame.getActualArguments(init) map (_.asInstanceOf[SourceValue])

              actualArgs exists { (sv: SourceValue) =>
                (sv.insns.size() == 1) && {
                  sv.insns.iterator.next() match {
                    case p: FakeParamLoad => p.isFormalParam()
                    case _ => false
                  }
                }
              }
            }
          }

          /**
           *  A private callee "promotes de-capture (after inlining)" whenever
           *    (a) all usages of an IntRef, ObjectRef, etc. it receives as argument do not escape that method; and
           *    (b) at least one such usage is of the write-variety.
           *  We don't touch the Volatile... versions on purpose.
           * */
          def promotesDeCapture(callee: MethodNode): Boolean = {
            // TODO test the more precise condition above, for now testing an over-approximation.
            BType.getMethodType(callee.desc).getArgumentTypes.exists(bt => bt.isCapturedCellRef)
          }

          def rejected(invoc: Invocation): Boolean = {
            val Invocation(caller, _, callee) = invoc
            val callerS = caller.instructions.size
            val calleeS = caller.instructions.size

            // rejection criteria 1: method sizes
            val badSizes = (callerS + calleeS) > 1000 || {
              (callerS + calleeS > 500) && (callerS > 50) && (calleeS > 50)
            }
            if(badSizes) {
              log(s"Refrained from attempting to percolate method ${methodSignature(cnode, callee)} upwards " +
                  s"into method ${methodSignature(cnode, caller)} because of method sizes " +
                  s"(caller has $callerS instructions and callee has $calleeS instructions)"
              )
              return true
            }

            // rejection criteria 2: inlining the callee brings no benefit
            val bytecodeWeight = (calleeS - (callee.desc.length / 4))
            val promotes = promotesSimplerCodeDownTheRoad(callee)
            val noGain = (bytecodeWeight > 50) && !promotes
            if(noGain) {
              log(s"Refrained from attempting to percolate method ${methodSignature(cnode, callee)} upwards " +
                  s"into method ${methodSignature(cnode, caller)} because " +
                  s"inlining brings no benefit (bytecodeWeight=$bytecodeWeight, promotesClosureRecycling=$promotes)"
              )
              return true
            }

            false // ie not rejected
          }



      var progress = true
      while (invocations.nonEmpty && progress) {
        /*
         * For this round, pick those tuples where callee doesn't appear in any caller position, ie pick "leaf" invocations
         * In this round, "leaf" tuples will be removed, either due to successful inlining or not.
         * */
        val round = invocations.filter(invoc => asCaller(invoc.callee).isEmpty )
        progress = round.nonEmpty // progress false for invocation cycles involving two or more candidates.
        /*
         * No ranking needed because we're inlining all qualifying candidates reaching this far.
         * */
        for(Invocation(caller, callsite, callee) <- round filterNot rejected) {

          Util.computeMaxLocalsMaxStack(caller)
          Util.computeMaxLocalsMaxStack(callee)
          // UnreachableCode eliminates null frames (which complicate further analyses).
          unreachCodeRemover.transform(cnode.name, callee)
          unreachCodeRemover.transform(cnode.name, caller)

          val callsiteIndex = caller.instructions.indexOf(callsite)


          // val txtCalee  = Util.textify(callee)
          // val txtBefore = Util.textify(caller)

          val tfa = new Analyzer[TFValue](new TypeFlowInterpreter)
          tfa.analyze(cnode.name, caller)
          val callsiteTypeFlow = tfa.frameAt(callsite).asInstanceOf[asm.tree.analysis.Frame[TFValue]]

          val inlineOutcome =
            inlineMethod(
              cnode.name, caller,
              callsite, callsiteTypeFlow,
              callee, cnode,
              doTrackClosureUsage = true
            )

          // val txtAfter = Util.textify(caller)

          inlineOutcome match {
            case Some(problem) =>
              log(s"Couldn't percolate method ${methodSignature(cnode, callee)} upwards into method ${methodSignature(cnode, caller)} because $problem")
            case None =>
              log(s"Percolated (and then removed) small-private-methods-used-once ${methodSignature(cnode, callee)} " +
                  s"upwards into method ${methodSignature(cnode, caller)}. The original callsite was located at index $callsiteIndex")
              tfa.analyze(cnode.name, caller)
              cnode.methods.remove(callee)
          }

        }
        invocations --= round
      }


    } // end of method percolateUpwards()

  } // end of class WholeProgramAnalysis

  /**
   * @param mnode a MethodNode, usually found via codeRepo.getMethod(bt: BType, name: String, desc: String)
   * @param owner ClassNode declaring mnode
   */
  case class MethodNodeAndOwner(mnode: MethodNode, owner: ClassNode) {
    assert(owner.methods.contains(mnode))
  }

  //---------------------------------------------------------------------------
  // Optimization pack: closures (located here due to proximity with closuRepo)
  //---------------------------------------------------------------------------

  /**
   * Detects those dclosures that the `cnode` argument is exclusively responsible for
   * (consequence: all usages of the dclosure are confined to two places: master and the dclosure itself).
   *
   * For each such closure:
   *
   *   (1) lack of usages in `cnode` (eg as a result of dead-code elimination) means the closure can be elided,
   *       along with its endpoint. This may lead to further tree-shaking in `cnode` (via UnusedPrivateElider).
   *
   *   (2) minimize the dclosure fields (in particular, outer) to those actually used.
   *       "Minimizing the outer instance" means the endpoint is made static.
   *       The dclosure itself remains, but with smaller GC overhead.
   *
   * */
  override def shakeAndMinimizeClosures(cnode: ClassNode): Boolean = {

    val cnodeBT = lookupRefBType(cnode.name)
    if(!closuRepo.isMasterClass(cnodeBT)) { return false }

    // Serializable or not, it's fine: only dclosure-endpoints in cnode (a master class) will be mutated.

    var changed = false
    for(d <- closuRepo.liveDClosures(cnode)) {

      val dep = closuRepo.endpoint(d).mnode
      // if d not in use anymore (e.g., due to dead-code elimination) then remove its endpoint, and elide the class.
      val unused = { JListWrapper(cnode.methods) forall { mnode => closuRepo.closureAccesses(mnode, d).isEmpty } }
      if(unused) {
        changed = true
        elidedClasses.add(d) // a concurrent set
        cnode.methods.remove(dep)
        /* At this point we should closuRepo.retractAsDClosure(d) but the supporting maps aren't concurrent,
         * and moreover all three of them should be updated atomically. Relying on elidedClasses is enough. */
      }
      else if (!Util.isStaticMethod(dep)) {
        // the dclosure remains in use in cnode (it wasn't elided). The endpoint must still be there.
        assert(cnode.methods.contains(dep))
        assert(Util.isPublicMethod(dep))
        changed |= minimizeDClosureFields(cnode, dep, d)
      }

    }

    changed
  }

  /**
   * All usages of the dclosure are confined to two places: its master class and the dclosure itself.
   * We can minimize dclosure fields (in particular, outer) because we know where to find
   * all of the (endpoint invocations, dclosure instantiations) that will require adapting to remain well-formed.
   *
   * */
  private def minimizeDClosureFields(masterCNode: ClassNode, endpoint: MethodNode, d: BType): Boolean = {
    import asm.optimiz.UnusedParamsElider
    import asm.optimiz.StaticMaker

    val dCNode: ClassNode = codeRepo.classes.get(d)

        /**
         *  (1) remove params that go unused at the endpoint in the master class,
         *      also removing the arguments provided by the callsite in the dclosure class.
         *
         *  (2) attempt to make static the endpoint (and its invocation).
         *
         *  A master-class of a non-elided dclosure contains:
         *    - a single instantiation of it, and
         *    - no invocations to the dclosure's endpoint.
         *  (the "non-elided" part is responsible for that property: a dclosure that was inlined
         *   has a callsite to the endpoint in the shio method that replaces the higher-order method invocation).
         *
         * */
        def adaptEndpointAndItsCallsite(): Boolean = {
          var changed  = false
          val oldDescr = endpoint.desc
          // don't run UnusedPrivateElider on a ClassNode with a method temporarily made private.
          Util.makePrivateMethod(endpoint) // temporarily

          val elidedParams: java.util.Set[java.lang.Integer] = UnusedParamsElider.elideUnusedParams(masterCNode, endpoint)
          if(!elidedParams.isEmpty) {
            changed = true
            global synchronized {
              BType.getMethodType(endpoint.desc)
            }
            log(
             s"In order to minimize closure-fields, one or more params were elided from endpoint ${methodSignature(masterCNode, endpoint)} " +
             s". Before the change, its method descriptor was $oldDescr"
            )
            for(dmethod <- JListWrapper(dCNode.methods)) {
              UnusedParamsElider.elideArguments(dCNode, dmethod, masterCNode, endpoint, oldDescr, elidedParams)
            }
            closuRepo.assertEndpointInvocationsIsEmpty(masterCNode, d) /*debug*/
          }

          if(Util.isInstanceMethod(endpoint) && StaticMaker.lacksUsagesOfTHIS(endpoint)) {
            changed = true
            log(s"In order to minimize closure-fields, made static endpoint ${methodSignature(masterCNode, endpoint)}")
            Util.makeStaticMethod(endpoint)
            StaticMaker.downShiftLocalVarUsages(endpoint)
            for (dmethod <- JListWrapper(dCNode.methods)) {
              assert(!Util.isAbstractMethod(dmethod))
              StaticMaker.adaptCallsitesTargeting(dCNode, dmethod, masterCNode, endpoint)
            }
            closuRepo.assertEndpointInvocationsIsEmpty(masterCNode, d) /*debug*/
          }

          Util.makePublicMethod(endpoint)

          changed
        }

    if(!adaptEndpointAndItsCallsite()) {
      return false
    }

    // past this point one or more closure-fields are to be elided (outer instance, captured local, or any combination thereof).

    // PUTFIELD instructions for dclosure-fields that are never read can be eliminated,
    // which in turn is a pre-requisite for removal of redundant closure-state fields.
    // The whole process involves several steps.

    /*
     * Step 1: cancel-out DROP of closure-state GETFIELD
     * -------------------------------------------------
     *
     * Even if PushPopCollapser is run on the dclosure, instruction pairs of the form:
     *   LOAD_0
     *   GETFIELD of a closure-field
     *   DROP
     * still remain (PushPopCollapser does not elide a GETFIELD of a private final field,
     * because it doesn't check whether it's been assigned already or not).
     *
     * The custom transform below gets rid of those GETFIELD instructions, rewriting the above into:
     *   LOAD_0
     *   DROP
     *
     * A follow-up round of PushPopCollapser finishes the code clean-up.
     * */
    val cp = ProdConsAnalyzer.create()
    for (caller <- JListWrapper(dCNode.methods)) {
      Util.computeMaxLocalsMaxStack(caller)
      cp.analyze(dCNode.name, caller)
      for(
        // we'll modify caller.instructions in the for-body, that's fine because toList returns another list.
        drop <- caller.instructions.toList;
        if Util.isDROP(drop);
        producers = cp.producers(drop);
        if producers.size() == 1;
        prod = producers.iterator().next;
        if prod.getOpcode == Opcodes.GETFIELD;
        if prod.asInstanceOf[FieldInsnNode].owner == dCNode.name;
        if cp.isPointToPoint(prod, drop)
      ) {
        caller.instructions.set(prod, Util.getDrop(1)) // drop the receiver of GETFIELD, ie drop the result of LOAD_0
        caller.instructions.remove(drop)               // cancel-out the DROP for the result of GETFIELD
      }
    }

    val cleanser = new BCodeCleanser(dCNode)
    cleanser.intraMethodFixpoints()

    /*
     * Step 2: determine (declared) `closureState` and (effectively used) `whatGetsRead`
     * ---------------------------------------------------------------------------------
     * */
    val closureState: Map[String, FieldNode] = {
      JListWrapper(dCNode.fields).toList filter { fnode => Util.isInstanceField(fnode) } map { fnode => (fnode.name -> fnode) }
    }.toMap
    val whatGetsRead = mutable.Set.empty[String]
    for(
      caller <- JListWrapper(dCNode.methods);
      insn   <- caller.instructions.toList
    ) {
      if (insn.getOpcode == Opcodes.GETFIELD) {
        val fieldRead = insn.asInstanceOf[FieldInsnNode]
        assert(fieldRead.owner == dCNode.name)
        if (closureState.contains(fieldRead.name)) {
          whatGetsRead += fieldRead.name
        }
      }
    }

    if(whatGetsRead.size == closureState.size) {
      // elidedParams may refer to an apply-arg or a captured local, or combination thereof.
      return true // no closure-state field to elide after all (e.g., outer was a module, see test/files/run/Course-2002-10.scala)
    }

    val fieldsToRemove = for(Pair(fname, fnode) <- closureState; if !whatGetsRead.contains(fname) ) yield fnode;
    log(
     s"Minimizing closure-fields in dclosure ${d.getInternalName}. The following fields will be removed " +
     (fieldsToRemove map { fnode => fnode.name + " : " + fnode.desc }).mkString
    )

    /*
     * Step 3: determine correspondence redundant-closure-field-name -> constructor-params-position
     * --------------------------------------------------------------------------------------------
     * */
    // redundant-closure-field-name -> zero-based position the constructor param providing the value for it.
    val posOfRedundantCtorParam = mutable.Map.empty[String, Int]
    val ctor = (JListWrapper(dCNode.methods) find { caller => caller.name == "<init>" }).get
    val ctorBT = BType.getMethodType(ctor.desc)
    Util.computeMaxLocalsMaxStack(ctor)
    cp.analyze(dCNode.name, ctor)
    for(
      insn   <- ctor.instructions.toList
    ) {
      if (insn.getOpcode == Opcodes.PUTFIELD) {
        val fieldWrite = insn.asInstanceOf[FieldInsnNode]
        assert(fieldWrite.owner == dCNode.name)
        if (!whatGetsRead.contains(fieldWrite.name)) {
          val nonThisLocals = {
            JSetWrapper(cp.producers(fieldWrite)) map { insn => insn.asInstanceOf[VarInsnNode].`var` } filterNot { _ == 0 }
          }
          assert(nonThisLocals.size == 1)
          assert(!posOfRedundantCtorParam.contains(fieldWrite.name))
          val localVarIdx = nonThisLocals.iterator.next
          val paramPos    = ctorBT.convertLocalVarIdxToFormalParamPos(localVarIdx, true)
          posOfRedundantCtorParam.put(fieldWrite.name, paramPos)
        }
      }
    }
    assert(posOfRedundantCtorParam.nonEmpty)

    /*
     * Step 4: In case outer-instance is being removed, get rid of the following preamble
     * ----------------------------------------------------------------------------------
     *     ALOAD 1
     *     IFNONNULL L0
     *     NEW java/lang/NullPointerException
     *     DUP
     *     INVOKESPECIAL java/lang/NullPointerException.<init> ()V
     *     ATHROW
     * */
    val isOuterRedundant = {
       closureState.contains(nme.OUTER.toString) &&
      !whatGetsRead.contains(nme.OUTER.toString)
    }
    if(isOuterRedundant) {

      assert(posOfRedundantCtorParam(nme.OUTER.toString) == 0)

      val preamble = ctor.toList.filter(i => Util.isExecutable(i)).take(6).toArray

          def preambleAssert(idx: Int, pf: PartialFunction[AbstractInsnNode, Boolean]) {
            val insn = preamble(idx)
            assert(
              pf.isDefinedAt(insn) && pf(insn),
              s"While eliding a preamble in constructor ${methodSignature(dCNode, ctor)}}, " +
              s"expected another instruction at index ${ctor.instructions.indexOf(insn)} but found ${Util.textify(insn)}\n." +
               "Here's the complete bytecode of that constructor:" + Util.textify(ctor)
            )
          }

      preambleAssert(0, { case vi: VarInsnNode  => vi.getOpcode == Opcodes.ALOAD && vi.`var` == 1 } )
      preambleAssert(1, { case ji: JumpInsnNode => ji.getOpcode == Opcodes.IFNONNULL } )
      preambleAssert(2, { case ti: TypeInsnNode => ti.getOpcode == Opcodes.NEW  && ti.desc == "java/lang/NullPointerException" } )
      preambleAssert(3, { case in: InsnNode     => in.getOpcode == Opcodes.DUP } )
      preambleAssert(4,
        { case mi: MethodInsnNode =>
            mi.getOpcode == Opcodes.INVOKESPECIAL &&
            mi.owner == "java/lang/NullPointerException" &&
            mi.name  == "<init>" &&
            mi.desc  == "()V"
        }
      )
      preambleAssert(5, { case in: InsnNode => in.getOpcode == Opcodes.ATHROW } )
      for(i <- preamble) { ctor.instructions.remove(i) }

      // TODO once $outer is gone, the dclosure will invoke a static endpoint, and there's no reason to keep it InnerClass.
    }

    /*
     * Step 5: in the dclosure (e.g. its constructor) get rid of PUTFIELDs to closure-state fields never read
     * ------------------------------------------------------------------------------------------------------
     * */
    for(
      caller <- JListWrapper(dCNode.methods);
      insn   <- caller.instructions.toList
    ) {
      if (insn.getOpcode == Opcodes.PUTFIELD) {
        val fieldWrite = insn.asInstanceOf[FieldInsnNode]
        assert(fieldWrite.owner == dCNode.name)
        if (!whatGetsRead.contains(fieldWrite.name)) {
          val fnode = closureState(fieldWrite.name)
          val size  = descrToBType(fnode.desc).getSize
          caller.instructions.insert(fieldWrite, Util.getDrop(1)) // drops THIS
          caller.instructions.set(fieldWrite, Util.getDrop(size)) // drops field value
        }
      }
    }

    /*
     * Step 6: back-propagate DROPs inserted above, and remove redundant fields
     * (otherwise another attempt will be made to delete them next time around)
     * ------------------------------------------------------------------------
     * */
    cleanser.intraMethodFixpoints()
    for(fnode <- closureState.values; if !whatGetsRead.contains(fnode.name)) {
      dCNode.fields.remove(fnode)
    }

    /*
     * Step 7: adapt the method descriptor of the dclosure constructor, as well as <init> callsite in master class
     * -----------------------------------------------------------------------------------------------------------
     * */
    Util.makePrivateMethod(ctor) // temporarily
    val oldCtorDescr = ctor.desc
    val elideCtorParams: java.util.Set[java.lang.Integer] = UnusedParamsElider.elideUnusedParams(dCNode, ctor)
    Util.makePublicMethod(ctor)
    global synchronized {
      BType.getMethodType(ctor.desc)
    }
    assert(!elideCtorParams.isEmpty)
    for(callerInMaster <- JListWrapper(masterCNode.methods)) {
      UnusedParamsElider.elideArguments(masterCNode, callerInMaster, dCNode, ctor, oldCtorDescr, elideCtorParams)
    }

    true
  } // end of method minimizeDClosureFields()

  /**
   * Once no further `minimizeDClosureFields()` is possible, dclosures can be partitioned into the following classes:
   *
   *   (1) empty closure state: the endpoint (necessarily a static method) is invoked with (a subset of) the apply()'s arguments.
   *       In this case the closure can be turned into a singleton.
   *
   *   (2) closure state consisting only of outer-instance: irrespective of the dclosure's arity,
   *       besides (a subset of) the apply()'s arguments, the only additional value needed
   *       to invoke the endpoint is the outer-instance value.
   *       In this case the closure can be allocated once per outer-instance
   *       (for example, in the constructor of the class of the outer instance).
   *       "Per-outer-instance closure-singletons" are a trade-off: the assumption being their instantiation
   *       will be amortized over the many times it's passed as argument.
   *
   *   (3) closure state consists of one or more values other than the outer instance, if any.
   *
   *       In other words the subcases are:
   *         (3.a) the outer-instance and one or more captured values, or
   *         (3.b) one or more captured values,
   *       constitute the closure state.
   *       Under (3.a) the endpoint is an instance-method, while for (3.b) it's static.
   *
   *       In this last case (3), an allocation is needed each time the closure is passed as argument (to convey those captured values).
   *
   *       In theory two closures of the same closure-class capturing the same values are inter-changeable,
   *       thus a runtime "dictionary lookup" could provide an existing closure instance for a given tuple of captured values. Expensive.
   *
   * */
  override def minimizeDClosureAllocations(masterCNode: ClassNode) {
    val masterBT = lookupRefBType(masterCNode.name)
    if(!closuRepo.isMasterClass(masterBT)) { return }

    singletonizeDClosures(masterCNode)         // Case (1) empty closure state
    bringBackStaticDClosureBodies(masterCNode) // Cosmetic rewriting
    cleanseDClosures(masterCNode)
  }

  override def closureCachingAndEviction(cnode: ClassNode) {
    closureCachingAndEvictionHelper(cnode)
    val masterBT = lookupRefBType(cnode.name)
    if(closuRepo.isMasterClass(masterBT)) {
      for(d <- closuRepo.exclusiveDClosures(masterBT); if !elidedClasses.contains(d)) {
        // those dclosures for which `bringBackStaticDClosureBodies()` run may benefit from closure caching and eviction.
        closureCachingAndEvictionHelper(codeRepo.classes.get(d))
      }
    }
  }

  /**
   *  Handle Cases (2) and (3) as described in minimizeDClosureAllocations(),
   *  by adding code for caching and eviction of the "representative closure"
   *  ie a closure instance that is interchangeable with any other in that closure-equivalence class.
   *
   *  Two instances of an anonymous closure class (delegating or not) are equivalent
   *  iff they have same closure-state. That's easier to check for delegating closures,
   *  where it's safe to assume that all of its instance fields make up the closure-state.
   *
   *  This method does not mutate closure classes, but those MethodNodes
   *  containing allocations of delegating closures (we focus on delegating closures only).
   *
   *  Gist
   *  ----
   *
   *  Rather than checking at allocation-site whether the arguments to the ctor match
   *  those of a cached representative (an "Available Expressions" or "Definite Alias" problem),
   *  we rely on each STORE to a local as above also "killing" the cached representative,
   *  by assigning null to the local holding it.
   *
   *  The above works well enough: for example, in case closure-state is loop invariant,
   *  the desired affect of allocating once during the first pass through the loop
   *  is achieved. It's not "loop hoisting proper", but with the same effect
   *  (we piggy-back on the JVM analyses to detect the cache won't be null after the first pass).
   *
   *  Rewriting
   *  ---------
   *
   *  (1) for each non-abstract method find pairs (NEW, INIT) of instructions that bracket
   *      a closure allocation, along with a Set[Int] representing the LOAD_x instructions
   *      providing values for the INIT.
   *
   *      Remarks:
   *        - instantiations not fulfulling the condition above aren't candidates for this transformation.
   *        - 0 is removed from Set[Int] if present, thus it may be empty (for a delegating-closure
   *          just capturing its outer instance. All delegating-closures capturing no value have been
   *          singleton-ized by now).
   *
   *  (2) if no pair found, move on to next method.
   *
   *  (3) for each bracket:
   *      - add a local var to cache it, initialized to null on method entry
   *      - right before the NEW, insert: LOAD  cache, IFNONNULL L1
   *      - right after the INIT, insert: STORE cache, LabelNode L1, LOAD cache
   *      - iterate over all instructions in the method,
   *        if STORE to a var in Set[Int], insert right after it a STORE NULL to cache
   *
   *  (4) run an intra-method fixpoint on the method, so as to:
   *      - elide redundant null stores
   *      - propagate nulls
   *
   * */
  private def closureCachingAndEvictionHelper(cnode: ClassNode) {
    val cnodeBT = lookupRefBType(cnode.name)
    if(elidedClasses.contains(cnodeBT)) { return }

        case class Bracket(newInsn: TypeInsnNode, initInsn: MethodInsnNode, stateLocals: collection.Set[Int])

        def findBracket(newInsn: TypeInsnNode, mnode: MethodNode): Bracket = {
          val dclosureIName = newInsn.desc
          val dclosureBT = lookupRefBType(dclosureIName)
          if(!closuRepo.isDelegatingClosure(dclosureBT)) {
            return null
          }

          def logUponOffendingInsn(offendingInsn: AbstractInsnNode, reason: String) {
            log(
              s"Attempt at closure caching and eviction in method ${methodSignature(cnode, mnode)} " +
              s"failed because $reason, " +
              s"more precisely at index ${mnode.instructions.indexOf(offendingInsn)} where instruction ${Util.textify(offendingInsn)} can be found.\n" +
               "Full bytecode of that method:" + Util.textify(mnode)
            )
          }

          val isLasInsnInBoilerplate: PartialFunction[AbstractInsnNode, Boolean] =
            { case mi: MethodInsnNode =>
                mi.getOpcode == Opcodes.INVOKESPECIAL &&
                mi.owner     == dclosureIName &&
                mi.name      == "<init>" // TODO we assume the constructor descriptor can't be any other than the right one :)
              case _ => false
            }

          if(newInsn.getNext.getOpcode != Opcodes.DUP) {
            logUponOffendingInsn(newInsn.getNext, "non-DUP instruction found right before the ctor-args-loading section")
            return null
          }
          var argLoader = newInsn.getNext.getNext
          val stateLocals = mutable.Set.empty[Int]
          while(!isLasInsnInBoilerplate(argLoader)) {
            if(Util.isExecutable(argLoader)) {
              if(Util.isLOAD(argLoader)) {
                val idx = argLoader.asInstanceOf[VarInsnNode].`var`
                if(idx != 0) {
                  stateLocals += idx
                }
              } else {
                val isOK = {
                  (argLoader.getOpcode == Opcodes.CHECKCAST) ||
                  (Util.isPrimitiveConstant(argLoader))      ||
                  (Util.isStringConstant(argLoader))         ||
                  (Util.isTypeConstant(argLoader))
                }
                if(!isOK) {
                  logUponOffendingInsn(argLoader, "of non-LOAD, non-CHECKCAST instruction in the ctor-args-loading section")
                  return null
                }
              }
            }
            argLoader = argLoader.getNext
          }

          Bracket(newInsn, argLoader.asInstanceOf[MethodInsnNode], stateLocals)
        } // end of method findBracket

        /**
         * Step (3) Perform transformation for each bracket
         * */
        def addCachingAndEviction(br: Bracket, mnode: MethodNode) {
          // add a local var to cache it, initialized to null on method entry
          val cacheIdx = mnode.maxLocals
          mnode.maxLocals += 1
          val insnList = mnode.instructions
          insnList.insert(new VarInsnNode(Opcodes.ASTORE, cacheIdx))
          insnList.insert(new InsnNode(Opcodes.ACONST_NULL))
          // right before the NEW, insert: LOAD  cache, IFNONNULL L1
          insnList.insertBefore(br.newInsn, new VarInsnNode(Opcodes.ALOAD, cacheIdx))
          val lnode = new LabelNode(new asm.Label)
          insnList.insertBefore(br.newInsn, new JumpInsnNode(Opcodes.IFNONNULL, lnode))
          // right after the INIT, insert: STORE cache, LabelNode L1, LOAD cache
          insnList.insert(br.initInsn, new VarInsnNode(Opcodes.ALOAD, cacheIdx))
          insnList.insert(br.initInsn, lnode)
          insnList.insert(br.initInsn, new VarInsnNode(Opcodes.ASTORE, cacheIdx))
          // iterate over all instructions in the method, if STORE to a var in Set[Int],
          // insert right after it a STORE NULL to cache
          val killers = mutable.Set.empty[AbstractInsnNode]
          for(
            i <- mnode.instructions.toList;
            if Util.isSTORE(i) && br.stateLocals(i.asInstanceOf[VarInsnNode].`var`)
          ) {
            killers += i
          }
          for(k <- killers) {
            insnList.insert(k, new VarInsnNode(Opcodes.ASTORE, cacheIdx))
            insnList.insert(k, new InsnNode(Opcodes.ACONST_NULL))
          }
        } // end of method addCachingAndEviction()


    for(mnode <- JListWrapper(cnode.methods); if !Util.isAbstractMethod(mnode) ) {
      // Step (1) Find brackets fulfilling conditions
      var brackets: List[Bracket] = Nil
      var current = mnode.instructions.getFirst
      while(current != null) {
        if(current.getOpcode == Opcodes.NEW) {
          val br = findBracket(current.asInstanceOf[TypeInsnNode], mnode)
          if(br != null) {
            brackets ::= br
            current = br.initInsn
          }
        }
        current = current.getNext
      }
      if(!brackets.isEmpty) {

        // val txtBefore = Util.textify(mnode); println("Before -------------------------------- " + txtBefore)

        // Step (3) Perform transformation for each bracket
        for(br <- brackets) {
          addCachingAndEviction(br, mnode)
        }

        // val txtDuring = Util.textify(mnode); println("During -------------------------------- " + txtDuring)

        // Step (4) run an intra-method fixpoint on all methods
        val cleanser = new BCodeCleanser(cnode)
        cleanser.basicIntraMethodOpt(mnode)

        // val txtAfter = Util.textify(mnode); println("After -------------------------------- " + txtAfter)
      }
    } // end of method iteration

  } // end of method closureCachingAndEvictionHelper()

  /**
   *  Handle the following subcase described in minimizeDClosureAllocations():
   *
   *   (1) empty closure state: the endpoint (necessarily a static method) is invoked with (a subset of) the apply()'s arguments.
   *       In this case the closure can be turned into a singleton.
   *
   * */
  private def singletonizeDClosures(masterCNode: ClassNode) {
    for(d <- closuRepo.liveDClosures(masterCNode)) {

      val dep    = closuRepo.endpoint(d).mnode
      val dCNode = codeRepo.classes.get(d)
      val closureState: Map[String, FieldNode] = {
        JListWrapper(dCNode.fields).toList filter { fnode => Util.isInstanceField(fnode) } map { fnode => (fnode.name -> fnode) }
      }.toMap
      val dClassDescriptor = "L" + dCNode.name + ";"

      // ------------------------------------------------------------------
      // Case (1): the dclosure can be turned into a program-wide singleton
      // ------------------------------------------------------------------
      val lacksClosureState = closureState.isEmpty
      if(lacksClosureState) {

        log("Singleton-closure: " + dCNode.name)

        // -------- (1.a) modify the dclosure class (add $single static field, initialize it in <clinit>)
        val ctor = (JListWrapper(dCNode.methods) find { caller => caller.name == "<init>" }).get
        Util.makePrivateMethod(ctor)
        val single =
          new FieldNode(
            Opcodes.ASM4,
            Opcodes.ACC_PUBLIC | Opcodes.ACC_FINAL | Opcodes.ACC_STATIC,
            "$single",
            dClassDescriptor,
            null, null
          )
        dCNode.fields.add(single)
        val staticClassInitializer =
          new MethodNode(
            Opcodes.ASM4,
            Opcodes.ACC_PUBLIC | Opcodes.ACC_STATIC,
            "<clinit>",
            "()V",
            null, null
          )
        dCNode.methods.add(staticClassInitializer)
        val insns = new InsnList()
        insns.add(new TypeInsnNode(Opcodes.NEW, dCNode.name))
        insns.add(new InsnNode(Opcodes.DUP))
        insns.add(new MethodInsnNode(Opcodes.INVOKESPECIAL, dCNode.name, "<init>", "()V"))
        insns.add(new FieldInsnNode(Opcodes.PUTSTATIC, dCNode.name, single.name, dClassDescriptor))
        insns.add(new InsnNode(Opcodes.RETURN))
        staticClassInitializer.instructions.add(insns)

        // -------- (1.b) modify the master class (replace instantiation by GETSTATIC of the singleton)
        for(
          callerInMaster <- JListWrapper(masterCNode.methods);
          newInsn        <- closuRepo.closureAccesses(callerInMaster, d)
        ) {
          assert(newInsn.getOpcode == Opcodes.NEW)
          /*
           * A dclosure instantiation (the code pattern to replace) usually looks like:
           *
           *     NEW dclosure
           *     DUP
           *     INVOKESPECIAL dclosure.<init> ()V
           *
           * In a few cases it may look like:
           *
           *     NEW dclosure
           *     DUP
           *     ALOAD 0
           *     CHECKCAST X
           *     POP
           *     INVOKESPECIAL dclosure.<init> ()V
           *
           * The second case arises because PushPopCollapser doesn't back-propagate POP over CHECKCAST
           * (that would requires a type-flow based analysis).
           *
           * */

              def snippetTest(idx: Int, insn: AbstractInsnNode, pf: PartialFunction[AbstractInsnNode, Boolean]): Boolean = {
                val isBoilerplate = pf.isDefinedAt(insn) && pf(insn)
                if(!isBoilerplate) {
                  log(
                    s"Attempt to replace instantiation with GETSTATIC of singleton dclosure ${d.getInternalName} " +
                    s"in method ${methodSignature(masterCNode, callerInMaster)}."  +
                    s"Expected another instruction at index ${callerInMaster.instructions.indexOf(insn)} but found ${Util.textify(insn)}\n." +
                     "Here's the complete bytecode of that method:" + Util.textify(callerInMaster)
                  )
                }

                isBoilerplate
              }

          val isLasInsnInBoilerplate: PartialFunction[AbstractInsnNode, Boolean] =
            { case mi: MethodInsnNode =>
                mi.getOpcode == Opcodes.INVOKESPECIAL &&
                mi.owner     == d.getInternalName     &&
                mi.name      == "<init>" &&
                mi.desc      == "()V"
              case _ => false
            }

              // logs only the first divergence from "boilerplate"
              def isBoilerplate = {
                snippetTest(0, newInsn,         { case ti: TypeInsnNode   => ti.getOpcode == Opcodes.NEW && ti.desc == d.getInternalName }) &&
                snippetTest(1, newInsn.getNext, { case di: InsnNode       => di.getOpcode == Opcodes.DUP }) &&
                snippetTest(2, newInsn.getNext.getNext, isLasInsnInBoilerplate)
              }

          val lastInsn: MethodInsnNode = {
            var current: AbstractInsnNode = newInsn
            while(!isLasInsnInBoilerplate(current)) {
              current = current.getNext
            }
            current.asInstanceOf[MethodInsnNode]
          }

          if(!isBoilerplate) {
            val dupInsn = newInsn.getNext
            assert(dupInsn.getOpcode == Opcodes.DUP)
            // move NEW, DUP right before INVOKESPECIAL <init> , ie right before `lastInsn` of the instruction bracket
            callerInMaster.instructions.remove(newInsn)
            callerInMaster.instructions.remove(dupInsn)
            callerInMaster.instructions.insertBefore(lastInsn, newInsn)
            callerInMaster.instructions.insertBefore(lastInsn, dupInsn)
            assert(isBoilerplate)
          }

          // remove all instructions of the bracket except for the first one, NEW dclosure
          var current: AbstractInsnNode = lastInsn
          while(current ne newInsn) {
            val prev = current.getPrevious
            callerInMaster.instructions.remove(current)
            current = prev
          }
          // replace NEW dclosure by GETSTATIC singleton
          callerInMaster.instructions.set(
            newInsn,
            new FieldInsnNode(Opcodes.GETSTATIC, d.getInternalName, single.name, single.desc)
          )
        }

      }

    }

  } // end of method singletonizeDClosures()

  /**
   *  Cosmetic rewriting: if possible, move back the endpoint's instructions to the dclosure's apply
   *
   * */
  private def bringBackStaticDClosureBodies(masterCNode: ClassNode) {

    for(d <- closuRepo.liveDClosures(masterCNode)) {

      val dep    = closuRepo.endpoint(d).mnode
      val dCNode = codeRepo.classes.get(d)
      val closureState: Map[String, FieldNode] = {
        JListWrapper(dCNode.fields).toList filter { fnode => Util.isInstanceField(fnode) } map { fnode => (fnode.name -> fnode) }
      }.toMap
      val dClassDescriptor = "L" + dCNode.name + ";"

      if(Util.isStaticMethod(dep) && masterCNode.methods.contains(dep)) {

        log(
          "Bringing back the endpoint's instructions to the dclosure's apply(), " +
         s"from endpoint ${methodSignature(masterCNode, dep)} to dclosure ${dCNode.name}"
        )

        val wp = new WholeProgramAnalysis(isMultithread = true)
        val endpointCallers: List[Pair[MethodNode, MethodInsnNode]] = {
          for(
            applyMethod <- JListWrapper(dCNode.methods).toList;
            if !Util.isConstructor(applyMethod);
            callsite    <- applyMethod.toList;
            if closuRepo.invokedDClosure(callsite) == d
          ) yield (applyMethod -> callsite.asInstanceOf[MethodInsnNode])
        }
        assert(endpointCallers.tail.isEmpty)
        val Pair(applyMethod, callsite) = endpointCallers.head

        Util.computeMaxLocalsMaxStack(applyMethod)
        val tfa = new asm.tree.analysis.Analyzer[TFValue](new TypeFlowInterpreter)
        tfa.analyze(dCNode.name, applyMethod)
        val frame = tfa.frameAt(callsite).asInstanceOf[asm.tree.analysis.Frame[TFValue]]

        val inlineOutcome =
          wp.inlineMethod(
            dCNode.name, applyMethod,
            callsite, frame,
            dep, masterCNode,
            doTrackClosureUsage = false
          )
        inlineOutcome match {
          case Some(problem) =>
            log(s"Couldn't bring back the endpoint's instructions because $problem")
          case None =>
            val cleanser = new BCodeCleanser(dCNode)
            cleanser.intraMethodFixpoints()
            // if the closure hasn't been elided, that implies its endpoint isn't invoked from any shio-method,
            // in fact it must be invoked only from the dclosure's apply(). Thus we can remove the endpoint from the master class.
            closuRepo.assertEndpointInvocationsIsEmpty(masterCNode, d) /*debug*/
            masterCNode.methods.remove(dep)
        }
      }

    }

  } // end of method bringBackStaticDClosureBodies()

  private def cleanseDClosures(masterCNode: ClassNode) {

    for(d <- closuRepo.liveDClosures(masterCNode)) {
      val dCNode: ClassNode = codeRepo.classes.get(d)
      val cleanser = new BCodeCleanser(dCNode)
      cleanser.intraMethodFixpoints()
    }

  } // end of method cleanseDClosures()

} // end of class BCodeOptInter


/*
 * TODO After method-inlining, some IntRef, VolatileIntRef, etc. may not escape anymore and can be converted back to local-vars.
 *
 *  In particular after inlining:
 *    (a) what used to be local-method; or
 *    (b) the delegate invoked by a closure converted via "closureConversionModern()"
 *
 *  In addition to not escaping, there should be no doubt as to what Ref value is being manipulated
 *  (e.g., merging two Refs prevents from "un-wrapping" it). This can be checked
 *  with a copy-propagating, param-aware, consumers-producers analysis, as follows.
 *  First, find all Ref instantiations, and for each:
 *    (1) check all consumers form a DEMUX,
 *        where each consumer instruction is either a GETFIELD or PUTFIELD of the "elem" field.
 *  Transformation proper:
 *    (2) for each survivor,
 *        (2.a) NEW, DUP, < init > becomes STORE
 *        (2.b) getter: LOAD ref, GETFIELD elem ----> LOAD  var
 *        (2.b) setter: LOAD ref, PUTFIELD elem ----> STORE var
 *  Shifting of local-vars:
 *    A local-var holding a ref holds a category-1 value. After "unwrapping" L or D the local-var will hold a category-2 value.
 *
 **/