/* NSC -- new Scala compiler
 * Copyright 2005-2011 LAMP/EPFL
 * @author  Martin Odersky
 */


package scala.tools.nsc
package backend
package jvm

import scala.collection.{ mutable, immutable }
import scala.collection.mutable.{ ListBuffer, Buffer }
import scala.tools.nsc.symtab._
import scala.annotation.switch
import scala.tools.asm
import asm.tree.ClassNode

/** Prepare in-memory representations of classfiles using the ASM Tree API, and serialize them to disk.
 *
 *  @author  Miguel Garcia, http://lamp.epfl.ch/~magarcia/ScalaCompilerCornerReloaded/
 *  @version 1.0
 */
abstract class GenBCode extends BCodeUtils {
  import global._
  import icodes._
  import icodes.opcodes._
  import definitions._

  val phaseName = "bcode"

  override def newPhase(prev: Phase) = new BCodePhase(prev)

  class BCodePhase(prev: Phase)
    extends StdPhase(prev)
    with    BCInnerClassGen
    with    BCClassGen
    with    BCAnnotGen
    with    BCJGenSigGen
    with    BCPickles
    with    BCCommonPhase {

    override def name = phaseName
    override def description = "Generate bytecode from ASTs"
    override def erasedTypes = true

    private var bytecodeWriter  : BytecodeWriter   = null
    private var mirrorCodeGen   : JMirrorBuilder   = null
    private var beanInfoCodeGen : JBeanInfoBuilder = null

    /* ---------------- what is currently being visited ---------------- */

    private var cunit: CompilationUnit     = null
    private val pkg = new mutable.Stack[String]
    private var cnode: asm.tree.ClassNode  = null
    private var thisName: String           = null // the internal name of the class being emitted
    private var mnode: asm.tree.MethodNode = null

    override def getCurrentCUnit(): CompilationUnit = { cunit }

    override def run() {
      scalaPrimitives.init
      bytecodeWriter  = initBytecodeWriter(cleanup.getEntryPoints)
      mirrorCodeGen   = new JMirrorBuilder(bytecodeWriter)
      beanInfoCodeGen = new JBeanInfoBuilder(bytecodeWriter)
      super.run()
      bytecodeWriter.close()
      reverseJavaName.clear()
    }

    override def apply(unit: CompilationUnit): Unit = {
      this.cunit = unit
      gen(unit.body)
      this.cunit = NoCompilationUnit
    }

    object bc extends JCodeMethodN {
      override def jmethod = BCodePhase.this.mnode
    }

    /* ---------------- top-down traversal invoking ASM Tree API along the way ---------------- */

    def gen(tree: Tree) {
      tree match {
        case EmptyTree => ()

        case PackageDef(pid, stats) =>
          pkg push pid.name.toString
          stats foreach gen
          pkg.pop()

        case cd: ClassDef =>
          genPlainClass(cd)
          // TODO mirror and bean info, if needed.

        case ModuleDef(mods, name, impl) =>
          abort("Modules should have been eliminated by refchecks: " + tree)

        case ValDef(mods, name, tpt, rhs) =>
          () // fields are added in the case handler for ClassDef

        case dd: DefDef if (dd.symbol.isStaticConstructor || definitions.isGetClass(dd.symbol)) =>
          ()

        case dd @ DefDef(mods, name, tparams, vparamss, tpt, rhs) =>
          val msym = tree.symbol
          // clear method-specific stuff
              // TODO local-ranges table
              // TODO exh-handlers table
          // add params
          assert(vparamss.isEmpty || vparamss.tail.isEmpty, "Malformed parameter list: " + vparamss)
          val paramIdx = if (msym.isStaticMember) 0 else 1;
          for (p <- vparamss.head) {
            // TODO val lv = new Local(p.symbol, toTypeKind(p.symbol.info), true)
          }

          val returnType =
            if (tree.symbol.isConstructor) UNIT
            else toTypeKind(tree.symbol.info.resultType)

          // addMethodParams(vparamss)
          val isNative = msym.hasAnnotation(definitions.NativeAttr)
          val isAbstractMethod = msym.isDeferred || msym.owner.isInterface

          if (!isAbstractMethod && !isNative) {
            genLoad(rhs, returnType)
            // TODO see JPlainBuilder.addAndroidCreatorCode()
            rhs match {
              case Block(_, Return(_)) => ()
              case Return(_) => ()
              case EmptyTree =>
                globalError("Concrete method has no definition: " + tree + (
                  if (settings.debug.value) "(found: " + msym.owner.info.decls.toList.mkString(", ") + ")"
                  else "")
                )
              case _ =>
                // TODO ctx1.bb.closeWith(RETURN(m.returnType), rhs.pos)
            }
          }

        case Template(_, _, body) =>
          body foreach gen

        case _ =>
          abort("Illegal tree in gen: " + tree)
      }
    } // end of method gen(Tree)

    def genLoad(tree: Tree, expectedType: TypeKind) {
      // TODO
    }

    /* ---------------- helper utils invoked from gen() methods ---------------- */

    def genPlainClass(cd: ClassDef) {
      assert(cnode == null, "GenBCode detected flatten didn't run.")
      innerClassBuffer.clear()

      val csym = cd.symbol
      thisName = javaName(csym)
      cnode = new asm.tree.ClassNode()
      initJClass(cnode, csym, thisName, getGenericSignature(csym, csym.owner))

      // TODO from visitSource to emitAnnotations

      // TODO addStaticInit, constructors

      addClassFields(csym)
      addSerialVUID(csym, cnode)

      gen(cd.impl)

      // TODO annotations, attributes

      addInnerClasses(csym, cnode)
      writeIfNotTooBig("" + csym.name, thisName, cnode, csym)
      cnode = null

    } // end of method genPlainClass()

    def addClassFields(cls: Symbol) {
      /** Non-method term members are fields, except for module members. Module
       *  members can only happen on .NET (no flatten) for inner traits. There,
       *  a module symbol is generated (transformInfo in mixin) which is used
       *  as owner for the members of the implementation class (so that the
       *  backend emits them as static).
       *  No code is needed for this module symbol.
       */
      for (f <- cls.info.decls ; if !f.isMethod && f.isTerm && !f.isModule) {
        val javagensig = getGenericSignature(f, cls)
        val flags = mkFlags(
          javaFieldFlags(f),
          if(isDeprecated(f)) asm.Opcodes.ACC_DEPRECATED else 0 // ASM pseudo access flag
        )

        val jfield = new asm.tree.FieldNode(
          flags,
          javaName(f),
          javaType(f.tpe).getDescriptor(),
          javagensig,
          null // no initial value
        )
        cnode.fields.add(jfield)
        emitAnnotations(jfield, f.annotations)
      }

    } // end of method addClassFields()

    /* if you look closely, there's almost no code duplication with JBuilder's `writeIfNotTooBig()` */
    def writeIfNotTooBig(label: String, jclassName: String, cnode: asm.tree.ClassNode, sym: Symbol) {
      try {
        val cw = new CClassWriter(extraProc)
        cnode.accept(cw)
        val arr = cw.toByteArray
        bytecodeWriter.writeClass(label, jclassName, arr, sym)
      } catch {
        case e: java.lang.RuntimeException if(e.getMessage() == "Class file too large!") =>
          // TODO check where ASM throws the equivalent of CodeSizeTooBigException
          log("Skipped class "+jclassName+" because it exceeds JVM limits (it's too big or has methods that are too long).")
      }
    }

  } // end of class BCodePhase

} // end of class GenBCode
