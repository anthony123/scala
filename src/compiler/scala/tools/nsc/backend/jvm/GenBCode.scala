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
    with    BCPickles
    with    BCCommonPhase {

    override def name = phaseName
    override def description = "Generate bytecode from ASTs"
    override def erasedTypes = true

    override def run() {
      scalaPrimitives.init
      super.run()
    }

    override def apply(unit: CompilationUnit): Unit = {
      // this.unit = unit
      // gen(unit.body)
      // this.unit = NoCompilationUnit
    }

    var cnode: asm.tree.ClassNode  = null
    var mnode: asm.tree.MethodNode = null

    object bc extends JCodeMethodN {
      override def jmethod = BCodePhase.this.mnode
    }

  } // end of class BCodePhase

} // end of class GenBCode
