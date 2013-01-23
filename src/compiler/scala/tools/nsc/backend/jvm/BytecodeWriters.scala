/* NSC -- new Scala compiler
 * Copyright 2005-2013 LAMP/EPFL
 * @author  Paul Phillips
 */

package scala.tools.nsc
package backend.jvm

import java.io.{ DataOutputStream, FileOutputStream, OutputStream, File => JFile }
import scala.tools.nsc.io._
import scala.tools.nsc.util.ScalaClassLoader
import scala.tools.util.{ Javap, JavapClass }
import java.util.jar.Attributes.Name
import scala.language.postfixOps

/** For the last mile: turning generated bytecode in memory into
 *  something you can use.  Has implementations for writing to class
 *  files, jars, and disassembled/javap output.
 */
trait BytecodeWriters {
  val global: Global
  import global._

  private def outputDirectory(sym: Symbol): AbstractFile = (
    settings.outputDirs.outputDirFor(enteringFlatten(sym.sourceFile))
  )
  private def getFile(base: AbstractFile, /*cls.getName()*/ clsName: String, suffix: String): AbstractFile = {
    var dir = base
    val pathParts = clsName.split("[./]").toList
    for (part <- pathParts.init) {
      dir = dir.subdirectoryNamed(part)
    }
    dir.fileNamed(pathParts.last + suffix)
  }
  private def getFile(sym: Symbol, clsName: String, suffix: String): AbstractFile =
    getFile(outputDirectory(sym), clsName, suffix)

  trait BytecodeWriter {
    def writeClass(label: String, jclassName: String, jclassBytes: Array[Byte], outfile: AbstractFile): Unit
    def close(): Unit = ()
  }

  class DirectToJarfileWriter(jfile: JFile) extends BytecodeWriter {
    val jarMainAttrs = (
      if (settings.mainClass.isDefault) Nil
      else List(Name.MAIN_CLASS -> settings.mainClass.value)
    )
    val writer = new Jar(jfile).jarWriter(jarMainAttrs: _*)

    def writeClass(label: String, jclassName: String, jclassBytes: Array[Byte], outfile: AbstractFile) {
      assert(outfile == null,
             "The outfile formal param is there just because ClassBytecodeWriter overrides this method and uses it.")
      val path = jclassName + ".class"
      val out  = writer.newOutputStream(path)

      try out.write(jclassBytes, 0, jclassBytes.length)
      finally out.flush()

      informProgress("added " + label + path + " to jar")
    }
    override def close() = writer.close()
  }

  /** To be mixed-in with the BytecodeWriter that generates
   *  the class file to be disassembled.
   */
  trait JavapBytecodeWriter extends BytecodeWriter {
    private val baseDir = Directory(settings.Ygenjavap.value).createDirectory()
    private val cl      = ScalaClassLoader.appLoader

    private def emitJavap(classFile: AbstractFile, javapFile: File) {
      val pw = javapFile.printWriter()
      try {
        val javap = new JavapClass(cl, pw) {
          override def findBytes(path: String): Array[Byte] = classFile.toByteArray
        }
        javap(Seq("-verbose", "-protected", classFile.name)) foreach (_.show())
      } finally pw.close()
    }
    abstract override def writeClass(label: String, jclassName: String, jclassBytes: Array[Byte], outfile: AbstractFile) {
      super.writeClass(label, jclassName, jclassBytes, outfile)

      val segments  = jclassName.split("[./]")
      val javapFile = segments.foldLeft(baseDir: Path)(_ / _) changeExtension "javap" toFile;
      javapFile.parent.createDirectory()

      if (Javap.isAvailable(cl)) emitJavap(outfile, javapFile)
      else warning("No javap on classpath, skipping javap output.")
    }
  }

  trait AsmpBytecodeWriter extends BytecodeWriter {
    import scala.tools.asm

    private val baseDir = Directory(settings.Ygenasmp.value).createDirectory()

    private def emitAsmp(jclassBytes: Array[Byte], asmpFile: io.File) {
      val pw = asmpFile.printWriter()
      try {
        val cnode = new asm.tree.ClassNode()
        val cr    = new asm.ClassReader(jclassBytes)
        cr.accept(cnode, 0)
        val trace = new scala.tools.asm.util.TraceClassVisitor(new java.io.PrintWriter(new java.io.StringWriter()))
        cnode.accept(trace)
        trace.p.print(pw)
      }
      finally pw.close()
    }

    abstract override def writeClass(label: String, jclassName: String, jclassBytes: Array[Byte], outfile: AbstractFile) {
      super.writeClass(label, jclassName, jclassBytes, outfile)

      val segments  = jclassName.split("[./]")
      val asmpFile = segments.foldLeft(baseDir: Path)(_ / _) changeExtension "asmp" toFile;

      asmpFile.parent.createDirectory()
      emitAsmp(jclassBytes, asmpFile)
    }
  }

  trait ClassBytecodeWriter extends BytecodeWriter {
    def writeClass(label: String, jclassName: String, jclassBytes: Array[Byte], outfile: AbstractFile) {
      assert(outfile != null,
             "Precisely this override requires its invoker to hand out a non-null AbstractFile.")
      val outstream = new DataOutputStream(outfile.bufferedOutput)

      try outstream.write(jclassBytes, 0, jclassBytes.length)
      finally outstream.close()
      informProgress("wrote '" + label + "' to " + outfile)
    }
  }

  trait DumpBytecodeWriter extends BytecodeWriter {
    val baseDir = Directory(settings.Ydumpclasses.value).createDirectory()

    abstract override def writeClass(label: String, jclassName: String, jclassBytes: Array[Byte], outfile: AbstractFile) {
      super.writeClass(label, jclassName, jclassBytes, outfile)

      val pathName = jclassName
      val dumpFile = pathName.split("[./]").foldLeft(baseDir: Path) (_ / _) changeExtension "class" toFile;
      dumpFile.parent.createDirectory()
      val outstream = new DataOutputStream(new FileOutputStream(dumpFile.path))

      try outstream.write(jclassBytes, 0, jclassBytes.length)
      finally outstream.close()
    }
  }
}
