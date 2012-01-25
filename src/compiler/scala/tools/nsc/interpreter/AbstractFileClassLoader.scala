/* NSC -- new Scala compiler
 * Copyright 2005-2011 LAMP/EPFL
 */

package scala.tools.nsc
package interpreter

import scala.tools.nsc.io.{ File, AbstractFile }
import util.ScalaClassLoader
import java.net.URL
import scala.collection.{ mutable, immutable }

/**
 * A class loader that loads files from a {@link scala.tools.nsc.io.AbstractFile}.
 *
 * @author Lex Spoon
 */
class AbstractFileClassLoader(root: AbstractFile, parent: java.lang.ClassLoader)
    extends ClassLoader(parent)
    with ScalaClassLoader
{
  // private val defined = mutable.Map[String, Class[_]]()
  override protected def trace =
    sys.props contains "scala.debug.classloader"

  protected def classNameToPath(name: String): String =
    if (name endsWith ".class") name
    else name.replace('.', '/') + ".class"

  protected def findAbstractFile(name: String): AbstractFile = {
    var file: AbstractFile = root
    val pathParts          = classNameToPath(name) split '/'

    for (dirPart <- pathParts.init) {
      file = file.lookupName(dirPart, true)
      if (file == null)
        return null
    }

    file.lookupName(pathParts.last, false) match {
      case null   => null
      case file   => file
    }
  }

  override def getResourceAsStream(name: String) = findAbstractFile(name) match {
    case null => super.getResourceAsStream(name)
    case file => file.input
  }
  override def classBytes(name: String): Array[Byte] = findAbstractFile(name) match {
    case null => super.classBytes(name)
    case file => file.toByteArray
  }
  override def loadClass(name: String, resolve: Boolean) = {
    classLoaderLog("load " + name + ".")
    super.loadClass(name, resolve)
  }
  override def findClass(name: String): JClass = {
    val bytes = classBytes(name)
    classLoaderLog("find %s: %s".format(name,
      if (bytes.isEmpty) "failed."
      else bytes.size + " bytes."
    ))
    if (bytes.isEmpty)
      throw new ClassNotFoundException(name)
    else {
      val clazz = defineClass(name, bytes, 0, bytes.length)
      // defined(name) = clazz
      clazz
    }
  }
  // Don't know how to construct an URL for something which exists only in memory
  // override def getResource(name: String): URL = findAbstractFile(name) match {
  //   case null   => super.getResource(name)
  //   case file   => new URL(...)
  // }
}
