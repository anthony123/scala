/* NSC -- new Scala compiler
 * Copyright 2005-2011 LAMP/EPFL
 * @author  Stephane Micheloud
 */


package scala.tools.nsc
package backend.jvm

import ch.epfl.lamp.fjbg._
import symtab.Flags

trait GenAndroid { // TODO keep members as sibling to genClass() (better: a trait holding them inherited by JPlainBuilder)
  self: GenJVM =>

  import global._
  import icodes._
  import opcodes._

  /** From the reference documentation of the Android SDK:
   *  The `Parcelable` interface identifies classes whose instances can be
   *  written to and restored from a `Parcel`. Classes implementing the
   *  `Parcelable` interface must also have a static field called `CREATOR`,
   *  which is an object implementing the `Parcelable.Creator` interface.
   */
  private val androidFieldName = newTermName("CREATOR")

  private lazy val AndroidParcelableInterface = definitions.getClassIfDefined("android.os.Parcelable")
  private lazy val AndroidCreatorClass        = definitions.getClassIfDefined("android.os.Parcelable$Creator")

  def isAndroidParcelableClass(sym: Symbol) =
    (AndroidParcelableInterface != NoSymbol) &&
    (sym.parentSymbols contains AndroidParcelableInterface)

  /* used only from BytecodeGenerator.genClass(), via addStaticInit() */
  def addCreatorCode(codegen: BytecodeGenerator, block: BasicBlock) {
    import codegen._
    val fieldSymbol = (
      clasz.symbol.newValue(newTermName(androidFieldName), NoPosition, Flags.STATIC | Flags.FINAL)
        setInfo AndroidCreatorClass.tpe
    )
    val methodSymbol = definitions.getMember(clasz.symbol.companionModule, androidFieldName)
    clasz addField new IField(fieldSymbol)
    block emit CALL_METHOD(methodSymbol, Static(false))
    block emit STORE_FIELD(fieldSymbol, true)
  }

  /* used only from BytecodeGenerator.genClass(), via legacyStaticInitializer() and addStaticInit() */
  def legacyAddCreatorCode(codegen: BytecodeGenerator, clinit: JExtendedCode) {
    import codegen._
    val creatorType = javaType(AndroidCreatorClass)
    jclass.addNewField(PublicStaticFinal,
                       androidFieldName,
                       creatorType)
    val moduleName = javaName(clasz.symbol)+"$"
    clinit.emitGETSTATIC(moduleName,
                         nme.MODULE_INSTANCE_FIELD.toString,
                         new JObjectType(moduleName))
    clinit.emitINVOKEVIRTUAL(moduleName, androidFieldName,
                             new JMethodType(creatorType, Array()))
    clinit.emitPUTSTATIC(jclass.getName(), androidFieldName, creatorType)
  }

}
