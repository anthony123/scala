import scala.tools.partest.ReplTest
import scala.tools.nsc.Settings

// see the commit message to understand what this stuff is about
// just a quick note:
// transformedType returns an erased version of the type
// as explained in the commit message, Type.erasure won't do for this test
// because it does some postprocessing to the result of transformedType
object Test extends ReplTest {

  override def transformSettings(s: Settings): Settings = {
    s.neo.value = "GenBCode"
    s
  }

  def code = """
:power
val s = transformedType(StringClass.toType).asInstanceOf[Type]
{ println(exitingPhase(currentRun.erasurePhase)(ConstantType(Constant(s)))) }
{ exitingPhase(currentRun.erasurePhase)(println(ConstantType(Constant(s)))) }
{ ConstantType(Constant(s)); println(exitingPhase(currentRun.erasurePhase)(ConstantType(Constant(s)))); }
{ ConstantType(Constant(s)); exitingPhase(currentRun.erasurePhase)(println(ConstantType(Constant(s)))); }
  """
}
