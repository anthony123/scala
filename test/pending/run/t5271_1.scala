import scala.reflect.mirror._

object Test extends App {
  reify {
    case class C(foo: Int, bar: Int)
  }.eval
}
