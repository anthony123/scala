package scala.runtime
import java.io.{OutputStream, PrintStream}
import scala.runtime.ScalaRunTime.stringOf

/** A utility object that's needed by the code that executes a worksheet.
 */
object WorksheetSupport {

  /** The offset in the source which should be printed */
  private var currentOffset = 0

  /** A stream that flushes in regular intervals so that output can be captured
   *  in real time. The flush interval is determined by the field "flushInterval".
   *  By default it is 30ms.
   */
  private class FlushedOutputStream(out: OutputStream) extends OutputStream {
    private var lastFlush: Long = 0L
    protected val flushInterval = 30000000L // 30ms
    private var lastCh: Int = '\n'
    override def write(b: Array[Byte], off: Int, len: Int) = {
      for (idx <- off until (off + len min b.length)) writeOne(b(idx))
      flush()
    }
    override def write(c: Int) {
      writeOne(c)
      flush()
    }
    override def flush() {
      val current = System.nanoTime
      if (current - lastFlush >= flushInterval) {
        out.flush()
        lastFlush = current
      }
    }
    def writeOne(c: Int) {
      if (lastCh == '\n') {
        lastCh = 0
        write((currentOffset+" ").getBytes)
      }
      out.write(c)
      lastCh = c
    }
    def ensureNewLine() = if (lastCh != '\n') writeOne('\n')
  }

  private val flushedOut = new FlushedOutputStream(System.out)
  private val printOut = new PrintStream(flushedOut)

  private def redirected(op: => Unit) = {
    val oldSysOut = System.out
    val oldSysErr = System.err
    val oldConsOut = Console.out
    val oldConsErr = Console.err
    System.setOut(printOut)
    System.setErr(printOut)
    Console.setOut(printOut)
    Console.setErr(printOut)
    try op
    finally {
      printOut.close()
      System.setOut(oldSysOut)
      System.setErr(oldSysErr)
      Console.setOut(oldConsOut)
      Console.setErr(oldConsErr)
    }
  }

  def $execute(op: => Unit) = redirected {
    try op
    catch {
      case ex: StopException => ;
      case ex => ex.printStackTrace()
    }
  }

  def $skip(n: Int) = {
    flushedOut.ensureNewLine()
    currentOffset += n
  }

  def $stop() = throw new StopException

  def $show(x: Any): String = stringOf(x, scala.Int.MaxValue)
}

class StopException extends Exception

