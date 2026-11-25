module

import Library.Examples.SingleAuthMessage.Printing
import all Library.Examples.SingleAuthMessage.SanityChecks

public def main : IO UInt32 := do
  let (result, tr) := DY.Example.SingleAuthMessage.honestProtocolRun.run DY.Trace.empty
  let stdout ← IO.getStdout
  stdout.putStr (DY.Example.SingleAuthMessage.traceToStr tr.val)
  if result == some () then
    return 0
  else
    let stderr ← IO.getStderr
    stderr.putStrLn "honestProtocolRun failed; stdout contains the trace up to failure."
    return 1
