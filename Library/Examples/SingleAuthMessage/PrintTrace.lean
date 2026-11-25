module

import all Library.Examples.SingleAuthMessage.Printing
public import Library.Examples.SingleAuthMessage.Printing

import all Library.Examples.SingleAuthMessage.SanityChecks

open DY

namespace DY.Example.SingleAuthMessage

def do_print [ExecTraceTypes]
  {α : Type} (run : Traceful α) (toString : ExecTrace → String) : IO Bool := do
  let stdout ← IO.getStdout
  let (result, tr) := run.run DY.Trace.empty
  stdout.putStr (toString tr.val)
  return result.isSome

public def print_trace (args : List String) : IO UInt32 := do
  let stderr ← IO.getStderr
  let selection : Option Nat := ((args[0]?).map (fun x => x.toNat?.getD 0)).getD (some 0)

  let status : Bool ←
    match selection with
    | some 0 => DY.Example.SingleAuthMessage.do_print DY.Example.SingleAuthMessage.honestProtocolRun DY.Example.SingleAuthMessage.traceToStr
    | some 1 => DY.Example.SingleAuthMessage.do_print DY.Example.SingleAuthMessage.compromisedProtocolRun DY.Example.SingleAuthMessage.traceToStr
    | _ => stderr.putStrLn "no protocol run selected"; return 1
  if status then
    return 0
  else
    stderr.putStrLn "protocol run failed; stdout contains the trace up to failure."
    return 1

public def main := print_trace

end DY.Example.SingleAuthMessage
