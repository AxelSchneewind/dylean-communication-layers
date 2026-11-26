module

import all Library.Examples.SingleConfMessage.Printing
public import Library.Examples.SingleConfMessage.Printing

import all Library.Examples.SingleConfMessage.SanityChecks

open DY

namespace DY.Example.SingleConfMessage

def do_print [ExecTraceTypes]
  {α : Type} (run : Traceful α) (toString : ExecTrace → String) : IO Bool := do
  let stdout ← IO.getStdout
  let (result, tr) := run.run DY.Trace.empty
  stdout.putStr (toString tr.val)
  return result.isSome


public def print_trace (args : List String) : IO UInt32 := do
  let stderr ← IO.getStderr
  let selection : Option Nat := ((args[0]?).map (fun x => x.toNat?.getD 0)).getD (some 0)

  let status : Bool ← match selection with
    | some 0 => DY.Example.SingleConfMessage.do_print DY.Example.SingleConfMessage.honestProtocolRun DY.Example.SingleConfMessage.traceToStr
    | some 1 => DY.Example.SingleConfMessage.do_print DY.Example.SingleConfMessage.compromisedProtocolRun DY.Example.SingleConfMessage.traceToStr
    | _ => stderr.putStrLn "no scenario selected"; return 1
  if status then
    return 0
  else
    stderr.putStrLn "protocol run failed; stdout contains the trace up to failure."
    return 1

public def main := print_trace

end DY.Example.SingleConfMessage
