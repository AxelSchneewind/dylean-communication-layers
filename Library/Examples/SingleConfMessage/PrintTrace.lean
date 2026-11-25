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


public
def print_trace (selection: Option Nat) : IO Bool := do
  let stderr ← IO.getStderr;
  match selection with
    | some 0 => do_print DY.Example.SingleConfMessage.honestProtocolRun DY.Example.SingleConfMessage.traceToStr
    | some 1 => do_print DY.Example.SingleConfMessage.compromisedProtocolRun DY.Example.SingleConfMessage.traceToStr
    | _ => stderr.putStrLn "no protocol run selected"; return false

end DY.Example.SingleConfMessage
