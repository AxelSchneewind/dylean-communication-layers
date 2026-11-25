module

public import Library.Examples.SingleConfMessage.PrintTrace
public import Library.Examples.SingleAuthMessage.PrintTrace

open DY

public def main (args : List String) : IO UInt32 := do
  let stderr ← IO.getStderr
  let selection : Option Nat := ((args[0]?).map (fun x => x.toNat?.getD 0))
  let sub_selection : Option Nat := ((args[1]?).map (fun x => x.toNat?.getD 0))

  let status : Bool ←
    match selection with
    | some 0 => DY.Example.SingleAuthMessage.print_trace sub_selection
    | some 1 => DY.Example.SingleConfMessage.print_trace sub_selection
    | _ => stderr.putStrLn "no protocol run selected"; return 1
  if status then
    return 0
  else
    stderr.putStrLn "protocol run failed; stdout contains the trace up to failure."
    return 1
