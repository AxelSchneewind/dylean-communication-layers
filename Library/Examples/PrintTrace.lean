module

public import Library.Examples.SingleConfMessage.PrintTrace
public import Library.Examples.SingleAuthMessage.PrintTrace

public
def main (args : List String) : IO UInt32 := do
  let stderr ← IO.getStderr
  let selection : Option Nat := ((args[0]?).map (fun x => x.toNat?.getD 0)).getD (some 0)

  let status ←
    match selection with
    | some 0 => DY.Example.SingleAuthMessage.main args.tail
    | some 1 => DY.Example.SingleConfMessage.main args.tail
    | _ => stderr.putStrLn "no protocol run selected"; return 1
  return status
