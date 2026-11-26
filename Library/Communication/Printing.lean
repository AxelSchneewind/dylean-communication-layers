module

public import DY.Trace

public import Library.Communication.Authenticated
public import Library.Communication.Confidential

public import DyLibraries.Printing
import all DyLibraries.Printing

public section

namespace DY.Communication.Authenticated
open _root_.Lean (toJson)

namespace Compromise
public
instance [BytesFunctor] : DY.Printing.PayloadPrinter ExecEntryT where
  tag := "Communication.Authenticated.Compromise"
  render _bytes _st := "communication was compromised"
  principal st := match st with
                  | ⟨ 0, {ev:={participant}} ⟩ => participant

public
def entryPrinter [BytesFunctor] [DY.Printing.PayloadPrinter ExecEntryT] : DY.Printing.EntryPrinter ExecEntryT :=
  fun p _i e => ⟨"Event", [("Principal", toJson (DY.Printing.PayloadPrinter.principal e)), ("Tag", toJson (DY.Printing.PayloadPrinter.tag (α := Compromise.ExecEntryT))), ("Content", toJson (DY.Printing.payloadToString p e))]⟩

end Compromise

public
instance [BytesFunctor] : DY.Printing.PayloadPrinter ExecEntryT where
  tag := "Communication.Authenticated"
  render bytes st := s!"{bytes st.payload} (authenticated from {st.sender})"
  principal st := st.sender

public
def entryPrinter [BytesFunctor] [DY.Printing.PayloadPrinter ExecEntryT] : DY.Printing.EntryPrinter ExecEntryT :=
  fun p _i e => ⟨"Message", [("Sender", toJson e.sender), ("Receiver", toJson e.receiver), ("Tag", toJson (DY.Printing.PayloadPrinter.tag (α := ExecEntryT))), ("Content", toJson (DY.Printing.payloadToString p e))]⟩

end DY.Communication.Authenticated






namespace DY.Communication.Confidential
open _root_.Lean (toJson)

namespace Compromise
public
instance [BytesFunctor] : DY.Printing.PayloadPrinter ExecEntryT where
  tag := "Communication.Confidential.Compromise"
  render _bytes _st := "communication was compromised"
  principal st := match st with
                  | ⟨ 0, {ev:={participant}} ⟩ => participant

public
def entryPrinter [BytesFunctor] [DY.Printing.PayloadPrinter ExecEntryT] : DY.Printing.EntryPrinter ExecEntryT :=
  fun p _i e => ⟨"Event", [("Principal", toJson (DY.Printing.PayloadPrinter.principal e)), ("Tag", toJson (DY.Printing.PayloadPrinter.tag (α := Compromise.ExecEntryT))), ("Content", toJson (DY.Printing.payloadToString p e))]⟩

end Compromise

public
instance [BytesFunctor] : DY.Printing.PayloadPrinter ExecEntryT where
  tag := "Communication.Confidential"
  render bytes st := s!"{bytes st.payload} (confidential for {st.receiver})"
  principal st := st.receiver

public
def entryPrinter [BytesFunctor] [DY.Printing.PayloadPrinter ExecEntryT] : DY.Printing.EntryPrinter ExecEntryT :=
  fun p _i e => ⟨"Message", [("Sender", toJson e.sender), ("Receiver", toJson e.receiver), ("Tag", toJson (DY.Printing.PayloadPrinter.tag (α := ExecEntryT))), ("Content", toJson (DY.Printing.payloadToString p e))]⟩

end DY.Communication.Confidential
