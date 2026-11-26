module

public import Library.Examples.SingleConfMessage.Specification
public import Library.Examples.SingleConfMessage.Instance
import all Library.Examples.SingleConfMessage.Specification
import all Library.Examples.SingleConfMessage.Instance

import all Library.Communication.Confidential
public import Library.Communication.Confidential

public import Library.Communication.Printing
import all Library.Communication.Printing

public import DyLibraries.Printing
import all DyLibraries.Printing


namespace DY.Example.SingleConfMessage

public section

#combine +toplevel into BytesPrinter from Random, Literal, Concat

def BytesPrinter : DY.Printing.PartialBytesPrinter BytesF := Bytes.PartialFunction.combine fun
  | 0 => Random.SubF.printing
  | 1 => Literal.SubF.printing
  | 2 => Concat.SubF.printing

def bytesToString (b : Bytes) : String := b.rec BytesPrinter

instance : DY.Printing.PayloadPrinter single_message_send_event where
  tag := "Event"
  render b e := s!"wants to send {b e.msg.payload}"
  principal e := e.sender

instance : DY.Printing.PayloadPrinter single_message_receive_event where
  tag := "Event"
  render b e := s!"received {b e.msg.payload}"
  principal e := e.receiver

instance : DY.Printing.PayloadPrinter single_message_send_state where
  tag := "State"
  render b e := s!"{e.sender} sent: {b e.msg.payload}"
  principal e := e.sender

instance : DY.Printing.PayloadPrinter single_message_receive_state where
  tag := "State"
  render b e := s!"{e.sender} sent: {b e.msg.payload}"
  principal e := e.sender

#combine +toplevel into
  entryPrinter
from
  Network,
  Communication.Confidential,
  Communication.Confidential.Compromise,
  Random,
  ProtocolEvent single_message_send_event,
  ProtocolEvent single_message_receive_event,
  PersistentLocalState.CompromisableState single_message_send_state,
  PersistentLocalState.CompromisableState single_message_receive_state

def Printers : DY.Printing.Printers :=
  let printers : DY.Printing.Printers := { bytesToString := bytesToString }
  { printers with messageToString := fun b => bytesToString b }

def traceToStr (tr : ExecTrace) : String := DY.Printing.traceToString entryPrinter Printers tr

end

#check DY.Example.SingleConfMessage.traceToStr
