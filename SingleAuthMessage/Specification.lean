module

public import DY.Trace
public import DY.Bytes
public import DY.EquationalTheory.Literal
public import DY.EquationalTheory.Concat
public import DY.Actions.Network
public import Communication
public import DY.Actions.Random
public import DY.Actions.ProtocolEvent
public import DY.Actions.PersistentLocalState
public import DY.Comparse

namespace DY.Example.SingleAuthMessage

open DY.Comparse


-- taken from Examples.ACME.Specification, TODO check if/what neccessary
-- Future work: the following section is boilerplate that could be meta-programmed
public section ExecBytesConfig

class HasExecBytes where
  [bytesFunc: BytesFunctor]
  [bytesFunc0: BytesFunctor.Has Random.SubF]
  [bytesFunc1: BytesFunctor.Has Literal.SubF]
  [bytesFunc2: BytesFunctor.Has Concat.SubF]
  [bytesLen: BytesLength]
  [bytesLen0: BytesLength.Has Random.SubF.length]
  [bytesLen1: BytesLength.Has Literal.SubF.length]
  [bytesLen2: BytesLength.Has Concat.SubF.length]
  [att: AttackerKnowledge]
  [att0: AttackerKnowledge.Has Random.attackerKnowledge]
  [att1: AttackerKnowledge.Has Literal.attackerKnowledge]
  [att2: AttackerKnowledge.Has Concat.attackerKnowledge]

attribute [reducible, scoped instance] HasExecBytes.bytesFunc
attribute [reducible, scoped instance] HasExecBytes.bytesFunc0
attribute [reducible, scoped instance] HasExecBytes.bytesFunc1
attribute [reducible, scoped instance] HasExecBytes.bytesFunc2
attribute [reducible, scoped instance] HasExecBytes.bytesLen
attribute [           scoped instance] HasExecBytes.bytesLen0
attribute [           scoped instance] HasExecBytes.bytesLen1
attribute [           scoped instance] HasExecBytes.bytesLen2
attribute [reducible, scoped instance] HasExecBytes.att
attribute [           scoped instance] HasExecBytes.att0
attribute [           scoped instance] HasExecBytes.att1
attribute [           scoped instance] HasExecBytes.att2

end ExecBytesConfig

public section Structures

variable [HasExecBytes]


public
structure single_message [BytesFunctor] where
  payload:Bytes
deriving DecidableEq

public
structure single_message_state where
  sender : Participant
  msg : single_message
deriving DecidableEq

public
structure single_message_send_event where
  sender : Participant
  msg : single_message
deriving DecidableEq

public
structure single_message_receive_event where
  sender : Participant
  receiver : Participant
  msg : single_message
deriving DecidableEq

end Structures





public section Formats

variable [HasExecBytes]

public
instance single_message.ps : ParseableSerializeable single_message := .make <|
  .triviallyIsomorphic
  (.bytes)
  (fun payload => { payload:=payload })
  (fun { payload:=payload } => payload)

public
theorem single_message.IsWellFormed_eq
  (pre: Bytes → τ → Prop) [BytesCompatibleTracePred pre] (x: single_message) (tr: τ):
  IsWellFormed pre x tr = pre x.payload tr
:= by
  simp [Comparse.IsWellFormed, Comparse.ParseableSerializeable.mf]

grind_pattern single_message.IsWellFormed_eq => IsWellFormed pre x tr
grind_pattern [grind_later] single_message.IsWellFormed_eq => IsWellFormed pre x tr


public
instance single_message_state.ps : ParseableSerializeable single_message_state := .make <|
  .triviallyIsomorphic
  (.prod .slowString /-.unboundedString (probably in next release) -/ single_message.ps.mf)
  (fun ⟨ sender, msg ⟩ => {sender, msg} )
  (fun { sender, msg } => ⟨sender, msg⟩ )
  (by grind)
  (by grind)

public
theorem single_message_state.IsWellFormed_eq
  (pre: Bytes → τ → Prop) [BytesCompatibleTracePred pre] (x: single_message_state) (tr: τ):
  Comparse.IsWellFormed pre x tr =
    pre x.msg.payload tr
:= by
  simp [Comparse.IsWellFormed, Comparse.ParseableSerializeable.mf]

grind_pattern single_message_state.IsWellFormed_eq => IsWellFormed pre x tr
grind_pattern [grind_later] single_message_state.IsWellFormed_eq => IsWellFormed pre x tr

end Formats

-- taken from Examples.ACME.Specification, TODO check
-- Future work: the following section is boilerplate that could be meta-programmed
public section ExecTraceConfig

public
class HasExecTrace extends HasExecBytes where
  [traceExec: ExecTraceTypes]
  [traceExec0: ExecTraceTypes.Has Network.ExecEntryT]
  [traceExec1: ExecTraceTypes.Has Communication.ExecEntryT]
  [traceExec2: ExecTraceTypes.Has Communication.Compromise.ExecEntryT]
  [traceExec3: ExecTraceTypes.Has Random.ExecEntryT]
  [traceExec4: ExecTraceTypes.Has (ProtocolEvent.ExecEntryT single_message_send_event)]
  [traceExec5: ExecTraceTypes.Has (ProtocolEvent.ExecEntryT single_message_receive_event)]
  [traceExec6: ExecTraceTypes.Has (PersistentLocalState.CompromisableState.ExecEntryT single_message_state)]
  [attBase: BaseAttackerKnowledge]

attribute [reducible, scoped instance] HasExecTrace.traceExec
attribute [reducible, scoped instance] HasExecTrace.traceExec0
attribute [reducible, scoped instance] HasExecTrace.traceExec1
attribute [reducible, scoped instance] HasExecTrace.traceExec2
attribute [reducible, scoped instance] HasExecTrace.traceExec3
attribute [reducible, scoped instance] HasExecTrace.traceExec4
attribute [reducible, scoped instance] HasExecTrace.traceExec5
attribute [reducible, scoped instance] HasExecTrace.traceExec6
attribute [reducible, scoped instance] HasExecTrace.attBase

end ExecTraceConfig

public section Specification

variable [HasExecTrace]

public
def prepare_message (sender _receiver : Participant) : Traceful Nat := do
  let payload ← Random.genRand 32
  let msg : single_message := { payload }
  ProtocolEvent.logEvent ({ sender, msg } : single_message_send_event)
  let state_id ← PersistentLocalState.storeLocalState sender ({sender, msg} : single_message_state)
  return state_id

public
def send_message (sender receiver : Participant) (state_id:Nat) : Traceful Nat := do
  let st:single_message_state ← PersistentLocalState.getLocalState sender state_id
  guard (st.sender = sender)
  Communication.sendAuthenticated sender receiver st.msg.payload

public
def receive_message (sender receiver : Participant) (msg_id : Nat) : Traceful Nat := do
  let msg_bytes ← Communication.receiveAuthenticated sender msg_id
  let msg : single_message := {payload:=msg_bytes}
  ProtocolEvent.logEvent ({sender, receiver, msg} : single_message_receive_event )
  let state_id ← PersistentLocalState.storeLocalState receiver ({sender, msg} : single_message_state)
  return state_id

end Specification

public section SecurityPredicates

variable [HasExecTrace]

end SecurityPredicates

public section Reachability

variable [HasExecTrace]

-- Future work: the following section is boilerplate that could be meta-programmed
@[expose] public section
def prepare_message.reachability: ReachabilityConfig := .make (fun (sender, receiver) => prepare_message sender receiver)
def send_message.reachability: ReachabilityConfig := .make (fun (sender, receiver, state_handle) => send_message sender receiver state_handle)
def receive_message.reachability: ReachabilityConfig := .make (fun (sender, receiver, state_handle) => receive_message sender receiver state_handle)
end

#combine into ReachabilityConfig from
  Network,
  Communication,
  prepare_message,
  send_message,
  receive_message,

end Reachability

end DY.Example.SingleAuthMessage
