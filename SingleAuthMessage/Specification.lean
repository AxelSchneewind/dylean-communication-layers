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
inductive single_message_state where
  | SenderState (sender: Participant) (msg:single_message)
  | ReceiverState (sender: Participant) (msg:single_message)
deriving DecidableEq

inductive single_message_event where
  | SenderSentMsg (sender:Participant) (msg:single_message)
  | ReceiverReceivedMsg (sender receiver:Participant) (msg:single_message)
deriving DecidableEq

end Structures





public section Formats

variable [HasExecBytes]

public
instance single_message.ps : ParseableSerializeable single_message := .make <|
  .triviallyIsomorphic
  (.bytes)
  (fun payload => { payload:=payload })
  (fun {payload:=payload} => payload)

-- TODO: necessary for what?
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
  (.prod .bool (.prod .slowString single_message.ps.mf))
  (fun ⟨ tp, ⟨ peer, payload ⟩ ⟩  =>
    match tp with
    | true  => single_message_state.SenderState peer payload
    | false => single_message_state.ReceiverState peer payload)
  (fun
    | single_message_state.SenderState peer payload => ⟨ true, ⟨ peer, payload ⟩ ⟩
    | single_message_state.ReceiverState peer payload => ⟨ false, ⟨ peer, payload ⟩ ⟩)
  (by grind)
  (by grind)

-- TODO: necessary for what?
public
theorem single_message_state.IsWellFormed_eq
  (pre: Bytes → τ → Prop) [BytesCompatibleTracePred pre] (x: single_message_state) (tr: τ):
  IsWellFormed pre x tr =
    match x with
    | .SenderState _r msg => pre msg.payload tr
    | .ReceiverState _s msg => pre msg.payload tr
:= by
  split
  . simp [Comparse.IsWellFormed, Comparse.ParseableSerializeable.mf]
  . simp [Comparse.IsWellFormed, Comparse.ParseableSerializeable.mf]

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
  [traceExec2: ExecTraceTypes.Has Random.ExecEntryT]
  [traceExec3: ExecTraceTypes.Has (ProtocolEvent.ExecEntryT single_message_event)]
  [traceExec4: ExecTraceTypes.Has (PersistentLocalState.CompromisableState.ExecEntryT single_message_state)]
  [attBase: BaseAttackerKnowledge]

attribute [reducible, scoped instance] HasExecTrace.traceExec
attribute [reducible, scoped instance] HasExecTrace.traceExec0
attribute [reducible, scoped instance] HasExecTrace.traceExec1
attribute [reducible, scoped instance] HasExecTrace.traceExec2
attribute [reducible, scoped instance] HasExecTrace.traceExec3
attribute [reducible, scoped instance] HasExecTrace.traceExec4
attribute [reducible, scoped instance] HasExecTrace.attBase



end ExecTraceConfig

public section Specification

variable [HasExecTrace]

-- (*** Stateful code ***)
public
def prepare_message (sender receiver : Participant) : Traceful Nat := do
      let payload ← Random.genRand 32
      let msg : single_message := { payload }
      ProtocolEvent.logEvent (single_message_event.SenderSentMsg sender msg)
      let state_id ← PersistentLocalState.storeLocalState sender (single_message_state.SenderState receiver msg)
      return state_id

public
def send_message (sender receiver : Participant) (state_id:Nat) : Traceful (Option Nat) := do
  let st:single_message_state ← PersistentLocalState.getLocalState sender state_id
  match st with
    | single_message_state.SenderState r msg =>
        -- only send to the same participant that the message was prepared for
        guard (r = receiver)
        Communication.sendMessageAuthenticated sender msg.payload
    | _ => return none

public
def receive_message (me other : Participant) (msg_id : Nat) : Traceful (Option Nat) := do
  let msg_bytes ← Communication.receiveMessageAuthenticated other msg_id
  let msg : single_message := {payload:=msg_bytes}
  ProtocolEvent.logEvent (single_message_event.ReceiverReceivedMsg other me msg)
  let state_id ← PersistentLocalState.storeLocalState me (single_message_state.ReceiverState other msg)
  return some state_id


def single_message_state.compromise (stHandle: Nat): Traceful Nat := do
  PersistentLocalState.compromise single_message_state stHandle

end Specification

public section SecurityPredicates

variable [HasExecTrace]

def StateCompromised
  (me: Participant)
  (tr: ExecTrace)
  : Prop
:=
  (∃ recipient message, PersistentLocalState.LocalStateCompromised me (single_message_state.SenderState recipient message) tr) ∨
  (∃ sender message, PersistentLocalState.LocalStateCompromised me (single_message_state.ReceiverState sender message) tr)

theorem StateCompromised_le
  (me: Participant)
  (tr1 tr2: ExecTrace)
  : tr1 ≤ tr2 →
    StateCompromised me tr1 →
    StateCompromised me tr2
:= by
  simp only [StateCompromised]
  grind

grind_pattern StateCompromised_le => tr1 ≤ tr2, StateCompromised me tr1

end SecurityPredicates

public section Reachability

variable [HasExecTrace]

-- Future work: the following section is boilerplate that could be meta-programmed
@[expose] public section
def prepare_message.reachability: ReachabilityConfig := .make (fun (me, other) => prepare_message me other)
def send_message.reachability: ReachabilityConfig := .make (fun (me, other, state_handle) => send_message me other state_handle)
def receive_message.reachability: ReachabilityConfig := .make (fun (me, other, state_handle) => receive_message me other state_handle)
def single_message_state.compromise.reachability: ReachabilityConfig := .make (fun state_handle => single_message_state.compromise state_handle)
end

#combine into ReachabilityConfig from
  Network,
  prepare_message,
  send_message,
  receive_message,
  single_message_state.compromise,

end Reachability

end DY.Example.SingleAuthMessage
