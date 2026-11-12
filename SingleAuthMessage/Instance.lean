module

public import SingleAuthMessage.Specification
public import SingleAuthMessage.Proof

namespace DY.Example.SingleAuthMessage

-- Future work: the following section could avoid a lot of repetition
public section

#combine +toplevel into BytesFunctor, BytesLength, attackerKnowledge from
  Random,
  Literal,
  Concat,

instance: HasExecBytes where

#combine +toplevel into
  ExecEntryT,
  baseAttackerKnowledge,
from
  Network,
  Communication,
  Communication.Compromise,
  Random,
  ProtocolEvent single_message_send_event,
  ProtocolEvent single_message_receive_event,
  PersistentLocalState.CompromisableState single_message_state

instance: HasExecTrace where

public
instance : Repr ExecTrace.Entry where
  reprPrec entry _ := match entry with
    | ⟨ 0, s ⟩ => "network: " ++ (repr s.msg.length) ++ "B"
    | ⟨ 1, e ⟩ => "communication: " ++ e.sender ++ " → " ++ e.receiver ++ ", " ++ (repr e.payload.length) ++ "B"
    | ⟨ 2, c ⟩ => "compromise: " ++ match c with
        | ⟨ 0, {ev} ⟩ => ev.participant
    | ⟨ 3, r ⟩ => "random: " ++ (repr r.length) ++ "B"
    | ⟨ 4, {ev} ⟩ => "send event: " ++ ev.sender ++ ": " ++ (repr ev.msg.payload.length)
    | ⟨ 5, {ev} ⟩ => "recv event: " ++ ev.sender ++ ": " ++ (repr ev.msg.payload.length)
    | ⟨ 6, st ⟩ => "state " ++
        match st with
        | ⟨ 0, ⟨ 0, {st} ⟩  ⟩ => st.participant ++ ": " ++ (repr st.state.msg.payload.length) ++ "B from " ++ st.state.sender
        | ⟨ 1, ⟨ 0, ⟨ 0, {ev:={state}} ⟩  ⟩  ⟩ => "corrupted " ++ state.participant ++ ": " ++ (repr state.state.msg.payload.length) ++ "B from " ++ state.state.sender

def reprHelper [Repr ExecTrace.Entry] : ExecTrace → Std.Format
  | .nil => ""
  | .snoc trBefore entry => (reprHelper trBefore) ++ "\n" ++ (repr entry)

public
instance [Repr ExecTrace.Entry] : Repr ExecTrace where
  reprPrec trace _ := reprHelper trace

class HasRepr extends HasExecTrace where
  [entry : Repr ExecTrace.Entry]
  [trace : Repr ExecTrace]

attribute [reducible, scoped instance] HasRepr.entry
attribute [reducible, scoped instance] HasRepr.trace

instance : HasRepr where

#combine +toplevel into
  ProofEntryT,
from
  Network,
  Communication,
  Communication.Compromise,
  Random,
  ProtocolEvent single_message_send_event,
  ProtocolEvent single_message_receive_event,
  PersistentLocalState.CompromisableState single_message_state,

instance: HasProofTrace where

#combine +toplevel into BytesInvariants, BytesInvariantsProofs from
  Random,
  Literal,
  Concat,

instance: HasBytesInvariants where

#combine +toplevel into
  SubTraceInvariant,
  SubBaseAttackerKnowledgeTheorem,
from
  Network,
  Communication,
  Communication.Compromise,
  Random,
  ProtocolEvent single_message_send_event,
  ProtocolEvent single_message_receive_event,
  PersistentLocalState.CompromisableState single_message_state,

#combine +toplevel into SubAttackerKnowledgeTheorem from
  Random,
  Literal,
  Concat,

instance: HasTraceInvariant where

end

end DY.Example.SingleAuthMessage
