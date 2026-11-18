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
instance : Repr Bytes where
  reprPrec entry _ :=
    match entry.view? Random.Random with
    | some r => "Random(" ++ repr r.timestamp ++ ")"
    | _ => match entry.view? Literal.SubF with
          | some l => "Literal(" ++ (repr l.id) ++ ")"
          | _ => "unknown bytes type"


public
instance /-[Repr Communication.ExecEntryT]-/ : Repr ExecTrace.Entry where
  reprPrec entry _ := match entry with
    | ⟨ 0, s ⟩ => "network: " ++ (repr s.msg)
    -- how to used the (Repr ExecEntryT)-Instance from communication here?
    | ⟨ 1, e ⟩ => "communication (" ++ e.sender ++ " → " ++ e.receiver ++ "): " ++ (repr e.payload)
    | ⟨ 2, c ⟩ => match c with
        | ⟨ 0, {ev} ⟩ => repr ev
    | ⟨ 3, r ⟩ => "random: " ++ (repr r.length) ++ "B sampled"
    | ⟨ 4, {ev} ⟩ => "send event " ++ ev.sender ++ ": " ++ (repr ev.msg.payload)
    | ⟨ 5, {ev} ⟩ => "recv event " ++ ev.sender ++ "→" ++ ev.receiver ++ ": " ++ (repr ev.msg.payload)
    | ⟨ 6, st ⟩ => "state " ++
        match st with
        | ⟨ 0, ⟨ 0, {st} ⟩  ⟩ => st.participant ++ ": " ++ (repr st.state.msg.payload) ++ " from " ++ st.state.sender
        | ⟨ 1, ⟨ 0, ⟨ 0, {ev:={state}} ⟩  ⟩  ⟩ => "corrupted " ++ state.participant ++ ": " ++ (repr state.state.msg.payload) ++ " from " ++ state.state.sender

def reprHelper [Repr ExecTrace.Entry] : ExecTrace → Std.Format
  | tr  => (tr.toArray.map repr).foldl (fun x y => x ++ "\n" ++ y) ""

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
