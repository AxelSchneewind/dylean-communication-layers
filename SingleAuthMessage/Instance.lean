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
    | ⟨ 0, s ⟩ => "network: " ++ (repr s.msg.length)
    | ⟨ 1, e ⟩ => "communication: " ++ e.sender ++ " → " ++ e.receiver ++ ", " ++ (repr e.payload.length) ++ "B"
    | ⟨ 2, c ⟩ => "compromise: " ++ match c with
        | ⟨ 0, ev ⟩ => ev.ev.participant
    | ⟨ 3, r ⟩ => "random: " ++ (repr r.length) ++ "B"
    | ⟨ 4, se ⟩ => "send event: " ++ se.ev.sender ++ ": " ++ (repr se.ev.msg.payload.length)
    | ⟨ 5, re ⟩ => "recv event: " ++ re.ev.sender ++ ": " ++ (repr re.ev.msg.payload.length)
    | ⟨ 6, st ⟩ => "state "

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
