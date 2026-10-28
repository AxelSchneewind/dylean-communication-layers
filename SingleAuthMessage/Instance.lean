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
  Random,
  ProtocolEvent single_message_event,
  PersistentLocalState.CompromisableState single_message_state,

instance: HasExecTrace where

#combine +toplevel into
  ProofEntryT,
from
  Network,
  Communication,
  Random,
  ProtocolEvent single_message_event,
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
  Random,
  ProtocolEvent single_message_event,
  PersistentLocalState.CompromisableState single_message_state,

#combine +toplevel into SubAttackerKnowledgeTheorem from
  Random,
  Literal,
  Concat,

instance: HasTraceInvariant where

end

end DY.Example.SingleAuthMessage
