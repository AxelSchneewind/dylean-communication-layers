module

import DY.Meta
public import Communication
public import SingleAuthMessage.Specification
import all SingleAuthMessage.Specification

namespace DY.Example.SingleAuthMessage

open DY.Comparse

-- Future work: the following section is boilerplate that could be meta-programmed
public section ProofTraceConfig

class HasProofTrace extends HasExecTrace where
  [traceProof: ProofTraceTypes]
  [traceProof0: ProofTraceTypes.Has Network.ProofEntryT]
  [traceProof1: ProofTraceTypes.Has Communication.ProofEntryT]
  [traceProof2: ProofTraceTypes.Has Random.ProofEntryT]
  [traceProof3: ProofTraceTypes.Has (ProtocolEvent.ProofEntryT single_message_event)]
  [traceProof4: ProofTraceTypes.Has (PersistentLocalState.CompromisableState.ProofEntryT single_message_state)]

attribute [reducible, scoped instance] HasProofTrace.traceProof
attribute [reducible, scoped instance] HasProofTrace.traceProof0
attribute [reducible, scoped instance] HasProofTrace.traceProof1
attribute [reducible, scoped instance] HasProofTrace.traceProof2
attribute [reducible, scoped instance] HasProofTrace.traceProof3
attribute [reducible, scoped instance] HasProofTrace.traceProof4

end ProofTraceConfig

public section BytesInvariants

variable [HasProofTrace]

def authenticatedLabel
  (_me _other: Participant)
  : Label := Label.pub

end BytesInvariants

-- Future work: the following section is boilerplate that could be meta-programmed
public section BytesInvariantsConfig

class HasBytesInvariants extends HasProofTrace where
  [bytesInv: BytesInvariants]
  [bytesInvProof: BytesInvariantsProofs]
  [bytesInv0: BytesInvariants.Has Random.invariants]
  [bytesInv1: BytesInvariants.Has Literal.invariants]
  [bytesInv2: BytesInvariants.Has Concat.invariants]

attribute [reducible, scoped instance] HasBytesInvariants.bytesInv
attribute [           scoped instance] HasBytesInvariants.bytesInvProof
attribute [           scoped instance] HasBytesInvariants.bytesInv0
attribute [           scoped instance] HasBytesInvariants.bytesInv1
attribute [           scoped instance] HasBytesInvariants.bytesInv2

end BytesInvariantsConfig

public section TraceInvariant

variable [HasBytesInvariants]

instance single_message_state.Invariant : PersistentLocalState.CompromisableLocalStateInv single_message_state where
    invariant me st tr :=
        let msg := st.message
        let sender := st.sender
        msg.payload.Invariant tr ∧
        msg.payload.Publishable tr ∧
        (msg.payload.label tr).canFlow (authenticatedLabel me sender) tr.erase ∧
        Comparse.IsWellFormed (Bytes.KnowableBy Label.pub) st tr ∧
        tr.erase.EventLogged (single_message_event.SenderSentMsg st.sender st.message)
    invariant_later := by grind
    invariant_implies_KnowableBy me st tr := by
      intro inv
      simp [single_message_state.IsWellFormed_eq]
      simp [single_message_state.IsWellFormed_eq] at inv
      grind [canFlowTrans]
      done

-- for monotonicity
theorem single_message_state_inv_imp_Invariant
  (tr : ProofTrace) (participant: Participant) (st: single_message_state)
  : PersistentLocalState.LocalStateInv.invariant participant st tr → st.message.payload.Invariant tr
:= by
  simp [PersistentLocalState.LocalStateInv.invariant]
  grind

grind_pattern [grind_later] single_message_state_inv_imp_Invariant => PersistentLocalState.LocalStateInv.invariant participant st tr



instance single_message_event.Invariant : ProtocolEvent.EventInv (single_message_event)
where
  invariant tr ev :=
    match ev with
    | .SenderSentMsg _sender msg => msg.payload.Invariant tr
        ∧ Bytes.KnowableBy (Label.pub) msg.payload tr
    | .ReceiverReceivedMsg sender _receiver msg => msg.payload.Invariant tr
        ∧ tr.erase.EventLogged (SenderSentMsg sender msg)

end TraceInvariant

-- Future work: the following section is boilerplate that could be meta-programmed
public section TraceInvariantConfig

class HasTraceInvariant extends HasBytesInvariants where
  [traceInv: TraceInvariant]
  [traceInv0: TraceInvariant.Has Network.ProofEntryT]
  [traceInv1: TraceInvariant.Has Communication.ProofEntryT]
  [traceInv2: TraceInvariant.Has Random.ProofEntryT]
  [traceInv3: TraceInvariant.Has (ProtocolEvent.ProofEntryT single_message_event)]
  [traceInv4: TraceInvariant.Has (PersistentLocalState.CompromisableState.ProofEntryT single_message_state)]
  [attBaseThm: BaseAttackerKnowledgeTheorem]
  [attThm: AttackerKnowledgeTheorem]

attribute [reducible, scoped instance] HasTraceInvariant.traceInv
attribute [           scoped instance] HasTraceInvariant.traceInv0
attribute [           scoped instance] HasTraceInvariant.traceInv1
attribute [           scoped instance] HasTraceInvariant.traceInv2
attribute [           scoped instance] HasTraceInvariant.traceInv3
attribute [           scoped instance] HasTraceInvariant.traceInv4
attribute [           scoped instance] HasTraceInvariant.attBaseThm
attribute [           scoped instance] HasTraceInvariant.attThm

end TraceInvariantConfig

public section Proofs

variable [HasTraceInvariant]

@[instance]
theorem prepare_message.spec (sender receiver: Participant)
  : HoareTriple
    (prepare_message sender receiver)
    (fun _ => True)
    (fun state_id tr => True) := by
      -- apply HoareTriple.mk
      unfold prepare_message
      step with ⟨ fun _ => Label.pub, Usage.nothing ⟩ -- have to pass ghost arguments to genRand here
      step_intro
      hoist
      step_intro
      step by
        simp only [ProtocolEvent.EventInv.invariant]
        grind
      step by
        simp only [PersistentLocalState.LocalStateInv.invariant]
        apply And.intro; sorry
        apply And.intro; sorry
        apply And.intro; sorry
        apply And.intro; sorry
        sorry
      trivial
      done

@[instance]
theorem send_message.spec (me other: Participant) (state_id: Nat)
  : HoareTriple
    (send_message me other state_id)
    (fun _ => True)
    (fun _ _ => True) := by
      -- apply HoareTriple.mk
      unfold send_message
      step
      split
      . step
        sorry
      . step
        trivial

@[instance]
theorem receive_message.spec (me other : Participant) (msg_id: Nat)
  : HoareTriple
    (receive_message me other msg_id)
    (fun _ => True)
    (fun h tr =>
      exists (b:Bytes), tr.erase.EventLoggedAt (single_message_event.ReceiverReceivedMsg other me ({ payload:=b } :single_message)) h
    ) := by
      apply HoareTriple.mk
      unfold receive_message
      sorry



@[instance]
theorem single_message_state.compromise.spec (stHandle: Nat)
  : HoareTriple (single_message_state.compromise stHandle) (fun _ => True) (fun _ _ => True)
:= by unfold single_message_state.compromise; step; grind

end Proofs

section ReachabilityImpliesInvariant

variable [HasTraceInvariant]

-- Future work: the following section is boilerplate that could be meta-programmed
section
public instance: ReachableImpliesInvariant prepare_message.reachability := .mk (fun (me, other) => prepare_message.spec me other)
public instance: ReachableImpliesInvariant send_message.reachability := .mk (fun (me, other, s_id) => send_message.spec me other s_id)
public instance: ReachableImpliesInvariant receive_message.reachability := .mk (fun (me, other, s_id) => receive_message.spec me other s_id)
public instance: ReachableImpliesInvariant single_message_state.compromise.reachability := .mk (fun (stHandle) => single_message_state.compromise.spec stHandle)
end

#combine into ReachabilityTheorem from
  Network,
  prepare_message,
  send_message,
  receive_message,
  single_message_state.compromise,

end ReachabilityImpliesInvariant

section LabelLemma

variable [HasTraceInvariant]

-- TODO: corruption lemmas

end LabelLemma

end DY.Example.SingleAuthMessage
