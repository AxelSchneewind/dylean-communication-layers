module

import DY.Meta
public import Library.Communication
public import Library.Examples.SingleConfMessage.Specification
import all Library.Examples.SingleConfMessage.Specification

namespace DY.Example.SingleConfMessage

open DY.Comparse

-- Future work: the following section is boilerplate that could be meta-programmed
public section ProofTraceConfig

class HasProofTrace extends HasExecTrace where
  [traceProof: ProofTraceTypes]
  [traceProof0: ProofTraceTypes.Has Network.ProofEntryT]
  [traceProof1: ProofTraceTypes.Has Communication.Confidential.ProofEntryT]
  [traceProof2: ProofTraceTypes.Has Communication.Confidential.Compromise.ProofEntryT]
  [traceProof3: ProofTraceTypes.Has Random.ProofEntryT]
  [traceProof4: ProofTraceTypes.Has (ProtocolEvent.ProofEntryT single_message_send_event)]
  [traceProof5: ProofTraceTypes.Has (ProtocolEvent.ProofEntryT single_message_receive_event)]
  [traceProof6: ProofTraceTypes.Has (PersistentLocalState.CompromisableState.ProofEntryT single_message_send_state)]
  [traceProof7: ProofTraceTypes.Has (PersistentLocalState.CompromisableState.ProofEntryT single_message_receive_state)]

attribute [reducible, scoped instance] HasProofTrace.traceProof
attribute [reducible, scoped instance] HasProofTrace.traceProof0
attribute [reducible, scoped instance] HasProofTrace.traceProof1
attribute [reducible, scoped instance] HasProofTrace.traceProof2
attribute [reducible, scoped instance] HasProofTrace.traceProof3
attribute [reducible, scoped instance] HasProofTrace.traceProof4
attribute [reducible, scoped instance] HasProofTrace.traceProof5
attribute [reducible, scoped instance] HasProofTrace.traceProof6
attribute [reducible, scoped instance] HasProofTrace.traceProof7

end ProofTraceConfig

public section BytesInvariants

variable [HasProofTrace]

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


section Labels

public
abbrev single_message_send_state_label
  [ExecTraceTypes]
  [ExecTraceTypes.Has (PersistentLocalState.Compromise.ExecEntryT single_message_send_state)]
  (sender receiver : Participant) (msg : single_message) : Label := PersistentLocalState.label sender ({sender, receiver, msg}: single_message_send_state)

public
abbrev single_message_receive_state_label
  [ExecTraceTypes]
  [ExecTraceTypes.Has (PersistentLocalState.Compromise.ExecEntryT single_message_receive_state)]
  (sender receiver : Participant) (msg : single_message) : Label := PersistentLocalState.label receiver ({sender, receiver, msg}: single_message_receive_state)

variable
  [ExecTraceTypes]
  [ExecTraceTypes.Has Communication.Confidential.Compromise.ExecEntryT]
  [ExecTraceTypes.Has (PersistentLocalState.Compromise.ExecEntryT single_message_send_state)]
  [ExecTraceTypes.Has (PersistentLocalState.Compromise.ExecEntryT single_message_receive_state)]

public
def single_message_state_label
  (msg : single_message) : Label := {
  isCorrupt tr :=
    ∃ (sender receiver : Participant),
    (single_message_send_state_label sender receiver msg).isCorrupt tr ∨
    (single_message_receive_state_label sender receiver msg).isCorrupt tr
  isCorruptLater tr1 tr2 := by
    grind
}

public
def single_message_label
  (_sender receiver : Participant) (msg : single_message) : Label :=
      (Communication.Confidential.CommunicationLabel receiver).join (single_message_state_label msg)

public
theorem single_message_label_canflow_PersistentLocalState_label_sender
  (sender receiver : Participant) (msg : single_message) (tr : ExecTrace)
  : (single_message_label sender receiver msg).canFlow (PersistentLocalState.label sender ({sender, receiver, msg}:single_message_send_state)) tr
  := by
    simp[Label.canFlow, single_message_label, single_message_state_label]
    grind[single_message_send_state, single_message_receive_state]

public
theorem single_message_label_canflow_PersistentLocalState_label_receiver
  (sender receiver : Participant) (msg : single_message) (tr : ExecTrace)
  : ∀ (sender':Participant), (single_message_label sender receiver msg).canFlow (PersistentLocalState.label receiver ({sender:=sender', receiver, msg}:single_message_receive_state)) tr
  := by
    simp[Label.canFlow, single_message_label, single_message_state_label]
    grind[single_message_send_state, single_message_receive_state]

public
theorem single_message_label_canflow_PersistentLocalState_label
  (sender receiver : Participant) (msg : single_message) (tr : ExecTrace)
  : (single_message_label sender receiver msg).canFlow (PersistentLocalState.label sender ({sender, receiver, msg}:single_message_send_state)) tr
    ∧
    ∀ (sender':Participant), (single_message_label sender receiver msg).canFlow (PersistentLocalState.label receiver ({sender:=sender', receiver, msg}:single_message_receive_state)) tr
  := by
    grind[single_message_label_canflow_PersistentLocalState_label_sender, single_message_label_canflow_PersistentLocalState_label_receiver]

end Labels

-- an upper bound on the message label
instance
  : Communication.Confidential.CommunicationInvariants where
  confidential tr sender receiver bytes :=
      bytes.Invariant tr ∧ bytes.WellFormed tr ∧
      ∃ sender', (bytes.label tr).canFlow (single_message_label sender' receiver {payload:=bytes}) tr.erase
  confidential_later := by
    intro tr1 tr2 sender receiver payload h_le
    intro h
    have : Bytes.WellFormed payload tr1 := by grind
    grind[Bytes.label_later, Label.canFlowLater]


-- State Invariants
instance single_message_send_state.Invariant : PersistentLocalState.CompromisableLocalStateInv single_message_send_state where
    invariant me st tr :=
        let msg := st.msg
        let sender := st.sender
        let receiver := st.receiver
        me = sender ∧
        (
          IsWellFormed (Bytes.KnowableBy (single_message_label sender receiver msg)) st tr ∧
          (single_message_label sender receiver msg) = (msg.payload.label tr)
        )
    invariant_later := by
      grind[Bytes.Publishable_later_fast, Trace.EventLogged_le, Communication.Confidential.participantCompromised_le]
    invariant_implies_KnowableBy me st tr := by
      intro inv
      simp [single_message_send_state.IsWellFormed_eq]
      simp [single_message_send_state.IsWellFormed_eq] at inv
      simp [Bytes.KnowableBy]
      simp [Bytes.KnowableBy] at inv
      obtain ⟨ h_eq, inv ⟩ := inv
      refine ⟨ ?_, ?_ ⟩
      . grind
      . have : (single_message_label st.sender st.receiver st.msg).canFlow (PersistentLocalState.label me st) tr.erase := by
          grind[single_message_send_state, single_message_label_canflow_PersistentLocalState_label]
        grind[single_message_label_canflow_PersistentLocalState_label, canFlowTrans]
      done

instance single_message_receive_state.Invariant : PersistentLocalState.CompromisableLocalStateInv single_message_receive_state where
    invariant me st tr :=
        let msg := st.msg
        let sender := st.sender
        let receiver := st.receiver
        me = receiver ∧
        (msg.payload.Publishable tr ∨
        ∃ sender', IsWellFormed (Bytes.KnowableBy (single_message_label sender' receiver msg)) st tr)
    invariant_later := by
      grind[Bytes.Publishable_later_fast, Trace.EventLogged_le, Communication.Confidential.participantCompromised_le]
    invariant_implies_KnowableBy me st tr := by
      intro inv
      simp [single_message_receive_state.IsWellFormed_eq]
      simp [single_message_receive_state.IsWellFormed_eq] at inv
      -- simp [Bytes.KnowableBy]
      -- simp [Bytes.KnowableBy] at inv
      obtain ⟨ h_eq, inv ⟩ := inv
      refine ⟨ ?_, ?_ ⟩
      . grind
      . rcases inv with pub | inv
        . grind[canFlowTrans]
        obtain ⟨ sender', inv ⟩ := inv
        have := single_message_label_canflow_PersistentLocalState_label_receiver sender' st.receiver st.msg tr.erase st.sender
        grind[single_message_receive_state, canFlowTrans]
      done


-- Event Invariants
instance single_message_send_event.Invariant : ProtocolEvent.EventInv (single_message_send_event)
where
  invariant tr ev := ev.msg.payload.Invariant tr ∧
    ∃ sender', (ev.msg.payload.label tr) = (single_message_label sender' ev.receiver ev.msg)


-- we don't know where the message came from
instance single_message_receive_event.Invariant : ProtocolEvent.EventInv (single_message_receive_event)
where
  invariant tr ev :=
    ev.msg.payload.Publishable tr ∨ (
      ev.msg.payload.Invariant tr ∧
      ∃ sender', (ev.msg.payload.label tr).canFlow (single_message_label sender' ev.receiver ev.msg) tr.erase
    )


-- monotonicity
theorem single_message_send_state_inv_imp_Invariant
  (tr : ProofTrace) (participant: Participant) (st: single_message_send_state)
  : PersistentLocalState.LocalStateInv.invariant participant st tr → st.msg.payload.Invariant tr
:= by
  simp [PersistentLocalState.LocalStateInv.invariant]
  grind

grind_pattern [grind_later] single_message_send_state_inv_imp_Invariant => PersistentLocalState.LocalStateInv.invariant participant st tr

theorem single_message_send_event_inv_imp_Invariant
  (tr : ProofTrace) (st: single_message_send_event)
  : ProtocolEvent.EventInv.invariant tr st → st.msg.payload.Invariant tr
:= by
  simp [ProtocolEvent.EventInv.invariant]
  grind

grind_pattern [grind_later] single_message_send_event_inv_imp_Invariant => ProtocolEvent.EventInv.invariant tr st

theorem single_message_receive_event_inv_imp_Invariant
  (tr : ProofTrace) (st: single_message_receive_event)
  : ProtocolEvent.EventInv.invariant tr st → st.msg.payload.Invariant tr
:= by
  simp [ProtocolEvent.EventInv.invariant]
  grind

grind_pattern [grind_later] single_message_receive_event_inv_imp_Invariant => ProtocolEvent.EventInv.invariant tr st

end TraceInvariant

-- Future work: the following section is boilerplate that could be meta-programmed
public section TraceInvariantConfig

class HasTraceInvariant extends HasBytesInvariants where
  [traceInv: TraceInvariant]
  [traceInv0: TraceInvariant.Has Network.ProofEntryT]
  [traceInv1: TraceInvariant.Has Communication.Confidential.ProofEntryT]
  [traceInv2: TraceInvariant.Has Communication.Confidential.Compromise.ProofEntryT]
  [traceInv3: TraceInvariant.Has Random.ProofEntryT]
  [traceInv4: TraceInvariant.Has (ProtocolEvent.ProofEntryT single_message_send_event)]
  [traceInv5: TraceInvariant.Has (ProtocolEvent.ProofEntryT single_message_receive_event)]
  [traceInv6: TraceInvariant.Has (PersistentLocalState.CompromisableState.ProofEntryT single_message_send_state)]
  [traceInv7: TraceInvariant.Has (PersistentLocalState.CompromisableState.ProofEntryT single_message_receive_state)]
  [attBaseThm: BaseAttackerKnowledgeTheorem]
  [attThm: AttackerKnowledgeTheorem]

attribute [reducible, scoped instance] HasTraceInvariant.traceInv
attribute [           scoped instance] HasTraceInvariant.traceInv0
attribute [           scoped instance] HasTraceInvariant.traceInv1
attribute [           scoped instance] HasTraceInvariant.traceInv2
attribute [           scoped instance] HasTraceInvariant.traceInv3
attribute [           scoped instance] HasTraceInvariant.traceInv4
attribute [           scoped instance] HasTraceInvariant.traceInv5
attribute [           scoped instance] HasTraceInvariant.traceInv6
attribute [           scoped instance] HasTraceInvariant.traceInv7
attribute [           scoped instance] HasTraceInvariant.attBaseThm
attribute [           scoped instance] HasTraceInvariant.attThm

end TraceInvariantConfig

public section Proofs

variable [HasTraceInvariant]

@[instance]
theorem prepare_message.proof (sender receiver : Participant)
  : HoareTriple
    (prepare_message sender receiver)
    (fun _ => True)
    (fun _state_id _tr => True)
  := by
      apply HoareTriple.mk
      unfold prepare_message
      -- Random.genRand
      step with ⟨ fun b => single_message_label sender receiver {payload:=b}, Usage.nothing ⟩
      -- ProtocolEvent.logEvent
      step_intro
      hoist; step_intro
      step by
        simp [ProtocolEvent.EventInv.invariant]
        constructor
        . grind
        . grind[single_message_label]
      -- PersistentLocalState.storeLocalState
      step by
        simp only [PersistentLocalState.LocalStateInv.invariant]
        repeat apply And.intro; grind
        grind[single_message_label]
      trivial

@[instance]
theorem send_message.proof (sender receiver: Participant) (state_id: Nat)
  : HoareTriple
    (send_message sender receiver state_id)
    (fun _ => True)
    (fun _ _ => True)
  := by
    apply HoareTriple.mk
    unfold send_message
    -- PersistentLocalState.getLocalState
    step
    -- guard
    step with ⟨ ⟩
    step with ⟨ ⟩
    -- Communication.sendConfidential
    hoist; step_intro
    have : st = ({sender, receiver, msg:={payload:=msg}}: single_message_send_state) := by
      -- maybe annotate single_message{_state} with @[grind]
      grind[single_message, single_message_send_state]
    have : msg.Invariant tr
      ∧ (msg.label tr) = (single_message_label sender receiver {payload:=msg})
      ∧ Communication.Confidential.CommunicationInvariants.confidential tr sender receiver msg := by
      have st_inv : single_message_send_state.Invariant.invariant sender st tr := by assumption
      simp[PersistentLocalState.LocalStateInv.invariant] at st_inv
      refine ⟨ ?_, ?_, ?_ ⟩
      . grind
      . obtain ⟨ h_eq, inv ⟩ := st_inv
        grind
      . -- does not work with grind only?
        simp[Communication.Confidential.CommunicationInvariants.confidential]
        grind
    step with ⟨ ⟩ by grind[single_message_label]
    trivial

@[instance]
theorem receive_message.proof
  (sender receiver : Participant) (msg_id: Nat)
  : HoareTriple
    (receive_message sender receiver msg_id)
    (fun _ => True)
    (fun _h _tr => True)
  := by
      apply HoareTriple.mk
      unfold receive_message
      -- Communication.receiveConfidential
      step with ⟨ ⟩
      -- TODO: use other tactic to get postcondition
      rename_i receiveConfidentialPost
      mark_non_monotone receiveConfidentialPost
      step_intro
      -- ProtocolEvent.logEvent
      hoist; step_intro
      step with ⟨ ⟩ by
        simp[ProtocolEvent.EventInv.invariant]
        simp at receiveConfidentialPost
        rcases receiveConfidentialPost with pub | inv
        . left; trivial
        . simp[Communication.Confidential.CommunicationInvariants.confidential] at inv
          right; grind
      -- PersistentLocalState.storeLocalState
      hoist; step_intro
      have : single_message_receive_state.Invariant.invariant receiver state tr := by
        simp[PersistentLocalState.LocalStateInv.invariant]
        refine ⟨ ?_, ?_ ⟩
        . grind
        let ⟨ i, recv_event_inv ⟩ := Trace.EventLogged_imp_EventInv ev tr h (by assumption)
        simp[ProtocolEvent.EventInv.invariant] at recv_event_inv
        rcases recv_event_inv with pub | inv
        . left
          grind
        . right
          obtain ⟨ bytes_inv, sender', inv ⟩ := inv
          refine ⟨ sender', ?_ ⟩
          simp[single_message_receive_state.IsWellFormed_eq, Bytes.KnowableBy]
          have : msg = state.msg := by grind
          have : msg = ev.msg := by grind
          simp_all
          constructor
          . grind[Bytes.Publishable]
          . grind
        done
      step with ⟨ ⟩ by grind
      grind


end Proofs

section Reachability

variable [HasTraceInvariant]

-- Future work: the following section is boilerplate that could be meta-programmed
section

-- ReachableImpliesInvariant.mk requires postcondition to be (fun _ _ => True)
public instance: ReachableImpliesInvariant prepare_message.reachability := .mk (fun (sender, receiver) => prepare_message.proof sender receiver)
public instance: ReachableImpliesInvariant send_message.reachability := .mk (fun (sender, receiver, s_id) => send_message.proof sender receiver s_id)
public instance: ReachableImpliesInvariant receive_message.reachability := .mk (fun (sender, receiver, s_id) => receive_message.proof sender receiver s_id)

end

#combine into ReachabilityTheorem from
  Network,
  Communication.Confidential,
  prepare_message,
  send_message,
  receive_message,

end Reachability

section LabelLemma

variable [HasTraceInvariant]

end LabelLemma

end DY.Example.SingleConfMessage
