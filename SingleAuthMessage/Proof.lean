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
  [traceProof3: ProofTraceTypes.Has (ProtocolEvent.ProofEntryT single_message_send_event)]
  [traceProof4: ProofTraceTypes.Has (ProtocolEvent.ProofEntryT single_message_receive_event)]
  [traceProof5: ProofTraceTypes.Has (PersistentLocalState.CompromisableState.ProofEntryT single_message_state)]

attribute [reducible, scoped instance] HasProofTrace.traceProof
attribute [reducible, scoped instance] HasProofTrace.traceProof0
attribute [reducible, scoped instance] HasProofTrace.traceProof1
attribute [reducible, scoped instance] HasProofTrace.traceProof2
attribute [reducible, scoped instance] HasProofTrace.traceProof3
attribute [reducible, scoped instance] HasProofTrace.traceProof4
attribute [reducible, scoped instance] HasProofTrace.traceProof5

end ProofTraceConfig

public section BytesInvariants

variable [HasProofTrace]

def layerLabel
  (me other: Participant)
  : Label
where
  isCorrupt tr := StateCompromised me tr ∨ StateCompromised other tr

@[simp]
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
        let msg := st.msg
        let sender := st.sender
        msg.payload.Invariant tr ∧
        msg.payload.Publishable tr ∧
        (msg.payload.label tr).canFlow (authenticatedLabel me sender) tr.erase ∧
        Comparse.IsWellFormed (Bytes.KnowableBy Label.pub) st tr ∧
        tr.erase.EventLogged ({ sender:=st.sender, msg:=st.msg } : single_message_send_event)
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
  : PersistentLocalState.LocalStateInv.invariant participant st tr → st.msg.payload.Invariant tr
:= by
  simp [PersistentLocalState.LocalStateInv.invariant]
  grind

grind_pattern [grind_later] single_message_state_inv_imp_Invariant => PersistentLocalState.LocalStateInv.invariant participant st tr



instance single_message_send_event.Invariant : ProtocolEvent.EventInv (single_message_send_event)
where
  invariant tr ev :=
    Bytes.KnowableBy (Label.pub) ev.msg.payload tr

instance single_message_receive_event.Invariant : ProtocolEvent.EventInv (single_message_receive_event)
where
  invariant tr ev :=
    Bytes.KnowableBy (Label.pub) ev.msg.payload tr
    ∧ (tr.erase.EventLogged ({ sender:=ev.sender, msg:=ev.msg } : single_message_send_event ))

end TraceInvariant

-- Future work: the following section is boilerplate that could be meta-programmed
public section TraceInvariantConfig

class HasTraceInvariant extends HasBytesInvariants where
  [traceInv: TraceInvariant]
  [traceInv0: TraceInvariant.Has Network.ProofEntryT]
  [traceInv1: TraceInvariant.Has Communication.ProofEntryT]
  [traceInv2: TraceInvariant.Has Random.ProofEntryT]
  [traceInv3: TraceInvariant.Has (ProtocolEvent.ProofEntryT single_message_send_event)]
  [traceInv4: TraceInvariant.Has (ProtocolEvent.ProofEntryT single_message_receive_event)]
  [traceInv5: TraceInvariant.Has (PersistentLocalState.CompromisableState.ProofEntryT single_message_state)]
  [attBaseThm: BaseAttackerKnowledgeTheorem]
  [attThm: AttackerKnowledgeTheorem]

attribute [reducible, scoped instance] HasTraceInvariant.traceInv
attribute [           scoped instance] HasTraceInvariant.traceInv0
attribute [           scoped instance] HasTraceInvariant.traceInv1
attribute [           scoped instance] HasTraceInvariant.traceInv2
attribute [           scoped instance] HasTraceInvariant.traceInv3
attribute [           scoped instance] HasTraceInvariant.traceInv4
attribute [           scoped instance] HasTraceInvariant.traceInv5
attribute [           scoped instance] HasTraceInvariant.attBaseThm
attribute [           scoped instance] HasTraceInvariant.attThm

end TraceInvariantConfig

public section Proofs

variable [HasTraceInvariant]

@[instance]
theorem prepare_message.spec (sender receiver : Participant)
  : HoareTriple
    (prepare_message sender receiver)
    (fun _ => True)
    (fun _state_id _tr => True)
  := by
      apply HoareTriple.mk
      unfold prepare_message
      step with ⟨ fun _ => Label.pub, Usage.nothing ⟩ -- have to pass ghost arguments to genRand here
      step_intro
      hoist
      step_intro
      step by
        have : payload = ev.msg.payload := by grind
        simp only [ProtocolEvent.EventInv.invariant, Bytes.KnowableBy]
        grind [single_message_send_event]
      step by
        simp only [PersistentLocalState.LocalStateInv.invariant]
        apply And.intro; simp; grind
        apply And.intro; simp; grind
        apply And.intro; simp; grind
        apply And.intro; simp; grind
        subst ev
        have : Trace.EventLogged ({ sender, msg } : single_message_send_event) tr.erase := by assumption
        simp
        grind
      trivial
      done

@[instance]
theorem send_message.spec (me other: Participant) (state_id: Nat)
  : HoareTriple
    (send_message me other state_id)
    (fun _ => True)
    (fun _ _ => True)
  := by
    apply HoareTriple.mk
    unfold send_message
    step
    let st : single_message_state := by assumption
    step with ⟨ ⟩
    step with ⟨ ⟩ by
      have : single_message_state.Invariant.invariant me st tr := by grind
      simp [PersistentLocalState.LocalStateInv.invariant] at this
      grind
    trivial

@[instance]
theorem receive_message.spec (me other : Participant) (msg_id: Nat)
  : HoareTriple
    (receive_message me other msg_id)
    (fun _ => True)
    (fun h tr => -- TODO: Nontrivial postcondition causes type error for reachability configuration
      ∃ (payload:Bytes), tr.erase.EventLogged (single_message_receive_event.mk other me {payload})
    ) := by
      apply HoareTriple.mk
      unfold receive_message
      step with ⟨ ⟩
      have m_pub : msg_bytes.Publishable tr := by grind
      have m_inv : msg_bytes.Invariant tr := by grind
      step_intro
      have : msg_bytes = msg.payload := by grind
      rename_i mb mb1
      -- have to clear for step to succeed
      clear mb1
      step with ⟨ ⟩ by
        subst msg
        simp [ProtocolEvent.EventInv.invariant]
        constructor
        . grind
        . sorry
      step with ⟨ ⟩ by sorry
      grind



@[instance]
theorem single_message_state.compromise.spec (stHandle: Nat)
  : HoareTriple (single_message_state.compromise stHandle) (fun _ => True) (fun _ _ => True)
:= by unfold single_message_state.compromise; step; grind

end Proofs

section Reachability

variable [HasTraceInvariant]

-- Future work: the following section is boilerplate that could be meta-programmed
section

-- ReachableImpliesInvariant.mk requires postcondition to be (fun _ _ => True)
public instance: ReachableImpliesInvariant prepare_message.reachability := .mk (fun (me, other) => prepare_message.spec me other)
public instance: ReachableImpliesInvariant send_message.reachability := .mk (fun (me, other, s_id) => send_message.spec me other s_id)
public instance: ReachableImpliesInvariant single_message_state.compromise.reachability := .mk (fun (stHandle) => single_message_state.compromise.spec stHandle)

variable [ProofTraceTypes] [TraceInvariant]
variable [BytesInvariants] [BytesInvariantsProofs]
variable [ProofTraceTypes.Has Communication.ProofEntryT] [TraceInvariant.Has Communication.ProofEntryT]
variable [BaseAttackerKnowledgeTheorem] [AttackerKnowledgeTheorem]

public
instance: ReachableImpliesInvariant receive_message.reachability where
  pf input :=
  by
    have ⟨ me, other, s_id ⟩ := input
    have spec := (receive_message.spec me other s_id).pf
    have ⟨ me, other, s_id ⟩ := input
    apply HoareTriple.mk
    have spec := (receive_message.spec me other s_id).pf
    unfold hoareTriple at *
    simp_all [receive_message.reachability]
    intro tr tr_inv
    -- intro tr pre tr_inv
    -- have spec := spec tr tr_inv
    sorry
    -- simp only [ProtocolEvent.EventInv, single_message_event.Invariant]
    -- grind [single_message_event.Invariant, Bytes.AttackerKnows_implies_Publishable]



end

#combine into ReachabilityTheorem from
  Network,
  prepare_message,
  send_message,
  receive_message,
  single_message_state.compromise,

end Reachability

section LabelLemma

variable [HasTraceInvariant]

-- theorem keyLabelMyTurn_isCorrupt_eq
--   (me recipient: Participant) (transcript: Transcript) (tr: ExecTrace)
--   : (keyLabelMyTurn me recipient transcript).isCorrupt tr = (
--       (
--         transcript.length ≤ 1 ∨
--         StateCompromised me transcript tr ∨
--         StateCompromised me transcript.tail tr ∨
--         StateCompromised recipient transcript tr
--       ) ∨ (
--         (keyLabelOtherTurn me recipient transcript.tail).isCorrupt tr ∧
--         (labelBeforeEvent (ltkLabel recipient) me recipient transcript).isCorrupt tr
--       )
--     )
-- := by
--   have: StateCompromised me transcript.tail tr → (keyLabelOtherTurn me recipient transcript.tail).isCorrupt tr := by
--     unfold keyLabelOtherTurn
--     split
--     · grind
--     · grind
--     simp [stateLabel]
--     grind
--   unfold keyLabelMyTurn
--   split
--   · grind
--   · grind
--   simp [stateLabel]
--   grind
--
-- theorem keyLabelOtherTurn_isCorrupt_eq
--   (me recipient: Participant) (transcript: Transcript) (tr: ExecTrace)
--   : (keyLabelOtherTurn me recipient transcript).isCorrupt tr = (
--       (
--         transcript.length ≤ 1 ∨
--         StateCompromised me transcript tr ∨
--         StateCompromised recipient transcript tr ∨
--         StateCompromised recipient transcript.tail tr
--       ) ∨ (
--         (keyLabelMyTurn me recipient transcript.tail).isCorrupt tr ∧
--         (labelBeforeEvent (ltkLabel recipient) me recipient transcript.tail).isCorrupt tr
--       )
--     )
-- := by
--   have: StateCompromised recipient transcript.tail tr → (keyLabelMyTurn me recipient transcript.tail).isCorrupt tr := by
--     unfold keyLabelMyTurn
--     split
--     · grind
--     · grind
--     simp [stateLabel]
--     grind
--   unfold keyLabelOtherTurn
--   split
--   · grind
--   · grind
--   simp [stateLabel]
--   grind
--
-- theorem keyLabelMyTurn_isCorrupt_implies_lemma
--   (me recipient: Participant) (transcript: Transcript) (tr: ExecTrace)
--   : (keyLabelOtherTurn me recipient transcript).isCorrupt tr →
--     ¬ (labelBeforeEvent (ltkLabel recipient) me recipient transcript.tail).isCorrupt tr →
--     (
--       transcript.length ≤ 1 ∨
--       StateCompromised me transcript tr ∨
--       StateCompromised recipient transcript tr ∨
--       StateCompromised recipient transcript.tail tr
--     )
-- := by
--   conv =>
--     lhs
--     rewrite [keyLabelOtherTurn_isCorrupt_eq]
--   grind
--
-- theorem keyLabelMyTurn_isCorrupt_implies
--   (me recipient: Participant) (transcript: Transcript) (tr: ExecTrace)
--   : (keyLabelMyTurn me recipient transcript).isCorrupt tr → (
--       (
--         transcript.length ≤ 1 ∨
--         StateCompromised me transcript tr ∨
--         StateCompromised me transcript.tail tr ∨
--         StateCompromised recipient transcript tr
--       ) ∨ (
--         ∃ previousTranscript,
--           previousTranscript <:+ transcript ∧
--           1 ≤ previousTranscript.length ∧
--           (previousTranscript.length % 2) = (transcript.length % 2) ∧
--           (labelBeforeEvent (ltkLabel recipient) me recipient previousTranscript).isCorrupt tr ∧ (
--             previousTranscript.length ≤ 2 ∨
--             StateCompromised me previousTranscript tr ∨
--             StateCompromised me previousTranscript.tail tr ∨
--             StateCompromised recipient previousTranscript.tail tr ∨
--             StateCompromised recipient previousTranscript.tail.tail tr
--           )
--       )
--     )
-- := by
--   intro h_corrupt
--   by_cases transcript.length ≤ 1
--   · left; grind
--   rewrite [keyLabelMyTurn_isCorrupt_eq] at h_corrupt
--   by_cases ¬ (labelBeforeEvent (ltkLabel recipient) me recipient transcript).isCorrupt tr
--   · left; grind
--   cases h_corrupt
--   · left; grind
--   right
--   rename_i h_corrupt
--   obtain ⟨ h_key_corrupt, h_sig_corrupt ⟩ := h_corrupt
--   by_cases (labelBeforeEvent (ltkLabel recipient) me recipient transcript.tail.tail).isCorrupt tr
--   · rewrite [keyLabelOtherTurn_isCorrupt_eq] at h_key_corrupt
--     cases h_key_corrupt
--     · grind [List.tail_suffix]
--     have := keyLabelMyTurn_isCorrupt_implies me recipient transcript.tail.tail tr (by grind)
--     cases this
--     · by_cases transcript.length ≤ 2
--       · exists transcript
--         grind
--       -- in the following, `grind` does case splitting
--       -- and chooses between `exists transcript` and `exists transcript.tail.tail`!
--       grind [List.tail_suffix]
--     rename_i h
--     obtain ⟨ previousTranscript, _, _ ⟩ := h
--     exists previousTranscript
--     grind [List.tail_suffix]
--   have := keyLabelMyTurn_isCorrupt_implies_lemma _ _ _ _ h_key_corrupt (by grind)
--   exists transcript
--   grind [List.tail_suffix]
-- termination_by transcript.length
-- decreasing_by grind [cases List]
--
-- theorem keyLabelOtherTurn_isCorrupt_implies
--   (me recipient: Participant) (transcript: Transcript) (tr: ExecTrace)
--   : (keyLabelOtherTurn me recipient transcript).isCorrupt tr → (
--       (
--         transcript.length ≤ 1 ∨
--         StateCompromised me transcript tr ∨
--         StateCompromised recipient transcript tr ∨
--         StateCompromised recipient transcript.tail tr
--       ) ∨ (
--         ∃ previousTranscript,
--           previousTranscript <:+ transcript.tail ∧
--           1 ≤ previousTranscript.length ∧
--           (previousTranscript.length % 2) = (transcript.tail.length % 2) ∧
--           (labelBeforeEvent (ltkLabel recipient) me recipient previousTranscript).isCorrupt tr ∧ (
--             previousTranscript.length ≤ 2 ∨
--             StateCompromised me previousTranscript tr ∨
--             StateCompromised me previousTranscript.tail tr ∨
--             StateCompromised recipient previousTranscript.tail tr ∨
--             StateCompromised recipient previousTranscript.tail.tail tr
--           )
--       )
--     )
-- := by
--   intro h_corrupt
--   by_cases transcript.length ≤ 1
--   · left; grind
--   rewrite [keyLabelOtherTurn_isCorrupt_eq] at h_corrupt
--   cases h_corrupt
--   · left; grind
--   rename_i h_corrupt
--   obtain ⟨ h_key_corrupt, h_sig_corrupt ⟩ := h_corrupt
--   have := keyLabelMyTurn_isCorrupt_implies _ _ _ _ h_key_corrupt
--   cases this
--   · grind [List.tail_suffix]
--   right
--   grind [List.tail_suffix]
--
-- theorem labelBeforeEvent_ltkLabel_isCorrupt_implies
--   (me recipient: Participant) (transcript: Transcript)
--   (tr: ExecTrace)
--   : (∃ k, tr.EventLogged (RatchetEvent.ReceiveUpdate me recipient transcript k)) →
--     (labelBeforeEvent (ltkLabel recipient) me recipient transcript).isCorrupt tr →
--     ∀ i k,
--       tr.EventLoggedAt (RatchetEvent.ReceiveUpdate me recipient transcript k) i →
--       (∃ spk, LongTermKeys.LongTermKeyCompromised "Ratchet PKI" recipient spk (tr.prefix i))
-- := by
--   intro h_ev h_corrupt
--   simp only [labelBeforeEvent, ltkLabel] at h_corrupt
--   have ⟨ i', ev, ⟨ k', h_ev' ⟩, h_ev'_logged ⟩ := event_minimum_prefix (fun ev => ∃ k, ev = (RatchetEvent.ReceiveUpdate me recipient transcript k)) tr (by grind)
--   intro i k h_ev
--   obtain ⟨ trBefore, _ ⟩ := h_corrupt
--   have := Trace.le_imp_prefix_eq trBefore tr (by grind)
--   have: ¬ tr.prefix (i'+1) ≤ trBefore := by grind
--   have := DY.Trace.EventLoggedAt_le' (RatchetEvent.ReceiveUpdate me recipient transcript k) i (tr.prefix (i+1)) tr
--   have := fun h => h_ev'_logged.right.right (i+1) (RatchetEvent.ReceiveUpdate me recipient transcript k) h (by grind) (by grind)
--   have: trBefore.length ≤ i' := by grind
--   have: i' < i+1 := by grind
--   have: trBefore ≤ tr.prefix i := by grind
--   grind
--
-- theorem logged_receive_update_implies_logged_previous_transcript
--   (me recipient: Participant) (transcript previousTranscript: Transcript) (tr: ProofTrace)
--   : tr.Invariant →
--     previousTranscript <:+ transcript →
--     1 ≤ previousTranscript.length →
--     (previousTranscript.length % 2) = (transcript.length % 2) →
--     (∃ k, tr.erase.EventLogged (RatchetEvent.ReceiveUpdate me recipient transcript k)) →
--     (∃ k, tr.erase.EventLogged (RatchetEvent.ReceiveUpdate me recipient previousTranscript k))
-- := by
--   intro h_inv h_suffix h_length1 h_length2
--   have h_disj: (previousTranscript = transcript ∨ previousTranscript = transcript.tail) ∨ previousTranscript <:+ transcript.tail.tail := by
--     obtain ⟨ pref, h_pref ⟩ := h_suffix
--     grind
--   cases h_disj
--   · grind
--   have: 3 ≤ transcript.length := by grind
--   intro ⟨ k, h_ev ⟩
--   apply logged_receive_update_implies_logged_previous_transcript me recipient transcript.tail.tail previousTranscript tr (by grind) (by grind) (by grind) (by grind [cases List])
--   have ⟨ _, h_ev' ⟩: (∃ k, tr.erase.EventLogged (RatchetEvent.SendUpdate me recipient transcript.tail k)) := by
--     have h_ev_inv := Trace.EventLogged_imp_EventInv _ _ h_inv h_ev
--     simp only [ProtocolEvent.EventInv.invariant] at h_ev_inv
--     grind
--   have ⟨ _, h_ev'' ⟩: (∃ k, tr.erase.EventLogged (RatchetEvent.ReceiveUpdate me recipient transcript.tail.tail k)) := by
--     have h_ev_inv := Trace.EventLogged_imp_EventInv _ _ h_inv h_ev'
--     simp only [ProtocolEvent.EventInv.invariant] at h_ev_inv
--     grind
--   grind


end LabelLemma

end DY.Example.SingleAuthMessage
