module

public import DY.Trace
public import DY.Bytes
public import DY.Label.Basic
public import DY.Actions.PersistentLocalState
import DY.Meta.Step

public import DyleanExtensions

namespace DY.Communication.Confidential

variable [BytesFunctor]

section Execution

namespace Compromise

-- TODO: adjust identifier
public
structure CommunicationCompromiseEvent where
  participant: Participant
  deriving DecidableEq

public
instance : Repr CommunicationCompromiseEvent where
  reprPrec e _ := "compromised: " ++ e.participant

#combine into ExecEntryT, baseAttackerKnowledge from ProtocolEvent CommunicationCompromiseEvent

end Compromise

public
def compromiseParticipant
  [ExecTraceTypes]
  [ExecTraceTypes.Has Compromise.ExecEntryT]
  (participant : Participant): Traceful Unit := do
  ProtocolEvent.logEvent (Compromise.CommunicationCompromiseEvent.mk participant)

@[expose]
public
def participantCompromisedAt
  [ExecTraceTypes]
  [ExecTraceTypes.Has Compromise.ExecEntryT]
  (tr : ExecTrace) (participant : Participant) (i : Nat) : Prop
    := tr.EventLoggedAt (Compromise.CommunicationCompromiseEvent.mk participant) i

public
def participantCompromised
  [ExecTraceTypes]
  [ExecTraceTypes.Has Compromise.ExecEntryT]
  (tr : ExecTrace) (participant : Participant) : Prop
    := ∃i, participantCompromisedAt tr participant i



public
structure ExecEntryT where
  payload : Bytes
  sender : Participant
  receiver : Participant

public
instance [Repr Bytes] : Repr ExecEntryT where
  reprPrec e _ := "communication: " ++ (repr e.payload) ++ " (" ++ e.sender ++ " → " ++ e.receiver ++ ")"


-- constructors
@[simp, grind]
public
def ExecEntryT.Confidential (sender receiver : Participant) (payload : Bytes) : ExecEntryT := { payload, sender, receiver}

-- Differs from authenticated
public
def baseAttackerKnowledge [ExecTraceTypes] [ExecTraceTypes.Has Compromise.ExecEntryT]: SubBaseAttackerKnowledge ExecEntryT where
  attackerKnows tr entry msg := entry.payload = msg ∧ (participantCompromised tr entry.receiver)



-- Still add attacker function here that does not require higher layer predicates
-- and requires message to be known?
-- How about receive? Attacker can learn from trace entry after compromising.
public
def sendConfidentialAttacker
  [ExecTraceTypes] [ExecTraceTypes.Has ExecEntryT]
  (sender receiver : Participant) (msg: Bytes): Traceful Nat :=
  do
  let entry: ExecEntryT := ExecEntryT.Confidential sender receiver msg
  appendEntry entry

public
def sendConfidential
  [ExecTraceTypes] [ExecTraceTypes.Has ExecEntryT]
  (sender receiver : Participant) (msg: Bytes): Traceful Nat :=
  do
  let entry: ExecEntryT := ExecEntryT.Confidential sender receiver msg
  appendEntry entry

public
def receiveConfidential
  [ExecTraceTypes] [ExecTraceTypes.Has ExecEntryT]
  (_sender receiver : Participant) (handle: Nat): Traceful Bytes :=
  do
  let entry: ExecEntryT ← getEntryExtended handle
  -- differs from authenticated
  guard (entry.receiver = receiver)
  return entry.payload

-- definitions like MessageSentAt from Network.lean
@[expose]
public
def confidentialMessageSentAt
  [ExecTraceTypes]
  [ExecTraceTypes.Has ExecEntryT]
  (tr : ExecTrace) (sender receiver : Participant) (bytes : Bytes) (i : Nat) :=
      tr.at? i = some (ExecEntryT.mk bytes sender receiver)

@[expose, simp]
public
def confidentialMessageSent
  [ExecTraceTypes]
  [ExecTraceTypes.Has ExecEntryT]
  (tr : ExecTrace) (sender receiver : Participant) (bytes : Bytes) :=
      exists i, confidentialMessageSentAt tr sender receiver bytes i

public
theorem confidentialMessageSentAt_le
  [ExecTraceTypes]
  [ExecTraceTypes.Has ExecEntryT]
  (tr1 tr2 : ExecTrace) (sender receiver : Participant) (bytes : Bytes) (i : Nat) :
    tr1 ≤ tr2
    → confidentialMessageSentAt tr1 sender receiver bytes i
    → confidentialMessageSentAt tr2 sender receiver bytes i
  := by
    unfold confidentialMessageSentAt
    grind[Trace.at?_le]

grind_pattern [grind_later] confidentialMessageSentAt_le =>
tr1 ≤ tr2, confidentialMessageSentAt tr1 sender receiver bytes i

public
theorem confidentialMessageSentAt_le'
  [ExecTraceTypes]
  [ExecTraceTypes.Has ExecEntryT]
  (tr1 tr2 : ExecTrace) (sender receiver : Participant) (bytes : Bytes) (i : Nat)
    : tr1 ≤ tr2
    → confidentialMessageSentAt tr2 sender receiver bytes i
    → i < tr1.length
    → confidentialMessageSentAt tr1 sender receiver bytes i
    := by
      unfold confidentialMessageSentAt
      grind[Trace.at?_eq_some]

grind_pattern [grind_later] confidentialMessageSentAt_le' =>
tr1 ≤ tr2, i < tr1.length, confidentialMessageSentAt tr1 sender receiver bytes i

public
theorem confidentialMessageSent_le
  [ExecTraceTypes]
  [ExecTraceTypes.Has ExecEntryT]
  (tr1 tr2 : ExecTrace) (sender receiver : Participant) (bytes : Bytes) :
    tr1 ≤ tr2
    → confidentialMessageSent tr1 sender receiver bytes
    → confidentialMessageSent tr2 sender receiver bytes
  := by
    unfold confidentialMessageSent
    intro le sent1
    let later := confidentialMessageSentAt_le tr1 tr2 sender receiver bytes
    grind

grind_pattern [grind_later] confidentialMessageSent_le =>
tr1 ≤ tr2, confidentialMessageSent tr1 sender receiver bytes


omit [BytesFunctor]
public
theorem participantCompromisedAt_le
  [ExecTraceTypes]
  [ExecTraceTypes.Has Compromise.ExecEntryT]
  (tr1 tr2 : ExecTrace) (participant : Participant) (i : Nat) :
    tr1 ≤ tr2 → participantCompromisedAt tr1 participant i → participantCompromisedAt tr2 participant i
    := by
      unfold participantCompromisedAt
      grind

grind_pattern [grind_later] participantCompromisedAt_le =>
tr1 ≤ tr2, participantCompromisedAt tr1 participant i


omit [BytesFunctor]
public
theorem participantCompromised_le
  [ExecTraceTypes]
  [ExecTraceTypes.Has Compromise.ExecEntryT]
  (tr1 tr2 : ExecTrace) (participant : Participant) :
    tr1 ≤ tr2 → participantCompromised tr1 participant → participantCompromised tr2 participant
    := by
      unfold participantCompromised
      unfold participantCompromisedAt
      grind

grind_pattern [grind_later] participantCompromised_le =>
tr1 ≤ tr2, participantCompromised tr1 participant


end Execution

section Proof

namespace Compromise

public instance
  [ExecTraceTypes] [ProofTraceTypes]
  : ProtocolEvent.EventInv CommunicationCompromiseEvent
  where
    invariant _ _ := True

#combine into ProofEntryT, SubTraceInvariant, SubBaseAttackerKnowledgeTheorem from
  ProtocolEvent CommunicationCompromiseEvent

end Compromise

public
abbrev ProofEntryT := ExecEntryT

public
instance: ErasableProofEntry ExecEntryT ProofEntryT := ErasableProofEntry.default ExecEntryT

public
instance: ExecEntryAssociatedWithProofEntry ExecEntryT ProofEntryT where


public
class CommunicationEventPredicates [BytesFunctor] [ExecTraceTypes] [ProofTraceTypes] where
  confidential : ProofTrace → Participant → Participant → Bytes → Prop

  confidential_later : ∀ tr1 tr2 sender receiver payload,
    tr1 ≤ tr2 → confidential tr1 sender receiver payload →
    confidential tr2 sender receiver payload

grind_pattern [grind_later] CommunicationEventPredicates.confidential_later =>
tr1 ≤ tr2, CommunicationEventPredicates.confidential tr1 sender receiver payload


public
def CommunicationLabel
  [ExecTraceTypes]
  [ExecTraceTypes.Has Compromise.ExecEntryT]
  (participant : Participant) : Label := {
  isCorrupt tr := participantCompromised tr participant
  isCorruptLater tr1 tr2 := participantCompromised_le tr1 tr2 participant
}

-- entry invariant
public
instance
  [ExecTraceTypes] [ExecTraceTypes.Has Compromise.ExecEntryT]
  [ProofTraceTypes] [BytesInvariants]
  [CommunicationEventPredicates]
  : SubTraceInvariant ProofEntryT
where
  invariant tr entry := (entry.payload.label tr).canFlow (CommunicationLabel entry.receiver) tr.erase
    ∧ entry.payload.Invariant tr
    -- TODO: do we require event predicates as entry invariant?
    -- ∧ (CommunicationEventPredicates.confidential tr entry.sender entry.receiver entry.payload ∨ participantCompromised tr.erase entry.sender)

-- public
-- theorem confidentialMessageSentAt_imp_higher_layer_invariants
--   [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant] [BytesInvariants]
--   [CommunicationEventPredicates]
--   [ExecTraceTypes.Has Compromise.ExecEntryT] [ProofTraceTypes.Has Compromise.ProofEntryT] [TraceInvariant.Has Compromise.ProofEntryT]
--   [ExecTraceTypes.Has ExecEntryT] [ProofTraceTypes.Has ProofEntryT] [TraceInvariant.Has ProofEntryT]
--   (sender receiver: Participant) (bytes: Bytes)
--   (i: Nat)
--   (tr: ProofTrace)
--   : tr.Invariant →
--     confidentialMessageSentAt tr.erase sender receiver bytes i →
--     (CommunicationEventPredicates.confidential (tr.prefix i) sender receiver bytes ∨ participantCompromised (tr.erase.prefix i) sender)
-- := by
--   intro h_inv h_ev
--   have := Trace.invariant_at tr i (by grind [confidentialMessageSentAt]) h_inv
--   suffices SubTraceInvariant.invariant (tr.prefix i) ({sender, receiver, payload:=bytes}:ExecEntryT) by
--     simp_all [SubTraceInvariant.invariant]
--     sorry
--   rewrite [← TraceInvariant.Has.inv_commutes]
--   simp [confidentialMessageSentAt, Trace.at?_eq_some, Trace.erase_at, ProofTrace.Entry.erase_eq_imp_exists, ErasableProofEntry.erase] at h_ev
--   grind


-- if attacker learns bytes from entry,
-- then the bytes must be publishable
public
instance baseAttackerKnowledgeTheorem
  [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant] [BytesInvariants]
  [CommunicationEventPredicates]
  [ExecTraceTypes.Has Compromise.ExecEntryT]
  [ProofTraceTypes.Has Compromise.ProofEntryT]
  [TraceInvariant.Has Compromise.ProofEntryT]
  [ExecTraceTypes.Has ExecEntryT]
  [ProofTraceTypes.Has ProofEntryT]
  [TraceInvariant.Has ProofEntryT]:
  SubBaseAttackerKnowledgeTheorem ProofEntryT baseAttackerKnowledge
where
  pf trBefore entry b := by
    intro invBefore attackerKnows
    simp [SubTraceInvariant.invariant] at invBefore
    simp [baseAttackerKnowledge, ErasableProofEntry.erase] at attackerKnows
    let ⟨ b_eq_entry, comp ⟩ := attackerKnows
    unfold Bytes.Publishable
    constructor
    . grind
    . unfold Label.canFlow
      intro tr h_le _
      subst b
      simp at attackerKnows
      have : (CommunicationLabel entry.receiver).isCorrupt tr := by
        simp[CommunicationLabel]
        grind[participantCompromised_le]
      have : (entry.payload.label trBefore).canFlow (CommunicationLabel entry.receiver) tr := by grind
      grind[Label.canFlow]

@[instance]
theorem compromiseParticipant.proof
  [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant]
  [BytesInvariants] [BytesInvariantsProofs]
  [CommunicationEventPredicates]
  [ExecTraceTypes.Has ExecEntryT]
  [ExecTraceTypes.Has Compromise.ExecEntryT]
  [ProofTraceTypes.Has ProofEntryT]
  [ProofTraceTypes.Has Compromise.ProofEntryT]
  [TraceInvariant.Has ProofEntryT]
  [TraceInvariant.Has Compromise.ProofEntryT]
  (participant: Participant)
  : HoareTriple (compromiseParticipant participant) (fun _ => True) (fun _ tr => participantCompromised tr.erase participant )
:= by
  unfold compromiseParticipant
  step by simp[ProtocolEvent.EventInv.invariant]
  trivial


@[instance]
public
theorem sendConfidentialAttacker.proof
  [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant]
  [BytesInvariants] [BytesInvariantsProofs]
  [CommunicationEventPredicates]
  [ExecTraceTypes.Has ExecEntryT]
  [ExecTraceTypes.Has Compromise.ExecEntryT]
  [ProofTraceTypes.Has ProofEntryT]
  [ProofTraceTypes.Has Compromise.ProofEntryT]
  [TraceInvariant.Has ProofEntryT]
  [TraceInvariant.Has Compromise.ProofEntryT]
  (sender receiver: Participant)
  (msg: Bytes)
  : HoareTriple
    (sendConfidentialAttacker sender receiver msg)
    (fun tr => msg.Publishable tr)
    (fun i tr => confidentialMessageSentAt tr.erase sender receiver msg i)
:= by
  apply HoareTriple.mk
  unfold sendConfidentialAttacker
  dsimp only
  -- appendEntry
  step with ⟨ fun _ => ExecEntryT.Confidential sender receiver msg ⟩ by
    simp_all [ErasableProofEntry.erase, SubTraceInvariant.invariant, ExecEntryT.Confidential]
    have : (msg.label tr).canFlow Label.pub tr.erase := by grind
    refine ⟨ ?_, ?_ ⟩
    . grind[canFlowTrans]
    . grind
  unfold confidentialMessageSentAt
  let entry : ExecEntryT := (ExecEntryT.Confidential sender receiver msg)
  have h_at?_x : tr.at? x = some entry := by assumption
  -- TODO: make this a reusable theorem? (also needed for receiveConfidential)
  have h_erase_at?_x : tr.erase.at? x = some entry := by
    simp[Trace.at?_eq_some] at h_at?_x
    simp[Trace.at?_eq_some, Trace.erase_at, ProofTrace.Entry.erase_eq_imp_exists, ErasableProofEntry.erase]
    grind
  grind

@[instance]
public
theorem sendConfidential.proof
  [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant]
  [BytesInvariants] [BytesInvariantsProofs]
  [CommunicationEventPredicates]
  [ExecTraceTypes.Has ExecEntryT]
  [ExecTraceTypes.Has Compromise.ExecEntryT]
  [ProofTraceTypes.Has ProofEntryT]
  [ProofTraceTypes.Has Compromise.ProofEntryT]
  [TraceInvariant.Has ProofEntryT]
  [TraceInvariant.Has Compromise.ProofEntryT]
  (sender receiver: Participant)
  (msg: Bytes)
  : HoareTriple
    (sendConfidential sender receiver msg)
    (fun tr => msg.Invariant tr ∧ (msg.label tr).canFlow Label.pub tr.erase)
    -- msg.Publishable tr
      -- has to be ensured by higher layer
      -- ∨ CommunicationEventPredicates.confidential tr sender receiver msg)
    (fun i tr => confidentialMessageSentAt tr.erase sender receiver msg i)
:= by
  apply HoareTriple.mk
  unfold sendConfidential
  dsimp only
  -- appendEntry
  step with ⟨ fun _ => ExecEntryT.Confidential sender receiver msg ⟩ by
    simp_all [ErasableProofEntry.erase, SubTraceInvariant.invariant, ExecEntryT.Confidential]
    grind[canFlowTrans]
  unfold confidentialMessageSentAt
  let entry : ExecEntryT := (ExecEntryT.Confidential sender receiver msg)
  have h_at?_x : tr.at? x = some entry := by assumption
  -- TODO: make this a reusable theorem? (also needed for receiveConfidential)
  have h_erase_at?_x : tr.erase.at? x = some entry := by
    simp[Trace.at?_eq_some] at h_at?_x
    simp[Trace.at?_eq_some, Trace.erase_at, ProofTrace.Entry.erase_eq_imp_exists, ErasableProofEntry.erase]
    grind
  grind

@[instance]
public
theorem receiveConfidential.proof
  [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant]
  [BytesInvariants] [BytesInvariantsProofs]
  [CommunicationEventPredicates]
  [ExecTraceTypes.Has ExecEntryT]
  [ExecTraceTypes.Has Compromise.ExecEntryT]
  [ProofTraceTypes.Has ProofEntryT]
  [TraceInvariant.Has ProofEntryT]
  (sender receiver : Participant)
  (handle: Nat)
  : HoareTriple
    (receiveConfidential sender receiver handle)
    (fun _ => True)
    (fun _msg _tr => True)
:= by
  apply HoareTriple.mk
  unfold receiveConfidential
  -- getEntry
  step
  -- get postcondition of getEntry
  have h_entry : ∃ proofEntry:ProofEntryT,
      entry = ErasableProofEntry.erase proofEntry ∧
      SubTraceInvariant.invariant (tr.prefix handle) proofEntry ∧
      tr.at? handle = some proofEntry := by grind
  have entry_at_handle : tr.erase.at? handle = some entry := by
    simp[Trace.at?_eq_some, ErasableProofEntry.erase] at h_entry
    simp[Trace.at?_eq_some, Trace.erase_at, ProofTrace.Entry.erase_eq_imp_exists, ErasableProofEntry.erase]
    grind
  clear h_entry
  -- clear postcondition
  rename_i p; clear p
  -- guard
  step
  -- pure
  step
  trivial

end Proof


section Reachability


section

variable
  [ExecTraceTypes]
  [ExecTraceTypes.Has Compromise.ExecEntryT]

omit [BytesFunctor]

-- compromisedProtocolRun_preservesReachability needs postcondition of compromiseParticipant
public
theorem compromiseParticipant.preservesReachability
  (config : ReachabilityConfig)
  (alice : Participant)
  : (compromiseParticipant alice).PreservesReachability config (fun _x => True) (fun _out tr => participantCompromised tr alice) := by
  dsimp only [compromiseParticipant, Traceful.PreservesReachability]
  intro tr h_reach h_pre
  simp[participantCompromised, participantCompromisedAt]
  apply ProtocolEvent.logEvent.preservesReachability
  . assumption
  . trivial
section

end


variable
  [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant]
  [BytesInvariants] [BytesInvariantsProofs]
  [CommunicationEventPredicates]
  [ExecTraceTypes.Has ExecEntryT] [ ExecTraceTypes.Has Compromise.ExecEntryT]
  [ProofTraceTypes.Has ProofEntryT] [ProofTraceTypes.Has Compromise.ProofEntryT]
  [TraceInvariant.Has ProofEntryT]  [TraceInvariant.Has Compromise.ProofEntryT]
  [BaseAttackerKnowledge] [AttackerKnowledge]

@[expose] public section
-- using abbrev instead of def allows these to be unfolded by simp

abbrev sendConfidentialAttacker.reachability: ReachabilityConfig where
  Input := Participant × Participant × Bytes
  PreCond input tr := participantCompromised tr input.fst ∧ input.snd.snd.AttackerKnows tr
  step input := ⟨ _, sendConfidentialAttacker input.fst input.snd.fst input.snd.snd ⟩

abbrev receiveConfidential.reachability: ReachabilityConfig where
  Input := Participant × Participant × Nat
  PreCond _input _tr := True
  step input := ⟨ _, receiveConfidential input.fst input.snd.fst input.snd.snd ⟩

abbrev compromiseParticipant.reachability: ReachabilityConfig := .make (fun (participant) => compromiseParticipant participant)


-- analogous to LongTermKeys
public
def reachability.internal (i:Fin 3) : ReachabilityConfig := match i with
      | 0 => compromiseParticipant.reachability
      | 1 => receiveConfidential.reachability
      | 2 => sendConfidentialAttacker.reachability
end

@[expose]
public
def reachability : ReachabilityConfig :=
  .combine reachability.internal

-- required in order to use the individual configs directly
public instance: ReachabilityConfig.HasStep compromiseParticipant.reachability reachability := inferInstanceAs <| ReachabilityConfig.HasStep (reachability.internal 0) (.combine (reachability.internal))
public instance: ReachabilityConfig.HasStep receiveConfidential.reachability reachability := inferInstanceAs <| ReachabilityConfig.HasStep (reachability.internal 1) (.combine (reachability.internal))
public instance: ReachabilityConfig.HasStep sendConfidentialAttacker.reachability reachability := inferInstanceAs <| ReachabilityConfig.HasStep (reachability.internal 2) (.combine (reachability.internal))


variable
  [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant]
  [BytesInvariants] [BytesInvariantsProofs]
  [CommunicationEventPredicates]
  [ExecTraceTypes.Has ExecEntryT]
  [ExecTraceTypes.Has Compromise.ExecEntryT]
  [ProofTraceTypes.Has ProofEntryT]
  [ProofTraceTypes.Has Compromise.ProofEntryT]
  [TraceInvariant.Has ProofEntryT]
  [TraceInvariant.Has Compromise.ProofEntryT]
  [BaseAttackerKnowledge]
  [BaseAttackerKnowledgeTheorem]
  [AttackerKnowledgeTheorem]

public instance: ReachableImpliesInvariant compromiseParticipant.reachability where
  pf input := by
    let participant := input
    apply HoareTriple.mk
    let pf := (compromiseParticipant.proof participant).pf
    unfold hoareTriple at *
    unfold compromiseParticipant.reachability
    simp
    simp at pf
    intro tr h_inv
    let ⟨ trp, pf ⟩ := pf tr h_inv
    refine ⟨ trp, ?_ ⟩
    grind

public instance: ReachableImpliesInvariant receiveConfidential.reachability where
  pf input := by
    have ⟨ sender, receiver, handle ⟩ := input
    apply HoareTriple.mk
    let pf := (receiveConfidential.proof sender receiver handle).pf
    unfold hoareTriple at *
    unfold receiveConfidential.reachability
    simp
    simp at pf
    simp[wp]
    simp[wp] at pf
    grind[Bytes.AttackerKnows_implies_Publishable]

public instance: ReachableImpliesInvariant sendConfidentialAttacker.reachability where
  pf input := by
    have ⟨ sender, receiver, payload ⟩ := input
    apply HoareTriple.mk
    let pf := (sendConfidentialAttacker.proof sender receiver payload).pf
    unfold hoareTriple at *
    unfold sendConfidentialAttacker.reachability
    simp
    simp at pf
    simp[wp]
    simp[wp] at pf
    grind[Bytes.AttackerKnows_implies_Publishable]

public instance: ∀ i, ReachableImpliesInvariant (reachability.internal i)
  | 0 => inferInstanceAs <| ReachableImpliesInvariant compromiseParticipant.reachability
  | 1 => inferInstanceAs <| ReachableImpliesInvariant receiveConfidential.reachability
  | 2 => inferInstanceAs <| ReachableImpliesInvariant sendConfidentialAttacker.reachability

public instance: ReachableImpliesInvariant (reachability) := inferInstanceAs (ReachableImpliesInvariant (.combine reachability.internal))

end


end Reachability

end DY.Communication.Confidential
