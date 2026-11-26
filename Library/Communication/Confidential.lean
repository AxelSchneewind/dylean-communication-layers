module

public import DY.Trace
public import DY.Bytes
public import DY.Label.Basic
public import DY.Actions.PersistentLocalState
import DY.Meta.Step

import all DY.Trace.Invariant

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
  deriving DecidableEq

public
instance [Repr Bytes] : Repr ExecEntryT where
  reprPrec e _ := "communication: " ++ (repr e.payload) ++ " (" ++ e.sender ++ " → " ++ e.receiver ++ ")"

-- Differs from authenticated
public
def baseAttackerKnowledge [ExecTraceTypes] [ExecTraceTypes.Has Compromise.ExecEntryT]: SubBaseAttackerKnowledge ExecEntryT where
  attackerKnows tr entry msg := entry.payload = msg ∧ (participantCompromised tr entry.receiver)


variable [ExecTraceTypes] [ExecTraceTypes.Has ExecEntryT]

-- Still add attacker function here that does not require higher layer predicates
-- and requires message to be known?
-- How about receive? Attacker can learn from trace entry after compromising.
public
def sendConfidentialAttacker (sender receiver : Participant) (msg: Bytes): Traceful Nat := do
  let entry := ({sender, receiver, payload:=msg}: ExecEntryT)
  appendEntry entry

public
def sendConfidential (sender receiver : Participant) (msg: Bytes): Traceful Nat := do
  let entry := ({sender, receiver, payload:=msg}: ExecEntryT)
  appendEntry entry

public
def receiveConfidential (_sender receiver : Participant) (handle: Nat): Traceful Bytes :=
  do
  let entry: ExecEntryT ← getEntryExtended handle
  -- differs from authenticated
  guard (entry.receiver = receiver)
  return entry.payload

-- definitions like MessageSentAt from Network.lean
@[expose]
public
def confidentialMessageSentAt (tr : ExecTrace) (sender receiver : Participant) (bytes : Bytes) (i : Nat) :=
  tr.at? i = some (ExecEntryT.mk bytes sender receiver)

@[expose, simp]
public
def confidentialMessageSent (tr : ExecTrace) (sender receiver : Participant) (bytes : Bytes) :=
  exists i, confidentialMessageSentAt tr sender receiver bytes i

public
theorem confidentialMessageSentAt_le (tr1 tr2 : ExecTrace) (sender receiver : Participant) (bytes : Bytes) (i : Nat)
  : tr1 ≤ tr2
    → confidentialMessageSentAt tr1 sender receiver bytes i
    → confidentialMessageSentAt tr2 sender receiver bytes i
  := by
    unfold confidentialMessageSentAt
    grind[Trace.at?_le]

grind_pattern [grind_later] confidentialMessageSentAt_le =>
tr1 ≤ tr2, confidentialMessageSentAt tr1 sender receiver bytes i

public
theorem confidentialMessageSentAt_le' (tr1 tr2 : ExecTrace) (sender receiver : Participant) (bytes : Bytes) (i : Nat)
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
theorem confidentialMessageSent_le (tr1 tr2 : ExecTrace) (sender receiver : Participant) (bytes : Bytes)
  : tr1 ≤ tr2
    → confidentialMessageSent tr1 sender receiver bytes
    → confidentialMessageSent tr2 sender receiver bytes
  := by
    unfold confidentialMessageSent
    have := confidentialMessageSentAt_le tr1 tr2 sender receiver bytes
    grind[confidentialMessageSentAt_le]

grind_pattern [grind_later] confidentialMessageSent_le =>
tr1 ≤ tr2, confidentialMessageSent tr1 sender receiver bytes

variable [ExecTraceTypes.Has Compromise.ExecEntryT]
omit [BytesFunctor]

public
theorem participantCompromisedAt_le
    (tr1 tr2 : ExecTrace) (participant : Participant) (i : Nat)
  : tr1 ≤ tr2
    → participantCompromisedAt tr1 participant i → participantCompromisedAt tr2 participant i
  := by
    unfold participantCompromisedAt
    grind

grind_pattern [grind_later] participantCompromisedAt_le =>
tr1 ≤ tr2, participantCompromisedAt tr1 participant i


public
theorem participantCompromised_le
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
class CommunicationInvariants [BytesFunctor] [ExecTraceTypes] [ProofTraceTypes] where
  confidential : ProofTrace → Participant → Participant → Bytes → Prop

  confidential_later : ∀ tr1 tr2 sender receiver payload,
    tr1 ≤ tr2 → confidential tr1 sender receiver payload →
    confidential tr2 sender receiver payload

grind_pattern [grind_later] CommunicationInvariants.confidential_later =>
tr1 ≤ tr2, CommunicationInvariants.confidential tr1 sender receiver payload


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
  [CommunicationInvariants]
  : SubTraceInvariant ProofEntryT
where
  invariant tr entry :=
      -- TODO: allow transfer of publishable messages. Then invariant does not hold.
      -- this has to be handled here in order for attacker send function to work.
      entry.payload.Publishable tr
    ∨ (entry.payload.Invariant tr
    ∧ (entry.payload.label tr).canFlow (CommunicationLabel entry.receiver) tr.erase
    ∧ (CommunicationInvariants.confidential tr entry.sender entry.receiver entry.payload))



-- if attacker learns bytes from entry,
-- then the bytes must be publishable
public
instance baseAttackerKnowledgeTheorem
  [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant] [BytesInvariants]
  [CommunicationInvariants]
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
      obtain ⟨ pub, invBefore ⟩ := invBefore
      . grind
      . have : (entry.payload.label trBefore).canFlow (CommunicationLabel entry.receiver) tr := by grind
        grind[Label.canFlow]
      done

@[instance]
theorem compromiseParticipant.proof
  [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant]
  [BytesInvariants] [BytesInvariantsProofs]
  [CommunicationInvariants]
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
  [CommunicationInvariants]
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
  let entry : ExecEntryT := ({sender, receiver, payload:=msg}:ExecEntryT)
  step with ⟨ fun _ => entry ⟩ by
    simp_all [ErasableProofEntry.erase, SubTraceInvariant.invariant]
    grind
  unfold confidentialMessageSentAt
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
  [CommunicationInvariants]
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
    (fun tr => msg.Invariant tr
      -- has to be ensured by higher layer, mainly concerning message label
      ∧ (msg.label tr).canFlow (CommunicationLabel receiver) tr.erase
      ∧ CommunicationInvariants.confidential tr sender receiver msg)
    (fun i tr => confidentialMessageSentAt tr.erase sender receiver msg i)
:= by
  apply HoareTriple.mk
  unfold sendConfidential
  dsimp only
  -- appendEntry
  let entry : ExecEntryT := ({sender, receiver, payload:=msg}:ExecEntryT)
  step with ⟨ fun _ => entry ⟩ by
    simp_all [ErasableProofEntry.erase, SubTraceInvariant.invariant]
    grind
  unfold confidentialMessageSentAt
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
  [CommunicationInvariants]
  [ExecTraceTypes.Has ExecEntryT]
  [ExecTraceTypes.Has Compromise.ExecEntryT]
  [ProofTraceTypes.Has ProofEntryT]
  [ProofTraceTypes.Has Compromise.ProofEntryT]
  [TraceInvariant.Has ProofEntryT]
  [TraceInvariant.Has Compromise.ProofEntryT]
  (sender receiver : Participant)
  (handle: Nat)
  : HoareTriple
    (receiveConfidential sender receiver handle)
    (fun _ => True)
    (fun msg tr =>
      msg.Publishable tr ∨ (
        msg.Invariant tr ∧
        -- we don't know if the message actually came from the expected sender
        ∃ sender', CommunicationInvariants.confidential tr sender' receiver msg
      )
    )
:= by
  apply HoareTriple.mk
  unfold receiveConfidential
  -- getEntry
  step
  -- postcondition of getEntry
  have h_entry : ∃ proofEntry:ProofEntryT,
      entry = ErasableProofEntry.erase proofEntry ∧
      SubTraceInvariant.invariant (tr.prefix handle) proofEntry ∧
      tr.at? handle = some proofEntry := by grind
  obtain ⟨ proof_entry, h_entry ⟩ := h_entry
  have : proof_entry = entry := by
    simp[ErasableProofEntry.erase] at h_entry
    grind
  rename_i p; clear p
  have : tr.at? handle = some proof_entry := by grind
  clear h_entry
  -- guard
  step
  -- pure
  step
  have h_entry_at : tr.at? handle = some proof_entry := by assumption
  have entry_inv : SubTraceInvariant.invariant (tr.prefix handle) proof_entry := by
    let i := Trace.invariant_at tr handle (by grind) h
    rewrite[←TraceInvariant.Has.inv_commutes (ProofEntryT := ProofEntryT)]
    rewrite[TraceInvariant.Has.inv_commutes]
    grind[Trace.at?_eq_some, Trace.invariant_at, TraceInvariant.Has.inv_commutes]
  simp[SubTraceInvariant.invariant] at entry_inv
  obtain ⟨ pub, entry_inv ⟩ := entry_inv
  . grind
  . right
    refine ⟨ ?_, entry.sender, ?_ ⟩
    . grind
    . grind[CommunicationInvariants.confidential_later]


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
  (participant : Participant)
  : (compromiseParticipant participant).PreservesReachability config (fun _x => True) (fun _ tr => participantCompromised tr participant) := by
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
  [CommunicationInvariants]
  [ExecTraceTypes.Has ExecEntryT] [ ExecTraceTypes.Has Compromise.ExecEntryT]
  [ProofTraceTypes.Has ProofEntryT] [ProofTraceTypes.Has Compromise.ProofEntryT]
  [TraceInvariant.Has ProofEntryT]  [TraceInvariant.Has Compromise.ProofEntryT]
  [BaseAttackerKnowledge] [AttackerKnowledge]

@[expose]
public section
-- using abbrev instead of def allows these to be unfolded by simp

abbrev sendConfidentialAttacker.reachability: ReachabilityConfig where
  Input := Participant × Participant × Bytes
  PreCond input tr := input.snd.snd.AttackerKnows tr
  step input := ⟨ _, sendConfidentialAttacker input.fst input.snd.fst input.snd.snd ⟩

abbrev receiveConfidential.reachability: ReachabilityConfig where
  Input := Participant × Participant × Nat
  PreCond input tr := participantCompromised tr input.snd.fst
  step input := ⟨ _, receiveConfidential input.fst input.snd.fst input.snd.snd ⟩

abbrev compromiseParticipant.reachability: ReachabilityConfig := .make compromiseParticipant


-- analogous to LongTermKeys
def reachability.internal (i:Fin 3) : ReachabilityConfig := match i with
  | 0 => compromiseParticipant.reachability
  | 1 => receiveConfidential.reachability
  | 2 => sendConfidentialAttacker.reachability


def reachability : ReachabilityConfig :=
  .combine reachability.internal

end

-- required in order to use the individual configs directly
public instance: ReachabilityConfig.HasStep compromiseParticipant.reachability reachability := inferInstanceAs <| ReachabilityConfig.HasStep (reachability.internal 0) (.combine (reachability.internal))
public instance: ReachabilityConfig.HasStep receiveConfidential.reachability reachability := inferInstanceAs <| ReachabilityConfig.HasStep (reachability.internal 1) (.combine (reachability.internal))
public instance: ReachabilityConfig.HasStep sendConfidentialAttacker.reachability reachability := inferInstanceAs <| ReachabilityConfig.HasStep (reachability.internal 2) (.combine (reachability.internal))


variable
  [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant]
  [BytesInvariants] [BytesInvariantsProofs]
  [CommunicationInvariants]
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
