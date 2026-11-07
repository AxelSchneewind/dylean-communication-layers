module

public import DY.Trace
public import DY.Bytes
public import DY.Actions.PersistentLocalState
import DY.Meta.Step

namespace DY.Communication


-- wrapper around getEntry with stronger postcondition
-- TODO: find a better solution
public
def getEntryStronger
  [ExecTraceTypes] {EntryT: Type} [ExecTraceTypes.Has EntryT]
  (timestamp: Nat)
  : Traceful EntryT
:=
  Traceful.mk (fun tr =>
    let result := tr.at? timestamp
    (result, ⟨ tr, by grind ⟩ )
  )

@[instance]
public
theorem getEntryStronger.spec
  [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant]
  {ExecEntryT ProofEntryT: Type}
  [ExecEntryAssociatedWithProofEntry ExecEntryT ProofEntryT]
  [ErasableProofEntry ExecEntryT ProofEntryT]
  [SubTraceInvariant ProofEntryT]
  [ExecTraceTypes.Has ExecEntryT]
  [ProofTraceTypes.Has ProofEntryT]
  [TraceInvariant.Has ProofEntryT]
  (timestamp: Nat)
  : HoareTriple
    (getEntryStronger timestamp: Traceful ExecEntryT)
    (fun _ => True)
    (fun entry tr =>
      ∃ proofEntry: ProofEntryT,
      entry = ErasableProofEntry.erase proofEntry ∧
      SubTraceInvariant.invariant (tr.prefix timestamp) proofEntry ∧
      tr.at? timestamp = some proofEntry
    )
:= by
  apply HoareTriple.mk
  simp only [hoareTriple, wp, getEntryStronger, Traceful.run_mk]
  intro trProof h_pre h_inv
  exists trProof
  split
  · grind
  simp only [h_inv, Trace.le_refl, and_true]
  let x : ExecEntryT := by assumption
  obtain heq : (tr_proof'.erase).at? timestamp = some x := by assumption
  cases h: (tr_proof'.at? timestamp: Option ProofEntryT)
  · simp_all [ProofTrace.Entry.at?_eq_none_erase]
  let proofEntry : ProofEntryT := by assumption
  exists proofEntry
  have := ProofTrace.Entry.at?_eq_some_erase tr_proof' timestamp proofEntry h
  constructor
  · grind
  rewrite [← TraceInvariant.Has.inv_commutes]
  grind [Trace.at?_eq_some, Trace.invariant_at]


public
theorem getEntryStronger.preservesReachability
  [ExecTraceTypes]
  {ExecEntryT: Type}
  [ExecTraceTypes.Has ExecEntryT]
  (config: ReachabilityConfig)
  (timestamp: Nat)
  : Traceful.PreservesReachability config
    (getEntryStronger timestamp: Traceful ExecEntryT)
    (fun _ => True)
    (fun entry tr => tr.at? timestamp = some entry)
:= by
  simp only [Traceful.PreservesReachability, Traceful.PreservesReachabilityFrom, getEntryStronger, Traceful.run_mk]
  grind

variable [BytesFunctor]

section Execution

namespace Compromise

public
structure ParticipantCompromiseEvent where
  participant: Participant

#combine into ExecEntryT, baseAttackerKnowledge from ProtocolEvent ParticipantCompromiseEvent

end Compromise

public
structure ExecEntryT where
  payload : Bytes
  sender : Participant
  receiver : Participant

-- constructors
@[simp, grind]
public
def ExecEntryT.Authenticated (sender receiver : Participant) (payload : Bytes) : ExecEntryT := { payload, sender, receiver}

public
def baseAttackerKnowledge [ExecTraceTypes]: SubBaseAttackerKnowledge ExecEntryT where
  attackerKnows _ entry msg := entry.payload = msg -- ∧ ¬entry.is_Confidential ∨ (participantCompromised receiver)


public
def compromiseParticipant
  [ExecTraceTypes]
  [ExecTraceTypes.Has Compromise.ExecEntryT]
  (participant : Participant): Traceful Unit := do
  ProtocolEvent.logEvent (Compromise.ParticipantCompromiseEvent.mk participant)


public
def sendMessageAuthenticated
  [ExecTraceTypes] [ExecTraceTypes.Has ExecEntryT]
  (sender receiver : Participant) (msg: Bytes): Traceful Nat :=
  do
  let entry: ExecEntryT := ExecEntryT.Authenticated sender receiver msg
  appendEntry entry

public
def receiveMessageAuthenticated
  [ExecTraceTypes] [ExecTraceTypes.Has ExecEntryT]
  (sender : Participant) (handle: Nat): Traceful Bytes :=
  do
  let entry: ExecEntryT ← getEntryStronger handle
  guard (entry.sender = sender)
  return entry.payload

-- could add definitions like MessageSentAt from Network.lean


public
def authenticatedMessageSentAt
  [ExecTraceTypes]
  [ExecTraceTypes.Has ExecEntryT]
  (tr : ExecTrace) (sender receiver : Participant) (bytes : Bytes) (i : Nat) :=
      tr.at? i = some (ExecEntryT.mk bytes sender receiver)

@[expose]
public
def authenticatedMessageSent
  [ExecTraceTypes]
  [ExecTraceTypes.Has ExecEntryT]
  (tr : ExecTrace) (sender receiver : Participant) (bytes : Bytes) :=
      exists i, authenticatedMessageSentAt tr sender receiver bytes i

public
theorem authenticatedMessageSentAt_later
  [ExecTraceTypes]
  [ExecTraceTypes.Has ExecEntryT]
  (tr1 tr2 : ExecTrace) (sender receiver : Participant) (bytes : Bytes) (i : Nat) :
    tr1 ≤ tr2
    → authenticatedMessageSentAt tr1 sender receiver bytes i
    → authenticatedMessageSentAt tr2 sender receiver bytes i
  := by
    unfold authenticatedMessageSentAt
    grind[Trace.at?_le]

public
theorem authenticatedMessageSent_later
  [ExecTraceTypes]
  [ExecTraceTypes.Has ExecEntryT]
  (tr1 tr2 : ExecTrace) (sender receiver : Participant) (bytes : Bytes) :
    tr1 ≤ tr2
    → authenticatedMessageSent tr1 sender receiver bytes
    → authenticatedMessageSent tr2 sender receiver bytes
  := by
    unfold authenticatedMessageSent
    intro le sent1
    let later := authenticatedMessageSentAt_later tr1 tr2 sender receiver bytes
    grind


public
def participantCorrupted
  [ExecTraceTypes]
  [ExecTraceTypes.Has Compromise.ExecEntryT]
  (tr : ExecTrace) (participant : Participant) : Prop
    := tr.EventLogged (Compromise.ParticipantCompromiseEvent.mk participant)


end Execution

section Proof

namespace Compromise

public instance
  [ExecTraceTypes] [ProofTraceTypes]
  : ProtocolEvent.EventInv ParticipantCompromiseEvent
  where
    invariant _ _ := True

#combine into ProofEntryT, SubTraceInvariant, SubBaseAttackerKnowledgeTheorem from
  ProtocolEvent ParticipantCompromiseEvent

end Compromise

public
abbrev ProofEntryT := ExecEntryT

public
instance: ErasableProofEntry ExecEntryT ProofEntryT := ErasableProofEntry.default ExecEntryT

public
instance: ExecEntryAssociatedWithProofEntry ExecEntryT ProofEntryT where

-- TODO: where to put this theorem?
-- needed for isCorrupt_later
omit [BytesFunctor] in
public theorem
participantCorrupted_later
  [ExecTraceTypes]
  [ExecTraceTypes.Has Compromise.ExecEntryT]
  (tr1 tr2 : ExecTrace) (participant : Participant) :
    tr1 ≤ tr2 → participantCorrupted tr1 participant → participantCorrupted tr2 participant
  := by
    unfold participantCorrupted
    grind

public
class HigherLevelInvariants [BytesFunctor] [ExecTraceTypes] [ProofTraceTypes] where
  authenticated : ProofTrace → Participant → Participant → Bytes → Prop

  authenticated_later : ∀ tr1 tr2 sender receiver payload,
    tr1 ≤ tr2 → authenticated tr1 sender receiver payload →
    authenticated tr2 sender receiver payload

grind_pattern [grind_later] HigherLevelInvariants.authenticated_later =>
tr1 ≤ tr2, HigherLevelInvariants.authenticated tr1 sender receiver payload


public
instance
  [ExecTraceTypes] [ProofTraceTypes] [BytesInvariants]
  [user_inv : HigherLevelInvariants]
  : SubTraceInvariant ProofEntryT
where
  invariant tr entry :=
    entry.payload.Publishable tr
    ∧ user_inv.authenticated tr entry.sender entry.receiver entry.payload
  -- TODO: user-defined invariant, no events for now
  -- see DyLibraries/COmmunication/Core/Invariants
  -- TODO: event for participant-corruption

public
instance baseAttackerKnowledgeTheorem
  [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant] [BytesInvariants]
  [HigherLevelInvariants]
  [ExecTraceTypes.Has ExecEntryT]
  [ProofTraceTypes.Has ProofEntryT]
  [TraceInvariant.Has ProofEntryT]:
  SubBaseAttackerKnowledgeTheorem ProofEntryT baseAttackerKnowledge
where
  pf trBefore entry b := by
    intro invBefore attackerKnows
    simp [SubTraceInvariant.invariant, /-baseAttackerKnowledge, ErasableProofEntry.erase-/] at invBefore
    simp [/-SubTraceInvariant.invariant, -/baseAttackerKnowledge, ErasableProofEntry.erase] at attackerKnows
    rw [←attackerKnows]
    grind

@[instance]
theorem compromiseParticipant.proof
  [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant]
  [BytesInvariants] [BytesInvariantsProofs]
  [HigherLevelInvariants]
  [ExecTraceTypes.Has ExecEntryT]
  [ExecTraceTypes.Has Compromise.ExecEntryT]
  [ProofTraceTypes.Has ProofEntryT]
  [ProofTraceTypes.Has Compromise.ProofEntryT]
  [TraceInvariant.Has ProofEntryT]
  [TraceInvariant.Has Compromise.ProofEntryT]
  (participant: Participant)
  : HoareTriple (compromiseParticipant participant) (fun _ => True) (fun _ _ => True)
:= by
  unfold compromiseParticipant
  step by simp[ProtocolEvent.EventInv.invariant]
  trivial

@[instance]
public
theorem sendMessageAuthenticated.proof
  [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant]
  [BytesInvariants] [BytesInvariantsProofs]
  [HigherLevelInvariants]
  [ExecTraceTypes.Has ExecEntryT]
  [ProofTraceTypes.Has ProofEntryT]
  [TraceInvariant.Has ProofEntryT]
  (sender receiver: Participant)
  (msg: Bytes)
  : HoareTriple
    (sendMessageAuthenticated sender receiver msg)
    (fun tr => msg.Publishable tr ∧ HigherLevelInvariants.authenticated tr sender receiver msg)
    (fun _ _ => True)
:= by
  apply HoareTriple.mk
  unfold sendMessageAuthenticated
  dsimp only
  step with ⟨ fun _ => ExecEntryT.Authenticated sender receiver msg ⟩ by
    simp_all [ErasableProofEntry.erase, SubTraceInvariant.invariant, ExecEntryT.Authenticated]
  trivial

@[instance]
public
theorem receiveMessageAuthenticated.proof
  [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant]
  [BytesInvariants] [BytesInvariantsProofs]
  [HigherLevelInvariants]
  [ExecTraceTypes.Has ExecEntryT]
  [ExecTraceTypes.Has Compromise.ExecEntryT]
  [ProofTraceTypes.Has ProofEntryT]
  [TraceInvariant.Has ProofEntryT]
  (sender : Participant)
  (handle: Nat)
  : HoareTriple
    (receiveMessageAuthenticated sender handle)
    (fun _ => True)
    (fun msg tr =>
      msg.Publishable tr ∧
      (
        ∃ receiver', tr.erase.at? handle = some (ExecEntryT.mk msg sender receiver')
        ∨ participantCorrupted tr.erase sender
      )
    )
:= by
  apply HoareTriple.mk
  unfold receiveMessageAuthenticated
  step
  have: entry.payload.Publishable tr := by simp_all [ErasableProofEntry.erase, SubTraceInvariant.invariant]; grind
  rename_i h_entry
  -- FIXME: how to get this proposition from getEntry call? postcondition not strong enough
  have entry_at_handle : tr.erase.at? handle = some entry := by
    simp[Trace.at?_eq_some, ErasableProofEntry.erase] at h_entry
    simp[Trace.at?_eq_some, Trace.erase_at, ProofTrace.Entry.erase_eq_imp_exists, ErasableProofEntry.erase]
    grind
  -- h_entry has to be cleared to avoid monotonization error
  clear h_entry
  step
  rename_i entry_at_handle sender_match
  step
  rename_i h_receiver h_x
  constructor
  . grind
  . simp[h_x]
    have entry_at_handle : tr.erase.at? handle = some entry := by grind
    exact ⟨ entry.receiver, by left; grind[ExecEntryT] ⟩

end Proof


section Reachability

variable [ExecTraceTypes] [ExecTraceTypes.Has ExecEntryT] [ExecTraceTypes.Has Compromise.ExecEntryT]
variable [BaseAttackerKnowledge] [AttackerKnowledge]

public
abbrev reachability : ReachabilityConfig where
  Input := Participant × Participant × Bytes
  PreCond i tr := (i.snd.snd).AttackerKnows tr
  step i   := ⟨ _, sendMessageAuthenticated i.fst i.snd.fst i.snd.snd ⟩

public
theorem receiveMessageAuthenticated.preservesReachability
  [BaseAttackerKnowledge.Has baseAttackerKnowledge]
  (config: ReachabilityConfig)
  (sender : Participant)
  (msg_handle: Nat)
  : (receiveMessageAuthenticated sender msg_handle).PreservesReachability config (fun _ => True) (fun msg tr => msg.AttackerKnows tr)
:= by
  dsimp only [receiveMessageAuthenticated, Traceful.PreservesReachability]
  intro tr h_reach h_pre
  apply Traceful.PreservesReachabilityFrom_bind
  · apply getEntryStronger.preservesReachability
  · grind
  · grind
  intro entry tr h_post h_reach h_le

  apply Traceful.PreservesReachabilityFrom_bind
  by_cases h:(entry.sender = some sender)
  . simp [guard,h]
    simp [Traceful.PreservesReachability, Traceful.PreservesReachabilityFrom /-, Traceful.run_mk-/]
    sorry
  . simp [guard,h]
    simp [Traceful.PreservesReachability, Traceful.PreservesReachabilityFrom/-, Traceful.run_mk-/]
    sorry
  · grind
  apply Traceful.PreservesReachabilityFrom_pure
  · sorry

  apply Bytes.AttackerKnows.prove_from_base
  apply Trace.prove_BaseAttackerKnows baseAttackerKnowledge tr entry entry.payload msg_handle
  · grind
  simp [baseAttackerKnowledge]
  exact reachability

  sorry
  sorry



variable [ProofTraceTypes] [TraceInvariant]
variable [BytesInvariants] [BytesInvariantsProofs]
variable [HigherLevelInvariants]
variable [ProofTraceTypes.Has ProofEntryT] [TraceInvariant.Has ProofEntryT]
variable [BaseAttackerKnowledgeTheorem] [AttackerKnowledgeTheorem]

public
instance: ReachableImpliesInvariant reachability
where
  pf input := by
    have ⟨ sender, payload ⟩ := input
    apply HoareTriple.mk
    have := (sendMessageAuthenticated.proof sender receiver payload).pf
    unfold hoareTriple at *
    grind [Bytes.AttackerKnows_implies_Publishable]

end Reachability

end DY.Communication
