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

@[expose, simp]
public
def authenticatedMessageSent
  [ExecTraceTypes]
  [ExecTraceTypes.Has ExecEntryT]
  (tr : ExecTrace) (sender receiver : Participant) (bytes : Bytes) :=
      exists i, authenticatedMessageSentAt tr sender receiver bytes i

public
theorem authenticatedMessageSentAt_le
  [ExecTraceTypes]
  [ExecTraceTypes.Has ExecEntryT]
  (tr1 tr2 : ExecTrace) (sender receiver : Participant) (bytes : Bytes) (i : Nat) :
    tr1 ≤ tr2
    → authenticatedMessageSentAt tr1 sender receiver bytes i
    → authenticatedMessageSentAt tr2 sender receiver bytes i
  := by
    unfold authenticatedMessageSentAt
    grind[Trace.at?_le]

grind_pattern [grind_later] authenticatedMessageSentAt_le =>
tr1 ≤ tr2, authenticatedMessageSentAt_le tr1 tr2 sender receiver bytes i

public
theorem authenticatedMessageSentAt_le'
  [ExecTraceTypes]
  [ExecTraceTypes.Has Communication.ExecEntryT]
  (tr1 tr2 : ExecTrace) (sender receiver : Participant) (bytes : Bytes) (i : Nat)
    : tr1 ≤ tr2
    → Communication.authenticatedMessageSentAt tr2 sender receiver bytes i
    → i < tr1.length
    → Communication.authenticatedMessageSentAt tr1 sender receiver bytes i
    := by
      unfold authenticatedMessageSentAt
      grind[Trace.at?_eq_some]


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
    let later := authenticatedMessageSentAt_le tr1 tr2 sender receiver bytes
    grind

grind_pattern [grind_later] authenticatedMessageSent_later =>
tr1 ≤ tr2, authenticatedMessageSent_later tr1 tr2 sender receiver bytes


public
def participantCorrupted
  [ExecTraceTypes]
  [ExecTraceTypes.Has Compromise.ExecEntryT]
  (tr : ExecTrace) (participant : Participant) : Prop
    := tr.EventLogged (Compromise.ParticipantCompromiseEvent.mk participant)

omit [BytesFunctor]
public
theorem participantCorrupted_later
  [ExecTraceTypes]
  [ExecTraceTypes.Has Compromise.ExecEntryT]
  (tr1 tr2 : ExecTrace) (participant : Participant) :
    tr1 ≤ tr2 → participantCorrupted tr1 participant → participantCorrupted tr2 participant
    := by
      unfold participantCorrupted
      grind

grind_pattern [grind_later] participantCorrupted_later =>
tr1 ≤ tr2, participantCorrupted_later tr1 tr2 participant


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

public
class HigherLayerInvariants [BytesFunctor] [ExecTraceTypes] [ProofTraceTypes] where
  authenticated : ProofTrace → Participant → Participant → Bytes → Prop

  authenticated_later : ∀ tr1 tr2 sender receiver payload,
    tr1 ≤ tr2 → authenticated tr1 sender receiver payload →
    authenticated tr2 sender receiver payload

grind_pattern [grind_later] HigherLayerInvariants.authenticated_later =>
tr1 ≤ tr2, HigherLayerInvariants.authenticated tr1 sender receiver payload


-- entry invariant
public
instance
  [ExecTraceTypes] [ProofTraceTypes] [BytesInvariants]
  [user_inv : HigherLayerInvariants]
  : SubTraceInvariant ProofEntryT
where
  invariant tr entry :=
    -- TODO: use IsWellFormed Bytes.Publishable instead?
    Bytes.Publishable entry.payload tr
    ∧ user_inv.authenticated tr entry.sender entry.receiver entry.payload

public
theorem authenticatedMessageSentAt_imp_higher_layer_invariants
  [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant] [BytesInvariants]
  [HigherLayerInvariants]
  [ExecTraceTypes.Has ExecEntryT] [ProofTraceTypes.Has ProofEntryT]
  [TraceInvariant.Has ProofEntryT]
  (sender receiver: Participant) (bytes: Bytes)
  (i: Nat)
  (tr: ProofTrace)
  : tr.Invariant →
    authenticatedMessageSentAt tr.erase sender receiver bytes i →
    HigherLayerInvariants.authenticated (tr.prefix i) sender receiver bytes
:= by
  intro h_inv h_ev
  have := Trace.invariant_at tr i (by grind [authenticatedMessageSentAt]) h_inv
  suffices SubTraceInvariant.invariant (tr.prefix i) ({sender, receiver, payload:=bytes}:ExecEntryT) by
    simp_all [SubTraceInvariant.invariant]
  rewrite [← TraceInvariant.Has.inv_commutes]
  simp [authenticatedMessageSentAt, Trace.at?_eq_some, Trace.erase_at, ProofTrace.Entry.erase_eq_imp_exists, ErasableProofEntry.erase] at h_ev
  grind


public
instance baseAttackerKnowledgeTheorem
  [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant] [BytesInvariants]
  [HigherLayerInvariants]
  [ExecTraceTypes.Has ExecEntryT]
  [ProofTraceTypes.Has ProofEntryT]
  [TraceInvariant.Has ProofEntryT]:
  SubBaseAttackerKnowledgeTheorem ProofEntryT baseAttackerKnowledge
where
  pf trBefore entry b := by
    intro invBefore attackerKnows
    simp [SubTraceInvariant.invariant] at invBefore
    simp [baseAttackerKnowledge, ErasableProofEntry.erase] at attackerKnows
    rw [←attackerKnows]
    grind

@[instance]
theorem compromiseParticipant.proof
  [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant]
  [BytesInvariants] [BytesInvariantsProofs]
  [HigherLayerInvariants]
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
  [HigherLayerInvariants]
  [ExecTraceTypes.Has ExecEntryT]
  [ProofTraceTypes.Has ProofEntryT]
  [TraceInvariant.Has ProofEntryT]
  (sender receiver: Participant)
  (msg: Bytes)
  : HoareTriple
    (sendMessageAuthenticated sender receiver msg)
    (fun tr => msg.Publishable tr
      -- has to be ensured by higher layer
      ∧ HigherLayerInvariants.authenticated tr sender receiver msg)
    (fun i tr => authenticatedMessageSentAt tr.erase sender receiver msg i)
:= by
  apply HoareTriple.mk
  unfold sendMessageAuthenticated
  dsimp only
  -- appendEntry
  step with ⟨ fun _ => ExecEntryT.Authenticated sender receiver msg ⟩ by
    simp_all [ErasableProofEntry.erase, SubTraceInvariant.invariant, ExecEntryT.Authenticated]
  unfold authenticatedMessageSentAt
  let entry : ExecEntryT := (ExecEntryT.Authenticated sender receiver msg)
  have h_at?_x : tr.at? x = some entry := by assumption
  -- TODO: make this a reusable theorem? (also needed for receiveMessageAuthenticated)
  have h_erase_at?_x : tr.erase.at? x = some entry := by
    simp[Trace.at?_eq_some] at h_at?_x
    simp[Trace.at?_eq_some, Trace.erase_at, ProofTrace.Entry.erase_eq_imp_exists, ErasableProofEntry.erase]
    grind
  grind

@[instance]
public
theorem receiveMessageAuthenticated.proof
  [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant]
  [BytesInvariants] [BytesInvariantsProofs]
  [HigherLayerInvariants]
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
      ((∃ receiver', authenticatedMessageSentAt tr.erase sender receiver' msg handle) ∨ participantCorrupted tr.erase sender)
    )
:= by
  apply HoareTriple.mk
  unfold receiveMessageAuthenticated
  -- getEntry
  step
  have: entry.payload.Publishable tr := by simp_all [ErasableProofEntry.erase, SubTraceInvariant.invariant]; grind
  rename_i h_entry
  have entry_at_handle : tr.erase.at? handle = some entry := by
    simp[Trace.at?_eq_some, ErasableProofEntry.erase] at h_entry
    simp[Trace.at?_eq_some, Trace.erase_at, ProofTrace.Entry.erase_eq_imp_exists, ErasableProofEntry.erase]
    grind
  clear h_entry
  -- guard
  step
  rename_i entry_at_handle sender_match
  -- pure
  step
  rename_i h_receiver h_x
  constructor
  . grind
  . simp[h_x]
    have entry_at_handle : tr.erase.at? handle = some entry := by grind
    exact Or.inl ⟨ entry.receiver, by grind[authenticatedMessageSentAt, ExecEntryT] ⟩

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
  . simp [guard]
    simp [Traceful.PreservesReachability, Traceful.PreservesReachabilityFrom /-, Traceful.run_mk-/]
    sorry
  . simp [guard]
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
variable [HigherLayerInvariants]
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
