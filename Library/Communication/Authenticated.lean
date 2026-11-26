module

public import DY.Trace
public import DY.Bytes
public import DY.Actions.PersistentLocalState
import DY.Meta.Step

public import DyleanExtensions

namespace DY.Communication.Authenticated

variable [BytesFunctor]

section Execution

namespace Compromise

-- TODO: adjust identifier
public
structure CommunicationCompromiseEvent where
  participant: Participant
  deriving DecidableEq

#combine into ExecEntryT, baseAttackerKnowledge from ProtocolEvent CommunicationCompromiseEvent

#check ProtocolEvent.ExecEntryT CommunicationCompromiseEvent

end Compromise

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
def ExecEntryT.Authenticated (sender receiver : Participant) (payload : Bytes) : ExecEntryT := { payload, sender, receiver}

public
def baseAttackerKnowledge [ExecTraceTypes]: SubBaseAttackerKnowledge ExecEntryT where
  attackerKnows _ entry msg := entry.payload = msg -- ∧ ¬entry.is_Confidential ∨ (participantCompromised receiver)


public
def compromiseParticipant
  [ExecTraceTypes]
  [ExecTraceTypes.Has Compromise.ExecEntryT]
  (participant : Participant): Traceful Unit := do
  ProtocolEvent.logEvent (Compromise.CommunicationCompromiseEvent.mk participant)

public
def sendAuthenticatedAttacker
  [ExecTraceTypes] [ExecTraceTypes.Has ExecEntryT]
  (sender receiver : Participant) (msg: Bytes): Traceful Nat :=
  do
  let entry: ExecEntryT := ExecEntryT.Authenticated sender receiver msg
  appendEntry entry

public
def sendAuthenticated
  [ExecTraceTypes] [ExecTraceTypes.Has ExecEntryT]
  (sender receiver : Participant) (msg: Bytes): Traceful Nat :=
  do
  let entry: ExecEntryT := ExecEntryT.Authenticated sender receiver msg
  appendEntry entry

public
def receiveAuthenticated
  [ExecTraceTypes] [ExecTraceTypes.Has ExecEntryT]
  (sender : Participant) (handle: Nat): Traceful Bytes :=
  do
  let entry: ExecEntryT ← getEntryExtended handle
  guard (entry.sender = sender)
  return entry.payload

-- definitions like MessageSentAt from Network.lean
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
tr1 ≤ tr2, authenticatedMessageSentAt tr1 sender receiver bytes i

public
theorem authenticatedMessageSentAt_le'
  [ExecTraceTypes]
  [ExecTraceTypes.Has ExecEntryT]
  (tr1 tr2 : ExecTrace) (sender receiver : Participant) (bytes : Bytes) (i : Nat)
    : tr1 ≤ tr2
    → authenticatedMessageSentAt tr2 sender receiver bytes i
    → i < tr1.length
    → authenticatedMessageSentAt tr1 sender receiver bytes i
    := by
      unfold authenticatedMessageSentAt
      grind[Trace.at?_eq_some]

grind_pattern [grind_later] authenticatedMessageSentAt_le' =>
tr1 ≤ tr2, i < tr1.length, authenticatedMessageSentAt tr1 sender receiver bytes i

public
theorem authenticatedMessageSent_le
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

grind_pattern [grind_later] authenticatedMessageSent_le =>
tr1 ≤ tr2, authenticatedMessageSent tr1 sender receiver bytes


@[expose]
public
def participantCompromisedAt
  [ExecTraceTypes]
  [ExecTraceTypes.Has Compromise.ExecEntryT]
  (tr : ExecTrace) (participant : Participant) (i : Nat) : Prop
    := tr.EventLoggedAt (Compromise.CommunicationCompromiseEvent.mk participant) i

@[expose]
public
def participantCompromised
  [ExecTraceTypes]
  [ExecTraceTypes.Has Compromise.ExecEntryT]
  (tr : ExecTrace) (participant : Participant) : Prop
    := ∃i, participantCompromisedAt tr participant i

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
class CommunicationInvariants [BytesFunctor] [ExecTraceTypes] [ProofTraceTypes] where
  authenticated : ProofTrace → Participant → Participant → Bytes → Prop

  authenticated_later : ∀ tr1 tr2 sender receiver payload,
    tr1 ≤ tr2 → authenticated tr1 sender receiver payload →
    authenticated tr2 sender receiver payload

grind_pattern [grind_later] CommunicationInvariants.authenticated_later =>
tr1 ≤ tr2, CommunicationInvariants.authenticated tr1 sender receiver payload


-- entry invariant
public
instance
  [ExecTraceTypes] [ExecTraceTypes.Has Compromise.ExecEntryT]
  [ProofTraceTypes] [BytesInvariants]
  [CommunicationInvariants]
  : SubTraceInvariant ProofEntryT
where
  invariant tr entry :=
    -- TODO: use IsWellFormed Bytes.Publishable entry instead?
    Bytes.Publishable entry.payload tr ∧
    (CommunicationInvariants.authenticated tr entry.sender entry.receiver entry.payload ∨ participantCompromised tr.erase entry.sender)

public
theorem authenticatedMessageSentAt_imp_higher_layer_invariants
  [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant] [BytesInvariants]
  [CommunicationInvariants]
  [ExecTraceTypes.Has Compromise.ExecEntryT] [ProofTraceTypes.Has Compromise.ProofEntryT] [TraceInvariant.Has Compromise.ProofEntryT]
  [ExecTraceTypes.Has ExecEntryT] [ProofTraceTypes.Has ProofEntryT] [TraceInvariant.Has ProofEntryT]
  (sender receiver: Participant) (bytes: Bytes)
  (i: Nat)
  (tr: ProofTrace)
  : tr.Invariant →
    authenticatedMessageSentAt tr.erase sender receiver bytes i →
    (CommunicationInvariants.authenticated (tr.prefix i) sender receiver bytes ∨ participantCompromised (tr.erase.prefix i) sender)
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
    rw [←attackerKnows]
    grind

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
theorem sendAuthenticatedAttacker.proof
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
    (sendAuthenticatedAttacker sender receiver msg)
    (fun tr => msg.Publishable tr ∧ participantCompromised tr.erase sender)
    -- could probably drop the postcondition
    (fun i tr => authenticatedMessageSentAt tr.erase sender receiver msg i)
:= by
  apply HoareTriple.mk
  unfold sendAuthenticatedAttacker
  dsimp only
  -- appendEntry
  let entry := ({sender, receiver, payload:=msg} : ExecEntryT)
  step with ⟨ fun _ => entry ⟩ by
    simp_all [ErasableProofEntry.erase, SubTraceInvariant.invariant]
    grind
  unfold authenticatedMessageSentAt
  have h_at?_x : tr.at? x = some entry := by assumption
  -- TODO: make this a reusable theorem? (also needed for receiveAuthenticated)
  have h_erase_at?_x : tr.erase.at? x = some entry := by
    simp[Trace.at?_eq_some] at h_at?_x
    simp[Trace.at?_eq_some, Trace.erase_at, ProofTrace.Entry.erase_eq_imp_exists, ErasableProofEntry.erase]
    grind
  grind

@[instance]
public
theorem sendAuthenticated.proof
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
    (sendAuthenticated sender receiver msg)
    (fun tr => msg.Publishable tr
      -- has to be ensured by higher layer
      ∧ CommunicationInvariants.authenticated tr sender receiver msg)
    (fun i tr => authenticatedMessageSentAt tr.erase sender receiver msg i)
:= by
  apply HoareTriple.mk
  unfold sendAuthenticated
  dsimp only
  -- appendEntry
  let entry := ({sender, receiver, payload:=msg} : ExecEntryT)
  step with ⟨ fun _ => entry ⟩ by
    simp_all [ErasableProofEntry.erase, SubTraceInvariant.invariant]
    grind
  unfold authenticatedMessageSentAt
  have h_at?_x : tr.at? x = some entry := by assumption
  -- TODO: make this a reusable theorem? (also needed for receiveAuthenticated)
  have h_erase_at?_x : tr.erase.at? x = some entry := by
    simp[Trace.at?_eq_some] at h_at?_x
    simp[Trace.at?_eq_some, Trace.erase_at, ProofTrace.Entry.erase_eq_imp_exists, ErasableProofEntry.erase]
    grind
  grind

@[instance]
public
theorem receiveAuthenticated.proof
  [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant]
  [BytesInvariants] [BytesInvariantsProofs]
  [CommunicationInvariants]
  [ExecTraceTypes.Has ExecEntryT]
  [ExecTraceTypes.Has Compromise.ExecEntryT]
  [ProofTraceTypes.Has ProofEntryT]
  [TraceInvariant.Has ProofEntryT]
  (sender : Participant)
  (handle: Nat)
  : HoareTriple
    (receiveAuthenticated sender handle)
    (fun _ => True)
    (fun msg tr =>
      msg.Publishable tr ∧
      ((∃ receiver', authenticatedMessageSentAt tr.erase sender receiver' msg handle) ∨ participantCompromised tr.erase sender)
    )
:= by
  apply HoareTriple.mk
  unfold receiveAuthenticated
  -- getEntry
  step
  -- get postcondition of getEntry
  have h_entry : ∃ proofEntry:ProofEntryT,
      entry = ErasableProofEntry.erase proofEntry ∧
      SubTraceInvariant.invariant (tr.prefix handle) proofEntry ∧
      tr.at? handle = some proofEntry := by grind
  have: entry.payload.Publishable tr := by
    simp [ErasableProofEntry.erase, SubTraceInvariant.invariant] at h_entry
    grind
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
  constructor
  . grind
  . exact Or.inl ⟨ entry.receiver, by grind[authenticatedMessageSentAt, ExecEntryT] ⟩

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
  [CommunicationInvariants]
  [ExecTraceTypes.Has ExecEntryT] [ ExecTraceTypes.Has Compromise.ExecEntryT]
  [ProofTraceTypes.Has ProofEntryT] [ProofTraceTypes.Has Compromise.ProofEntryT]
  [TraceInvariant.Has ProofEntryT]  [TraceInvariant.Has Compromise.ProofEntryT]
  [BaseAttackerKnowledge] [AttackerKnowledge]

@[expose] public section
-- using abbrev instead of def allows these to be unfolded by simp

abbrev sendAuthenticatedAttacker.reachability: ReachabilityConfig where
  Input := Participant × Participant × Bytes
  PreCond input tr := participantCompromised tr input.fst ∧ input.snd.snd.AttackerKnows tr
  step input := ⟨ _, sendAuthenticatedAttacker input.fst input.snd.fst input.snd.snd ⟩

abbrev receiveAuthenticated.reachability: ReachabilityConfig where
  Input := Participant × Nat
  PreCond _input _tr := True
  step input := ⟨ _, receiveAuthenticated input.fst input.snd ⟩

abbrev compromiseParticipant.reachability: ReachabilityConfig := .make (fun (participant) => compromiseParticipant participant)


-- analogous to LongTermKeys
public
def reachability.internal (i:Fin 3) : ReachabilityConfig := match i with
      | 0 => compromiseParticipant.reachability
      | 1 => receiveAuthenticated.reachability
      | 2 => sendAuthenticatedAttacker.reachability
end

@[expose]
public
def reachability : ReachabilityConfig :=
  .combine reachability.internal

-- required in order to use the individual configs directly
public instance: ReachabilityConfig.HasStep compromiseParticipant.reachability reachability := inferInstanceAs <| ReachabilityConfig.HasStep (reachability.internal 0) (.combine (reachability.internal))
public instance: ReachabilityConfig.HasStep receiveAuthenticated.reachability reachability := inferInstanceAs <| ReachabilityConfig.HasStep (reachability.internal 1) (.combine (reachability.internal))
public instance: ReachabilityConfig.HasStep sendAuthenticatedAttacker.reachability reachability := inferInstanceAs <| ReachabilityConfig.HasStep (reachability.internal 2) (.combine (reachability.internal))


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

public instance: ReachableImpliesInvariant receiveAuthenticated.reachability where
  pf input := by
    have ⟨ sender, handle ⟩ := input
    apply HoareTriple.mk
    let pf := (receiveAuthenticated.proof sender handle).pf
    unfold hoareTriple at *
    unfold receiveAuthenticated.reachability
    simp
    simp at pf
    simp[wp]
    simp[wp] at pf
    grind[Bytes.AttackerKnows_implies_Publishable]

public instance: ReachableImpliesInvariant sendAuthenticatedAttacker.reachability where
  pf input := by
    have ⟨ sender, receiver, payload ⟩ := input
    apply HoareTriple.mk
    let pf := (sendAuthenticatedAttacker.proof sender receiver payload).pf
    unfold hoareTriple at *
    unfold sendAuthenticatedAttacker.reachability
    simp
    simp at pf
    simp[wp]
    simp[wp] at pf
    grind[Bytes.AttackerKnows_implies_Publishable]

public instance: ∀ i, ReachableImpliesInvariant (reachability.internal i)
  | 0 => inferInstanceAs <| ReachableImpliesInvariant compromiseParticipant.reachability
  | 1 => inferInstanceAs <| ReachableImpliesInvariant receiveAuthenticated.reachability
  | 2 => inferInstanceAs <| ReachableImpliesInvariant sendAuthenticatedAttacker.reachability

public instance: ReachableImpliesInvariant (reachability) := inferInstanceAs (ReachableImpliesInvariant (.combine reachability.internal))

end


end Reachability

end DY.Communication.Authenticated
