module

public import DY.Trace
public import DY.Bytes
public import DY.Actions.PersistentLocalState
import DY.Meta.Step

namespace DY.Communication

variable [BytesFunctor]

section Execution

public
structure ExecEntryT where
  payload : Bytes
  sender : Option Participant
  receiver : Option Participant
  deriving DecidableEq

-- constructors
@[simp, grind]
public
def ExecEntryT.Authenticated (sender : Participant) (payload : Bytes) : ExecEntryT := { payload, sender:=some sender, receiver:=none}
@[simp, grind]
public
def ExecEntryT.Confidential (receiver : Participant) (payload : Bytes) : ExecEntryT := { payload, sender:=none, receiver:= some receiver}
@[simp, grind]
public
def ExecEntryT.ConfidentialAuthenticated (sender receiver : Participant) (payload : Bytes) : ExecEntryT := { payload, sender:= some sender, receiver:= some receiver}

@[simp, grind]
public
def ExecEntryT.is_Authenticated (entry: ExecEntryT) : Prop := entry.sender.isSome
@[simp, grind]
public
def ExecEntryT.is_Confidential (entry : ExecEntryT) : Prop := entry.receiver.isSome
@[simp, grind]
public
def ExecEntryT.is_ConfidentialAuthenticated (entry : ExecEntryT) : Prop := entry.sender.isSome ∧ entry.receiver.isSome


public
def baseAttackerKnowledge [ExecTraceTypes]: SubBaseAttackerKnowledge ExecEntryT where
  attackerKnows _ entry msg := entry.payload = msg -- ∧ ¬entry.is_Confidential ∨ (receiver compromised)


-- don't include receiver in interface
public
def sendMessageAuthenticated [ExecTraceTypes] [ExecTraceTypes.Has ExecEntryT] (sender : Participant) (msg: Bytes): Traceful Nat :=
  do
  let entry: ExecEntryT := ExecEntryT.Authenticated sender msg
  appendEntry entry

-- receive message from sender to receiver through channel, with required security property.
public
def receiveMessageAuthenticated [ExecTraceTypes] [ExecTraceTypes.Has ExecEntryT] (sender : Participant) (handle: Nat): Traceful Bytes :=
  do
  let entry: ExecEntryT ← getEntry handle
  guard (entry.sender = sender)
  guard (entry.receiver = none)
  return entry.payload


-- taken and modified from Network.lean, predicates and theorems analogous to the ones below have to be shown
-- TODO: what do these _root_ definitions do? Are they needed

public
def _root_.DY.Trace.AuthenticatedMessageSentAt
  [ExecTraceTypes] [ExecTraceTypes.Has ExecEntryT]
  (tr: ExecTrace) (msg: Bytes) (i: Nat)
  : Prop
:=
  exists sender, tr.at? i = some (ExecEntryT.Authenticated sender msg)

public
def _root_.DY.Trace.AuthenticatedMessageSentAtBy
  [ExecTraceTypes] [ExecTraceTypes.Has ExecEntryT]
  (tr: ExecTrace) (sender : Participant) (msg: Bytes) (i: Nat)
  : Prop
:=
  tr.at? i = some (ExecEntryT.Authenticated sender msg)

public
def _root_.DY.Trace.AuthenticatedMessageSent
  [ExecTraceTypes] [ExecTraceTypes.Has ExecEntryT]
  (tr: ExecTrace) (msg: Bytes)
  : Prop
:=
  exists i, tr.AuthenticatedMessageSentAt msg i

public
def _root_.DY.Trace.AuthenticatedMessageSentBy
  [ExecTraceTypes] [ExecTraceTypes.Has ExecEntryT]
  (tr: ExecTrace) (sender : Participant) (msg: Bytes)
  : Prop
:=
  exists i, tr.AuthenticatedMessageSentAtBy sender msg i

public
def _root_.DY.Trace.getAuthenticatedMessageSentAt
  [ExecTraceTypes] [ExecTraceTypes.Has ExecEntryT]
  (i: Nat)
  (tr: ExecTrace)
  : Option Bytes
:=
  match (tr.at? i: Option ExecEntryT) with
  | none => none
  | some entry => entry.payload

public
def _root_.DY.Trace.getAuthenticatedMessageSentAtBy
  [ExecTraceTypes] [ExecTraceTypes.Has ExecEntryT]
  (i: Nat)
  (sender: Participant)
  (tr: ExecTrace)
  : Option Bytes
:=
  match (tr.at? i: Option ExecEntryT) with
  | some (s : ExecEntryT) => if s.sender = sender then s.payload else none
  -- | some (ExecEntryT.Authenticated s m) => if s = sender then m else none
  | _ => none

public
theorem _root_.DY.Trace.AuthenticatedMessageSentAt_imp_getAuthenticatedMessageSentAt
  [ExecTraceTypes]
  [ExecTraceTypes.Has ExecEntryT]
  (msg: Bytes) (i: Nat) (tr: ExecTrace)
  : tr.AuthenticatedMessageSentAt msg i → (tr.getAuthenticatedMessageSentAt i = some msg)
:= by
  intro h
  dsimp only [Trace.AuthenticatedMessageSentAt, Trace.getAuthenticatedMessageSentAt]
  unfold Trace.AuthenticatedMessageSentAt at h
  let ⟨s, eq⟩ := h
  rw [eq]
  simp


public
theorem _root_.DY.Trace.AuthenticatedMessageSentAtBy_imp_getAuthenticatedMessageSentAtBy
  [ExecTraceTypes]
  [ExecTraceTypes.Has ExecEntryT]
  (sender : Participant) (msg: Bytes) (i: Nat) (tr: ExecTrace)
  : tr.AuthenticatedMessageSentAtBy sender msg i → (tr.getAuthenticatedMessageSentAtBy i sender = some msg)
:= by
  intro h
  dsimp only [Trace.AuthenticatedMessageSentAtBy, Trace.getAuthenticatedMessageSentAtBy]
  unfold Trace.AuthenticatedMessageSentAtBy at h
  rw [h]
  simp

public
theorem _root_.DY.Trace.AuthenticatedMessageSentAt_implies_AttackerKnows
  [ExecTraceTypes] [ExecTraceTypes.Has ExecEntryT]
  [BaseAttackerKnowledge] [AttackerKnowledge]
  [BaseAttackerKnowledge.Has baseAttackerKnowledge]
  (tr: ExecTrace) (sender : Participant) (msg: Bytes) (i: Nat)
  : tr.AuthenticatedMessageSentAtBy sender msg i →
    msg.AttackerKnows tr
:= by
  dsimp only [Trace.AuthenticatedMessageSentAtBy]
  intro h
  apply Bytes.AttackerKnows.prove_from_base
  apply Trace.prove_BaseAttackerKnows baseAttackerKnowledge tr (ExecEntryT.Authenticated sender msg) msg i
  · grind
  simp [baseAttackerKnowledge]

end Execution

section Proof

-- analogously to Network.lean, predicates and theorems analogous to the ones below have to be shown

public
abbrev ProofEntryT := ExecEntryT

public
instance: ErasableProofEntry ExecEntryT ProofEntryT := ErasableProofEntry.default ExecEntryT

public
instance: ExecEntryAssociatedWithProofEntry ExecEntryT ProofEntryT where

public
instance
  [ExecTraceTypes] [ProofTraceTypes] [BytesInvariants]
  : SubTraceInvariant ProofEntryT
where
  invariant tr entry := entry.payload.Publishable tr
    -- match entry with
    -- | ExecEntryT.Authenticated _sender msg => msg.Publishable tr
    -- | _ => True

public
instance baseAttackerKnowledgeTheorem
  [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant] [BytesInvariants]
  [ExecTraceTypes.Has ExecEntryT]
  [ProofTraceTypes.Has ProofEntryT]
  [TraceInvariant.Has ProofEntryT]:
  SubBaseAttackerKnowledgeTheorem ProofEntryT baseAttackerKnowledge
where
  pf trBefore entry b := by
    intro invBefore attackerKnows
    simp [SubTraceInvariant.invariant, /-baseAttackerKnowledge, ErasableProofEntry.erase-/] at invBefore
    simp [/-SubTraceInvariant.invariant, -/baseAttackerKnowledge, ErasableProofEntry.erase] at attackerKnows
    -- split at invBefore
    -- . simp at attackerKnows
    rw [←attackerKnows]
    exact invBefore
    -- . done -- simp at attackerKnows

@[instance]
public
theorem sendMessageAuthenticated.spec
  [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant]
  [BytesInvariants] [BytesInvariantsProofs]
  [ExecTraceTypes.Has ExecEntryT]
  [ProofTraceTypes.Has ProofEntryT]
  [TraceInvariant.Has ProofEntryT]
  (sender: Participant)
  (msg: Bytes)
  : HoareTriple
    (sendMessageAuthenticated sender msg)
    (fun tr => msg.Publishable tr)
    (fun _ _ => True)
:= by
  apply HoareTriple.mk
  unfold sendMessageAuthenticated
  dsimp only
  step with ⟨ fun _ => ExecEntryT.Authenticated sender msg ⟩ by simp_all [ErasableProofEntry.erase, SubTraceInvariant.invariant, ExecEntryT.Authenticated]
  trivial

@[instance]
public
theorem receiveMessageAuthenticated.spec
  [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant]
  [BytesInvariants] [BytesInvariantsProofs]
  [ExecTraceTypes.Has ExecEntryT]
  [ProofTraceTypes.Has ProofEntryT]
  [TraceInvariant.Has ProofEntryT]
  (sender: Participant)
  (handle: Nat)
  : HoareTriple
    (receiveMessageAuthenticated sender handle)
    (fun _ => True)
    (fun msg tr =>
      msg.Publishable tr ∧
      tr.erase.AuthenticatedMessageSentAtBy sender msg handle
    )
:= by
  apply HoareTriple.mk
  unfold receiveMessageAuthenticated
  step
  have: entry.payload.Publishable tr := by simp_all [ErasableProofEntry.erase, SubTraceInvariant.invariant]; grind
  rename_i h_entry
  -- how to get this statement from getEntry call? postcondition not strong enough
  have entry_at_handle : tr.erase.at? handle = some entry := by sorry -- grind[tr.at?_eq_some]
  -- why is this required for step below? (otherwise monotonization error)
  -- How to keep this hypothesis?
  clear h_entry
  step
  rename_i entry_at_handle sender_match
  step
  step
  rename_i h_receiver h_x
  constructor
  . grind
  . simp[h_x]
    have : entry = ExecEntryT.mk x (some sender) none := by grind[ExecEntryT]
    simp[Trace.AuthenticatedMessageSentAtBy, ←h_x, ←this]
    grind

end Proof


section Reachability

-- taken from Network.lean, theorems analogous to the ones below have to be shown

variable [ExecTraceTypes] [ExecTraceTypes.Has ExecEntryT]
variable [BaseAttackerKnowledge] [AttackerKnowledge]

public
abbrev reachability : ReachabilityConfig where
  Input := Participant × Bytes
  PreCond i tr := (i.snd).AttackerKnows tr
  step i   := ⟨ _, sendMessageAuthenticated i.fst i.snd ⟩

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
  · apply getEntry.preservesReachability
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
variable [ProofTraceTypes.Has ProofEntryT] [TraceInvariant.Has ProofEntryT]
variable [BaseAttackerKnowledgeTheorem] [AttackerKnowledgeTheorem]

public
instance: ReachableImpliesInvariant reachability
where
  pf input := by
    have ⟨ sender, payload ⟩ := input
    apply HoareTriple.mk
    have := (sendMessageAuthenticated.spec sender payload).pf
    unfold hoareTriple at *
    grind [Bytes.AttackerKnows_implies_Publishable]

end Reachability

end DY.Communication
