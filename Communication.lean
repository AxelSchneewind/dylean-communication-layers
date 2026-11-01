module

public import DY.Trace
public import DY.Bytes
public import DY.Actions.PersistentLocalState
import DY.Meta.Step

namespace DY.Communication

variable [BytesFunctor]

section Execution

public
inductive SecurityProperty where
  | Confidential
  | Authenticated
  | ConfidentialAuthenticated
  deriving DecidableEq


public
inductive ExecEntryT where
  | Authenticated (sender : Participant) (msg : Bytes)
  | Confidential (receiver : Participant) (msg : Bytes)
  | ConfidentialAuthenticated (receiver sender : Participant) (msg : Bytes)

public
def ExecEntryT.payload (entry : ExecEntryT) : Bytes :=
  match entry with
  | Authenticated _sender msg => msg
  | Confidential _receiver msg => msg
  | ConfidentialAuthenticated _receiver _sender msg => msg

-- TODO: attacker may know only non-confidential messages
public
def baseAttackerKnowledge [ExecTraceTypes]: SubBaseAttackerKnowledge ExecEntryT where
  attackerKnows _ entry msg := match entry with
    | ExecEntryT.Authenticated _sender m => m = msg
    | _ => False
    -- | ExecEntryT.Confidential _receiver m => False
    -- | ExecEntryT.ConfidentialAuthenticated _receiver _sender _m => False


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
  match entry with
  | ExecEntryT.Authenticated s msg =>
      guard (s = sender)
      return msg
  | _ => failure


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
  | some (ExecEntryT.Authenticated s m) => if s = sender then m else none
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
  unfold ExecEntryT.payload
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

-- analogously to Network.lean

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
  invariant tr entry := match entry with
    | ExecEntryT.Authenticated _sender msg => msg.Publishable tr
    | _ => True

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
    split at invBefore
    . simp at attackerKnows
      rw [←attackerKnows]
      exact invBefore
    . simp at attackerKnows

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
  step with ⟨ fun _ => ExecEntryT.Authenticated sender msg ⟩ by simp_all [ErasableProofEntry.erase, SubTraceInvariant.invariant]
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
    (fun msg tr => msg.Publishable tr)
:= by
  apply HoareTriple.mk
  unfold receiveMessageAuthenticated
  step
  sorry

end Proof


section Reachability

-- TODO: reachabillity analogous to DY.Network


end Reachability

end DY.Communication
