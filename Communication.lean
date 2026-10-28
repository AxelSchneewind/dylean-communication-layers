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
  (tr: ExecTrace) (sender : Participant) (msg: Bytes) (i: Nat)
  : Prop
:=
  tr.at? i = some (ExecEntryT.Authenticated sender msg)
--
public
def _root_.DY.Trace.AuthenticatedMessageSent
  [ExecTraceTypes] [ExecTraceTypes.Has ExecEntryT]
  (tr: ExecTrace) (sender : Participant) (msg: Bytes)
  : Prop
:=
  exists i, tr.AuthenticatedMessageSentAt sender msg i

-- public
-- def _root_.DY.Trace.getLayerMessageSentAt
--   [ExecTraceTypes] [ExecTraceTypes.Has ExecEntryT]
--   (i: Nat)
--   (tr: ExecTrace)
--   : Option Bytes
-- :=
--   match (tr.at? i: Option ExecEntryT) with
--   | none => none
--   | some entry => entry
--
-- public
-- theorem _root_.DY.Trace.LayerMessageSentAt_eq_getLayerMessageSentAt
--   [ExecTraceTypes]
--   [ExecTraceTypes.Has ExecEntryT]
--   (msg: Bytes) (i: Nat) (tr: ExecTrace)
--   : tr.LayerMessageSentAt msg i = (tr.getLayerMessageSentAt i = some msg)
-- := by
--   dsimp only [Trace.LayerMessageSentAt, Trace.getLayerMessageSentAt]
--   grind [cases ExecEntryT]
--
public
theorem _root_.DY.Trace.AuthenticatedMessageSentAt_implies_AttackerKnows
  [ExecTraceTypes] [ExecTraceTypes.Has ExecEntryT]
  [BaseAttackerKnowledge] [AttackerKnowledge]
  [BaseAttackerKnowledge.Has baseAttackerKnowledge]
  (tr: ExecTrace) (sender : Participant) (msg: Bytes) (i: Nat)
  : tr.AuthenticatedMessageSentAt sender msg i →
    msg.AttackerKnows tr
:= by
  dsimp only [Trace.AuthenticatedMessageSentAt]
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
  match entry with
  | ExecEntryT.Authenticated s m =>
      have pub: m.Publishable tr := by simp_all [ErasableProofEntry.erase, SubTraceInvariant.invariant]; grind
      simp
      -- TODO: step through guard (s = sender)
      sorry
  | ExecEntryT.Confidential s m => sorry
  | ExecEntryT.ConfidentialAuthenticated r s m => sorry

end Proof


section Reachability

-- taken from Network.lean, theorems analogous to the ones below have to be shown

-- variable [ExecTraceTypes] [ExecTraceTypes.Has ExecEntryT]
-- variable [BaseAttackerKnowledge] [AttackerKnowledge]
--
-- public
-- abbrev reachability : ReachabilityConfig where
--   Input := Participant × Bytes
--   PreCond i tr := (i.snd).AttackerKnows tr
--   step i   := ⟨ _, sendMessageAuthenticated i.fst i.snd ⟩
--
-- public
-- theorem receiveLayerMessage.preservesReachability
--   [BaseAttackerKnowledge.Has baseAttackerKnowledge]
--   (config: ReachabilityConfig)
--   (msgHandle: Nat)
--   : (receiveLayerMessage msgHandle).PreservesReachability config (fun _ => True) (fun msg tr => msg.AttackerKnows tr)
-- := by
--   dsimp only [receiveLayerMessage, Traceful.PreservesReachability]
--   intro tr h_reach h_pre
--   apply Traceful.PreservesReachabilityFrom_bind
--   · apply getEntry.preservesReachability
--   · grind
--   · grind
--   intro entry tr h_post h_reach h_le
--
--   apply Traceful.PreservesReachabilityFrom_pure
--   · grind
--
--   apply Bytes.AttackerKnows.prove_from_base
--   apply Trace.prove_BaseAttackerKnows baseAttackerKnowledge tr entry entry.msg msgHandle
--   · grind
--   simp [baseAttackerKnowledge]
--
-- variable [ProofTraceTypes] [TraceInvariant]
-- variable [BytesInvariants] [BytesInvariantsProofs]
-- variable [ProofTraceTypes.Has ProofEntryT] [TraceInvariant.Has ProofEntryT]
-- variable [BaseAttackerKnowledgeTheorem] [AttackerKnowledgeTheorem]
--
-- public
-- instance: ReachableImpliesInvariant reachability
-- where
--   pf b := by
--     apply HoareTriple.mk
--     have := (sendMessageAuthenticated.spec b).pf
--     unfold hoareTriple at *
--     grind [Bytes.AttackerKnows_implies_Publishable]

end Reachability

end DY.Communication
