module

import DY.Meta
import DY.Meta.Utils
public import Library.Examples.SingleConfMessage.Specification
public import Library.Examples.SingleConfMessage.SecurityTheorems
import Library.Examples.SingleConfMessage.Instance
public meta import Library.Examples.SingleConfMessage.Instance

import all DY.Bytes.AttackerKnowledge
import all DY.Misc.Fixpoint

-- for formatting
public import Init.Data.Format.Basic

public import Library.Communication

namespace DY.Example.SingleConfMessage

abbrev alice := "Alice"
abbrev bob := "Bob"
abbrev msg : Bytes := Literal.literalToBytes "evil message".toByteArray

section honest

def honestProtocolRun: Traceful Unit := do
  -- alice prepares msg for bob
  let i ← prepare_message alice bob
  let j ← send_message alice bob i
  let _ ← receive_message alice bob j
  return ()

#guard (honestProtocolRun.run Trace.empty).fst = some ()

def honestProtocolRun_trace := (honestProtocolRun.run Trace.empty).snd.val

theorem honestProtocolRun_preservesReachability
  : honestProtocolRun.PreservesReachability reachability (fun _ => True) (fun _ _ => True)
:= by
  unfold honestProtocolRun

  intro tr reach _
  apply Traceful.PreservesReachabilityFrom_bind
  . apply Traceful.PreservesReachability_base prepare_message.reachability _ (alice, bob)
  . assumption
  . assumption

  intro i tr post tr_inv le
  apply Traceful.PreservesReachabilityFrom_bind
  . apply Traceful.PreservesReachability_base send_message.reachability _ (alice, bob, i)
  . assumption
  . assumption

  intro j tr post tr_inv le
  apply Traceful.PreservesReachabilityFrom_bind
  . apply Traceful.PreservesReachability_base receive_message.reachability _ (alice, bob, j)
  . assumption
  . assumption

  intro j tr post tr_inv le
  apply Traceful.PreservesReachabilityFrom_pure
  grind
  grind

theorem honestProtocolRun_properties:
  let tr := (honestProtocolRun.run Trace.empty).snd.val
  tr.Reachable reachability ∧
  ∃ (tr1 tr2 : Nat) (msg : single_message),
  tr1 ≤ tr2
  ∧ tr.EventLoggedAt (single_message_send_event.mk alice bob msg) tr1
  ∧ tr.EventLoggedAt (single_message_receive_event.mk bob msg) tr2
  ∧ ¬ msg.payload.AttackerKnows tr
  := by
    intro tr
    refine ⟨ ?_, ?_ ⟩
    . apply Traceful.PreservesReachability_to_Reachable honestProtocolRun_preservesReachability
      grind
    simp only[DY.Trace.EventLoggedAt_eq_getEventAt]
    let witness := match (Trace.getEventAt single_message_send_event 1 tr) with
       | some event => event.msg
       | none => single_message.mk Comparse.BytesLike.empty
    refine ⟨ 1, 4, witness, ?_, ?_ ⟩
    trivial
    refine ⟨ ?_, ?_, ?_ ⟩
    native_decide
    native_decide
    unfold Bytes.AttackerKnows
    let f := Fixpoint.mkLeastFixpoint (Bytes.AttackerKnows.attackerKnowledge tr).pred
    sorry
    --grind

#print axioms honestProtocolRun_properties

end honest




section compromised

def compromisedProtocolRun : Traceful Bytes := do
  let i ← prepare_message alice bob
  let j ← send_message alice bob i
  Communication.Confidential.compromiseParticipant bob
  let msg' ← Communication.Confidential.receiveConfidential alice bob j
  let _ ← receive_message alice bob j
  return msg'

def compromised_trace := (compromisedProtocolRun.run Trace.empty).snd.val
#eval compromised_trace

#guard (compromisedProtocolRun.run Trace.empty).fst.isSome

theorem compromisedProtocolRun_preservesReachability
  : compromisedProtocolRun.PreservesReachability reachability (fun _ => True) (fun m tr => m.AttackerKnows tr)
:= by
  unfold compromisedProtocolRun
  intro tr tr_inv _

  -- prepare_message
  apply Traceful.PreservesReachabilityFrom_bind
  . apply Traceful.PreservesReachability_base prepare_message.reachability _ (alice, bob)
  . assumption
  . assumption
  intro i tr post tr_inv le

  -- send_message
  apply Traceful.PreservesReachabilityFrom_bind
  . apply Traceful.PreservesReachability_base send_message.reachability _ (alice, bob, i)
  . assumption
  . assumption
  intro j tr post tr_inv le

  -- compromiseParticipant
  apply Traceful.PreservesReachabilityFrom_bind
  . apply Communication.Confidential.compromiseParticipant.preservesReachability _ (bob)
  . assumption
  . assumption
  intro c tr post tr_inv le

  -- -- cannot use this as the last statement?
  -- receiveConfidential
  apply Traceful.PreservesReachabilityFrom_bind
  . apply Traceful.PreservesReachability_base Communication.Confidential.receiveConfidential.reachability _ (alice, bob, j)
  . assumption
  . grind
  intro msg' tr post tr_inv le

  -- receive_message
  apply Traceful.PreservesReachabilityFrom_bind
  . apply Traceful.PreservesReachability_base receive_message.reachability _ (alice, bob, j)
  . assumption
  . assumption
  intro j tr post tr_inv le

  apply Traceful.PreservesReachabilityFrom_pure
  . grind
  . have : Communication.Confidential.participantCompromised tr bob := by grind[grind_later]
    sorry
    -- grind

theorem compromisedProtocolRun_properties:
  let tr := (compromisedProtocolRun.run Trace.empty).snd.val
  let bytes := (compromisedProtocolRun.run Trace.empty).fst.get (by native_decide)
  tr.Reachable reachability ∧
  ∃ (tr1 : Nat),
    Communication.Confidential.confidentialMessageSentAt tr alice bob bytes tr1
    ∧ bytes.AttackerKnows tr
  := by
    intro tr
    refine ⟨ ?_, ?_ ⟩
    . apply Traceful.PreservesReachability_to_Reachable compromisedProtocolRun_preservesReachability
      grind
    -- let r := Traceful.PreservesReachability_to_Post compromisedProtocolRun_preservesReachability
    -- simp at r
    refine ⟨ 3, ?_, ?_ ⟩
    . simp[Communication.Confidential.confidentialMessageSentAt]
      native_decide
    . sorry
    done

#print axioms compromisedProtocolRun_properties

end compromised

























section honest_from_attacker

def honest_from_attackerProtocolRun : Traceful Unit := do
  -- attacker prepares msg for bob
  -- let _msg ← prepare_message alice bob
  Communication.Confidential.compromiseParticipant bob
  let j ← Communication.Confidential.sendConfidentialAttacker alice bob msg
  let _ ← receive_message alice bob j
  return ()

#guard (honest_from_attackerProtocolRun.run Trace.empty).fst = some ()

def honest_from_attacker_trace := (honest_from_attackerProtocolRun.run Trace.empty).snd.val
#eval honest_from_attacker_trace

theorem honest_from_attackerProtocolRun_preservesReachability
  : honest_from_attackerProtocolRun.PreservesReachability reachability (fun _ => True) (fun _ _ => True)
:= by
  unfold honest_from_attackerProtocolRun
  intro i tr tr_inv

  -- compromiseParticipant
  apply Traceful.PreservesReachabilityFrom_bind
  . apply Communication.Confidential.compromiseParticipant.preservesReachability _ bob
  . assumption
  . grind
  intro i tr post tr_inv le

  -- sendConfidentialAttacker
  apply Traceful.PreservesReachabilityFrom_bind
  . apply Traceful.PreservesReachability_base Communication.Confidential.sendConfidentialAttacker.reachability _ (alice, bob, msg)
  . assumption
  . unfold Communication.Confidential.sendConfidentialAttacker.reachability
    grind[Literal.attacker_knows_literalToBytes]
  intro j tr post tr_inv le

  -- receiveConfidential
  apply Traceful.PreservesReachabilityFrom_bind
  . apply Traceful.PreservesReachability_base receive_message.reachability _ (alice, bob, j)
  . assumption
  . unfold receive_message.reachability
    simp

  intro j tr post tr_inv le
  apply Traceful.PreservesReachabilityFrom_pure
  . grind
  . grind

theorem honest_from_attackerProtocolRun_properties:
  let tr := (compromisedProtocolRun.run Trace.empty).snd.val
  tr.Reachable reachability ∧
  ∃ (tr1 : Nat) (bytes: Bytes),
  -- tr1 ≤ tr2
  -- ∧
  Communication.Confidential.confidentialMessageSentAt tr alice bob bytes tr1
  ∧ bytes.AttackerKnows tr
  := by
    intro tr
    refine ⟨ ?_, ?_ ⟩
    . apply Traceful.PreservesReachability_to_Reachable compromisedProtocolRun_preservesReachability
      grind
    simp only[Communication.Confidential.confidentialMessageSentAt, DY.Trace.EventLoggedAt_eq_getEventAt]
    refine ⟨ 3, ?_, ⟨ ?_, ?_ ⟩ ⟩
    . sorry
    . sorry
    . sorry

#print axioms honest_from_attackerProtocolRun_properties

end honest_from_attacker






end DY.Example.SingleConfMessage
