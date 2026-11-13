module

import DY.Meta
import DY.Meta.Utils
public import SingleAuthMessage.Specification
public import SingleAuthMessage.SecurityTheorems
import SingleAuthMessage.Instance
public meta import SingleAuthMessage.Instance

-- for formatting
public import Init.Data.Format.Basic

public import Communication

namespace DY.Example.SingleAuthMessage

abbrev alice := "Alice"
abbrev bob := "Bob"

section honest

def honestProtocolRun: Traceful Unit := do
  -- alice prepares msg for bob
  let i ← prepare_message alice bob
  let j ← send_message alice bob i
  let _ ← receive_message alice bob j
  return ()

#guard (honestProtocolRun.run Trace.nil).fst = some ()

def honestProtocolRun_trace := (honestProtocolRun.run Trace.nil).snd.val
#eval honestProtocolRun_trace

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
  let tr := (honestProtocolRun.run Trace.nil).snd.val
  tr.Reachable reachability ∧
  ∃ (tr1 tr2 : Nat) (msg : single_message),
  tr1 ≤ tr2
  ∧ tr.EventLoggedAt (single_message_send_event.mk alice msg) tr1
  ∧ tr.EventLoggedAt (single_message_receive_event.mk alice bob msg) tr2 := by
    intro tr
    refine ⟨ ?_, ?_ ⟩
    . apply Traceful.PreservesReachability_to_Reachable honestProtocolRun_preservesReachability
      grind
    simp only[DY.Trace.EventLoggedAt_eq_getEventAt]
    let witness := match (Trace.getEventAt single_message_send_event 1 tr) with
       | some event => event.msg
       | none => single_message.mk Comparse.BytesLike.empty
    refine ⟨ 1, 4, witness, ?_ ⟩
    native_decide

#print axioms honestProtocolRun_properties

end honest




section compromised

def msg [Literal.CanMkLiteral Bytes] : Bytes := Literal.literalToBytes (ByteArray.mk (Array.mk [1,2]))

def compromisedProtocolRun : Traceful Unit := do
  -- attacker prepares msg for bob
  Communication.compromiseParticipant alice
  let j ← Communication.sendAuthenticatedAttacker alice bob msg
  let _ ← receive_message alice bob j
  return ()

#guard (compromisedProtocolRun.run Trace.nil).fst = some ()

def example_trace := (compromisedProtocolRun.run Trace.nil).snd.val
#eval example_trace

theorem compromisedProtocolRun_preservesReachability
  : compromisedProtocolRun.PreservesReachability reachability (fun _ => True) (fun _ _ => True)
:= by
  unfold compromisedProtocolRun

  intro tr reach pre
  apply Traceful.PreservesReachabilityFrom_bind
  . -- TODO: is there a way to use Communication.compromiseParticipant.reachability directly?
    apply Traceful.PreservesReachability_base Communication.compromiseParticipant.reachability _ (alice)
  . assumption
  . -- precondition proof
    unfold Communication.compromiseParticipant.reachability
    grind


  intro i tr post tr_inv le
  -- these are required for precondition, how to get from previous step?
  have : Communication.participantCorrupted tr alice := by sorry
  have : msg.AttackerKnows tr := by sorry
  apply Traceful.PreservesReachabilityFrom_bind
  . apply Traceful.PreservesReachability_base Communication.sendAuthenticatedAttacker.reachability _ (alice, bob, msg)
  . assumption
  . -- precondition proof
    unfold Communication.sendAuthenticatedAttacker.reachability
    grind

  intro j tr post tr_inv le
  apply Traceful.PreservesReachabilityFrom_bind
  . apply Traceful.PreservesReachability_base receive_message.reachability _ (alice, bob, j)
  . assumption
  . assumption

  intro j tr post tr_inv le
  apply Traceful.PreservesReachabilityFrom_pure
  . grind
  . grind

-- TODO: use security theorem
theorem compromisedProtocolRun_properties:
  let tr := (compromisedProtocolRun.run Trace.nil).snd.val
  tr.Reachable reachability ∧
  ∃ (tr1 tr2 : Nat),
  tr1 ≤ tr2
  ∧ Communication.participantCorruptedAt tr alice tr1
  ∧ tr.EventLoggedAt (single_message_receive_event.mk alice bob {payload:=msg}) tr2 := by
    intro tr
    refine ⟨ ?_, ?_ ⟩
    . apply Traceful.PreservesReachability_to_Reachable compromisedProtocolRun_preservesReachability
      grind
    simp only[Communication.participantCorruptedAt, DY.Trace.EventLoggedAt_eq_getEventAt]
    refine ⟨ 0, 2, ?_ ⟩
    native_decide

#print axioms compromisedProtocolRun_properties

end compromised


end DY.Example.SingleAuthMessage
