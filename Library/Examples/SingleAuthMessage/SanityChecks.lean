module

import DY.Meta
import DY.Meta.Utils
public import Library.Examples.SingleAuthMessage.Specification
public import Library.Examples.SingleAuthMessage.SecurityTheorems
import Library.Examples.SingleAuthMessage.Instance
public meta import Library.Examples.SingleAuthMessage.Instance

public meta import Library.Examples.SingleAuthMessage.Printing
import Library.Examples.SingleAuthMessage.Printing

public import Library.Communication

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

#guard (honestProtocolRun.run Trace.empty).fst = some ()

def honestProtocolRun_trace := (honestProtocolRun.run Trace.empty).snd.val
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
  let tr := (honestProtocolRun.run Trace.empty).snd.val
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

def msg : Bytes := Literal.literalToBytes (ByteArray.mk (Array.mk [1,2]))

def compromisedProtocolRun : Traceful Unit := do
  -- attacker prepares msg for bob
  Communication.Authenticated.compromiseParticipant alice
  let j ← Communication.Authenticated.sendAuthenticatedAttacker alice bob msg
  let _ ← receive_message alice bob j
  return ()

#guard (compromisedProtocolRun.run Trace.empty).fst = some ()

def compromisedProtocolRun_trace := (compromisedProtocolRun.run Trace.empty).snd.val
#eval traceToStr compromisedProtocolRun_trace

theorem compromisedProtocolRun_preservesReachability
  : compromisedProtocolRun.PreservesReachability reachability (fun _ => True) (fun _ _ => True)
:= by
  unfold compromisedProtocolRun

  intro tr reach pre
  apply Traceful.PreservesReachabilityFrom_bind
  . apply Communication.Authenticated.compromiseParticipant.preservesReachability
  . assumption
  . assumption

  intro i tr post tr_inv le

  have : Communication.Authenticated.participantCompromised tr alice := by assumption
  have : msg.AttackerKnows tr := by apply Literal.attacker_knows_literalToBytes
  apply Traceful.PreservesReachabilityFrom_bind
  . apply Traceful.PreservesReachability_base Communication.Authenticated.sendAuthenticatedAttacker.reachability _ (alice, bob, msg)
  . assumption
  . -- precondition proof
    unfold Communication.Authenticated.sendAuthenticatedAttacker.reachability
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

theorem compromisedProtocolRun_properties:
  let tr := (compromisedProtocolRun.run Trace.empty).snd.val
  tr.Reachable reachability ∧
  ∃ (tr1 tr2 : Nat),
  tr1 ≤ tr2
  ∧ Communication.Authenticated.participantCompromisedAt tr alice tr1
  ∧ tr.EventLoggedAt (single_message_receive_event.mk alice bob {payload:=msg}) tr2 := by
    intro tr
    refine ⟨ ?_, ?_ ⟩
    . apply Traceful.PreservesReachability_to_Reachable compromisedProtocolRun_preservesReachability
      grind
    simp only[Communication.Authenticated.participantCompromisedAt, DY.Trace.EventLoggedAt_eq_getEventAt]
    refine ⟨ 0, 2, ?_, ?_ ⟩
    trivial
    native_decide

#print axioms compromisedProtocolRun_properties

end compromised


end DY.Example.SingleAuthMessage
