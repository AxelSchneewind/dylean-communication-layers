module

import DY.Meta
import DY.Meta.Utils
public import Library.Examples.SingleConfMessage.Specification
public import Library.Examples.SingleConfMessage.SecurityTheorems
import Library.Examples.SingleConfMessage.Instance
public meta import Library.Examples.SingleConfMessage.Instance

-- for formatting
public import Init.Data.Format.Basic

public import Library.Communication

namespace DY.Example.SingleConfMessage

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
  ∧ tr.EventLoggedAt (single_message_send_event.mk alice bob msg) tr1
  ∧ tr.EventLoggedAt (single_message_receive_event.mk alice bob msg) tr2
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
    -- labels needed?
    sorry -- native_decide

#print axioms honestProtocolRun_properties

end honest




section compromised

-- TODO: how to add to initial attacker knowledge?
def msg [Literal.CanMkLiteral Bytes] : Bytes := Literal.literalToBytes (ByteArray.mk (Array.mk [1,2]))

def compromisedProtocolRun : Traceful Unit := do
  -- attacker prepares msg for bob
  let _msg ← prepare_message alice bob
  Communication.Confidential.compromiseParticipant bob
  -- let j ← Communication.Confidential.sendConfidentialAttacker alice bob msg
  -- let _ ← receive_message alice bob j
  return ()

#guard (compromisedProtocolRun.run Trace.empty).fst = some ()

def example_trace := (compromisedProtocolRun.run Trace.empty).snd.val
#eval example_trace

theorem compromisedProtocolRun_preservesReachability
  : compromisedProtocolRun.PreservesReachability reachability (fun _ => True) (fun _ _ => True)
:= by
  unfold compromisedProtocolRun

  intro tr reach pre
  apply Traceful.PreservesReachabilityFrom_bind
  . apply Traceful.PreservesReachability_base  prepare_message.reachability _ (alice, bob)
  . assumption
  . assumption

  intro i tr post tr_inv le

  apply Traceful.PreservesReachabilityFrom_bind
  . apply Traceful.PreservesReachability_base Communication.Confidential.compromiseParticipant.reachability _ bob
  . assumption
  . grind

  intro j tr post tr_inv le
  apply Traceful.PreservesReachabilityFrom_pure
  . grind
  . grind

theorem compromisedProtocolRun_properties:
  let tr := (compromisedProtocolRun.run Trace.empty).snd.val
  tr.Reachable reachability ∧
  ∃ (tr1 : Nat) (bytes: Bytes),
  -- tr1 ≤ tr2
  -- ∧
  Communication.Confidential.participantCompromisedAt tr bob tr1
  -- ∧ Communication.Confidential.confidentialMessageSentAt tr alice bob bytes tr1
  ∧ bytes.AttackerKnows tr := by
    intro tr
    refine ⟨ ?_, ?_ ⟩
    . apply Traceful.PreservesReachability_to_Reachable compromisedProtocolRun_preservesReachability
      grind
    simp only[Communication.Confidential.participantCompromisedAt, DY.Trace.EventLoggedAt_eq_getEventAt]
    refine ⟨ 3, ?_, ?_ ⟩
    . sorry
    . sorry

#print axioms compromisedProtocolRun_properties

end compromised


end DY.Example.SingleConfMessage
