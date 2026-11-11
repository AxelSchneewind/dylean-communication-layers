module

import DY.Meta
import DY.Meta.Utils
public import SingleAuthMessage.Specification
import SingleAuthMessage.Instance
public meta import SingleAuthMessage.Instance

-- for formatting
public import Init.Data.Format.Basic

import Communication

namespace DY.Example.SingleAuthMessage

abbrev alice := "Alice"
abbrev bob := "Bob"

def honestProtocolRun: Traceful Unit := do
  -- alice prepares msg for bob
  let i ← prepare_message alice bob
  let j ← send_message alice bob i
  let _ ← receive_message alice bob j
  return ()

#guard (honestProtocolRun.run Trace.nil).fst = some ()

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

    sorry

#print axioms honestProtocolRun_properties


end DY.Example.SingleAuthMessage
