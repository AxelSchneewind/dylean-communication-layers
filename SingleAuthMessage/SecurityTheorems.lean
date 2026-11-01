module


import DY.Meta
import DY.Meta.Utils
public import SingleAuthMessage.Specification
public import SingleAuthMessage.Proof
import all SingleAuthMessage.Proof
public import SingleAuthMessage.Instance

namespace DY.Example.SingleAuthMessage

-- For authenticated messages we can prove on the receiver side that either the
-- sender triggered a send event or the sender is corrupt.
public
theorem sender_authentication
      (sender receiver:Participant)
      (msg:single_message)
    : ∀ tr: ExecTrace,
    tr.Reachable reachability →
    tr.EventLogged/-At-/ (single_message_event.ReceiverReceivedMsg sender receiver msg)  /- time-/ →
    (
      tr.EventLogged (single_message_event.SenderSentMsg sender msg)
      ∨ StateCompromised sender tr
    ) := by
      apply Trace.apply_Reachable_implies_Invariant
      intro tr h_trinv h_ev -- trBefore
      have event_invariant : single_message_event.Invariant.invariant tr (single_message_event.ReceiverReceivedMsg sender receiver msg)
      := by
        have := Trace.EventLogged_imp_EventInv _ _ h_trinv h_ev
        simp_all [ProtocolEvent.EventInv.invariant]
        grind
      simp [ProtocolEvent.EventInv.invariant] at event_invariant
      grind
