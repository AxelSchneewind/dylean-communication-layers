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
    tr.EventLogged/-At-/ ({sender, receiver, msg} : single_message_receive_event)  /- time-/ →
    (
      tr.EventLogged ({sender, msg} : single_message_send_event)
      ∨ Communication.participantCorrupted tr sender
    ) := by
      -- requires ReachableImpliesInvariant for Communication
      apply Trace.apply_Reachable_implies_Invariant
      intro tr h_trinv h_recv_event
      have event_invariant : single_message_receive_event.Invariant.invariant tr (single_message_receive_event.mk sender receiver msg)
      := by
        -- receive event logged
        have recv_event_inv := Trace.EventLogged_imp_EventInv _ _ h_trinv h_recv_event
        simp [ProtocolEvent.EventInv.invariant] at recv_event_inv
        simp [ProtocolEvent.EventInv.invariant]
        constructor
        . -- obtain : ∃i, msg.payload.Publishable (tr.prefix i) := by grind
          grind
        . obtain ⟨ i, propl, propr ⟩ := recv_event_inv
          let logged := Trace.EventLogged_le ({sender, msg} : single_message_send_event) (tr.erase.prefix i) tr.erase (by grind)
          cases propr
          . grind
          . grind[Communication.participantCorrupted_later]
      simp [ProtocolEvent.EventInv.invariant] at event_invariant
      grind
