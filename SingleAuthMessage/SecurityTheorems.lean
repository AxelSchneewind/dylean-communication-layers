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
      (msg:single_message) (time : Nat)
    : ∀ tr: ExecTrace,
    tr.Reachable reachability →
    tr.EventLoggedAt ({sender, receiver, msg} : single_message_receive_event)  time →
    (
      (tr.prefix time).EventLogged ({sender, msg} : single_message_send_event)
      ∨ Communication.participantCorrupted (tr.prefix time) sender
    ) := by
      -- requires ReachableImpliesInvariant for Communication
      apply Trace.apply_Reachable_implies_Invariant
      intro tr h_trinv h_recv_event
      have event_invariant : single_message_receive_event.Invariant.invariant (tr.prefix time) (single_message_receive_event.mk sender receiver msg) := by
        -- receive event logged
        have recv_event_inv := Trace.EventLoggedAt_imp_EventInv _ time _ h_trinv h_recv_event
        simp [ProtocolEvent.EventInv.invariant] at recv_event_inv
        simp [ProtocolEvent.EventInv.invariant]
        grind[Communication.participantCorrupted_le]
      simp [ProtocolEvent.EventInv.invariant, Trace.EventLogged] at event_invariant
      grind
