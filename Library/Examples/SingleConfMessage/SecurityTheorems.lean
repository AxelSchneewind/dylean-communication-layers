module


import DY.Meta
import DY.Meta.Utils
import DY.Actions.PersistentLocalState
public import Library.Examples.SingleConfMessage.Specification
public import Library.Examples.SingleConfMessage.Proof
import all Library.Examples.SingleConfMessage.Proof
public import Library.Examples.SingleConfMessage.Instance

namespace DY.Example.SingleConfMessage

-- For confidential messages we can prove on the receiver side that either the
-- sender triggered a send event or the sender is corrupt.
public
theorem message_confidentiality
      (sender receiver:Participant)
      (msg:single_message) (send_time recv_time : Nat)
    : ∀ tr: ExecTrace,
    tr.Reachable reachability →
    tr.EventLoggedAt ({sender, receiver, msg} : single_message_receive_event) send_time →
    ¬msg.payload.AttackerKnows (tr.prefix send_time) →
    ( -- attacker can only learn message by compromising receiver communication keys or participant states
      ¬ msg.payload.AttackerKnows tr
      ∨ Communication.Confidential.participantCompromised tr receiver
      ∨ PersistentLocalState.LocalStateCompromised p ({sender:=s, receiver:=r, msg:=msg}: single_message_state) tr
    ) := by
      -- requires ReachableImpliesInvariant for Communication
      apply Trace.apply_Reachable_implies_Invariant
      intro tr h_trinv h_send_event h_not_known
      have event_invariant : single_message_receive_event.Invariant.invariant (tr.prefix recv_time) (single_message_receive_event.mk sender receiver msg) := by
        -- receive event logged
        have recv_event_inv := Trace.EventLoggedAt_imp_EventInv _ send_time _ h_trinv h_send_event
        simp [ProtocolEvent.EventInv.invariant] at recv_event_inv
        simp [ProtocolEvent.EventInv.invariant]
        -- grind[Communication.participantCompromised_le]
        sorry
      simp [ProtocolEvent.EventInv.invariant, Trace.EventLogged] at event_invariant
      sorry
