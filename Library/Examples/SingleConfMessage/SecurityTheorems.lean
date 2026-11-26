module


import DY.Meta
import DY.Meta.Utils
import DY.Actions.PersistentLocalState
import all DY.Bytes.AttackerKnowledge
import all DY.Trace.Invariant
public import Library.Examples.SingleConfMessage.Specification
public import Library.Examples.SingleConfMessage.Proof
import all Library.Examples.SingleConfMessage.Proof
public import Library.Examples.SingleConfMessage.Instance

import all Library.Communication.Confidential

namespace DY.Example.SingleConfMessage

-- For confidential messages we can prove on the receiver side that either the
-- sender triggered a send event or the sender is corrupt.
public
theorem message_confidentiality
      (sender receiver:Participant)
      (msg:single_message) (send_time : Nat)
    : ∀ tr: ExecTrace,
    tr.Reachable reachability →
    tr.EventLoggedAt ({sender, receiver, msg} : single_message_send_event) send_time →
    msg.payload.AttackerKnows tr →
    ( -- attacker can only learn message by compromising receiver communication keys or participant states
      Communication.Confidential.participantCompromised tr receiver
      ∨ ∃ p s r, PersistentLocalState.LocalStateCompromised p ({sender:=s, receiver:=r, msg:=msg}: single_message_send_state) tr
      ∨ ∃ p s r, PersistentLocalState.LocalStateCompromised p ({sender:=s, receiver:=r, msg:=msg}: single_message_receive_state) tr
    ) := by
      -- requires ReachableImpliesInvariant for Communication
      apply Trace.apply_Reachable_implies_Invariant
      intro tr h_trinv h_send_event h_known
      have send_event_inv := Trace.EventLoggedAt_imp_EventInv _ send_time _ h_trinv h_send_event
      simp [ProtocolEvent.EventInv.invariant] at send_event_inv
      simp_all[single_message_label, single_message_state_label, Communication.Confidential.CommunicationLabel]
      grind
