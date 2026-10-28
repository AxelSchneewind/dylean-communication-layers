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
      tr.EventLogged (single_message_event.SenderSentMsg sender msg) -- \/
      -- or key of sender was compromised
    ) := by
      apply Trace.apply_Reachable_implies_Invariant
      intro tr h_inv h_e -- trBefore
      -- unfold Trace.EventLogged
      have event_invariant : single_message_event.Invariant.invariant tr (single_message_event.ReceiverReceivedMsg sender receiver msg) :=
        by
        unfold Trace.Invariant at h_inv
        simp [ProtocolEvent.EventInv.invariant]
        constructor
        . sorry
        . sorry
      simp [ProtocolEvent.EventInv.invariant] at event_invariant
      -- unfold [Trace.EventLogged] at event_invariant
      exact event_invariant.right
-- let sender_authentication tr i sender receiver payload = ()

-- // This is the same securtiy lemma as above but with the events from the
-- // communication layer. This allows us to argue with the `(prefix tr i)`
-- // function. (Not sure why this does not work in the lemma above)
-- val sender_authentication':
--   tr:trace -> i:timestamp ->
--   sender:principal -> receiver:principal ->
--   payload:single_message ->
--   Lemma
--   (requires
--     trace_invariant tr /\
--     event_triggered_at tr i receiver (CommAuthReceiveMsg sender receiver payload <: communication_core_event single_message)
--   )
--   (ensures
--     event_triggered (prefix tr i) sender (CommAuthSendMsg sender payload <: communication_core_event single_message) \/
--     is_corrupt (prefix tr i) (long_term_key_label sender)
--   )
-- let sender_authentication' tr i sender receiver payload = ()
