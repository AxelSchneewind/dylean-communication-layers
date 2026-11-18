module

public import DY.Trace
public import DY.Bytes
import DY.Meta.Step

public import DyleanExtensions.Manipulation

public import DY.Actions.ProtocolEvent
import all DY.Actions.ProtocolEvent

namespace DY.ProtocolEvent


public
theorem logEvent.preservesReachability
  {EventT}
  [ExecTraceTypes]
  [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT EventT)]
  (config : ReachabilityConfig)
  (event : EventT)
  : (ProtocolEvent.logEvent event).PreservesReachability config (fun _x => True) (fun _out tr => tr.EventLogged event) := by
    dsimp only [ProtocolEvent.logEvent, Traceful.PreservesReachability]
    intro tr h_reach h_pre
    apply Traceful.PreservesReachabilityFrom_bind
    . apply appendEntry.preservesReachability
    . assumption
    . assumption
    intro x tr h_post h_reach h_le
    apply Traceful.PreservesReachabilityFrom_pure
    . assumption
    . have : tr.EventLoggedAt event x := by grind[Trace.EventLoggedAt]
      grind
    done

end DY.ProtocolEvent
