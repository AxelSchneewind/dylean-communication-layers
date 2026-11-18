module

public import DY.Trace
public import DY.Bytes
import DY.Meta.Step

public import DyleanExtensions.Manipulation

public import DY.Actions.ProtocolEvent

namespace DY.ProtocolEvent

public
theorem logEvent.preservesReachability
  {EventT}
  [ExecTraceTypes]
  [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT EventT)]
  (config : ReachabilityConfig)
  (event : EventT)
  : (ProtocolEvent.logEvent event).PreservesReachability config (fun x => True) (fun out tr => tr.EventLogged event) := by
    dsimp only [ProtocolEvent.logEvent, Traceful.PreservesReachability]
    intro tr h_reach h_pre
    apply appendEntry.preservesReachability
    . apply appendEntry.preservesReachability
    . assumption
    . assumption
    intro x tr h_post h_reach h_le
    apply Traceful.PreservesReachabilityFrom_pure
    . assumption
    . assumption
    done

end DY.ProtocolEvent
