module

public import DY.Trace
public import DY.Bytes
public import DY.Comparse
import DY.Meta.Step

public import Communication.Authenticated
public import Communication.Confidential


open DY.Comparse

namespace Communication


-- variable [BytesFunctor]
--
-- section Execution
--
-- #combine into ExecEntryT from
--   Communication.Authenticated,
--   Communication.Authenticated.Compromise,
--   Communication.Confidential,
--   Communication.Confidential.Compromise
--
-- end Execution

end Communication
