import LeanOS.FailStop.Latch
import LeanOS.FailStop.Composite
import LeanOS.FailStop.BlockingIPC
import LeanOS.FailStop.Operations
import LeanOS.FailStop.Footprint
import LeanOS.FailStop.Gate
import LeanOS.FailStop.ProjectionInvariants
import LeanOS.FailStop.IPC
import LeanOS.FailStop.Capabilities
import LeanOS.FailStop.Memory
import LeanOS.FailStop.OperationRegistry
import LeanOS.FailStop.Scheduler
import LeanOS.FailStop.Faults
import LeanOS.FailStop.DeferredBlocking
import LeanOS.FailStop.AuthoritativeGate
import LeanOS.FailStop.ReadSets
import LeanOS.FailStop.Resources
import LeanOS.FailStop.AuthoritativeTraces
import LeanOS.FailStop.Evidence

/-!
# Irreversible exception fail-stop model

This composite layer makes interrupt entry transactional and fatality absorbing.
The underlying interrupt classifier remains the source of vector, origin, and
subject-containment policy; this layer is the authoritative execution latch.

The model lives in the `LeanOS.FailStop` namespace and is split by subsystem
into the `LeanOS.FailStop.*` modules imported above (issue #499).  This module
re-exports all of them, so `import LeanOS.FailStop` still provides every
declaration under its original name.  See `docs/fail-stop.md` for the module
map and the operation-footprint frame rule.
-/
