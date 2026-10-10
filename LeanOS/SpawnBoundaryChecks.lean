import LeanOS.SpawnBoundary

/-!
# Isolation, cleanup, and stale handles at the spawn-family tokens

`LeanOS.SpawnBoundary` proves that every edge of the generated spawn table is
one gate step, and that rejecting edges keep the complete state.  This module
checks, on the complete states the tokens name, what those edges leave
behind: the child's inheritance set and isolation, what termination cleans up,
how released and returned frames are reused, and which handle words stay
stale.  The checks are closed evaluations on the sample boot plan
(`native_decide`, classified `bounded-model`).
-/
namespace LeanOS.SpawnBoundary

open LeanOS
open LeanOS.FailStop
open LeanOS.SpawnOracle
open LeanOS.SpawnAccountingOracle

def slotsOf (state : CompositeState) (subject : Nat) : List (Option Capability.Capability) :=
  (List.range 4).map (state.capabilities.slots subject)

/-- Whether a handle word resolves for a subject to a capability of a kind. -/
def resolves (state : CompositeState) (subject : Nat) (word : UInt64)
    (kind : Capability.ObjectKind) : Bool :=
  match CapabilityHandle.resolveCurrent state.capabilities { caller := subject } word kind with
  | .ok _ => true
  | .error _ => false

/-- Whether a handle word is rejected as stale for a subject. -/
def staleFor (state : CompositeState) (subject : Nat) (word : UInt64)
    (kind : Capability.ObjectKind) : Bool :=
  match CapabilityHandle.resolveCurrent state.capabilities { caller := subject } word kind with
  | .error (.denied .staleHandle) => true
  | _ => false

/-- Whether every byte of a frame is the initial byte, at both ends and the
middle (`FrameScrub.scrubFrame` writes every offset; the general statements
are `allocateMemory_fresh` and `releaseMemory_returns`). -/
def scrubbed (state : CompositeState) (frame : Nat) : Bool :=
  state.scrub.bytes frame 0 == FrameScrub.initialByte &&
    state.scrub.bytes frame (FrameScrub.frameBytes / 2) == FrameScrub.initialByte &&
    state.scrub.bytes frame (FrameScrub.frameBytes - 1) == FrameScrub.initialByte

/-- Everything a subject not involved in the spawn family can observe of its
own resources. -/
def bystanderView (state : CompositeState) :
    List (Option Capability.Capability) × Nat × Nat × Option SpawnCapability ×
      List (Option ChildEntry) × Bool :=
  (slotsOf state 1, state.budgetLimit 1, state.budgetUsage 1, state.spawn.authority 1,
    (List.range 4).map (state.spawn.children 1), state.lifecycle.runnable 1)

/-- The states of the main seed's family. -/
def mainStates : List StateId :=
  [.seed, .authorized, .spawned, .released, .granted, .terminated, .reallocated, .respawned,
    .secondTerminated, .otherSubject, .revoked, .regranted, .regrantedSpawned, .narrowedSend,
    .narrowedGrant]

/-- Spawn: the child gets exactly the send-only endpoint derived from the
parent's capability and the root of its own empty address space; it holds no
spawn authority, is not runnable or queued, and has a zero frame budget; the
parent's and the bystander's slots are unchanged; and the parent's endpoint
handle word is stale in the child's slot space. -/
def spawnIsolationChecks (plan : BootPageTablePlan.Plan) : Bool :=
  let authorized := stateOf plan .authorized
  let spawned := stateOf plan .spawned
  slotsOf spawned 3 == expectedChildSlots &&
    slotsOf spawned 2 == slotsOf authorized 2 && slotsOf spawned 1 == slotsOf authorized 1 &&
    spawned.spawn.authority 3 == none && spawned.spawn.parent 3 == some 2 &&
    spawned.spawn.children 2 0 == some { child := 3, generation := 1, charge := 0 } &&
    staleFor spawned 3 parentEndpoint .endpoint &&
    spawned.lifecycle.runnable 3 == false && !(spawned.scheduler.ready.contains 3) &&
    spawned.virtualMemory.owner 21 == some 3 &&
    (List.range 8).all (fun page => spawned.virtualMemory.mappings 21 page == none) &&
    spawned.budgetLimit 3 == 0 && spawned.budgetUsage 3 == 0

/-- No state of the main family changes what the bystander, subject 1, holds:
its slots, frame budget and usage, spawn authority, child table, and
runnability. -/
def bystanderChecks (plan : BootPageTablePlan.Plan) : Bool :=
  mainStates.all fun id => bystanderView (stateOf plan id) == bystanderView (spawnSeed plan)

/-- Release returns the parent's frame free and scrubbed; a grant commits it to
the child and charges it; the parent has no frame left to allocate. -/
def frameChecks (plan : BootPageTablePlan.Plan) : Bool :=
  let released := stateOf plan .released
  let granted := stateOf plan .granted
  released.capabilities.objects 20 == false &&
    released.virtualMemory.memory.allocator.status 4 == .free && scrubbed released 4 &&
    released.budgetUsage 2 == 0 && released.budgetLimit 2 == 1 &&
    granted.frameBudgets.commitment 4 == some 3 && granted.budgetLimit 2 == 0 &&
    granted.budgetLimit 3 == 1 &&
    granted.spawn.children 2 0 == some { child := 3, generation := 1, charge := 1 } &&
    entitlement granted 2 == entitlement released 2

/-- Termination releases everything the child was given: its identity is dead
and holds nothing, its address space is gone, its frame is committed to the
parent again, free and scrubbed, and its records and table entry are gone; the
parent's subject budget is free again. -/
def cleanupChecks (plan : BootPageTablePlan.Plan) : Bool :=
  let granted := stateOf plan .granted
  let terminated := stateOf plan .terminated
  terminated.capabilities.subjects 3 == false &&
    slotsOf terminated 3 == [none, none, none, none] &&
    terminated.virtualMemory.owner 21 == none && terminated.lifecycle.addressOwner 21 == none &&
    terminated.capabilities.objects 21 == false &&
    terminated.frameBudgets.commitment 4 == some 2 &&
    terminated.virtualMemory.memory.allocator.status 4 == .free && scrubbed terminated 4 &&
    terminated.spawn.children 2 0 == none && terminated.spawn.parent 3 == none &&
    terminated.spawn.addressSpace 3 == none && childCount terminated 2 == 0 &&
    terminated.budgetLimit 2 == 1 && terminated.budgetLimit 3 == 0 &&
    entitlement terminated 2 == entitlement granted 2 &&
    terminated.lifecycle.issuedSubjects 3 == true

/-- The returned frame is allocatable again by the parent: the new object is a
never-issued identity on the same, scrubbed frame, and the parent's old memory
handle word for the released object stays stale after its slot is reused. -/
def reclaimChecks (plan : BootPageTablePlan.Plan) : Bool :=
  let terminated := stateOf plan .terminated
  let reallocated := stateOf plan .reallocated
  terminated.virtualMemory.memory.issued 22 == false &&
    reallocated.virtualMemory.memory.allocator.status 4 == .owned 22 &&
    reallocated.virtualMemory.memory.binding 22 == some 4 && scrubbed reallocated 4 &&
    (reallocated.capabilities.slots 2 2).map (·.object) == some 22 &&
    reallocated.budgetUsage 2 == 1 && reallocated.budgetLimit 2 == 1 &&
    staleFor (stateOf plan .released) 2 0x50002 .memory && staleFor reallocated 2 0x50002 .memory

/-- The second child is a fresh identity in the reused child-table slot with
the next generation; the first child's identity stays issued and dead; the
second termination leaves no child. -/
def respawnChecks (plan : BootPageTablePlan.Plan) : Bool :=
  let respawned := stateOf plan .respawned
  let second := stateOf plan .secondTerminated
  respawned.spawn.children 2 0 == some { child := 4, generation := 2, charge := 0 } &&
    respawned.spawn.parent 4 == some 2 && respawned.spawn.addressSpace 4 == some 23 &&
    respawned.capabilities.subjects 3 == false &&
    respawned.lifecycle.issuedSubjects 3 == true &&
    second.capabilities.subjects 4 == false && childCount second 2 == 0 &&
    second.spawn.children 2 0 == none

/-- The bystander, made current by the timer switch, names nothing of the
parent's: the parent's child entry is untouched and the bystander holds no
child table, spawn authority, or frame. -/
def bystanderCurrentChecks (plan : BootPageTablePlan.Plan) : Bool :=
  let other := stateOf plan .otherSubject
  memoryActor other == 1 && spawnParent other == 1 &&
    other.spawn.children 2 0 == some { child := 3, generation := 1, charge := 0 } &&
    other.spawn.children 1 0 == none && other.spawn.authority 1 == none &&
    other.budgetLimit 1 == 0 && slotsOf other 3 == slotsOf (stateOf plan .spawned) 3

/-- A revoked and re-granted spawn capability has a fresh generation; the
narrowed endpoints carry exactly the copied rights. -/
def authorityChecks (plan : BootPageTablePlan.Plan) : Bool :=
  (stateOf plan .authorized).spawn.authority 2 == some { generation := 1, subjectBudget := 1 } &&
    (stateOf plan .revoked).spawn.authority 2 == none &&
    (stateOf plan .regranted).spawn.authority 2 == some { generation := 2, subjectBudget := 1 } &&
    ((stateOf plan .narrowedSend).capabilities.slots 2 3).map (·.rights) ==
      some { send := true } &&
    ((stateOf plan .narrowedGrant).capabilities.slots 2 3).map (·.rights) ==
      some { send := true, grant := true }

def boundaryChecks (plan : BootPageTablePlan.Plan) : Bool :=
  spawnIsolationChecks plan && bystanderChecks plan && frameChecks plan && cleanupChecks plan &&
    reclaimChecks plan && respawnChecks plan && bystanderCurrentChecks plan &&
    authorityChecks plan

/-- **Every check passes** on the sample boot plan. -/
theorem boundary_checks_pass :
    (match BootPageTablePlan.compile BootPageTablePlan.sampleInput with
      | .ok plan => boundaryChecks plan
      | .error _ => false) = true := by
  native_decide

end LeanOS.SpawnBoundary
