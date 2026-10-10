import LeanOS.SpawnAccountingOracle

namespace LeanOS.NegativeFixtures.SpawnAccounting

open LeanOS
open LeanOS.FailStop
open LeanOS.SpawnOracle
open LeanOS.SpawnAccountingOracle

def withPlan (check : BootPageTablePlan.Plan → Bool) : Bool :=
  match BootPageTablePlan.compile BootPageTablePlan.sampleInput with
  | .ok plan => check plan
  | .error _ => false

def acceptedRequest : SpawnRequest :=
  { spawnWord := 1, endpointWord := parentEndpointWord, rights := sendOnly }

/-! ## Subject budget -/

/-- A charged spawn that forgets the subject budget: it records the child in
the first free slot whatever the parent's count. -/
def budgetlessSpawn (state : CompositeState) (request : SpawnRequest) : ChildOutcome :=
  match freeChildSlot state (spawnParent state), (spawn state request).result with
  | some slot, .spawned child addressSpace =>
      { state := installChild (spawn state request).state (spawnParent state) slot child
        result := .spawned child addressSpace (controlWord slot state.spawn.nextChildGeneration) }
  | _, .rejected reason => { state, result := .spawnRejected (.spawn reason) }
  | none, _ => { state, result := .spawnRejected .subjectBudgetExhausted }

/-- The exhaustion check: with subject budget 1 and one child, a second spawn
must be the typed rejection with the pre-state. -/
def budgetExhausts (run : CompositeState → SpawnRequest → ChildOutcome) : Bool :=
  withPlan fun plan =>
    let pre := withSubjectBudget (runCommands (framesSeed plan) [acceptedCommand]) 2 1
    let outcome := run pre acceptedRequest
    outcome.result == .spawnRejected .subjectBudgetExhausted &&
      observeAccounting outcome.state == observeAccounting pre

/- The budgetless spawn creates a second child: the check must fail. -/
/--
error: Tactic `native_decide` evaluated that the proposition
  budgetExhausts budgetlessSpawn = true
is false
-/
#guard_msgs in
example : budgetExhausts budgetlessSpawn = true := by
  native_decide

/-- The charged spawn passes the same check. -/
example : budgetExhausts spawnCharged = true := by
  native_decide

/-! ## Frame budget -/

/-- A frame grant that mints a frame: it appends a fresh frame to the
allocator, commits it to the child, and charges it, instead of moving one of
the parent's frames. -/
def mintingGrant (state : CompositeState) (word : UInt64) (_frames : Nat) : ChildOutcome :=
  match resolveControl state word with
  | .error reason => { state, result := .framesRejected (.control reason) }
  | .ok (slot, entry) =>
      let fresh := 100
      let allocator := { state.virtualMemory.memory.allocator with
        frames := state.virtualMemory.memory.allocator.frames ++ [fresh]
        status := fun frame => if frame = fresh then .free
          else state.virtualMemory.memory.allocator.status frame }
      { state := { setChildEntry state (spawnParent state) slot (some (chargeEntry entry 1)) with
          virtualMemory := { state.virtualMemory with
            memory := { state.virtualMemory.memory with allocator } }
          frameBudgets := { commitment := fun frame =>
            if frame = fresh then some entry.child else state.frameBudgets.commitment frame } }
        result := .framesGranted entry.child 1 }

/-- The no-new-frames check: a one-frame grant keeps the allocator's frames
and the parent's entitlement, and takes the frame from the parent. -/
def grantMovesFrames (run : CompositeState → UInt64 → Nat → ChildOutcome) : Bool :=
  withPlan fun plan =>
    let pre := runCommands (framesSeed plan) [acceptedCommand]
    let outcome := run pre firstControl 1
    outcome.result == .framesGranted 3 1 &&
      outcome.state.virtualMemory.memory.allocator.frames ==
        pre.virtualMemory.memory.allocator.frames &&
      outcome.state.budgetLimit 2 + 1 == pre.budgetLimit 2 &&
      entitlement outcome.state 2 == entitlement pre 2

/- The minting grant creates a frame and leaves the parent's limit: the check
must fail. -/
/--
error: Tactic `native_decide` evaluated that the proposition
  grantMovesFrames mintingGrant = true
is false
-/
#guard_msgs in
example : grantMovesFrames mintingGrant = true := by
  native_decide

/-- The charged grant passes the same check. -/
example : grantMovesFrames grantFrames = true := by
  native_decide

/-! ## Returning the charge -/

/-- A child termination that forgets to return the child's frames. -/
def chargeKeepingTerminate (state : CompositeState) (word : UInt64) : ChildOutcome :=
  match resolveControl state word with
  | .error reason => { state, result := .terminateRejected reason }
  | .ok (slot, entry) =>
      let released := releaseChild (terminatedChild state entry.child) (spawnParent state) slot
        entry.child
      { state := { released with frameBudgets := state.frameBudgets }
        result := .terminated entry.child (state.budgetLimit entry.child) }

/-- The return check: terminating a child holding two frames gives them back
to the parent. -/
def terminateReturns (run : CompositeState → UInt64 → ChildOutcome) : Bool :=
  withPlan fun plan =>
    let pre := runCommands (framesSeed plan) [acceptedCommand, encodeGrant firstControl 2]
    let outcome := run pre firstControl
    outcome.result == .terminated 3 2 && outcome.state.budgetLimit 2 == 4 &&
      outcome.state.budgetLimit 3 == 0

/- The charge-keeping termination strands two frames with the dead child: the
check must fail. -/
/--
error: Tactic `native_decide` evaluated that the proposition
  terminateReturns chargeKeepingTerminate = true
is false
-/
#guard_msgs in
example : terminateReturns chargeKeepingTerminate = true := by
  native_decide

/-- The charged termination passes the same check. -/
example : terminateReturns terminateChild = true := by
  native_decide

end LeanOS.NegativeFixtures.SpawnAccounting
