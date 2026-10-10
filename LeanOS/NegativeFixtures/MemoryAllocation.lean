import LeanOS.SpawnAccountingOracle

namespace LeanOS.NegativeFixtures.MemoryAllocation

open LeanOS
open LeanOS.FailStop
open LeanOS.SpawnAccountingOracle

def withPlan (check : BootPageTablePlan.Plan → Bool) : Bool :=
  match BootPageTablePlan.compile BootPageTablePlan.sampleInput with
  | .ok plan => check plan
  | .error _ => false

/-- The accounting oracle's seed, with every frame byte set to a canary so
that an unscrubbed frame is observable.  Subject 2 is current and has frames 5,
6, and 7 of its budget free. -/
def dirtySeed (plan : BootPageTablePlan.Plan) : CompositeState :=
  let seed := framesSeed plan
  { seed with scrub := { seed.scrub with bytes := fun _ _ => 0xcc } }

/-- The same seed with frames 5, 6, and 7 committed to subject 1 instead, so
subject 2's only committed frame (frame 4) is in use: its budget is full. -/
def fullSeed (plan : BootPageTablePlan.Plan) : CompositeState :=
  let seed := framesSeed plan
  let commitment : FrameAllocator.FrameId → Option Capability.SubjectId := fun frame =>
    if frame = 4 then some 2 else if 5 ≤ frame ∧ frame ≤ 7 then some 1 else none
  { seed with frameBudgets := { commitment } }

/-- A slot of subject 2 that is empty in the seed. -/
def freeSlot : Nat := 3

/-! ## Scrubbing -/

/-- An allocation that forgets to scrub: it publishes the object with the
frame's old bytes. -/
def unscrubbedAllocate (state : CompositeState) (slot : Nat) : MemoryOutcome :=
  match allocateDecision state slot with
  | .allocated object frame =>
      { state := { allocatedState state object (memoryActor state) slot frame with
          scrub := { state.scrub with
            written := FrameScrub.setWritten state.scrub.written object false } }
        result := .allocated object frame }
  | result => { state, result }

/-- The scrub check: an accepted allocation publishes a frame that reads only
initial bytes, as an unwritten lifetime. -/
def allocationScrubs (run : CompositeState → Nat → MemoryOutcome) : Bool :=
  withPlan fun plan =>
    let pre := dirtySeed plan
    let outcome := run pre freeSlot
    match outcome.result with
    | .allocated object frame =>
        outcome.state.scrub.bytes frame 0 == FrameScrub.initialByte &&
          outcome.state.scrub.bytes frame (FrameScrub.frameBytes - 1) ==
            FrameScrub.initialByte &&
          outcome.state.scrub.written object == false
    | _ => false

/- The unscrubbed allocation leaks the canary: the check must fail. -/
/--
error: Tactic `native_decide` evaluated that the proposition
  allocationScrubs unscrubbedAllocate = true
is false
-/
#guard_msgs in
example : allocationScrubs unscrubbedAllocate = true := by
  native_decide

/-- The composite allocation passes the same check. -/
example : allocationScrubs allocateMemory = true := by
  native_decide

/-! ## Charging the actor's budget -/

/-- An allocation that ignores the budget: when the actor has no free
committed frame it takes the allocator's first free frame instead. -/
def budgetlessAllocate (state : CompositeState) (slot : Nat) : MemoryOutcome :=
  match allocateDecision state slot with
  | .rejected .frameBudgetExhausted =>
      match state.virtualMemory.memory.allocator.frames.find?
          (fun frame => state.virtualMemory.memory.allocator.status frame == .free) with
      | some frame =>
          { state := allocatedState state state.issuers.object.next (memoryActor state) slot frame
            result := .allocated state.issuers.object.next frame }
      | none => { state, result := .rejected .frameBudgetExhausted }
  | .allocated object frame =>
      { state := allocatedState state object (memoryActor state) slot frame
        result := .allocated object frame }
  | result => { state, result }

/-- The exhaustion check: with a full budget, allocation is the typed
rejection `frameBudgetExhausted` and leaves the pre-state, so every subject's
usage is unchanged. -/
def fullBudgetRejects (run : CompositeState → Nat → MemoryOutcome) : Bool :=
  withPlan fun plan =>
    let pre := fullSeed plan
    let outcome := run pre freeSlot
    outcome.result == .rejected .frameBudgetExhausted &&
      outcome.state.budgetUsage 1 == pre.budgetUsage 1 &&
      outcome.state.budgetUsage 2 == pre.budgetUsage 2 &&
      outcome.state.issuers.object.next == pre.issuers.object.next

/- The budgetless allocation charges subject 1's frame to subject 2: the check
must fail. -/
/--
error: Tactic `native_decide` evaluated that the proposition
  fullBudgetRejects budgetlessAllocate = true
is false
-/
#guard_msgs in
example : fullBudgetRejects budgetlessAllocate = true := by
  native_decide

/-- The composite allocation passes the same check. -/
example : fullBudgetRejects allocateMemory = true := by
  native_decide

end LeanOS.NegativeFixtures.MemoryAllocation
