import LeanOS.SpawnBoundary

/-!
# The dispatcher's frame-budget tokens, simulated by the composite

`CompositeDispatcher` routes state tokens `0x4001`–`0x4b01` to
`FrameBudgetScenario.dispatch`, whose edges are defined over the standalone
`FrameBudgetScenario.Runtime` (a `FrameBudget.State`, a separate
`FrameScrub.State`, and a current subject).  ADR 0010's gate item 1 carried
that as a caveat: the tokens denote a runtime other than the composite.

This module gives every token of that graph a composite denotation and proves
a forward simulation.  `compositeOf id` is the composite state reached from a
kernel-owned composite seed by replaying, for each scenario command on the
token's path, its composite counterpart (`counterpart`):

| Scenario command | Composite step |
| --- | --- |
| `allocateA`, `allocateB`, `publishFreshB` | `memoryGate (.allocate slot)` |
| `retryA` | `memoryGate (.allocate slot)`, rejected `frameBudgetExhausted` |
| `selectB` | the dispatcher's authoritative timer switch |
| `terminateA` | authoritative `terminateSubject` |
| `denyStaleA` | authoritative map syscall with A's old handle word, rejected |
| `releaseA`, `repeatReleaseA` | `memoryGate (.release slot)` |
| `complete`, `completeReleased` | no step |

Subject A of the scenario is composite subject 2 and B is subject 1.  The
simulation (`budget_tokens_simulated`) says, for every edge of the token
graph:

1. the composite successor is the counterpart step on the composite
   predecessor (`compositeOf_edge`);
2. the counterpart's typed result is the scenario's reply
   (`counterpart_matches_reply`), which is also the dispatcher's reply word,
   since the generated table is unchanged; and
3. the budget view agrees at every token (`views_agree`): which of A and B is
   current, which is live, and for each live one its frame usage and frame
   limit.  These are what decide every later allocation.

On the budget projection, every allocation and release step of the composite
is exactly `FrameBudget.allocate` and `FrameBudget.release`, which are the
steps the scenario's edges run (`allocateMemory_refines`,
`releaseMemory_refines`).

**What the view hides, and why.**  The two models differ on a dead subject's
frame and on physical frame identity:

- `FrameBudget.terminate` frees A's frame; composite termination of a subject
  that is not a spawned child retires A's object but keeps its frame owned by
  that retired object.  Commitments never move except between a parent and a
  child, so in both models no live subject can ever allocate A's frame again:
  the difference cannot change any later decision.  The composite reclaims
  frames only for a terminated child (`terminateChild`, `reclaimChildFrames`).
- The scenario's separate `FrameScrub.State` reuses one physical frame for A's
  object and then B's fresh object, and the QEMU frame-budget image maps that
  one physical frame for both.  In the composite there is one frame space and
  B's fresh object is on B's own committed frame.  Cross-subject physical
  reuse after a non-child termination is therefore a behavior of the
  standalone scrub model and the machine scenario only; the composite
  publishes every allocation on a scrubbed frame (`allocateMemory_fresh`).
-/
namespace LeanOS.FrameBudgetComposite

open LeanOS
open LeanOS.FailStop
open LeanOS.FrameBudgetScenario (StateId Command Reply)

/-! ## The composite seed -/

/-- The dispatcher seed with three more free frames (5, 6, 7) in every view of
the allocator, eight capability slots per subject, the issuers past the seed's
histories, frame 5 committed to subject 2 (A) and frames 6 and 7 to subject 1
(B). -/
def budgetSeed (plan : BootPageTablePlan.Plan) : CompositeState :=
  let base := compositeDispatcherInitial plan
  let allocator : FrameAllocator.State :=
    { frames := [4, 5, 6, 7]
      status := fun frame => if frame = 5 ∨ frame = 6 ∨ frame = 7 then .free
        else base.virtualMemory.memory.allocator.status frame }
  let virtualMemory : VirtualMapping.State :=
    { base.virtualMemory with memory := { base.virtualMemory.memory with allocator } }
  let framed : CompositeState :=
    { base with
      virtualMemory
      ipc := { base.ipc with virtualMemory }
      resumable := { base.resumable with
        translations := { base.resumable.translations with virtual := virtualMemory } } }
  { installCopiedCapabilities framed { framed.capabilities with slotCapacity := fun _ => 8 } with
    issuers := { subject := { next := 3 }, object := { next := 21 } }
    frameBudgets := { commitment := fun frame =>
      if frame = 5 then some 2 else if frame = 6 ∨ frame = 7 then some 1 else none } }

/-! ## Composite counterparts of the scenario commands -/

inductive Step where
  | memory (operation : MemoryOperation)
  | authoritative (operation : AuthoritativeOperation)
  | none

def Step.apply (state : CompositeState) : Step → CompositeState
  | .memory operation => (memoryGate state operation).state
  | .authoritative operation => (authoritativeGate state operation).state
  | .none => state

/-- A's old memory handle word: slot 3, the capability generation 6 its first
allocation received. -/
def staleAWord : UInt64 := 0x60003

def counterpart : Command → Step
  | .allocateA => .memory (.allocate 3)
  | .retryA => .memory (.allocate 4)
  | .selectB => .authoritative SpawnBoundary.switchOperation
  | .allocateB => .memory (.allocate 2)
  | .terminateA => .authoritative (.ordinary (.terminateSubject 2))
  | .publishFreshB => .memory (.allocate 3)
  | .denyStaleA =>
      .authoritative (.ordinary (.syscall { number := 0, arg0 := staleAWord, arg1 := 7, arg2 := 1 }))
  | .complete => .none
  | .releaseA => .memory (.release 3)
  | .repeatReleaseA => .memory (.release 3)
  | .completeReleased => .none

/-- The scenario commands leading to each token, as in `FrameBudgetScenario`. -/
def path : StateId → List Command
  | .initial => []
  | .aAllocated => [.allocateA]
  | .aExhausted => [.allocateA, .retryA]
  | .bSelected => [.allocateA, .retryA, .selectB]
  | .bAllocated => [.allocateA, .retryA, .selectB, .allocateB]
  | .aTerminated => [.allocateA, .retryA, .selectB, .allocateB, .terminateA]
  | .bFresh => [.allocateA, .retryA, .selectB, .allocateB, .terminateA, .publishFreshB]
  | .staleDenied =>
      [.allocateA, .retryA, .selectB, .allocateB, .terminateA, .publishFreshB, .denyStaleA]
  | .complete =>
      [.allocateA, .retryA, .selectB, .allocateB, .terminateA, .publishFreshB, .denyStaleA,
        .complete]
  | .aReleased => [.allocateA, .releaseA]
  | .releaseDenied => [.allocateA, .releaseA, .repeatReleaseA]
  | .releaseComplete => [.allocateA, .releaseA, .repeatReleaseA, .completeReleased]

def runCommands (state : CompositeState) : List Command → CompositeState
  | [] => state
  | command :: rest => runCommands ((counterpart command).apply state) rest

theorem runCommands_append (state : CompositeState) (commands : List Command) (command : Command) :
    runCommands state (commands ++ [command]) =
      (counterpart command).apply (runCommands state commands) := by
  induction commands generalizing state with
  | nil => rfl
  | cons first rest ih => exact ih _

/-- The composite denotation of a frame-budget token. -/
def compositeOf (plan : BootPageTablePlan.Plan) (id : StateId) : CompositeState :=
  runCommands (budgetSeed plan) (path id)

def allStates : List StateId :=
  [.initial, .aAllocated, .aExhausted, .bSelected, .bAllocated, .aTerminated, .bFresh,
    .staleDenied, .complete, .aReleased, .releaseDenied, .releaseComplete]

def allCommands : List Command :=
  [.allocateA, .retryA, .selectB, .allocateB, .terminateA, .publishFreshB, .denyStaleA,
    .complete, .releaseA, .repeatReleaseA, .completeReleased]

/-- Every edge of the token graph extends its predecessor's path by its
command. -/
theorem paths_follow_edges :
    allStates.all (fun state => allCommands.all fun command =>
      match FrameBudgetScenario.next state command with
      | some next => path next == path state ++ [command]
      | none => true) = true := by
  decide

theorem allStates_complete (state : StateId) : state ∈ allStates := by
  cases state <;> decide

theorem allCommands_complete (command : Command) : command ∈ allCommands := by
  cases command <;> decide

/-- **The composite successor is the counterpart step.** -/
theorem compositeOf_edge (plan : BootPageTablePlan.Plan) (state : StateId) (command : Command)
    (next : StateId) (edge : FrameBudgetScenario.next state command = some next) :
    compositeOf plan next = (counterpart command).apply (compositeOf plan state) := by
  have follows := List.all_eq_true.1
    (List.all_eq_true.1 paths_follow_edges state (allStates_complete state)) command
    (allCommands_complete command)
  rw [edge] at follows
  simp only [beq_iff_eq] at follows
  simp only [compositeOf, follows, runCommands_append]

/-! ## The budget view -/

/-- Which of A and B is current, which is live, and each live subject's frame
usage and limit. -/
structure BudgetView where
  currentIsA : Bool
  aLive : Bool
  bLive : Bool
  a : Option (Nat × Nat)
  b : Option (Nat × Nat)
  deriving DecidableEq, Repr

def scenarioView (runtime : FrameBudgetScenario.Runtime) : BudgetView :=
  let live := runtime.budget.memory.capabilities.subjects
  let accounting := fun subject =>
    if live subject then some (FrameBudget.usage runtime.budget subject,
      FrameBudget.limit runtime.budget subject) else none
  { currentIsA := runtime.currentSubject == 0
    aLive := live 0, bLive := live 1, a := accounting 0, b := accounting 1 }

def compositeView (state : CompositeState) : BudgetView :=
  let live := state.capabilities.subjects
  let accounting := fun subject =>
    if live subject then some (state.budgetUsage subject, state.budgetLimit subject) else none
  { currentIsA := memoryActor state == 2
    aLive := live 2, bLive := live 1, a := accounting 2, b := accounting 1 }

/-- **The views agree at every token.** -/
theorem views_agree :
    (match BootPageTablePlan.compile BootPageTablePlan.sampleInput with
      | .ok plan => allStates.all fun id =>
          compositeView (compositeOf plan id) == scenarioView (FrameBudgetScenario.materialize id)
      | .error _ => false) = true := by
  native_decide

/-! ## Typed results -/

/-- Whether a handle word is rejected as stale for a subject. -/
def staleFor (state : CompositeState) (subject : Nat) (word : UInt64)
    (kind : Capability.ObjectKind) : Bool :=
  match CapabilityHandle.resolveCurrent state.capabilities { caller := subject } word kind with
  | .error (.denied .staleHandle) => true
  | _ => false

/-- The composite typed result a scenario reply corresponds to. -/
def resultMatches (state : CompositeState) (command : Command) : Reply → Bool
  | .allocatedA | .allocatedB | .freshB =>
      match counterpart command with
      | .memory operation =>
          match (memoryGate state operation).result with
          | .completed (.allocated _ _) => true
          | _ => false
      | _ => false
  | .budgetExhaustedUnchanged =>
      match counterpart command with
      | .memory operation =>
          (memoryGate state operation).result == .completed (.rejected .frameBudgetExhausted)
      | _ => false
  | .releasedA =>
      match counterpart command with
      | .memory operation =>
          match (memoryGate state operation).result with
          | .completed (.released _ _) => true
          | _ => false
      | _ => false
  | .repeatedReleaseDenied =>
      match counterpart command with
      | .memory operation =>
          (memoryGate state operation).result == .completed (.rejected .staleSlot)
      | _ => false
  | .selectedB | .terminatedA =>
      match counterpart command with
      | .authoritative operation =>
          SpawnBoundary.authoritativeStatus (authoritativeGate state operation).result == 0x01
      | _ => false
  | .staleDenied =>
      match counterpart command with
      | .authoritative operation =>
          SpawnBoundary.authoritativeStatus (authoritativeGate state operation).result == 0x80 &&
            staleFor state (memoryActor state) staleAWord .memory
      | _ => false
  | .passed =>
      match counterpart command with
      | .none => true
      | _ => false

/-- **Every counterpart's typed result is the scenario's reply.** -/
theorem counterpart_matches_reply :
    (match BootPageTablePlan.compile BootPageTablePlan.sampleInput with
      | .ok plan => allStates.all fun state => allCommands.all fun command =>
          match FrameBudgetScenario.replyFor state command with
          | some reply => resultMatches (compositeOf plan state) command reply
          | none => true
      | .error _ => false) = true := by
  native_decide

/-- **The frame-budget tokens are simulated by the composite.**  For every
edge of the token graph, the composite successor is the counterpart gate step
on the composite predecessor, the counterpart's typed result is the edge's
reply, and the budget view of the composite successor is the scenario
successor's. -/
theorem budget_tokens_simulated (plan : BootPageTablePlan.Plan)
    (compiled : BootPageTablePlan.compile BootPageTablePlan.sampleInput = .ok plan)
    (state : StateId) (command : Command) (next : StateId) (reply : Reply)
    (edge : FrameBudgetScenario.next state command = some next)
    (replied : FrameBudgetScenario.replyFor state command = some reply) :
    compositeOf plan next = (counterpart command).apply (compositeOf plan state) ∧
      resultMatches (compositeOf plan state) command reply = true ∧
      compositeView (compositeOf plan next) =
        scenarioView (FrameBudgetScenario.materialize next) := by
  have results := counterpart_matches_reply
  have views := views_agree
  rw [compiled] at results views
  have result := List.all_eq_true.1
    (List.all_eq_true.1 results state (allStates_complete state)) command
    (allCommands_complete command)
  rw [replied] at result
  have view := List.all_eq_true.1 views next (allStates_complete next)
  simp only [beq_iff_eq] at view
  exact ⟨compositeOf_edge plan state command next edge, result, view⟩

end LeanOS.FrameBudgetComposite
