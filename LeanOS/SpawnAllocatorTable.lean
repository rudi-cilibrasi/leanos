import LeanOS.SpawnAllocatorWordsNext
import LeanOS.SpawnBoundaryChecks

/-!
# The fixed spawn table is derived from the allocator (#575)

`SpawnBoundary` gave the spawn family's boot boundary as a fixed table:
twenty-one state tokens, each naming the complete composite state replayed
from a hand-picked seed, and fifty-four edges.  This module reads every such
composite state as an allocator record (`abstraction`) and proves, by closed
evaluation on the sample boot plan, that the table is a fragment of the
allocator:

* `tokens_abstract`: every token whose state the allocator represents names a
  composite state whose abstraction is a bounded allocator record, and the
  thirteen words of that record (`tokenWords`) are canonical;
* `edges_are_allocator_steps`: every edge between represented tokens whose
  command is an allocator command is one `SpawnAllocator.step` on the
  abstraction of its pre-state: same status, same value word, and the
  successor record is the abstraction of the edge's post-state;
* `edges_are_word_steps`: the same edges on the thirteen words, through the
  generated functions (`codeReply`, `codeValue`, `codeNext`).

Three tokens are not allocator records, and their edges are not allocator
steps: `otherSubject`, where the bystander is current after the dispatcher's
timer switch, and `narrowedSend` and `narrowedGrant`, where the dispatcher's
capability copy put an endpoint in the parent's slot 3.  The switch and the
copy are dispatcher-only commands (`SpawnBoundary.switchTag`,
`SpawnBoundary.copyTag`), not syscalls, and the allocator does not take them.

The exhaustion tokens are ordinary allocator records here: each has one
counter at its bound, and the allocator decides them like every other record
(`SpawnAllocator.spawn_subjects_exhausted` and its siblings).
-/
namespace LeanOS.SpawnAllocator

open LeanOS
open LeanOS.FailStop
open LeanOS.SpawnBoundary
open LeanOS.SpawnAllocatorWords

/-! ## The abstraction of a composite state -/

/-- The parent's memory capability in a slot: its identity, or none. -/
def memoryIn (state : CompositeState) (slot : Nat) : Option Nat :=
  match state.capabilities.slots parent slot with
  | some capability => if capability.kind = .memory then some capability.identity else none
  | none => none

/-- **The allocator record of a composite state.** -/
def abstraction (state : CompositeState) : State :=
  { subjectNext := state.issuers.subject.next
    objectNext := state.issuers.object.next
    capabilityNext := state.capabilities.nextIdentity
    controlNext := state.spawn.nextChildGeneration
    authorityNext := state.spawn.nextGeneration
    authority := (state.spawn.authority parent).map SpawnCapability.generation
    budget := FailStop.subjectBudget state parent
    children := (List.range childCapacity).map fun slot =>
      (state.spawn.children parent slot).map fun entry =>
        { generation := entry.generation, charge := entry.charge }
    memory := [memoryIn state 2, memoryIn state 3]
    parentFrames := state.budgetLimit parent }

/-- The allocator command of a family command, if it is one. -/
def toCommand : FamilyCommand → Option Command
  | .child operation => some (.child operation)
  | .memory operation => some (.memory operation)
  | .switch => none
  | .copy _ _ _ _ => none

/-- The tokens whose states are allocator records. -/
def recordTokens : List StateId :=
  [.seed, .authorized, .spawned, .released, .granted, .terminated, .reallocated, .respawned,
    .secondTerminated, .revoked, .regranted, .regrantedSpawned, .subjectsExhausted,
    .objectsExhausted, .controlsExhausted, .loaderRespawned, .loaderGranted, .loaderTerminated]

/-- The thirteen words of a token's record. -/
def tokenWords (plan : BootPageTablePlan.Plan) (id : StateId) : Words :=
  encode (abstraction (stateOf plan id))

/-- A token's state is an allocator record: the parent is the current subject
of a running latch, its slots 0 and 1 hold the family's endpoint and address
space root, every other slot below the capacity holds memory or nothing, no
child slot past `childCapacity` is used, and the record is bounded and
encodes exactly. -/
def isRecord (plan : BootPageTablePlan.Plan) (id : StateId) : Bool :=
  let state := stateOf plan id
  spawnParent state == parent &&
    (match state.execution.mode with | .running => true | _ => false) &&
    (state.capabilities.slots parent 0).map (·.identity) == some endpointIdentity &&
    (state.capabilities.slots parent 1).map (·.identity) == some spaceIdentity &&
    [2, 3].all (fun slot => match state.capabilities.slots parent slot with
      | some capability => capability.kind == .memory
      | none => true) &&
    (List.range (childSlots - childCapacity)).all
      (fun index => (state.spawn.children parent (childCapacity + index)).isNone) &&
    Canonical (tokenWords plan id) &&
    decode (tokenWords plan id) == abstraction state

/-- **Every listed token names an allocator record.** -/
theorem tokens_abstract :
    (match BootPageTablePlan.compile BootPageTablePlan.sampleInput with
      | .ok plan => recordTokens.all (isRecord plan)
      | .error _ => false) = true := by
  native_decide

/-- An edge of the table is an allocator step when its state and successor
are records and its command is an allocator command. -/
def Edge.isAllocatorStep (plan : BootPageTablePlan.Plan) (edge : Edge) : Bool :=
  match toCommand edge.command with
  | none => true
  | some command =>
      if recordTokens.contains edge.state then
        step (abstraction (stateOf plan edge.state)) command ==
          some { next := abstraction (stateOf plan edge.next), status := edge.status,
                 value := edge.value }
      else true

/-- The edges whose state is a record and whose command is an allocator
command: 45 of the 54. -/
def allocatorEdges : List Edge :=
  edges.filter fun edge => (toCommand edge.command).isSome && recordTokens.contains edge.state

theorem allocatorEdges_count : allocatorEdges.length = 45 := by decide

/-- **Every allocator edge of the fixed table is one allocator step.** -/
theorem edges_are_allocator_steps :
    (match BootPageTablePlan.compile BootPageTablePlan.sampleInput with
      | .ok plan => edges.all (Edge.isAllocatorStep plan)
      | .error _ => false) = true := by
  native_decide

/-- The same edges on the thirteen words, through the generated functions. -/
def Edge.isWordStep (plan : BootPageTablePlan.Plan) (edge : Edge) : Bool :=
  let words := tokenWords plan edge.state
  let command := encodeFamily edge.command
  codeReply words command == edge.status && codeValue words command == edge.value &&
    codeNext words command == tokenWords plan edge.next

/-- **The generated functions decide every allocator edge of the table.** -/
theorem edges_are_word_steps :
    (match BootPageTablePlan.compile BootPageTablePlan.sampleInput with
      | .ok plan => allocatorEdges.all (Edge.isWordStep plan)
      | .error _ => false) = true := by
  native_decide

end LeanOS.SpawnAllocator
