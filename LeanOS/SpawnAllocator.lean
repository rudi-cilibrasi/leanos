import LeanOS.SpawnAccountingOracle

/-!
# The spawn family as a general bounded allocator (#575)

The spawn family's boot boundary (#543, #546, #547, #554) decided every
command by a fixed table: eighteen, later twenty-one, state tokens, each
naming one complete composite state replayed from a hand-picked seed, and a
fixed list of edges between them.  This module replaces the table's states by
a **bounded allocator**: a small record of counters and tables that is the
part of a composite state the spawn family's decisions read, and a step
function that decides every command of the family on every such record.

## What the allocator holds

The parent is subject 2, the current subject of the execution latch; its
capability slots 0 and 1 hold the family's fixed endpoint (identity 3) and
its own address-space root (identity 4).  The allocator holds:

| Field | Composite source | Meaning |
| --- | --- | --- |
| `subjectNext` | `issuers.subject.next` | next subject identity (children) |
| `objectNext` | `issuers.object.next` | next object identity (address spaces, memory) |
| `capabilityNext` | `capabilities.nextIdentity` | next capability identity |
| `controlNext` | `spawn.nextChildGeneration` | next control-handle generation |
| `authorityNext` | `spawn.nextGeneration` | next spawn-capability generation |
| `authority` | `spawn.authority 2` | the parent's spawn-capability generation |
| `budget` | its subject budget | children the parent may have at once |
| `children` | `spawn.children 2 0..3` | generation and frame charge per child-table slot |
| `memory` | `capabilities.slots 2 2..3` | identity of the parent's memory capability per slot |
| `parentFrames` | frames committed to 2 | the parent's frame budget, in use or free |

Frames are counted, not named: every frame committed to the parent is either
backing one of its memory objects or free, and every frame committed to a
child is free (a child never runs in the family).  So the parent has
`parentFrames - memoryUsed` free frames, and a grant moves free frames from
the parent to a child by count.

## Commands

`Command` is exactly the public spawn family (`ChildOperation`) and the
memory family (`MemoryOperation`), run by the parent.  `step` decides each
one: either a `Step` (the successor record, the status byte, and the value
word, with the codes of the hosted oracles), or `none` when the command lies
outside the bounded representation.  Only two kernel commands can be outside
it: a spawn-authority grant that would be accepted for the bystander
(subject 1) or with a subject budget above `childCapacity`, and a grant when
`authorityNext` has no successor word.  Every syscall command is decided
(`syscall_commands_covered`).

## Theorems (general: every record, every command)

* `step_rejected_unchanged` (rollback): every rejection returns the record
  itself.
* `step_bounded` (the representation is closed under steps).
* `step_frames_conserved` (accounting): the frames of the parent and its
  children never change in number; `step_memory_within` keeps the parent's
  memory within its frames; `step_budget` keeps the children within the
  subject budget.
* `step_retired_forever` and `retired_rejected` (stale handles): a control
  word that names no live entry and whose generation was issued never names
  one again, and every grant or termination presenting it is rejected with
  the record unchanged; `terminate_retires` retires the word it terminated.
* `spawn_exact` (inheritance exactness at the allocator): an accepted spawn
  records exactly one new child, in the first free slot, with charge zero and
  the fresh generation, and changes nothing else but the four counters.
* `step_confined` (confinement at the allocator): a grant or termination
  changes only the entry its control word names and the parent's frames; a
  memory command changes no child entry.
* the exhaustion theorems: each counter at its bound is a typed rejection
  with the record unchanged, without any hand-picked seed.

`LeanOS.SpawnAllocatorWords` packs a record into thirteen words and decides
`step` with fixed-width code that the boot image runs;
`LeanOS.SpawnAllocatorSimulation` proves every decided command is one
composite gate step on every `Family` state.
-/
namespace LeanOS.SpawnAllocator

open LeanOS
open LeanOS.FailStop
open LeanOS.SpawnOracle
open LeanOS.SpawnAccountingOracle

set_option linter.unusedSimpArgs false

/-! ## The representation -/

/-- Child-table slots the representation holds.  A subject budget above it
is outside the representation. -/
def childCapacity : Nat := 4

/-- The parent's capability slots (`Capability.State.slotCapacity`). -/
def parentSlots : Nat := 4

/-- The first of the parent's slots that can hold memory; slots 0 and 1 hold
the endpoint and the address-space root. -/
def memoryBase : Nat := 2

/-- The parent's memory slots, `memoryBase` to `parentSlots - 1`. -/
def memoryCapacity : Nat := parentSlots - memoryBase

/-- The identity of the parent's endpoint capability in slot 0. -/
def endpointIdentity : Nat := 3

/-- The identity of the parent's address-space root in slot 1. -/
def spaceIdentity : Nat := 4

/-- The family's parent and bystander. -/
def parent : Nat := 2
def bystander : Nat := 1

/-- A word's range. -/
def wordBound : Nat := 2 ^ 64

/-- The frame-count range of the packed representation. -/
def frameBound : Nat := 2 ^ 16

/-- One child-table entry: the generation of its control word and the frames
charged to the child.  The child's identity is not a decision input. -/
structure ChildRecord where
  generation : Nat
  charge : Nat
  deriving DecidableEq, Repr

/-- The allocator record. -/
structure State where
  subjectNext : Nat
  objectNext : Nat
  capabilityNext : Nat
  controlNext : Nat
  authorityNext : Nat
  authority : Option Nat
  budget : Nat
  children : List (Option ChildRecord)
  memory : List (Option Nat)
  parentFrames : Nat
  deriving DecidableEq, Repr

/-- The decision of one command: the successor record, the status byte
(`0x01` accepted, `0x80 + code` rejected), and the value word. -/
structure Step where
  next : State
  status : UInt64
  value : UInt64
  deriving DecidableEq, Repr

/-- The commands the allocator decides: the public spawn family and the
memory family, run by the parent. -/
inductive Command where
  | child (operation : ChildOperation)
  | memory (operation : MemoryOperation)
  deriving DecidableEq, Repr

/-! ## Reading the record -/

def State.childAt (state : State) (slot : Nat) : Option ChildRecord :=
  (state.children[slot]?).join

/-- The memory capability identity in a parent slot; slots 0 and 1 and every
slot past the parent's capacity hold none. -/
def State.memoryAt (state : State) (slot : Nat) : Option Nat :=
  if slot < memoryBase then none else (state.memory[slot - memoryBase]?).join

def State.childCount (state : State) : Nat := state.children.countP Option.isSome

/-- The frames charged in one child-table entry. -/
def entryCharge (entry : Option ChildRecord) : Nat := (entry.map ChildRecord.charge).getD 0

def State.chargeSum (state : State) : Nat := (state.children.map entryCharge).sum

def State.memoryUsed (state : State) : Nat := state.memory.countP Option.isSome

/-- The parent's free frames. -/
def State.available (state : State) : Nat := state.parentFrames - state.memoryUsed

/-- The first free child-table slot. -/
def State.freeSlot (state : State) : Option Nat := state.children.findIdx? Option.isNone

/-- Counter exhaustion, as `LifetimeIssuer.exhausted`. -/
def identityExhausted (next : Nat) : Bool :=
  next = 0 || LifetimeIssuer.identityReserved ≤ next

/-- Capability-identity exhaustion, as the composite's capability checks. -/
def capabilityExhausted (next : Nat) : Bool :=
  next = 0 || CapabilityHandle.generationReserved ≤ next

/-- Control-generation availability, as `controlGenerationAvailable`. -/
def controlAvailable (next : Nat) : Bool :=
  0 < next && next < CapabilityHandle.generationReserved

/-- Resolve an endpoint handle word in the parent's capability space:
`none` when it names the parent's endpoint, else the typed denial. -/
def State.resolveEndpoint (state : State) (word : UInt64) :
    Option CapabilityHandle.WordResolveDenial :=
  match CapabilityHandle.decode word with
  | .error reason => some (.malformed reason)
  | .ok handle =>
      if parentSlots ≤ handle.slot then some (.denied .outOfRange)
      else if handle.slot = 0 then
        if handle.identity = endpointIdentity then none else some (.denied .staleHandle)
      else if handle.slot = 1 then
        if handle.identity = spaceIdentity then some (.denied .kindMismatch)
        else some (.denied .staleHandle)
      else match state.memoryAt handle.slot with
        | none => some (.denied .staleHandle)
        | some identity =>
            if handle.identity = identity then some (.denied .kindMismatch)
            else some (.denied .staleHandle)

/-- Resolve a control word in the parent's child table, as
`FailStop.resolveControl`. -/
def State.resolveControl (state : State) (word : UInt64) :
    Except ControlDenial (Nat × ChildRecord) :=
  match CapabilityHandle.decode word with
  | .error reason => .error (.malformed reason)
  | .ok handle =>
      match state.childAt handle.slot with
      | some entry =>
          if entry.generation = handle.identity then .ok (handle.slot, entry) else .error .stale
      | none => .error .stale

/-- The control word of a child-table slot and generation. -/
def controlWord (slot generation : Nat) : UInt64 := UInt64.ofNat (slot + generation * 65536)

/-! ## The step -/

def rejectWith (state : State) (code : UInt64) : Step := ⟨state, 0x80 + code, 0⟩

def acceptWith (next : State) (value : UInt64) : Step := ⟨next, 0x01, value⟩

/-- **Charged spawn**, in the order of `FailStop.spawnCharged` and
`FailStop.spawn`. -/
def spawnStep (state : State) (request : SpawnRequest) : Step :=
  let reject := fun (error : ChildSpawnError) => rejectWith state (childSpawnErrorCode error)
  match state.authority with
  | none => reject (.spawn .missingSpawnRight)
  | some generation =>
      if generation ≠ request.spawnWord.toNat then reject (.spawn .staleSpawnCapability)
      else if state.budget ≤ state.childCount then reject .subjectBudgetExhausted
      else match state.freeSlot with
        | none => reject .subjectBudgetExhausted
        | some slot =>
            if controlAvailable state.controlNext = false then reject .controlGenerationExhausted
            else if identityExhausted state.subjectNext then reject (.spawn .identityExhausted)
            else if identityExhausted state.objectNext then
              reject (.spawn .addressSpaceIdentityExhausted)
            else if capabilityExhausted state.capabilityNext then
              reject (.spawn (.addressSpaceRejected .generationExhausted))
            else match state.resolveEndpoint request.endpointWord with
              | some denial => reject (.spawn (.endpointHandle denial))
              | none =>
                  if Capability.rightsValid .endpoint request.rights = false then
                    reject (.spawn .invalidRights)
                  else
                    acceptWith
                      { state with
                        subjectNext := state.subjectNext + 1
                        objectNext := state.objectNext + 1
                        capabilityNext := state.capabilityNext + 2
                        controlNext := state.controlNext + 1
                        children := state.children.set slot
                          (some { generation := state.controlNext, charge := 0 }) }
                      (controlWord slot state.controlNext)

/-- **A frame slice for a child.** -/
def grantStep (state : State) (control : UInt64) (frames : Nat) : Step :=
  match state.resolveControl control with
  | .error denial => rejectWith state (frameGrantErrorCode (.control denial))
  | .ok (slot, entry) =>
      if state.available < frames then rejectWith state (frameGrantErrorCode .frameBudgetExhausted)
      else
        acceptWith
          { state with
            parentFrames := state.parentFrames - frames
            children := state.children.set slot (some { entry with charge := entry.charge + frames }) }
          (UInt64.ofNat frames)

/-- **Child termination**: the child's frames return to the parent. -/
def terminateStep (state : State) (control : UInt64) : Step :=
  match state.resolveControl control with
  | .error denial => rejectWith state (controlDenialCode denial)
  | .ok (slot, entry) =>
      acceptWith
        { state with
          parentFrames := state.parentFrames + entry.charge
          children := state.children.set slot none }
        (UInt64.ofNat entry.charge)

/-- The status of a rejected kernel grant of spawn authority. -/
def authorityRejected (state : State) : Step := ⟨state, 0x80, 0⟩

/-- **Kernel grant of spawn authority**, as `grantBudgetedAuthority`.  An
accepted grant to the bystander, or with a subject budget the representation
does not hold, is outside the representation. -/
def grantAuthorityStep (state : State) (subject budget : Nat) : Option Step :=
  if subject = parent then
    if budget ≤ childSlots ∧ state.childCount ≤ budget then
      if childCapacity < budget ∨ wordBound ≤ state.authorityNext + 1 then none
      else some (acceptWith
        { state with
          authority := some state.authorityNext
          budget
          authorityNext := state.authorityNext + 1 }
        (UInt64.ofNat state.authorityNext))
    else some (authorityRejected state)
  else if subject = bystander then
    if budget ≤ childSlots then none else some (authorityRejected state)
  else some (authorityRejected state)

/-- **Kernel revocation of spawn authority.** -/
def revokeAuthorityStep (state : State) (subject : Nat) : Step :=
  if subject = parent then acceptWith { state with authority := none, budget := 0 } 0
  else acceptWith state 0

/-- The memory family's codes (`SpawnFamily.memoryErrorCode`). -/
def memoryCode : MemoryError → UInt64
  | .invalidSubject => 0x01 | .outOfRange => 0x02 | .capabilityIdentityExhausted => 0x03
  | .occupiedSlot => 0x04 | .objectIdentityExhausted => 0x05 | .objectUnavailable => 0x06
  | .frameBudgetExhausted => 0x07 | .frameUnavailable => 0x08 | .staleSlot => 0x09
  | .kindMismatch => 0x0a | .missingRevoke => 0x0b | .retiredObject => 0x0c
  | .allocatorMismatch => 0x0d | .notOwner => 0x0e

/-- **Budget-charged allocation** into a parent slot, as `allocateDecision`. -/
def allocateStep (state : State) (slot : Nat) : Step :=
  let reject := fun (error : MemoryError) => rejectWith state (memoryCode error)
  if CapabilityHandle.slotReserved ≤ slot ∨ parentSlots ≤ slot then reject .outOfRange
  else if capabilityExhausted state.capabilityNext then reject .capabilityIdentityExhausted
  else if slot < memoryBase ∨ (state.memoryAt slot).isSome then reject .occupiedSlot
  else if identityExhausted state.objectNext then reject .objectIdentityExhausted
  else if state.available = 0 then reject .frameBudgetExhausted
  else
    acceptWith
      { state with
        capabilityNext := state.capabilityNext + 1
        objectNext := state.objectNext + 1
        memory := state.memory.set (slot - memoryBase) (some state.capabilityNext) }
      0

/-- **Release** of a parent memory slot, as `releaseDecision`. -/
def releaseStep (state : State) (slot : Nat) : Step :=
  if parentSlots ≤ slot then rejectWith state (memoryCode .staleSlot)
  else if slot < memoryBase then rejectWith state (memoryCode .kindMismatch)
  else match state.memoryAt slot with
    | none => rejectWith state (memoryCode .staleSlot)
    | some _ => acceptWith { state with memory := state.memory.set (slot - memoryBase) none } 0

/-- **The allocator.**  `none` only for the kernel grants outside the
representation (`grantAuthorityStep`). -/
def step (state : State) : Command → Option Step
  | .child (.spawn request) => some (spawnStep state request)
  | .child (.grantFrames control frames) => some (grantStep state control frames)
  | .child (.terminateChild control) => some (terminateStep state control)
  | .child (.grantAuthority subject budget) => grantAuthorityStep state subject budget
  | .child (.revokeAuthority subject) => some (revokeAuthorityStep state subject)
  | .memory (.allocate slot) => some (allocateStep state slot)
  | .memory (.release slot) => some (releaseStep state slot)

/-- The syscall commands: spawn, grant, terminate, allocate, release. -/
def Command.isSyscall : Command → Bool
  | .child (.spawn _) | .child (.grantFrames _ _) | .child (.terminateChild _) => true
  | .memory _ => true
  | _ => false

/-- **Every syscall command is decided.** -/
theorem syscall_commands_covered (state : State) (command : Command)
    (syscall : command.isSyscall = true) : (step state command).isSome = true := by
  rcases command with (_ | _ | _ | _ | _) | (_ | _) <;>
    simp_all [Command.isSyscall, step]

/-! ## The bounded representation -/

/-- The records the packed representation holds.  Every counter fits a word,
the tables have their fixed lengths, generations and identities are nonzero
and in their domains, and the frames fit the frame field. -/
structure Bounded (state : State) : Prop where
  subjectNext : state.subjectNext < wordBound
  objectNext : state.objectNext < wordBound
  capabilityNext : state.capabilityNext < wordBound
  controlNext : state.controlNext < wordBound
  authorityPositive : 0 < state.authorityNext
  authorityNext : state.authorityNext < wordBound
  authority : ∀ generation, state.authority = some generation →
    0 < generation ∧ generation < wordBound
  budget : state.budget ≤ childCapacity
  childrenLength : state.children.length = childCapacity
  memoryLength : state.memory.length = memoryCapacity
  childRecords : ∀ entry, some entry ∈ state.children →
    0 < entry.generation ∧ entry.generation < CapabilityHandle.generationReserved
  memoryRecords : ∀ identity, some identity ∈ state.memory → 0 < identity ∧ identity < wordBound
  frames : state.parentFrames + state.chargeSum < frameBound

/-! ## Basic facts -/

theorem rejectWith_next (state : State) (code : UInt64) : (rejectWith state code).next = state := rfl

theorem rejectWith_status (state : State) (code : UInt64) :
    (rejectWith state code).status = 0x80 + code := rfl

theorem acceptWith_status (next : State) (value : UInt64) : (acceptWith next value).status = 0x01 :=
  rfl

/-- Every code the allocator rejects with is below `0x7f`, so a rejection's
status byte is never `0x01`. -/
theorem childSpawnErrorCode_lt (error : ChildSpawnError) : childSpawnErrorCode error < 0x7f := by
  cases error with
  | spawn reason =>
      cases reason <;> (try rename_i inner; cases inner) <;> (try rename_i innermost; cases innermost) <;>
        decide
  | subjectBudgetExhausted => decide
  | controlGenerationExhausted => decide

theorem frameGrantErrorCode_lt (error : FrameGrantError) : frameGrantErrorCode error < 0x7f := by
  cases error <;> (try rename_i reason; cases reason) <;> (try rename_i inner; cases inner) <;> decide

theorem controlDenialCode_lt (denial : ControlDenial) : controlDenialCode denial < 0x7f := by
  cases denial <;> (try rename_i reason; cases reason) <;> decide

theorem memoryCode_lt (error : MemoryError) : memoryCode error < 0x7f := by
  cases error <;> decide

theorem reject_status_ne {code : UInt64} (small : code < 0x7f) : (0x80 : UInt64) + code ≠ 0x01 := by
  intro same
  have := congrArg UInt64.toNat same
  rw [UInt64.lt_iff_toNat_lt] at small
  simp at small this
  omega

/-! ## Rollback -/

/-- A step either returns the record itself with value zero, or is accepted. -/
def Decided (state : State) (result : Step) : Prop :=
  (result.next = state ∧ result.value = 0) ∨ result.status = 0x01

theorem spawnStep_decided (state : State) (request : SpawnRequest) :
    Decided state (spawnStep state request) := by
  dsimp only [spawnStep]
  repeat' split
  all_goals first | exact Or.inl ⟨rfl, rfl⟩ | exact Or.inr rfl

theorem grantStep_decided (state : State) (control : UInt64) (frames : Nat) :
    Decided state (grantStep state control frames) := by
  dsimp only [grantStep]
  repeat' split
  all_goals first | exact Or.inl ⟨rfl, rfl⟩ | exact Or.inr rfl

theorem terminateStep_decided (state : State) (control : UInt64) :
    Decided state (terminateStep state control) := by
  dsimp only [terminateStep]
  repeat' split
  all_goals first | exact Or.inl ⟨rfl, rfl⟩ | exact Or.inr rfl

theorem grantAuthorityStep_decided (state : State) (subject budget : Nat) (result : Step)
    (decided : grantAuthorityStep state subject budget = some result) : Decided state result := by
  unfold grantAuthorityStep at decided
  repeat' split at decided
  all_goals simp only [Option.some.injEq, reduceCtorEq] at decided
  all_goals subst decided
  all_goals first | exact Or.inl ⟨rfl, rfl⟩ | exact Or.inr rfl

theorem revokeAuthorityStep_decided (state : State) (subject : Nat) :
    Decided state (revokeAuthorityStep state subject) := by
  dsimp only [revokeAuthorityStep]
  split <;> exact Or.inr rfl

theorem allocateStep_decided (state : State) (slot : Nat) :
    Decided state (allocateStep state slot) := by
  dsimp only [allocateStep]
  repeat' split
  all_goals first | exact Or.inl ⟨rfl, rfl⟩ | exact Or.inr rfl

theorem releaseStep_decided (state : State) (slot : Nat) :
    Decided state (releaseStep state slot) := by
  dsimp only [releaseStep]
  repeat' split
  all_goals first | exact Or.inl ⟨rfl, rfl⟩ | exact Or.inr rfl

theorem step_decided (state : State) (command : Command) (result : Step)
    (decided : step state command = some result) : Decided state result := by
  rcases command with (request | ⟨control, frames⟩ | control | ⟨subject, budget⟩ | subject) |
    (slot | slot) <;>
    simp only [step, Option.some.injEq] at decided
  · subst decided; exact spawnStep_decided _ _
  · subst decided; exact grantStep_decided _ _ _
  · subst decided; exact terminateStep_decided _ _
  · exact grantAuthorityStep_decided _ _ _ _ decided
  · subst decided; exact revokeAuthorityStep_decided _ _
  · subst decided; exact allocateStep_decided _ _
  · subst decided; exact releaseStep_decided _ _

/-- **Rollback.**  Every rejected command returns the record itself. -/
theorem step_rejected_unchanged (state : State) (command : Command) (result : Step)
    (decided : step state command = some result) (rejected : result.status ≠ 0x01) :
    result.next = state := by
  rcases step_decided state command result decided with ⟨same, _⟩ | accepted
  · exact same
  · exact absurd accepted rejected

/-- A rejected command has value word zero. -/
theorem step_rejected_value (state : State) (command : Command) (result : Step)
    (decided : step state command = some result) (rejected : result.status ≠ 0x01) :
    result.value = 0 := by
  rcases step_decided state command result decided with ⟨_, zero⟩ | accepted
  · exact zero
  · exact absurd accepted rejected

/-! ## Inversion of accepted steps -/

theorem rejectWith_status_ne {state : State} {code : UInt64} (small : code < 0x7f) :
    (rejectWith state code).status ≠ 0x01 := reject_status_ne small

/-- The record after an accepted spawn into `slot`. -/
def spawned (state : State) (slot : Nat) : State :=
  { state with
    subjectNext := state.subjectNext + 1
    objectNext := state.objectNext + 1
    capabilityNext := state.capabilityNext + 2
    controlNext := state.controlNext + 1
    children := state.children.set slot (some { generation := state.controlNext, charge := 0 }) }

/-- Everything an accepted spawn checked and did. -/
theorem spawnStep_accepted (state : State) (request : SpawnRequest)
    (accepted : (spawnStep state request).status = 0x01) :
    ∃ slot, state.authority = some request.spawnWord.toNat ∧ state.childCount < state.budget ∧
      state.freeSlot = some slot ∧ controlAvailable state.controlNext = true ∧
      identityExhausted state.subjectNext = false ∧ identityExhausted state.objectNext = false ∧
      capabilityExhausted state.capabilityNext = false ∧
      state.resolveEndpoint request.endpointWord = none ∧
      Capability.rightsValid .endpoint request.rights = true ∧
      spawnStep state request = acceptWith (spawned state slot) (controlWord slot state.controlNext) := by
  have small := childSpawnErrorCode_lt
  dsimp only [spawnStep] at accepted ⊢
  split at accepted
  · exact absurd accepted (rejectWith_status_ne (small _))
  next generation held =>
  split at accepted
  · exact absurd accepted (rejectWith_status_ne (small _))
  next same =>
  split at accepted
  · exact absurd accepted (rejectWith_status_ne (small _))
  next room =>
  split at accepted
  · exact absurd accepted (rejectWith_status_ne (small _))
  next slot free =>
  split at accepted
  · exact absurd accepted (rejectWith_status_ne (small _))
  next control =>
  split at accepted
  · exact absurd accepted (rejectWith_status_ne (small _))
  next subjects =>
  split at accepted
  · exact absurd accepted (rejectWith_status_ne (small _))
  next objects =>
  split at accepted
  · exact absurd accepted (rejectWith_status_ne (small _))
  next capabilities =>
  split at accepted
  · exact absurd accepted (rejectWith_status_ne (small _))
  next resolved =>
  split at accepted
  · exact absurd accepted (rejectWith_status_ne (small _))
  next valid =>
  refine ⟨slot, by simp only [Decidable.not_not] at same; rw [held, same], by omega, free,
    by simpa using control, by simpa using subjects, by simpa using objects,
    by simpa using capabilities, resolved, by simpa using valid, ?_⟩
  simp only [held, same, room, free, control, subjects, objects, capabilities, resolved, valid,
    ne_eq, not_true_eq_false, ↓reduceIte, Bool.false_eq_true, spawned]
  simp

/-- The record after an accepted grant of `frames` frames to the entry in
`slot`. -/
def granted (state : State) (slot : Nat) (entry : ChildRecord) (frames : Nat) : State :=
  { state with
    parentFrames := state.parentFrames - frames
    children := state.children.set slot (some { entry with charge := entry.charge + frames }) }

theorem grantStep_accepted (state : State) (control : UInt64) (frames : Nat)
    (accepted : (grantStep state control frames).status = 0x01) :
    ∃ slot entry, state.resolveControl control = .ok (slot, entry) ∧ frames ≤ state.available ∧
      grantStep state control frames =
        acceptWith (granted state slot entry frames) (UInt64.ofNat frames) := by
  dsimp only [grantStep] at accepted ⊢
  split at accepted
  · exact absurd accepted (rejectWith_status_ne (frameGrantErrorCode_lt _))
  next slot entry resolved =>
  split at accepted
  · exact absurd accepted (rejectWith_status_ne (frameGrantErrorCode_lt _))
  next enough =>
  refine ⟨slot, entry, resolved, by omega, ?_⟩
  simp [resolved, enough, granted]

/-- The record after an accepted termination of the entry in `slot`. -/
def terminated (state : State) (slot : Nat) (entry : ChildRecord) : State :=
  { state with
    parentFrames := state.parentFrames + entry.charge
    children := state.children.set slot none }

theorem terminateStep_accepted (state : State) (control : UInt64)
    (accepted : (terminateStep state control).status = 0x01) :
    ∃ slot entry, state.resolveControl control = .ok (slot, entry) ∧
      terminateStep state control =
        acceptWith (terminated state slot entry) (UInt64.ofNat entry.charge) := by
  dsimp only [terminateStep] at accepted ⊢
  split at accepted
  · exact absurd accepted (rejectWith_status_ne (controlDenialCode_lt _))
  next slot entry resolved =>
  exact ⟨slot, entry, resolved, by simp [resolved, terminated]⟩

/-- The record after an accepted allocation into `slot`. -/
def allocated (state : State) (slot : Nat) : State :=
  { state with
    capabilityNext := state.capabilityNext + 1
    objectNext := state.objectNext + 1
    memory := state.memory.set (slot - memoryBase) (some state.capabilityNext) }

theorem allocateStep_accepted (state : State) (slot : Nat)
    (accepted : (allocateStep state slot).status = 0x01) :
    slot < parentSlots ∧ memoryBase ≤ slot ∧ state.memoryAt slot = none ∧
      capabilityExhausted state.capabilityNext = false ∧
      identityExhausted state.objectNext = false ∧ 0 < state.available ∧
      allocateStep state slot = acceptWith (allocated state slot) 0 := by
  dsimp only [allocateStep] at accepted ⊢
  split at accepted
  · exact absurd accepted (rejectWith_status_ne (memoryCode_lt _))
  next range =>
  split at accepted
  · exact absurd accepted (rejectWith_status_ne (memoryCode_lt _))
  next capabilities =>
  split at accepted
  · exact absurd accepted (rejectWith_status_ne (memoryCode_lt _))
  next occupied =>
  split at accepted
  · exact absurd accepted (rejectWith_status_ne (memoryCode_lt _))
  next objects =>
  split at accepted
  · exact absurd accepted (rejectWith_status_ne (memoryCode_lt _))
  next frames =>
  simp only [not_or, Nat.not_le, Nat.not_lt] at range occupied
  have empty : state.memoryAt slot = none := by
    cases h : state.memoryAt slot
    · rfl
    · exact absurd (by simp [h]) occupied.2
  refine ⟨range.2, occupied.1, empty, by simpa using capabilities, by simpa using objects,
    by omega, ?_⟩
  simp only [allocated]
  simp [range.2, Nat.not_lt.2 occupied.1, empty, capabilities, objects, frames,
    Nat.not_le.2 range.2]
  omega

/-- The record after an accepted release of `slot`. -/
def released (state : State) (slot : Nat) : State :=
  { state with memory := state.memory.set (slot - memoryBase) none }

theorem releaseStep_accepted (state : State) (slot : Nat)
    (accepted : (releaseStep state slot).status = 0x01) :
    ∃ identity, slot < parentSlots ∧ memoryBase ≤ slot ∧ state.memoryAt slot = some identity ∧
      releaseStep state slot = acceptWith (released state slot) 0 := by
  dsimp only [releaseStep] at accepted ⊢
  split at accepted
  · exact absurd accepted (rejectWith_status_ne (memoryCode_lt _))
  next range =>
  split at accepted
  · exact absurd accepted (rejectWith_status_ne (memoryCode_lt _))
  next low =>
  split at accepted
  · exact absurd accepted (rejectWith_status_ne (memoryCode_lt _))
  next identity held =>
  exact ⟨identity, by omega, by omega, held, by simp [range, low, held, released]⟩

/-- The record after an accepted kernel grant of spawn authority. -/
def authorized (state : State) (budget : Nat) : State :=
  { state with
    authority := some state.authorityNext
    budget
    authorityNext := state.authorityNext + 1 }

theorem grantAuthorityStep_accepted (state : State) (subject budget : Nat) (result : Step)
    (decided : grantAuthorityStep state subject budget = some result)
    (accepted : result.status = 0x01) :
    subject = parent ∧ budget ≤ childCapacity ∧ state.childCount ≤ budget ∧
      state.authorityNext + 1 < wordBound ∧
      result = acceptWith (authorized state budget) (UInt64.ofNat state.authorityNext) := by
  unfold grantAuthorityStep at decided
  split at decided
  next isParent =>
    split at decided
    next allowed =>
      split at decided
      · cases decided
      next representable =>
        simp only [Option.some.injEq] at decided
        subst decided
        simp only [not_or, Nat.not_lt, Nat.not_le] at representable
        exact ⟨isParent, representable.1, allowed.2, representable.2, rfl⟩
    · simp only [Option.some.injEq] at decided
      subst decided
      exact absurd accepted (by simp [authorityRejected])
  · split at decided
    · split at decided
      · cases decided
      · simp only [Option.some.injEq] at decided
        subst decided
        exact absurd accepted (by simp [authorityRejected])
    · simp only [Option.some.injEq] at decided
      subst decided
      exact absurd accepted (by simp [authorityRejected])

/-! ## Fields of the accepted successors -/

@[simp] theorem spawned_subjectNext (state : State) (slot : Nat) :
    (spawned state slot).subjectNext = state.subjectNext + 1 := rfl

@[simp] theorem spawned_objectNext (state : State) (slot : Nat) :
    (spawned state slot).objectNext = state.objectNext + 1 := rfl

@[simp] theorem spawned_capabilityNext (state : State) (slot : Nat) :
    (spawned state slot).capabilityNext = state.capabilityNext + 2 := rfl

@[simp] theorem spawned_controlNext (state : State) (slot : Nat) :
    (spawned state slot).controlNext = state.controlNext + 1 := rfl

@[simp] theorem spawned_authorityNext (state : State) (slot : Nat) :
    (spawned state slot).authorityNext = state.authorityNext := rfl

@[simp] theorem spawned_authority (state : State) (slot : Nat) :
    (spawned state slot).authority = state.authority := rfl

@[simp] theorem spawned_budget (state : State) (slot : Nat) :
    (spawned state slot).budget = state.budget := rfl

@[simp] theorem spawned_children (state : State) (slot : Nat) :
    (spawned state slot).children = state.children.set slot (some { generation := state.controlNext, charge := 0 }) := rfl

@[simp] theorem spawned_memory (state : State) (slot : Nat) :
    (spawned state slot).memory = state.memory := rfl

@[simp] theorem spawned_parentFrames (state : State) (slot : Nat) :
    (spawned state slot).parentFrames = state.parentFrames := rfl

@[simp] theorem spawned_memoryUsed (state : State) (slot : Nat) :
    (spawned state slot).memoryUsed = state.memoryUsed := rfl

@[simp] theorem spawned_memoryAt (state : State) (slot : Nat) (other : Nat) :
    (spawned state slot).memoryAt other = state.memoryAt other := rfl

@[simp] theorem granted_subjectNext (state : State) (slot : Nat) (entry : ChildRecord) (frames : Nat) :
    (granted state slot entry frames).subjectNext = state.subjectNext := rfl

@[simp] theorem granted_objectNext (state : State) (slot : Nat) (entry : ChildRecord) (frames : Nat) :
    (granted state slot entry frames).objectNext = state.objectNext := rfl

@[simp] theorem granted_capabilityNext (state : State) (slot : Nat) (entry : ChildRecord) (frames : Nat) :
    (granted state slot entry frames).capabilityNext = state.capabilityNext := rfl

@[simp] theorem granted_controlNext (state : State) (slot : Nat) (entry : ChildRecord) (frames : Nat) :
    (granted state slot entry frames).controlNext = state.controlNext := rfl

@[simp] theorem granted_authorityNext (state : State) (slot : Nat) (entry : ChildRecord) (frames : Nat) :
    (granted state slot entry frames).authorityNext = state.authorityNext := rfl

@[simp] theorem granted_authority (state : State) (slot : Nat) (entry : ChildRecord) (frames : Nat) :
    (granted state slot entry frames).authority = state.authority := rfl

@[simp] theorem granted_budget (state : State) (slot : Nat) (entry : ChildRecord) (frames : Nat) :
    (granted state slot entry frames).budget = state.budget := rfl

@[simp] theorem granted_children (state : State) (slot : Nat) (entry : ChildRecord) (frames : Nat) :
    (granted state slot entry frames).children = state.children.set slot (some { entry with charge := entry.charge + frames }) := rfl

@[simp] theorem granted_memory (state : State) (slot : Nat) (entry : ChildRecord) (frames : Nat) :
    (granted state slot entry frames).memory = state.memory := rfl

@[simp] theorem granted_parentFrames (state : State) (slot : Nat) (entry : ChildRecord) (frames : Nat) :
    (granted state slot entry frames).parentFrames = state.parentFrames - frames := rfl

@[simp] theorem granted_memoryUsed (state : State) (slot : Nat) (entry : ChildRecord) (frames : Nat) :
    (granted state slot entry frames).memoryUsed = state.memoryUsed := rfl

@[simp] theorem granted_memoryAt (state : State) (slot : Nat) (entry : ChildRecord) (frames : Nat) (other : Nat) :
    (granted state slot entry frames).memoryAt other = state.memoryAt other := rfl

@[simp] theorem terminated_subjectNext (state : State) (slot : Nat) (entry : ChildRecord) :
    (terminated state slot entry).subjectNext = state.subjectNext := rfl

@[simp] theorem terminated_objectNext (state : State) (slot : Nat) (entry : ChildRecord) :
    (terminated state slot entry).objectNext = state.objectNext := rfl

@[simp] theorem terminated_capabilityNext (state : State) (slot : Nat) (entry : ChildRecord) :
    (terminated state slot entry).capabilityNext = state.capabilityNext := rfl

@[simp] theorem terminated_controlNext (state : State) (slot : Nat) (entry : ChildRecord) :
    (terminated state slot entry).controlNext = state.controlNext := rfl

@[simp] theorem terminated_authorityNext (state : State) (slot : Nat) (entry : ChildRecord) :
    (terminated state slot entry).authorityNext = state.authorityNext := rfl

@[simp] theorem terminated_authority (state : State) (slot : Nat) (entry : ChildRecord) :
    (terminated state slot entry).authority = state.authority := rfl

@[simp] theorem terminated_budget (state : State) (slot : Nat) (entry : ChildRecord) :
    (terminated state slot entry).budget = state.budget := rfl

@[simp] theorem terminated_children (state : State) (slot : Nat) (entry : ChildRecord) :
    (terminated state slot entry).children = state.children.set slot none := rfl

@[simp] theorem terminated_memory (state : State) (slot : Nat) (entry : ChildRecord) :
    (terminated state slot entry).memory = state.memory := rfl

@[simp] theorem terminated_parentFrames (state : State) (slot : Nat) (entry : ChildRecord) :
    (terminated state slot entry).parentFrames = state.parentFrames + entry.charge := rfl

@[simp] theorem terminated_memoryUsed (state : State) (slot : Nat) (entry : ChildRecord) :
    (terminated state slot entry).memoryUsed = state.memoryUsed := rfl

@[simp] theorem terminated_memoryAt (state : State) (slot : Nat) (entry : ChildRecord) (other : Nat) :
    (terminated state slot entry).memoryAt other = state.memoryAt other := rfl

@[simp] theorem allocated_subjectNext (state : State) (slot : Nat) :
    (allocated state slot).subjectNext = state.subjectNext := rfl

@[simp] theorem allocated_objectNext (state : State) (slot : Nat) :
    (allocated state slot).objectNext = state.objectNext + 1 := rfl

@[simp] theorem allocated_capabilityNext (state : State) (slot : Nat) :
    (allocated state slot).capabilityNext = state.capabilityNext + 1 := rfl

@[simp] theorem allocated_controlNext (state : State) (slot : Nat) :
    (allocated state slot).controlNext = state.controlNext := rfl

@[simp] theorem allocated_authorityNext (state : State) (slot : Nat) :
    (allocated state slot).authorityNext = state.authorityNext := rfl

@[simp] theorem allocated_authority (state : State) (slot : Nat) :
    (allocated state slot).authority = state.authority := rfl

@[simp] theorem allocated_budget (state : State) (slot : Nat) :
    (allocated state slot).budget = state.budget := rfl

@[simp] theorem allocated_children (state : State) (slot : Nat) :
    (allocated state slot).children = state.children := rfl

@[simp] theorem allocated_memory (state : State) (slot : Nat) :
    (allocated state slot).memory = state.memory.set (slot - memoryBase) (some state.capabilityNext) := rfl

@[simp] theorem allocated_parentFrames (state : State) (slot : Nat) :
    (allocated state slot).parentFrames = state.parentFrames := rfl

@[simp] theorem allocated_childCount (state : State) (slot : Nat) :
    (allocated state slot).childCount = state.childCount := rfl

@[simp] theorem allocated_chargeSum (state : State) (slot : Nat) :
    (allocated state slot).chargeSum = state.chargeSum := rfl

@[simp] theorem allocated_childAt (state : State) (slot : Nat) (other : Nat) :
    (allocated state slot).childAt other = state.childAt other := rfl

@[simp] theorem released_subjectNext (state : State) (slot : Nat) :
    (released state slot).subjectNext = state.subjectNext := rfl

@[simp] theorem released_objectNext (state : State) (slot : Nat) :
    (released state slot).objectNext = state.objectNext := rfl

@[simp] theorem released_capabilityNext (state : State) (slot : Nat) :
    (released state slot).capabilityNext = state.capabilityNext := rfl

@[simp] theorem released_controlNext (state : State) (slot : Nat) :
    (released state slot).controlNext = state.controlNext := rfl

@[simp] theorem released_authorityNext (state : State) (slot : Nat) :
    (released state slot).authorityNext = state.authorityNext := rfl

@[simp] theorem released_authority (state : State) (slot : Nat) :
    (released state slot).authority = state.authority := rfl

@[simp] theorem released_budget (state : State) (slot : Nat) :
    (released state slot).budget = state.budget := rfl

@[simp] theorem released_children (state : State) (slot : Nat) :
    (released state slot).children = state.children := rfl

@[simp] theorem released_memory (state : State) (slot : Nat) :
    (released state slot).memory = state.memory.set (slot - memoryBase) none := rfl

@[simp] theorem released_parentFrames (state : State) (slot : Nat) :
    (released state slot).parentFrames = state.parentFrames := rfl

@[simp] theorem released_childCount (state : State) (slot : Nat) :
    (released state slot).childCount = state.childCount := rfl

@[simp] theorem released_chargeSum (state : State) (slot : Nat) :
    (released state slot).chargeSum = state.chargeSum := rfl

@[simp] theorem released_childAt (state : State) (slot : Nat) (other : Nat) :
    (released state slot).childAt other = state.childAt other := rfl

@[simp] theorem authorized_subjectNext (state : State) (budget : Nat) :
    (authorized state budget).subjectNext = state.subjectNext := rfl

@[simp] theorem authorized_objectNext (state : State) (budget : Nat) :
    (authorized state budget).objectNext = state.objectNext := rfl

@[simp] theorem authorized_capabilityNext (state : State) (budget : Nat) :
    (authorized state budget).capabilityNext = state.capabilityNext := rfl

@[simp] theorem authorized_controlNext (state : State) (budget : Nat) :
    (authorized state budget).controlNext = state.controlNext := rfl

@[simp] theorem authorized_authorityNext (state : State) (budget : Nat) :
    (authorized state budget).authorityNext = state.authorityNext + 1 := rfl

@[simp] theorem authorized_authority (state : State) (budget : Nat) :
    (authorized state budget).authority = some state.authorityNext := rfl

@[simp] theorem authorized_budget (state : State) (budget : Nat) :
    (authorized state budget).budget = budget := rfl

@[simp] theorem authorized_children (state : State) (budget : Nat) :
    (authorized state budget).children = state.children := rfl

@[simp] theorem authorized_memory (state : State) (budget : Nat) :
    (authorized state budget).memory = state.memory := rfl

@[simp] theorem authorized_parentFrames (state : State) (budget : Nat) :
    (authorized state budget).parentFrames = state.parentFrames := rfl

@[simp] theorem authorized_childCount (state : State) (budget : Nat) :
    (authorized state budget).childCount = state.childCount := rfl

@[simp] theorem authorized_chargeSum (state : State) (budget : Nat) :
    (authorized state budget).chargeSum = state.chargeSum := rfl

@[simp] theorem authorized_childAt (state : State) (budget : Nat) (other : Nat) :
    (authorized state budget).childAt other = state.childAt other := rfl

@[simp] theorem authorized_memoryUsed (state : State) (budget : Nat) :
    (authorized state budget).memoryUsed = state.memoryUsed := rfl

@[simp] theorem authorized_memoryAt (state : State) (budget : Nat) (other : Nat) :
    (authorized state budget).memoryAt other = state.memoryAt other := rfl

/-! ## Facts about the tables -/

theorem sum_set (values : List Nat) (index value : Nat) (inRange : index < values.length) :
    (values.set index value).sum + values[index] = values.sum + value := by
  induction values generalizing index with
  | nil => simp at inRange
  | cons head tail ih =>
      cases index with
      | zero => simp; omega
      | succ index =>
          simp only [List.set_cons_succ, List.sum_cons, List.getElem_cons_succ]
          have := ih index (by simpa using inRange)
          omega

theorem childAt_some {state : State} {slot : Nat} {entry : ChildRecord}
    (found : state.childAt slot = some entry) :
    ∃ inRange : slot < state.children.length, state.children[slot] = some entry := by
  unfold State.childAt at found
  cases lookup : state.children[slot]? with
  | none => rw [lookup] at found; cases found
  | some value =>
      rw [lookup] at found
      simp only [Option.join_some] at found
      obtain ⟨inRange, eq⟩ := List.getElem?_eq_some_iff.1 lookup
      exact ⟨inRange, by rw [eq, found]⟩

theorem freeSlot_some {state : State} {slot : Nat} (found : state.freeSlot = some slot) :
    ∃ inRange : slot < state.children.length, state.children[slot] = none := by
  unfold State.freeSlot at found
  obtain ⟨inRange, free, _⟩ := List.findIdx?_eq_some_iff_getElem.1 found
  exact ⟨inRange, by simpa using free⟩

theorem resolveControl_ok {state : State} {word : UInt64} {slot : Nat} {entry : ChildRecord}
    (resolved : state.resolveControl word = .ok (slot, entry)) :
    CapabilityHandle.decode word = .ok { slot, identity := entry.generation } ∧
      state.childAt slot = some entry := by
  unfold State.resolveControl at resolved
  split at resolved
  · cases resolved
  next handle decoded =>
  split at resolved
  next found heldEntry =>
    split at resolved
    next same =>
      simp only [Except.ok.injEq, Prod.mk.injEq] at resolved
      obtain ⟨rfl, rfl⟩ := resolved
      refine ⟨?_, heldEntry⟩
      rw [decoded, same]
    · cases resolved
  · cases resolved

theorem childAt_set {next state : State} {slot : Nat} {entry : Option ChildRecord}
    (children : next.children = state.children.set slot entry)
    (inRange : slot < state.children.length) (other : Nat) :
    next.childAt other = if slot = other then entry else state.childAt other := by
  unfold State.childAt
  rw [children]
  simp only [List.getElem?_set]
  by_cases same : slot = other
  · subst same; simp [inRange]
  · simp [same]

theorem chargeSum_set {next state : State} {slot : Nat} {entry : Option ChildRecord}
    (children : next.children = state.children.set slot entry)
    (inRange : slot < state.children.length) :
    next.chargeSum + entryCharge state.children[slot] = state.chargeSum + entryCharge entry := by
  simp only [State.chargeSum, children, List.map_set]
  have := sum_set (state.children.map entryCharge) slot (entryCharge entry) (by simpa using inRange)
  simpa using this

theorem childCount_set {next state : State} {slot : Nat} {entry : Option ChildRecord}
    (children : next.children = state.children.set slot entry)
    (inRange : slot < state.children.length) :
    next.childCount + (if state.children[slot].isSome then 1 else 0) =
      state.childCount + (if entry.isSome then 1 else 0) := by
  simp only [State.childCount, children]
  rw [List.countP_set inRange]
  have le : (if state.children[slot].isSome = true then 1 else 0) ≤
      state.children.countP Option.isSome := by
    split
    · next some =>
      exact List.countP_pos_iff.2 ⟨_, List.getElem_mem inRange, some⟩
    · exact Nat.zero_le _
  omega

theorem memoryUsed_set {next state : State} {index : Nat} {entry : Option Nat}
    (memory : next.memory = state.memory.set index entry)
    (inRange : index < state.memory.length) :
    next.memoryUsed + (if state.memory[index].isSome then 1 else 0) =
      state.memoryUsed + (if entry.isSome then 1 else 0) := by
  simp only [State.memoryUsed, memory]
  rw [List.countP_set inRange]
  have le : (if state.memory[index].isSome = true then 1 else 0) ≤
      state.memory.countP Option.isSome := by
    split
    · next some =>
      exact List.countP_pos_iff.2 ⟨_, List.getElem_mem inRange, some⟩
    · exact Nat.zero_le _
  omega

theorem memoryAt_some {state : State} {slot identity : Nat}
    (found : state.memoryAt slot = some identity) :
    memoryBase ≤ slot ∧ ∃ inRange : slot - memoryBase < state.memory.length,
      state.memory[slot - memoryBase] = some identity := by
  unfold State.memoryAt at found
  split at found
  · cases found
  next high =>
  cases lookup : state.memory[slot - memoryBase]? with
  | none => rw [lookup] at found; cases found
  | some value =>
      rw [lookup] at found
      simp only [Option.join_some] at found
      obtain ⟨inRange, eq⟩ := List.getElem?_eq_some_iff.1 lookup
      exact ⟨by omega, inRange, by rw [eq, found]⟩

end LeanOS.SpawnAllocator
