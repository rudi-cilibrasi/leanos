import LeanOS.SpawnOracle
import LeanOS.FailStop.SpawnAccountingTraces

/-!
# Charged spawn, frame slices, and child termination: hosted oracle vectors

ADR 0010 gate item 5 for issues #490 and #491.  Like `LeanOS.SpawnOracle`,
this is a **hosted, Lean-side oracle only**: none of these commands is in the
generated boot dispatcher, none has a C export, and none is a ring-3 syscall
(`boot_dispatcher_rejects_child_tags`).  `childOracleStep` runs the public
spawn family (`childGate`), so the spawn command `0x7001` of `SpawnOracle`
is charged against the parent's subject budget here.

## Encoding

| Tag | Command | `arg0` | `arg1` | `arg2` | `arg3` |
| --- | --- | --- | --- | --- | --- |
| `0x7001` | spawn (as in `SpawnOracle`) | spawn generation | endpoint handle | rights | 0 |
| `0x7101` | grant frames | control word | frame count, nonzero | 0 | 0 |
| `0x7201` | terminate child | control word | 0 | 0 | 0 |

The control word is the `CapabilityHandle` word of the child-table slot and
the entry's generation.  `decodeChild_encodeGrant`, `encodeGrant_decodeChild`,
`decodeChild_encodeTerminate`, and `encodeTerminate_decodeChild` make both new
encodings canonical.

The result is two words.  The first is the tag with status `0x01` in bits
16..23 when accepted, or `0x80 + code` when rejected, one code per typed
error (`childSpawnErrorCode`, `frameGrantErrorCode`, `controlDenialCode`, each
injective).  The second is the control word of an accepted spawn, the frames
moved by an accepted grant, or the frames returned by an accepted
termination.

## Vectors

`framesSeed plan` is `SpawnOracle.spawnOracleSeed` with three free frames
(5, 6, 7) added to the composite allocator, frames 4 to 7 committed to
subject 2, and subject 2's spawn capability carrying subject budget 2.
`child_vectors_pass` checks, by closed evaluation on the sample boot plan:

- every `SpawnOracle` vector gives the same result through the charged
  oracle when the parent has a subject budget;
- accepted spawn returns control word `0x10000` (slot 0, generation 1) and
  records the child with charge zero;
- subject-budget exhaustion (budget 1 and a second spawn; budget 0 from the
  #489 grant) and frame-budget exhaustion are typed rejections with the
  pre-state;
- a frame grant moves exactly the requested free frames and charges them;
- child termination returns them, releases the child's capabilities,
  address space, and records;
- after termination the old control word is rejected with the pre-state,
  and still rejected after a new child reuses slot 0 with generation 2,
  whose control word is accepted;
- a parent's capability over the child's address space (copied to it by the
  child) is removed by the termination and its handle word stays stale after
  the respawn;
- another subject presenting a parent's control word is rejected;
- malformed and reserved command words are rejected before running.
-/
namespace LeanOS.SpawnAccountingOracle

open LeanOS
open LeanOS.FailStop
open LeanOS.SpawnOracle
open LeanOS.CompositeDispatcher (CommandWords DecodeError)

/-! ## Canonical encoding -/

def grantFramesTag : UInt64 := 0x7101
def terminateChildTag : UInt64 := 0x7201

def encodeGrant (control frames : UInt64) : CommandWords :=
  { tag := grantFramesTag, arg0 := control, arg1 := frames, arg2 := 0, arg3 := 0 }

def encodeTerminate (control : UInt64) : CommandWords :=
  { tag := terminateChildTag, arg0 := control, arg1 := 0, arg2 := 0, arg3 := 0 }

/-- Decode a command of the public spawn family.  Kernel grant and revocation
of spawn authority have no command words. -/
def decodeChild (words : CommandWords) : Except DecodeError ChildOperation :=
  if words.tag = spawnCommandTag then
    match decodeSpawn words with
    | .error reason => .error reason
    | .ok request => .ok (.spawn request)
  else if words.tag = grantFramesTag then
    if words.arg2 ≠ 0 ∨ words.arg3 ≠ 0 then .error .reservedBits
    else if words.arg1 = 0 then .error .noncanonicalArguments
    else .ok (.grantFrames words.arg0 words.arg1.toNat)
  else if words.tag = terminateChildTag then
    if words.arg1 ≠ 0 ∨ words.arg2 ≠ 0 ∨ words.arg3 ≠ 0 then .error .reservedBits
    else .ok (.terminateChild words.arg0)
  else .error .unknownCommand

theorem decodeChild_encodeGrant (control frames : UInt64) (nonzero : frames ≠ 0) :
    decodeChild (encodeGrant control frames) = .ok (.grantFrames control frames.toNat) := by
  simp [decodeChild, encodeGrant, grantFramesTag, spawnCommandTag, nonzero]

theorem decodeChild_encodeTerminate (control : UInt64) :
    decodeChild (encodeTerminate control) = .ok (.terminateChild control) := by
  simp [decodeChild, encodeTerminate, terminateChildTag, grantFramesTag, spawnCommandTag]

/-- **Canonical grant words.**  A word sequence that decodes to a frame grant
is exactly its encoding. -/
theorem encodeGrant_decodeChild (words : CommandWords) (control : UInt64) (frames : Nat)
    (decoded : decodeChild words = .ok (.grantFrames control frames)) :
    words = encodeGrant control (UInt64.ofNat frames) ∧ frames ≠ 0 := by
  unfold decodeChild at decoded
  split at decoded
  · split at decoded <;> simp at decoded
  next notSpawn =>
  split at decoded
  · next tag =>
    split at decoded
    · simp at decoded
    next reserved =>
    split at decoded
    · simp at decoded
    next nonzero =>
    simp only [Except.ok.injEq, ChildOperation.grantFrames.injEq] at decoded
    obtain ⟨rfl, rfl⟩ := decoded
    simp only [not_or, Decidable.not_not] at reserved
    refine ⟨?_, ?_⟩
    · cases words
      simp_all [encodeGrant]
    · intro zero
      apply nonzero
      have := UInt64.toNat_inj.1 (by rw [zero]; rfl : words.arg1.toNat = (0 : UInt64).toNat)
      exact this
  · split at decoded
    · split at decoded <;> simp at decoded
    · simp at decoded

/-- **Canonical termination words.** -/
theorem encodeTerminate_decodeChild (words : CommandWords) (control : UInt64)
    (decoded : decodeChild words = .ok (.terminateChild control)) :
    words = encodeTerminate control := by
  unfold decodeChild at decoded
  split at decoded
  · split at decoded <;> simp at decoded
  split at decoded
  · split at decoded
    · simp at decoded
    split at decoded <;> simp at decoded
  next notGrant =>
  split at decoded
  · next tag =>
    split at decoded
    · simp at decoded
    next reserved =>
    simp only [Except.ok.injEq, ChildOperation.terminateChild.injEq] at decoded
    subst decoded
    simp only [not_or, Decidable.not_not] at reserved
    cases words
    simp_all [encodeTerminate]
  · simp at decoded

/-- The generated boot dispatcher's version-one decoder knows neither new
tag: frame grants and child termination are not reachable through the boot
boundary. -/
theorem boot_dispatcher_rejects_child_tags (arg0 arg1 arg2 arg3 : UInt64) :
    CompositeDispatcher.decodeCommand
        { tag := grantFramesTag, arg0, arg1, arg2, arg3 } = .error .reservedBits ∧
      CompositeDispatcher.decodeCommand
        { tag := terminateChildTag, arg0, arg1, arg2, arg3 } = .error .reservedBits := by
  simp [CompositeDispatcher.decodeCommand, grantFramesTag, terminateChildTag,
    CompositeDispatcher.abiVersion]

/-! ## Result words -/

def controlDenialCode : ControlDenial → UInt64
  | .invalidParent => 0x40
  | .malformed .reservedSlot => 0x41
  | .malformed .reservedGeneration => 0x42
  | .stale => 0x43

def childSpawnErrorCode : ChildSpawnError → UInt64
  | .spawn reason => spawnErrorCode reason
  | .subjectBudgetExhausted => 0x0c
  | .controlGenerationExhausted => 0x0d

def frameGrantErrorCode : FrameGrantError → UInt64
  | .control reason => controlDenialCode reason
  | .childNotLive => 0x44
  | .frameBudgetExhausted => 0x45

def allControlDenials : List ControlDenial :=
  [.invalidParent, .malformed .reservedSlot, .malformed .reservedGeneration, .stale]

def allChildSpawnErrors : List ChildSpawnError :=
  allSpawnErrors.map .spawn ++ [.subjectBudgetExhausted, .controlGenerationExhausted]

def allFrameGrantErrors : List FrameGrantError :=
  allControlDenials.map .control ++ [.childNotLive, .frameBudgetExhausted]

theorem childSpawnErrorCodes_distinct : (allChildSpawnErrors.map childSpawnErrorCode).Nodup := by
  decide

theorem frameGrantErrorCodes_distinct : (allFrameGrantErrors.map frameGrantErrorCode).Nodup := by
  decide

theorem controlDenialCodes_distinct : (allControlDenials.map controlDenialCode).Nodup := by
  decide

theorem allChildSpawnErrors_complete (error : ChildSpawnError) : error ∈ allChildSpawnErrors := by
  cases error with
  | spawn reason =>
      exact List.mem_append_left _ (List.mem_map_of_mem (allSpawnErrors_complete reason))
  | subjectBudgetExhausted => decide
  | controlGenerationExhausted => decide

theorem allControlDenials_complete (denial : ControlDenial) : denial ∈ allControlDenials := by
  cases denial with
  | malformed reason => cases reason <;> decide
  | _ => decide

theorem allFrameGrantErrors_complete (error : FrameGrantError) : error ∈ allFrameGrantErrors := by
  cases error with
  | control reason =>
      exact List.mem_append_left _ (List.mem_map_of_mem (allControlDenials_complete reason))
  | _ => decide

def decodeChildSpawnErrorCode (code : UInt64) : Option ChildSpawnError :=
  allChildSpawnErrors.find? fun error => childSpawnErrorCode error == code

def decodeFrameGrantErrorCode (code : UInt64) : Option FrameGrantError :=
  allFrameGrantErrors.find? fun error => frameGrantErrorCode error == code

def decodeControlDenialCode (code : UInt64) : Option ControlDenial :=
  allControlDenials.find? fun denial => controlDenialCode denial == code

theorem decodeChildSpawnErrorCode_code (error : ChildSpawnError) :
    decodeChildSpawnErrorCode (childSpawnErrorCode error) = some error := by
  cases error <;> (try rename_i reason; cases reason) <;>
    (try rename_i inner; cases inner) <;> (try rename_i innermost; cases innermost) <;> decide

theorem decodeFrameGrantErrorCode_code (error : FrameGrantError) :
    decodeFrameGrantErrorCode (frameGrantErrorCode error) = some error := by
  cases error <;> (try rename_i reason; cases reason) <;>
    (try rename_i inner; cases inner) <;> decide

theorem decodeControlDenialCode_code (denial : ControlDenial) :
    decodeControlDenialCode (controlDenialCode denial) = some denial := by
  cases denial <;> (try rename_i reason; cases reason) <;> decide

/-- **Injective error codes.**  Decoding a rejection code recovers the typed
error exactly, so two typed errors of the same command never share a code. -/
theorem childErrorCodes_injective :
    (∀ left right, childSpawnErrorCode left = childSpawnErrorCode right → left = right) ∧
      (∀ left right, frameGrantErrorCode left = frameGrantErrorCode right → left = right) ∧
      (∀ left right, controlDenialCode left = controlDenialCode right → left = right) := by
  refine ⟨fun left right same => ?_, fun left right same => ?_, fun left right same => ?_⟩
  · have := decodeChildSpawnErrorCode_code left
    rw [same, decodeChildSpawnErrorCode_code] at this
    exact (Option.some.inj this).symm
  · have := decodeFrameGrantErrorCode_code left
    rw [same, decodeFrameGrantErrorCode_code] at this
    exact (Option.some.inj this).symm
  · have := decodeControlDenialCode_code left
    rw [same, decodeControlDenialCode_code] at this
    exact (Option.some.inj this).symm

def statusWord (tag status : UInt64) : UInt64 := (status <<< 16) ||| tag

/-- The two result words of a child-family result. -/
def encodeChildResult : ChildResult → UInt64 × UInt64
  | .spawned _ _ control => (statusWord spawnCommandTag 0x01, control)
  | .spawnRejected reason => (statusWord spawnCommandTag (0x80 + childSpawnErrorCode reason), 0)
  | .framesGranted _ moved => (statusWord grantFramesTag 0x01, UInt64.ofNat moved)
  | .framesRejected reason => (statusWord grantFramesTag (0x80 + frameGrantErrorCode reason), 0)
  | .terminated _ returned => (statusWord terminateChildTag 0x01, UInt64.ofNat returned)
  | .terminateRejected reason =>
      (statusWord terminateChildTag (0x80 + controlDenialCode reason), 0)
  | _ => (0xfe03, 0)

/-! ## The hosted oracle -/

/-- Decode, run under the latch through `childGate`, and encode. -/
def childOracleStep (state : CompositeState) (words : CommandWords) :
    CompositeState × UInt64 × UInt64 :=
  match decodeChild words with
  | .error reason => (state, CompositeDispatcher.errorWord reason, 0)
  | .ok operation =>
      match childGate state operation with
      | { state := next, result := .completed result } => (next, encodeChildResult result)
      | { state := next, result := .rejectedBusy } => (next, 0xfe01, 0)
      | { state := next, result := .rejectedHalted _ } => (next, 0xfe02, 0)

/-- What the child vectors compare, beyond `SpawnOracle.observe`: the child
tables, the generation counter, every spawn budget, the commitment of the
seed's frames, and every observed subject's frame limit. -/
structure AccountingObservation where
  base : Observation
  children : List (List (Option ChildEntry))
  nextChildGeneration : Nat
  budgets : List (Option Nat)
  commitment : List (Option Nat)
  limits : List Nat
  deriving DecidableEq, Repr

def observedFrames : List Nat := [4, 5, 6, 7]

def observeAccounting (state : CompositeState) : AccountingObservation :=
  { base := observe state
    children := observedSubjects.map fun parent =>
      (List.range 4).map (state.spawn.children parent)
    nextChildGeneration := state.spawn.nextChildGeneration
    budgets := observedSubjects.map fun subject =>
      (state.spawn.authority subject).map SpawnCapability.subjectBudget
    commitment := observedFrames.map state.frameBudgets.commitment
    limits := observedSubjects.map state.budgetLimit }

/-! ## Seeds -/

/-- Give `subject` a subject budget on the spawn capability it holds. -/
def withSubjectBudget (state : CompositeState) (subject budget : Nat) : CompositeState :=
  { state with spawn := { state.spawn with
      authority := fun candidate =>
        if candidate = subject then
          (state.spawn.authority candidate).map fun capability =>
            { capability with subjectBudget := budget }
        else state.spawn.authority candidate } }

/-- The oracle seed with free frames 5, 6, and 7 added to the composite
allocator (in every projection that carries it), frames 4 to 7 committed to
subject 2, and subject budget 2 on subject 2's spawn capability. -/
def framesSeed (plan : BootPageTablePlan.Plan) : CompositeState :=
  let seed := spawnOracleSeed plan
  let allocator : FrameAllocator.State :=
    { frames := [4, 5, 6, 7]
      status := fun frame => if frame = 5 ∨ frame = 6 ∨ frame = 7 then .free
        else seed.virtualMemory.memory.allocator.status frame }
  let virtualMemory : VirtualMapping.State :=
    { seed.virtualMemory with memory := { seed.virtualMemory.memory with allocator } }
  withSubjectBudget
    { seed with
      virtualMemory
      ipc := { seed.ipc with virtualMemory }
      resumable := { seed.resumable with
        translations := { seed.resumable.translations with virtual := virtualMemory } }
      frameBudgets := { commitment := fun frame =>
        if 4 ≤ frame ∧ frame ≤ 7 then some 2 else none } } 2 2

/-- Run a sequence of commands. -/
def runCommands (state : CompositeState) : List CommandWords → CompositeState
  | [] => state
  | words :: rest => runCommands (childOracleStep state words).1 rest

def accept (tag : UInt64) : UInt64 := statusWord tag 0x01

def rejectSpawn (error : ChildSpawnError) : UInt64 :=
  statusWord spawnCommandTag (0x80 + childSpawnErrorCode error)

def rejectGrant (error : FrameGrantError) : UInt64 :=
  statusWord grantFramesTag (0x80 + frameGrantErrorCode error)

def rejectTerminate (denial : ControlDenial) : UInt64 :=
  statusWord terminateChildTag (0x80 + controlDenialCode denial)

/-- The first child's control word: slot 0, generation 1. -/
def firstControl : UInt64 := 0x10000

/-- The second child's control word after the first is terminated: slot 0
reused, generation 2. -/
def secondControl : UInt64 := 0x20000

/-- Make `subject` the current subject (a hosted test surgery). -/
def withCurrent (state : CompositeState) (subject : Nat) : CompositeState :=
  { state with execution := { state.execution with core := { state.execution.core with
      context := { state.execution.core.context with currentSubject := subject } } } }

/-! ## Single-command vectors -/

/-- One vector: a pre-state, a command, the expected result words, and
whether the post-state must be observably the pre-state. -/
structure ChildVector where
  name : String
  pre : CompositeState
  words : CommandWords
  status : UInt64
  value : UInt64
  rollback : Bool

def vectorPasses (vector : ChildVector) : Bool :=
  let (post, status, value) := childOracleStep vector.pre vector.words
  status == vector.status && value == vector.value &&
    (!vector.rollback || observeAccounting post == observeAccounting vector.pre)

def childVectors (plan : BootPageTablePlan.Plan) : List ChildVector :=
  let seed := framesSeed plan
  let spawned := runCommands seed [acceptedCommand]
  let granted := runCommands spawned [encodeGrant firstControl 2]
  let terminated := runCommands granted [encodeTerminate firstControl]
  let respawned := runCommands terminated [acceptedCommand]
  [ { name := "charged spawn", pre := seed, words := acceptedCommand,
      status := accept spawnCommandTag, value := firstControl, rollback := false }
  , { name := "subject budget exhausted", pre := withSubjectBudget spawned 2 1,
      words := acceptedCommand, status := rejectSpawn .subjectBudgetExhausted, value := 0,
      rollback := true }
  , { name := "zero subject budget from the #489 grant",
      pre := (grantSpawnAuthority (revokeSpawnAuthority seed 2) 2).1,
      words := request 2 parentEndpointWord sendOnly,
      status := rejectSpawn .subjectBudgetExhausted, value := 0, rollback := true }
  , { name := "frame grant", pre := spawned, words := encodeGrant firstControl 2,
      status := accept grantFramesTag, value := 2, rollback := false }
  , { name := "frame budget exhausted", pre := spawned, words := encodeGrant firstControl 4,
      status := rejectGrant .frameBudgetExhausted, value := 0, rollback := true }
  , { name := "frame budget exhausted after a grant", pre := granted,
      words := encodeGrant firstControl 2,
      status := rejectGrant .frameBudgetExhausted, value := 0, rollback := true }
  , { name := "grant with a stale generation", pre := spawned,
      words := encodeGrant secondControl 1,
      status := rejectGrant (.control .stale), value := 0, rollback := true }
  , { name := "grant with a malformed control word", pre := spawned,
      words := encodeGrant 0xffff 1,
      status := rejectGrant (.control (.malformed .reservedSlot)), value := 0, rollback := true }
  , { name := "zero frames is noncanonical", pre := spawned, words := encodeGrant firstControl 0,
      status := CompositeDispatcher.errorWord .noncanonicalArguments, value := 0,
      rollback := true }
  , { name := "grant reserved argument", pre := spawned,
      words := { encodeGrant firstControl 1 with arg2 := 1 },
      status := CompositeDispatcher.errorWord .reservedBits, value := 0, rollback := true }
  , { name := "another subject presents the control word", pre := withCurrent spawned 1,
      words := encodeTerminate firstControl,
      status := rejectTerminate .stale, value := 0, rollback := true }
  , { name := "terminate child", pre := granted, words := encodeTerminate firstControl,
      status := accept terminateChildTag, value := 2, rollback := false }
  , { name := "terminate reserved argument", pre := granted,
      words := { encodeTerminate firstControl with arg1 := 1 },
      status := CompositeDispatcher.errorWord .reservedBits, value := 0, rollback := true }
  , { name := "stale control word after termination: grant", pre := terminated,
      words := encodeGrant firstControl 1,
      status := rejectGrant (.control .stale), value := 0, rollback := true }
  , { name := "stale control word after termination: terminate", pre := terminated,
      words := encodeTerminate firstControl,
      status := rejectTerminate .stale, value := 0, rollback := true }
  , { name := "respawn reuses slot 0 with generation 2", pre := terminated,
      words := acceptedCommand, status := accept spawnCommandTag, value := secondControl,
      rollback := false }
  , { name := "stale control word after slot reuse: grant", pre := respawned,
      words := encodeGrant firstControl 1,
      status := rejectGrant (.control .stale), value := 0, rollback := true }
  , { name := "stale control word after slot reuse: terminate", pre := respawned,
      words := encodeTerminate firstControl,
      status := rejectTerminate .stale, value := 0, rollback := true }
  , { name := "the reused slot's new control word", pre := respawned,
      words := encodeGrant secondControl 1,
      status := accept grantFramesTag, value := 1, rollback := false } ]

/-! ## Scenario checks -/

/-- Accepted spawn: the child-table entry, the counter, the count, and the
zero limit. -/
def spawnChecks (plan : BootPageTablePlan.Plan) : Bool :=
  let seed := framesSeed plan
  let post := runCommands seed [acceptedCommand]
  post.spawn.children 2 0 == some { child := 3, generation := 1, charge := 0 } &&
    post.spawn.nextChildGeneration == 2 && childCount post 2 == 1 &&
    post.budgetLimit 3 == 0 && entitlement post 2 == entitlement seed 2

/-- A frame grant moves free frames 5 and 6 to the child and charges them;
the parent's entitlement is unchanged and covers its usage and the child's
limit. -/
def grantChecks (plan : BootPageTablePlan.Plan) : Bool :=
  let seed := framesSeed plan
  let spawned := runCommands seed [acceptedCommand]
  let post := runCommands spawned [encodeGrant firstControl 2]
  post.budgetLimit 2 == 2 && post.budgetLimit 3 == 2 &&
    observedFrames.map post.frameBudgets.commitment == [some 2, some 3, some 3, some 2] &&
    post.spawn.children 2 0 == some { child := 3, generation := 1, charge := 2 } &&
    entitlement post 2 == entitlement seed 2 &&
    decide (post.budgetUsage 2 + childLimits post 2 ≤ entitlement post 2) &&
    post.virtualMemory.memory.allocator.frames == seed.virtualMemory.memory.allocator.frames

/-- Child termination returns the frames and releases everything the child
was given. -/
def terminateChecks (plan : BootPageTablePlan.Plan) : Bool :=
  let seed := framesSeed plan
  let granted := runCommands seed [acceptedCommand, encodeGrant firstControl 2]
  let post := runCommands granted [encodeTerminate firstControl]
  post.capabilities.subjects 3 == false &&
    (List.range 4).all (fun slot => post.capabilities.slots 3 slot == none) &&
    post.budgetLimit 2 == 4 && post.budgetLimit 3 == 0 &&
    observedFrames.map post.frameBudgets.commitment == [some 2, some 2, some 2, some 2] &&
    post.spawn.children 2 0 == none && post.spawn.parent 3 == none &&
    post.spawn.addressSpace 3 == none && post.virtualMemory.owner 21 == none &&
    post.lifecycle.addressOwner 21 == none && childCount post 2 == 0 &&
    entitlement post 2 == entitlement seed 2

/-- The respawned child is identity 4 with address space 22, in slot 0 with
generation 2. -/
def respawnChecks (plan : BootPageTablePlan.Plan) : Bool :=
  let seed := framesSeed plan
  let post := runCommands seed [acceptedCommand, encodeGrant firstControl 2,
    encodeTerminate firstControl, acceptedCommand]
  post.spawn.children 2 0 == some { child := 4, generation := 2, charge := 0 } &&
    post.spawn.parent 4 == some 2 && post.spawn.addressSpace 4 == some 22 &&
    post.capabilities.subjects 3 == false && post.lifecycle.issuedSubjects 3 == true

/-- The child copies its address-space root into the parent's slot 3; that
handle word resolves for the parent, is stale after the child's termination,
and stays stale after a new child takes the same child-table slot. -/
def capabilityChecks (plan : BootPageTablePlan.Plan) : Bool :=
  let seed := framesSeed plan
  let spawned := runCommands seed [acceptedCommand]
  let copied := withCurrent
    (authoritativeGate (withCurrent spawned 3)
      (.ordinary (.capabilityCopy childAddressSpaceSlot 2 3
        VirtualMapping.addressSpaceRootRights))).state 2
  match copied.capabilities.slots 2 3 with
  | none => false
  | some capability =>
      let word := (CapabilityHandle.encode (CapabilityHandle.issue 3 capability)).getD 0
      let terminated := runCommands copied [encodeTerminate firstControl]
      let respawned := runCommands terminated [acceptedCommand]
      let resolves := fun (state : CompositeState) =>
        match CapabilityHandle.resolveCurrent state.capabilities { caller := 2 } word
            .addressSpace with
        | .ok _ => true
        | .error _ => false
      capability.object == 21 && resolves copied && !resolves terminated &&
        !resolves respawned && terminated.capabilities.slots 2 3 == none &&
        respawned.capabilities.slots 2 3 == none

/-- Every `SpawnOracle` vector gives the same result words through the charged
oracle when the parent has a subject budget. -/
def legacyChecks (plan : BootPageTablePlan.Plan) : Bool :=
  (spawnVectors plan).all fun vector =>
    let pre := withSubjectBudget vector.pre 2 2
    let (post, status, _) := childOracleStep pre vector.words
    status == vector.expected && (!vector.rollback || observe post == observe pre)

def allChildChecks (plan : BootPageTablePlan.Plan) : Bool :=
  (childVectors plan).all vectorPasses && spawnChecks plan && grantChecks plan &&
    terminateChecks plan && respawnChecks plan && capabilityChecks plan && legacyChecks plan

/-- **Every vector passes** on the sample boot plan.  This is a closed,
bounded evaluation (`native_decide`, classified `bounded-model` in
`scripts/native-decide-modules.tsv`). -/
theorem child_vectors_pass :
    (match BootPageTablePlan.compile BootPageTablePlan.sampleInput with
      | .ok plan => allChildChecks plan
      | .error _ => false) = true := by
  native_decide

end LeanOS.SpawnAccountingOracle
