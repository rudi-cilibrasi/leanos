import LeanOS.SpawnAccountingOracle

/-!
# The spawn family at the generated composite-dispatcher boundary

ADR 0010 gate item 5 for explicit spawn (#489).  `LeanOS.SpawnOracle` and
`LeanOS.SpawnAccountingOracle` gave the spawn family a canonical encoding and
adversarial vectors as a hosted Lean oracle only.  This module puts the same
commands, with the same tags, into the boot-compiled
`CompositeDispatcher.dispatch` (export `leanos_composite_dispatch`, oracle
adapter 18) and proves that every edge of the generated table is exactly one
step of `childGate`, `memoryGate`, or the authoritative gate on the complete
composite state its state token names.

It adds no syscall: the dispatcher is a bounded table of state tokens, each
naming the complete `CompositeState` reached by replaying the preceding gate
steps, and no ring-3 path reaches it.

## Command words

Every command uses the dispatcher's six-word input: state token, tag, and four
arguments.  The three child tags are those of the hosted oracles.

| Tag | Command | `arg0` | `arg1` | `arg2` | `arg3` | Model step |
| --- | --- | --- | --- | --- | --- | --- |
| `0x7001` | spawn | spawn generation | endpoint handle | rights mask | 0 | `childGate (.spawn _)` |
| `0x7101` | grant frames | control word | frames, nonzero | 0 | 0 | `childGate (.grantFrames _ _)` |
| `0x7201` | terminate child | control word | 0 | 0 | 0 | `childGate (.terminateChild _)` |
| `0x7301` | allocate memory | slot | 0 | 0 | 0 | `memoryGate (.allocate _)` |
| `0x7401` | release memory | slot | 0 | 0 | 0 | `memoryGate (.release _)` |
| `0x7501` | kernel grant of spawn authority | subject | subject budget | 0 | 0 | `childGate (.grantAuthority _ _)` |
| `0x7601` | kernel revocation of spawn authority | subject | 0 | 0 | 0 | `childGate (.revokeAuthority _)` |
| `0x7701` | timer switch | 0 | 0 | 0 | 0 | authoritative `resumePreempt` |
| `0x7801` | capability copy | source slot | destination subject | destination slot | rights mask | authoritative `capabilityCopy` |

`decodeFamily (encodeFamily command) = .ok command` for every representable
command (`decodeFamily_encodeFamily`), and every word sequence that decodes is
the encoding of what it decodes to (`encodeFamily_decodeFamily`).  The two
kernel tags and the copy tag exist only at this bounded boundary; the later
ring-3 syscall of #489 is not bound by them.

## Result words

The dispatcher's result word zero is `0x01 | next << 8 | status << 16`, the
same layout as every other family.  The status byte is the hosted oracle's:
`0x01` for an accepted step and `0x80 + code` for a typed rejection, with the
codes of `SpawnOracle` and `SpawnAccountingOracle` (`childStatus`), and
`memoryErrorCode` for the memory family.  So for a child command the hosted
oracle's word `(status << 16) | tag` and the dispatcher's word carry the same
status byte (`edges_match_hosted_oracle`).  Result word one is the hosted
oracle's value word: the control word of an accepted spawn, the frames moved
by a grant or returned by a termination, and the generation of a kernel grant.
-/
namespace LeanOS.SpawnBoundary

open LeanOS
open LeanOS.FailStop
open LeanOS.SpawnOracle
open LeanOS.SpawnAccountingOracle
open LeanOS.CompositeDispatcher (CommandWords DecodeError)

/-! ## Commands and their canonical encoding -/

def allocateTag : UInt64 := 0x7301
def releaseTag : UInt64 := 0x7401
def grantAuthorityTag : UInt64 := 0x7501
def revokeAuthorityTag : UInt64 := 0x7601
def switchTag : UInt64 := 0x7701
def copyTag : UInt64 := 0x7801

/-- A command of the dispatcher's spawn family. -/
inductive FamilyCommand where
  | child (operation : ChildOperation)
  | memory (operation : MemoryOperation)
  | switch
  | copy (source destination destinationSlot : Nat) (rights : Capability.Rights)
  deriving DecidableEq, Repr

def scalar (tag arg0 arg1 arg2 arg3 : UInt64) : CommandWords :=
  { tag, arg0, arg1, arg2, arg3 }

def encodeFamily : FamilyCommand → CommandWords
  | .child (.spawn request) => encodeSpawn request
  | .child (.grantFrames control frames) => encodeGrant control (UInt64.ofNat frames)
  | .child (.terminateChild control) => encodeTerminate control
  | .child (.grantAuthority subject budget) =>
      scalar grantAuthorityTag (UInt64.ofNat subject) (UInt64.ofNat budget) 0 0
  | .child (.revokeAuthority subject) => scalar revokeAuthorityTag (UInt64.ofNat subject) 0 0 0
  | .memory (.allocate slot) => scalar allocateTag (UInt64.ofNat slot) 0 0 0
  | .memory (.release slot) => scalar releaseTag (UInt64.ofNat slot) 0 0 0
  | .switch => scalar switchTag 0 0 0 0
  | .copy source destination slot rights =>
      scalar copyTag (UInt64.ofNat source) (UInt64.ofNat destination) (UInt64.ofNat slot)
        (encodeRights rights)

/-- Decode one command of the family.  Every reserved argument must be zero. -/
def decodeFamily (words : CommandWords) : Except DecodeError FamilyCommand :=
  if words.tag = spawnCommandTag ∨ words.tag = grantFramesTag ∨
      words.tag = terminateChildTag then
    match decodeChild words with
    | .error reason => .error reason
    | .ok operation => .ok (.child operation)
  else if words.tag = allocateTag then
    if words.arg1 ≠ 0 ∨ words.arg2 ≠ 0 ∨ words.arg3 ≠ 0 then .error .reservedBits
    else .ok (.memory (.allocate words.arg0.toNat))
  else if words.tag = releaseTag then
    if words.arg1 ≠ 0 ∨ words.arg2 ≠ 0 ∨ words.arg3 ≠ 0 then .error .reservedBits
    else .ok (.memory (.release words.arg0.toNat))
  else if words.tag = grantAuthorityTag then
    if words.arg2 ≠ 0 ∨ words.arg3 ≠ 0 then .error .reservedBits
    else .ok (.child (.grantAuthority words.arg0.toNat words.arg1.toNat))
  else if words.tag = revokeAuthorityTag then
    if words.arg1 ≠ 0 ∨ words.arg2 ≠ 0 ∨ words.arg3 ≠ 0 then .error .reservedBits
    else .ok (.child (.revokeAuthority words.arg0.toNat))
  else if words.tag = switchTag then
    if words.arg0 ≠ 0 ∨ words.arg1 ≠ 0 ∨ words.arg2 ≠ 0 ∨ words.arg3 ≠ 0 then
      .error .reservedBits
    else .ok .switch
  else if words.tag = copyTag then
    match decodeRights words.arg3 with
    | .error reason => .error reason
    | .ok rights =>
        .ok (.copy words.arg0.toNat words.arg1.toNat words.arg2.toNat rights)
  else .error .unknownCommand

/-- A command is representable when its numbers fit the argument words and
the hosted oracles' canonical-argument rules hold (a nonzero spawn word, a
nonzero frame count). -/
def Representable : FamilyCommand → Prop
  | .child (.spawn request) => request.spawnWord ≠ 0
  | .child (.grantFrames _ frames) => 0 < frames ∧ frames < UInt64.size
  | .child (.terminateChild _) => True
  | .child (.grantAuthority subject budget) => subject < UInt64.size ∧ budget < UInt64.size
  | .child (.revokeAuthority subject) => subject < UInt64.size
  | .memory (.allocate slot) => slot < UInt64.size
  | .memory (.release slot) => slot < UInt64.size
  | .switch => True
  | .copy source destination slot _ =>
      source < UInt64.size ∧ destination < UInt64.size ∧ slot < UInt64.size

private theorem toNat_ofNat_of_lt {value : Nat} (small : value < UInt64.size) :
    (UInt64.ofNat value).toNat = value := by
  simp [Nat.mod_eq_of_lt small]

private theorem ofNat_ne_zero {value : Nat} (positive : 0 < value) (small : value < UInt64.size) :
    UInt64.ofNat value ≠ 0 := by
  intro zero
  have := congrArg UInt64.toNat zero
  rw [toNat_ofNat_of_lt small] at this
  simp at this
  omega

/-- **Round trip.** -/
theorem decodeFamily_encodeFamily (command : FamilyCommand) (representable : Representable command) :
    decodeFamily (encodeFamily command) = .ok command := by
  rcases command with operation | operation | _ | ⟨source, destination, slot, rights⟩
  · cases operation with
    | spawn request =>
        have tag : (encodeSpawn request).tag = spawnCommandTag := rfl
        have decoded := decodeSpawn_encodeSpawn request representable
        simp only [encodeFamily, decodeFamily, decodeChild, tag, decoded, true_or, ↓reduceIte]
    | grantFrames control frames =>
        obtain ⟨positive, small⟩ := representable
        have decoded := decodeChild_encodeGrant control (UInt64.ofNat frames)
          (ofNat_ne_zero positive small)
        rw [toNat_ofNat_of_lt small] at decoded
        simp only [encodeFamily, decodeFamily, encodeGrant, grantFramesTag, spawnCommandTag,
          terminateChildTag] at decoded ⊢
        simp [decoded]
    | terminateChild control =>
        have decoded := decodeChild_encodeTerminate control
        simp only [encodeFamily, decodeFamily, encodeTerminate, grantFramesTag, spawnCommandTag,
          terminateChildTag] at decoded ⊢
        simp [decoded]
    | grantAuthority subject budget =>
        obtain ⟨subjectSmall, budgetSmall⟩ := representable
        simp [encodeFamily, decodeFamily, scalar, grantAuthorityTag, spawnCommandTag,
          grantFramesTag, terminateChildTag, allocateTag, releaseTag,
          toNat_ofNat_of_lt subjectSmall, toNat_ofNat_of_lt budgetSmall]
    | revokeAuthority subject =>
        simp [encodeFamily, decodeFamily, scalar, revokeAuthorityTag, spawnCommandTag,
          grantFramesTag, terminateChildTag, allocateTag, releaseTag, grantAuthorityTag,
          toNat_ofNat_of_lt (show subject < UInt64.size from representable)]
  · cases operation with
    | allocate slot =>
        simp [encodeFamily, decodeFamily, scalar, allocateTag, spawnCommandTag,
          grantFramesTag, terminateChildTag,
          toNat_ofNat_of_lt (show slot < UInt64.size from representable)]
    | release slot =>
        simp [encodeFamily, decodeFamily, scalar, releaseTag, allocateTag, spawnCommandTag,
          grantFramesTag, terminateChildTag,
          toNat_ofNat_of_lt (show slot < UInt64.size from representable)]
  · simp [encodeFamily, decodeFamily, scalar, switchTag, spawnCommandTag, grantFramesTag,
      terminateChildTag, allocateTag, releaseTag, grantAuthorityTag, revokeAuthorityTag]
  · obtain ⟨sourceSmall, destinationSmall, slotSmall⟩ := representable
    simp [encodeFamily, decodeFamily, scalar, copyTag, switchTag, spawnCommandTag,
      grantFramesTag, terminateChildTag, allocateTag, releaseTag, grantAuthorityTag,
      revokeAuthorityTag, decodeRights_encodeRights, toNat_ofNat_of_lt sourceSmall,
      toNat_ofNat_of_lt destinationSmall, toNat_ofNat_of_lt slotSmall]

theorem decodeChild_spawn {words : CommandWords} {request : SpawnRequest}
    (decoded : decodeChild words = .ok (.spawn request)) : decodeSpawn words = .ok request := by
  unfold decodeChild at decoded
  split at decoded
  · split at decoded
    · cases decoded
    · next spawnDecoded => cases decoded; exact spawnDecoded
  · repeat' split at decoded
    all_goals cases decoded

theorem decodeChild_not_kernel {words : CommandWords} {operation : ChildOperation}
    (decoded : decodeChild words = .ok operation) :
    (∀ subject budget, operation ≠ .grantAuthority subject budget) ∧
      ∀ subject, operation ≠ .revokeAuthority subject := by
  unfold decodeChild at decoded
  repeat' split at decoded
  all_goals cases decoded
  all_goals simp

/-- **Canonical.**  A word sequence that decodes is exactly the encoding of the
command it decodes to. -/
theorem encodeFamily_decodeFamily (words : CommandWords) (command : FamilyCommand)
    (decoded : decodeFamily words = .ok command) : encodeFamily command = words := by
  unfold decodeFamily at decoded
  by_cases childTag : words.tag = spawnCommandTag ∨ words.tag = grantFramesTag ∨
      words.tag = terminateChildTag
  · simp only [childTag, ↓reduceIte] at decoded
    cases childDecoded : decodeChild words with
    | error reason => rw [childDecoded] at decoded; cases decoded
    | ok operation =>
        rw [childDecoded] at decoded
        cases decoded
        obtain ⟨notGrant, notRevoke⟩ := decodeChild_not_kernel childDecoded
        cases operation with
        | spawn request =>
            exact encodeSpawn_decodeSpawn words request (decodeChild_spawn childDecoded)
        | grantFrames control frames =>
            obtain ⟨wordsEq, _⟩ := encodeGrant_decodeChild words control frames childDecoded
            simp [encodeFamily, wordsEq]
        | terminateChild control =>
            simp [encodeFamily, encodeTerminate_decodeChild words control childDecoded]
        | grantAuthority subject budget => exact absurd rfl (notGrant subject budget)
        | revokeAuthority subject => exact absurd rfl (notRevoke subject)
  simp only [childTag, ↓reduceIte] at decoded
  obtain ⟨tag, arg0, arg1, arg2, arg3⟩ := words
  simp only at decoded ⊢
  by_cases allocate : tag = allocateTag
  · subst allocate
    simp only [↓reduceIte] at decoded
    split at decoded
    · cases decoded
    · next reserved =>
      cases decoded
      simp only [not_or, Decidable.not_not] at reserved
      obtain ⟨rfl, rfl, rfl⟩ := reserved
      simp [encodeFamily, scalar]
  simp only [allocate, ↓reduceIte] at decoded
  by_cases release : tag = releaseTag
  · subst release
    simp only [↓reduceIte] at decoded
    split at decoded
    · cases decoded
    · next reserved =>
      cases decoded
      simp only [not_or, Decidable.not_not] at reserved
      obtain ⟨rfl, rfl, rfl⟩ := reserved
      simp [encodeFamily, scalar]
  simp only [release, ↓reduceIte] at decoded
  by_cases grant : tag = grantAuthorityTag
  · subst grant
    simp only [↓reduceIte] at decoded
    split at decoded
    · cases decoded
    · next reserved =>
      cases decoded
      simp only [not_or, Decidable.not_not] at reserved
      obtain ⟨rfl, rfl⟩ := reserved
      simp [encodeFamily, scalar]
  simp only [grant, ↓reduceIte] at decoded
  by_cases revoke : tag = revokeAuthorityTag
  · subst revoke
    simp only [↓reduceIte] at decoded
    split at decoded
    · cases decoded
    · next reserved =>
      cases decoded
      simp only [not_or, Decidable.not_not] at reserved
      obtain ⟨rfl, rfl, rfl⟩ := reserved
      simp [encodeFamily, scalar]
  simp only [revoke, ↓reduceIte] at decoded
  by_cases switch : tag = switchTag
  · subst switch
    simp only [↓reduceIte] at decoded
    split at decoded
    · cases decoded
    · next reserved =>
      cases decoded
      simp only [not_or, Decidable.not_not] at reserved
      obtain ⟨rfl, rfl, rfl, rfl⟩ := reserved
      simp [encodeFamily, scalar]
  simp only [switch, ↓reduceIte] at decoded
  by_cases copy : tag = copyTag
  · subst copy
    simp only [↓reduceIte] at decoded
    split at decoded
    · cases decoded
    · next rights rightsDecoded =>
      cases decoded
      simp [encodeFamily, scalar, encodeRights_decodeRights _ _ rightsDecoded]
  simp only [copy, ↓reduceIte] at decoded
  cases decoded

/-! ## Typed results as status and value words -/

def memoryErrorCode : MemoryError → UInt64
  | .invalidSubject => 0x01 | .outOfRange => 0x02 | .capabilityIdentityExhausted => 0x03
  | .occupiedSlot => 0x04 | .objectIdentityExhausted => 0x05 | .objectUnavailable => 0x06
  | .frameBudgetExhausted => 0x07 | .frameUnavailable => 0x08 | .staleSlot => 0x09
  | .kindMismatch => 0x0a | .missingRevoke => 0x0b | .retiredObject => 0x0c
  | .allocatorMismatch => 0x0d | .notOwner => 0x0e

def allMemoryErrors : List MemoryError :=
  [.invalidSubject, .outOfRange, .capabilityIdentityExhausted, .occupiedSlot,
    .objectIdentityExhausted, .objectUnavailable, .frameBudgetExhausted, .frameUnavailable,
    .staleSlot, .kindMismatch, .missingRevoke, .retiredObject, .allocatorMismatch, .notOwner]

theorem memoryErrorCode_injective (left right : MemoryError)
    (same : memoryErrorCode left = memoryErrorCode right) : left = right := by
  cases left <;> cases right <;> first | rfl | (simp [memoryErrorCode] at same)

/-- The hosted oracles' status byte and value word of a child-family result. -/
def childStatus : ChildResult → UInt64 × UInt64
  | .spawned _ _ control => (0x01, control)
  | .spawnRejected reason => (0x80 + childSpawnErrorCode reason, 0)
  | .framesGranted _ moved => (0x01, UInt64.ofNat moved)
  | .framesRejected reason => (0x80 + frameGrantErrorCode reason, 0)
  | .terminated _ returned => (0x01, UInt64.ofNat returned)
  | .terminateRejected reason => (0x80 + controlDenialCode reason, 0)
  | .authorityGranted generation => (0x01, UInt64.ofNat generation)
  | .authorityRejected => (0x80, 0)
  | .authorityRevoked => (0x01, 0)

def memoryStatus : MemoryResult → UInt64
  | .allocated _ _ | .released _ _ => 0x01
  | .rejected reason => 0x80 + memoryErrorCode reason

/-- Busy and halted latches are `0x7e` and `0x7f`; the bounded table never
reaches them. -/
def childGateStatus : ChildGateResult → UInt64 × UInt64
  | .completed result => childStatus result
  | .rejectedBusy => (0x7e, 0)
  | .rejectedHalted _ => (0x7f, 0)

def memoryGateStatus : MemoryGateResult → UInt64
  | .completed result => memoryStatus result
  | .rejectedBusy => 0x7e
  | .rejectedHalted _ => 0x7f

def authoritativeStatus : AuthoritativeGateResult → UInt64
  | .completed (.ordinary reply) => if reply.isNonfatalRejection then 0x80 else 0x01
  | .completed _ => 0x80
  | .rejectedBusy => 0x7e
  | .rejectedHalted _ => 0x7f

/-- An accepted child result has status `0x01`; every other status is a
rejection. -/
theorem childStatus_accepted_or_rejected (result : ChildResult) :
    (childStatus result).1 = 0x01 ∨ result.rejected = true := by
  cases result <;> simp [childStatus, ChildResult.rejected]

theorem memoryStatus_accepted_or_rejected (result : MemoryResult) :
    memoryStatus result = 0x01 ∨ ∃ reason, result = .rejected reason := by
  cases result <;> simp [memoryStatus]

/-! ## One step of the family -/

/-- The operation the timer-switch command runs: the dispatcher's own
resumable switch, as in the capability-transfer family. -/
def switchOperation : AuthoritativeOperation :=
  .ordinary (.resumePreempt compositeDispatcherTimerFrame compositeDispatcherTimerRegisters)

def copyOperation (source destination slot : Nat) (rights : Capability.Rights) :
    AuthoritativeOperation :=
  .ordinary (.capabilityCopy source destination slot rights)

structure FamilyOutcome where
  state : CompositeState
  status : UInt64
  value : UInt64

/-- One step: the gate's post-state and the encoded typed result. -/
def familyStep (state : CompositeState) : FamilyCommand → FamilyOutcome
  | .child operation =>
      { state := (childGate state operation).state
        status := (childGateStatus (childGate state operation).result).1
        value := (childGateStatus (childGate state operation).result).2 }
  | .memory operation =>
      { state := (memoryGate state operation).state
        status := memoryGateStatus (memoryGate state operation).result
        value := 0 }
  | .switch =>
      { state := (authoritativeGate state switchOperation).state
        status := authoritativeStatus (authoritativeGate state switchOperation).result
        value := 0 }
  | .copy source destination slot rights =>
      { state := (authoritativeGate state (copyOperation source destination slot rights)).state
        status := authoritativeStatus
          (authoritativeGate state (copyOperation source destination slot rights)).result
        value := 0 }

/-- The family as steps of the whole-trace theorem `child_resource_trace`. -/
def FamilyCommand.toStep : FamilyCommand → ChildTraceStep
  | .child operation => .child operation
  | .memory operation => .memory operation
  | .switch => .composite (.authoritative switchOperation)
  | .copy source destination slot rights =>
      .composite (.authoritative (copyOperation source destination slot rights))

/-- The two authoritative commands; every other command is a child or memory
step, whose rejections keep the pre-state. -/
def FamilyCommand.isAuthoritative : FamilyCommand → Bool
  | .switch | .copy _ _ _ _ => true
  | _ => false

theorem familyStep_state (state : CompositeState) (command : FamilyCommand) :
    (familyStep state command).state = command.toStep.apply state := by
  cases command <;> rfl

/-- A rejected child or memory step keeps the pre-state. -/
theorem familyStep_stutter (state : CompositeState) (command : FamilyCommand)
    (notAuthoritative : command.isAuthoritative = false)
    (rejected : (familyStep state command).status ≠ 0x01) :
    (familyStep state command).state = state := by
  cases command with
  | child operation =>
      simp only [familyStep, childGate, childGateStatus] at rejected ⊢
      cases mode : state.execution.mode <;> simp only [mode] at rejected ⊢
      rcases childStatus_accepted_or_rejected (operation.apply state).result with accepted | yes
      · exact absurd accepted rejected
      · exact ChildOperation.apply_rejected_unchanged state operation yes
  | memory operation =>
      simp only [familyStep, memoryGate, memoryGateStatus] at rejected ⊢
      cases mode : state.execution.mode <;> simp only [mode] at rejected ⊢
      rcases memoryStatus_accepted_or_rejected (operation.apply state).result with
        accepted | ⟨reason, yes⟩
      · exact absurd accepted rejected
      · exact MemoryOperation.apply_rejected_unchanged state operation reason yes
  | switch => simp [FamilyCommand.isAuthoritative] at notAuthoritative
  | copy => simp [FamilyCommand.isAuthoritative] at notAuthoritative

/-! ## Seeds and state tokens -/

/-- The family's kernel-owned seed: the dispatcher seed
(`compositeDispatcherInitial`), in which subject 2 is current and holds
endpoint 10 (slot 0, handle `0x30000`) and memory object 20 on frame 4 (slot
2), with the issuers past the seed's histories and frame 4 committed to
subject 2.  No spawn authority is held; the first edge grants it through the
kernel command. -/
def spawnSeed (plan : BootPageTablePlan.Plan) : CompositeState :=
  { compositeDispatcherInitial plan with
    issuers := { subject := { next := 3 }, object := { next := 21 } }
    frameBudgets := { commitment := fun frame => if frame = 4 then some 2 else none } }

/-- The family seeds.  The three exhaustion seeds are the main seed with one
never-reused counter at its bound; no bounded trace reaches a bound of
`2^64 - 1`, so they are seeds of their own, each with one rejecting edge. -/
inductive Seed where
  | main
  | subjectsExhausted
  | objectsExhausted
  | controlsExhausted
  deriving DecidableEq, Repr

def seedState (plan : BootPageTablePlan.Plan) : Seed → CompositeState
  | .main => spawnSeed plan
  | .subjectsExhausted => withSubjectNext (spawnSeed plan) LifetimeIssuer.identityReserved
  | .objectsExhausted => withObjectNext (spawnSeed plan) LifetimeIssuer.identityReserved
  | .controlsExhausted =>
      { spawnSeed plan with spawn :=
          { (spawnSeed plan).spawn with nextChildGeneration := CapabilityHandle.generationReserved } }

/-- The observable states of the spawn family. -/
inductive StateId where
  | seed | authorized | spawned | released | granted | terminated | reallocated
  | respawned | secondTerminated | otherSubject | revoked | regranted | regrantedSpawned
  | subjectsExhausted | objectsExhausted | controlsExhausted | narrowedSend | narrowedGrant
  deriving DecidableEq, Repr

def allStates : List StateId :=
  [.seed, .authorized, .spawned, .released, .granted, .terminated, .reallocated,
    .respawned, .secondTerminated, .otherSubject, .revoked, .regranted, .regrantedSpawned,
    .subjectsExhausted, .objectsExhausted, .controlsExhausted, .narrowedSend, .narrowedGrant]

/-- State tokens `0x7001` to `0x8101`: version 1 in bits 0..7, the selector in
bits 8..15. -/
def encodeState : StateId → UInt64
  | .seed => 0x7001 | .authorized => 0x7101 | .spawned => 0x7201 | .released => 0x7301
  | .granted => 0x7401 | .terminated => 0x7501 | .reallocated => 0x7601
  | .respawned => 0x7701 | .secondTerminated => 0x7801 | .otherSubject => 0x7901
  | .revoked => 0x7a01 | .regranted => 0x7b01 | .regrantedSpawned => 0x7c01
  | .subjectsExhausted => 0x7d01 | .objectsExhausted => 0x7e01
  | .controlsExhausted => 0x7f01 | .narrowedSend => 0x8001 | .narrowedGrant => 0x8101

def decodeState (word : UInt64) : Except DecodeError StateId :=
  match allStates.find? (fun state => encodeState state == word) with
  | some state => .ok state
  | none => .error .unknownState

theorem decodeState_encodeState (state : StateId) : decodeState (encodeState state) = .ok state := by
  cases state <;> rfl

theorem encodeState_injective (first second : StateId)
    (same : encodeState first = encodeState second) : first = second := by
  have := decodeState_encodeState first
  rw [same, decodeState_encodeState] at this
  exact (Except.ok.inj this).symm

/-! ## The commands of the bounded table -/

def parentEndpoint : UInt64 := 0x30000

def spawnWith (spawnWord endpointWord : UInt64) (rights : Capability.Rights) : FamilyCommand :=
  .child (.spawn { spawnWord, endpointWord, rights })

def spawnOne : FamilyCommand := spawnWith 1 parentEndpoint sendOnly
def grantAuthority (subject budget : Nat) : FamilyCommand := .child (.grantAuthority subject budget)
def revokeAuthority (subject : Nat) : FamilyCommand := .child (.revokeAuthority subject)
def grant (control : UInt64) (frames : Nat) : FamilyCommand := .child (.grantFrames control frames)
def terminate (control : UInt64) : FamilyCommand := .child (.terminateChild control)
def allocate (slot : Nat) : FamilyCommand := .memory (.allocate slot)
def release (slot : Nat) : FamilyCommand := .memory (.release slot)

/-- Where each state comes from: a seed and the commands replayed from it. -/
def origin : StateId → Seed × List FamilyCommand
  | .seed => (.main, [])
  | .authorized => (.main, [grantAuthority 2 1])
  | .spawned => (.main, [grantAuthority 2 1, spawnOne])
  | .released => (.main, [grantAuthority 2 1, spawnOne, release 2])
  | .granted => (.main, [grantAuthority 2 1, spawnOne, release 2, grant firstControl 1])
  | .terminated =>
      (.main, [grantAuthority 2 1, spawnOne, release 2, grant firstControl 1,
        terminate firstControl])
  | .reallocated =>
      (.main, [grantAuthority 2 1, spawnOne, release 2, grant firstControl 1,
        terminate firstControl, allocate 2])
  | .respawned =>
      (.main, [grantAuthority 2 1, spawnOne, release 2, grant firstControl 1,
        terminate firstControl, allocate 2, spawnOne])
  | .secondTerminated =>
      (.main, [grantAuthority 2 1, spawnOne, release 2, grant firstControl 1,
        terminate firstControl, allocate 2, spawnOne, terminate secondControl])
  | .otherSubject => (.main, [grantAuthority 2 1, spawnOne, .switch])
  | .revoked => (.main, [grantAuthority 2 1, revokeAuthority 2])
  | .regranted => (.main, [grantAuthority 2 1, revokeAuthority 2, grantAuthority 2 1])
  | .regrantedSpawned =>
      (.main, [grantAuthority 2 1, revokeAuthority 2, grantAuthority 2 1,
        spawnWith 2 parentEndpoint sendOnly])
  | .subjectsExhausted => (.subjectsExhausted, [grantAuthority 2 1])
  | .objectsExhausted => (.objectsExhausted, [grantAuthority 2 1])
  | .controlsExhausted => (.controlsExhausted, [grantAuthority 2 1])
  | .narrowedSend => (.main, [grantAuthority 2 1, .copy 0 2 3 { send := true }])
  | .narrowedGrant => (.main, [grantAuthority 2 1, .copy 0 2 3 { send := true, grant := true }])

def runFamily (state : CompositeState) : List FamilyCommand → CompositeState
  | [] => state
  | command :: rest => runFamily (familyStep state command).state rest

/-- The complete composite state a token names: replay from its seed. -/
def stateOf (plan : BootPageTablePlan.Plan) (id : StateId) : CompositeState :=
  runFamily (seedState plan (origin id).1) (origin id).2

theorem runFamily_append (state : CompositeState) (commands : List FamilyCommand)
    (command : FamilyCommand) :
    runFamily state (commands ++ [command]) =
      (familyStep (runFamily state commands) command).state := by
  induction commands generalizing state with
  | nil => rfl
  | cons first rest ih => exact ih _

/-! ## The edge table -/

/-- Whether a decoding succeeded with exactly this value. -/
def okIs {ε α : Type} [DecidableEq α] (result : Except ε α) (expected : α) : Bool :=
  match result with
  | .ok value => value == expected
  | .error _ => false

theorem okIs_iff {ε α : Type} [DecidableEq α] (result : Except ε α) (expected : α) :
    okIs result expected = true ↔ result = .ok expected := by
  cases result <;> simp [okIs]

/-- One edge of the bounded table: a state, a command, the successor state,
and the status and value words of the typed result. -/
structure Edge where
  state : StateId
  command : FamilyCommand
  next : StateId
  status : UInt64
  value : UInt64
  deriving DecidableEq, Repr

/-- Result word zero of the dispatcher for an edge: version, next-state
selector, status byte. -/
def replyWord (next : StateId) (status : UInt64) : UInt64 :=
  CompositeDispatcher.abiVersion + (encodeState next / 256) * 256 + status * 65536

/-- Decode result word zero of the spawn family into the next state and the
status byte. -/
def decodeReply (word : UInt64) : Except DecodeError (StateId × UInt64) :=
  if word % 256 != CompositeDispatcher.abiVersion then .error .wrongVersion
  else if 0x1000000 ≤ word then .error .reservedBits
  else match decodeState (word % 65536) with
    | .ok next => .ok (next, word / 65536)
    | .error reason => .error reason

/-- The 49 edges.  Fourteen are accepted and advance; the other 35 are typed
rejections that leave the state token, and the composite state, unchanged. -/
def edges : List Edge :=
  [ ⟨.seed, spawnOne, .seed, 0x81, 0x0⟩
  , ⟨.seed, grant firstControl 1, .seed, 0xc3, 0x0⟩
  , ⟨.seed, grantAuthority 2 1, .authorized, 0x1, 0x1⟩
  , ⟨.seed, grantAuthority 3 1, .seed, 0x80, 0x0⟩
  , ⟨.authorized, spawnOne, .spawned, 0x1, 0x10000⟩
  , ⟨.authorized, spawnWith 2 parentEndpoint sendOnly, .authorized, 0x82, 0x0⟩
  , ⟨.authorized, spawnWith 1 0xffff sendOnly, .authorized, 0xa0, 0x0⟩
  , ⟨.authorized, spawnWith 1 0x40000 sendOnly, .authorized, 0xa4, 0x0⟩
  , ⟨.authorized, spawnWith 1 0x30007 sendOnly, .authorized, 0xa3, 0x0⟩
  , ⟨.authorized, spawnWith 1 0x40001 sendOnly, .authorized, 0xa5, 0x0⟩
  , ⟨.authorized, spawnWith 1 parentEndpoint { read := true }, .authorized, 0x8a, 0x0⟩
  , ⟨.authorized, terminate firstControl, .authorized, 0xc3, 0x0⟩
  , ⟨.authorized, revokeAuthority 2, .revoked, 0x1, 0x0⟩
  , ⟨.authorized, allocate 3, .authorized, 0x87, 0x0⟩
  , ⟨.authorized, .copy 0 2 3 { send := true }, .narrowedSend, 0x1, 0x0⟩
  , ⟨.authorized, .copy 0 2 3 { send := true, grant := true }, .narrowedGrant, 0x1, 0x0⟩
  , ⟨.spawned, spawnOne, .spawned, 0x8c, 0x0⟩
  , ⟨.spawned, grant firstControl 1, .spawned, 0xc5, 0x0⟩
  , ⟨.spawned, grant secondControl 1, .spawned, 0xc3, 0x0⟩
  , ⟨.spawned, grant 0xffff 1, .spawned, 0xc1, 0x0⟩
  , ⟨.spawned, release 2, .released, 0x1, 0x0⟩
  , ⟨.spawned, .switch, .otherSubject, 0x1, 0x0⟩
  , ⟨.spawned, grantAuthority 3 1, .spawned, 0x80, 0x0⟩
  , ⟨.released, release 2, .released, 0x89, 0x0⟩
  , ⟨.released, grant firstControl 2, .released, 0xc5, 0x0⟩
  , ⟨.released, grant firstControl 1, .granted, 0x1, 0x1⟩
  , ⟨.granted, allocate 2, .granted, 0x87, 0x0⟩
  , ⟨.granted, terminate firstControl, .terminated, 0x1, 0x1⟩
  , ⟨.terminated, terminate firstControl, .terminated, 0xc3, 0x0⟩
  , ⟨.terminated, grant firstControl 1, .terminated, 0xc3, 0x0⟩
  , ⟨.terminated, allocate 2, .reallocated, 0x1, 0x0⟩
  , ⟨.reallocated, spawnOne, .respawned, 0x1, 0x20000⟩
  , ⟨.respawned, terminate firstControl, .respawned, 0xc3, 0x0⟩
  , ⟨.respawned, grant firstControl 1, .respawned, 0xc3, 0x0⟩
  , ⟨.respawned, spawnOne, .respawned, 0x8c, 0x0⟩
  , ⟨.respawned, terminate secondControl, .secondTerminated, 0x1, 0x0⟩
  , ⟨.otherSubject, terminate firstControl, .otherSubject, 0xc3, 0x0⟩
  , ⟨.otherSubject, grant firstControl 1, .otherSubject, 0xc3, 0x0⟩
  , ⟨.otherSubject, spawnWith 1 0x20001 sendOnly, .otherSubject, 0x81, 0x0⟩
  , ⟨.otherSubject, allocate 2, .otherSubject, 0x87, 0x0⟩
  , ⟨.revoked, spawnOne, .revoked, 0x81, 0x0⟩
  , ⟨.revoked, grantAuthority 2 1, .regranted, 0x1, 0x2⟩
  , ⟨.regranted, spawnOne, .regranted, 0x82, 0x0⟩
  , ⟨.regranted, spawnWith 2 parentEndpoint sendOnly, .regrantedSpawned, 0x1, 0x10000⟩
  , ⟨.subjectsExhausted, spawnOne, .subjectsExhausted, 0x83, 0x0⟩
  , ⟨.objectsExhausted, spawnOne, .objectsExhausted, 0x87, 0x0⟩
  , ⟨.controlsExhausted, spawnOne, .controlsExhausted, 0x8d, 0x0⟩
  , ⟨.narrowedSend, spawnWith 1 0x60003 sendOnly, .narrowedSend, 0x89, 0x0⟩
  , ⟨.narrowedGrant, spawnWith 1 0x60003 { receive := true }, .narrowedGrant, 0x8b, 0x0⟩
  ]

def Edge.words (edge : Edge) : CommandWords := encodeFamily edge.command

/-- The generated dispatcher's answer for an edge. -/
def Edge.dispatched (edge : Edge) : UInt64 × UInt64 :=
  let words := edge.words
  (CompositeDispatcher.dispatch (encodeState edge.state) words.tag words.arg0 words.arg1
      words.arg2 words.arg3,
    CompositeDispatcher.dispatchValue (encodeState edge.state) words.tag words.arg0 words.arg1
      words.arg2 words.arg3)

/-- **The generated table is the edge table.**  For every edge, the
boot-compiled dispatcher returns the edge's reply and value words, and the
reply word decodes to the edge's successor and status. -/
theorem edges_dispatch :
    edges.all (fun edge => edge.dispatched == (replyWord edge.next edge.status, edge.value) &&
      okIs (decodeReply (replyWord edge.next edge.status)) (edge.next, edge.status)) = true := by
  native_decide

/-- **Every edge's words decode to its command** (round trip on the table). -/
theorem edges_decode :
    edges.all (fun edge => okIs (decodeFamily edge.words) edge.command) = true := by
  decide

/-- An edge either replays one more command from the same seed, or it is a
rejected child or memory step that keeps its state token. -/
def Edge.shape (edge : Edge) : Bool :=
  ((origin edge.next).1 == (origin edge.state).1 &&
      (origin edge.next).2 == (origin edge.state).2 ++ [edge.command]) ||
    (edge.next == edge.state && edge.status != 0x01 && !edge.command.isAuthoritative)

theorem edges_shape : edges.all Edge.shape = true := by
  decide

/-- The model's typed result on the materialized pre-state is the edge's. -/
def Edge.modelAgrees (plan : BootPageTablePlan.Plan) (edge : Edge) : Bool :=
  let outcome := familyStep (stateOf plan edge.state) edge.command
  outcome.status == edge.status && outcome.value == edge.value

/-- The model's results on every edge, by closed evaluation on the sample boot
plan the dispatcher uses (`native_decide`, classified `bounded-model`). -/
theorem edges_model :
    (match BootPageTablePlan.compile BootPageTablePlan.sampleInput with
      | .ok plan => edges.all (Edge.modelAgrees plan)
      | .error _ => false) = true := by
  native_decide

/-- **Each edge is exactly one gate step.**  On the complete composite state
the edge's token names, the family step (`childGate`, `memoryGate`, or the
authoritative gate) returns the complete state the successor token names,
with the edge's status and value words. -/
theorem edge_refines (plan : BootPageTablePlan.Plan)
    (compiled : BootPageTablePlan.compile BootPageTablePlan.sampleInput = .ok plan)
    (edge : Edge) (member : edge ∈ edges) :
    familyStep (stateOf plan edge.state) edge.command =
      { state := stateOf plan edge.next, status := edge.status, value := edge.value } := by
  have model := edges_model
  rw [compiled] at model
  have agrees := List.all_eq_true.1 model edge member
  have shape := List.all_eq_true.1 edges_shape edge member
  simp only [Edge.modelAgrees, Bool.and_eq_true, beq_iff_eq] at agrees
  obtain ⟨status, value⟩ := agrees
  have stateEq : (familyStep (stateOf plan edge.state) edge.command).state =
      stateOf plan edge.next := by
    simp only [Edge.shape, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq,
      Bool.not_eq_true'] at shape
    rcases shape with ⟨⟨seed, path⟩⟩ | ⟨⟨same, rejected⟩, notAuthoritative⟩
    · simp only [stateOf, seed, path, runFamily_append]
    · rw [same]
      exact familyStep_stutter _ _ notAuthoritative (by rw [status]; exact rejected)
  cases outcome : familyStep (stateOf plan edge.state) edge.command
  simp only [outcome] at stateEq status value
  simp [stateEq, status, value]

/-- **The dispatcher's spawn commands refine the gates.**  For every edge of the
bounded table: the command words decode to the edge's command, the generated
dispatcher maps the pre-state token and the words to the successor token and
the status and value words, and that result is exactly the gate step on the
complete composite state the token names. -/
theorem dispatcher_refines (plan : BootPageTablePlan.Plan)
    (compiled : BootPageTablePlan.compile BootPageTablePlan.sampleInput = .ok plan)
    (edge : Edge) (member : edge ∈ edges) :
    decodeFamily edge.words = .ok edge.command ∧
      edge.dispatched = (replyWord edge.next edge.status, edge.value) ∧
      decodeReply (replyWord edge.next edge.status) = .ok (edge.next, edge.status) ∧
      familyStep (stateOf plan edge.state) edge.command =
        { state := stateOf plan edge.next, status := edge.status, value := edge.value } := by
  have decoded := List.all_eq_true.1 edges_decode edge member
  have dispatched := List.all_eq_true.1 edges_dispatch edge member
  simp only [Bool.and_eq_true, beq_iff_eq, okIs_iff] at decoded dispatched
  exact ⟨decoded, dispatched.1, dispatched.2, edge_refines plan compiled edge member⟩

/-- Exactly the accepted edges advance. -/
theorem edges_rejections_stay :
    edges.all (fun edge => (edge.status == 0x01) != (edge.next == edge.state)) = true := by
  decide

/-- **Rollback.**  Every rejecting edge leaves the complete composite state
unchanged and keeps its state token. -/
theorem rejected_edge_unchanged (plan : BootPageTablePlan.Plan)
    (compiled : BootPageTablePlan.compile BootPageTablePlan.sampleInput = .ok plan)
    (edge : Edge) (member : edge ∈ edges) (rejected : edge.status ≠ 0x01) :
    edge.next = edge.state ∧
      (familyStep (stateOf plan edge.state) edge.command).state = stateOf plan edge.state := by
  have stays := List.all_eq_true.1 edges_rejections_stay edge member
  have same : edge.next = edge.state := by
    simp only [bne_iff_ne, ne_eq] at stays
    by_cases different : edge.next = edge.state
    · exact different
    · exact absurd (by rw [beq_false_of_ne rejected, beq_false_of_ne different]) stays
  refine ⟨same, ?_⟩
  rw [edge_refines plan compiled edge member, same]

/-! ## Agreement with the hosted oracles -/

/-- For every child command of the table other than the two kernel commands,
the hosted oracle `SpawnAccountingOracle.childOracleStep` gives the status
word `(status << 16) | tag` and the value word the dispatcher gives. -/
def Edge.matchesOracle (plan : BootPageTablePlan.Plan) (edge : Edge) : Bool :=
  match edge.command with
  | .child (.grantAuthority _ _) | .child (.revokeAuthority _) => true
  | .child _ =>
      let hosted := childOracleStep (stateOf plan edge.state) edge.words
      hosted.2.1 == statusWord edge.words.tag edge.status && hosted.2.2 == edge.value
  | _ => true

theorem edges_match_hosted_oracle :
    (match BootPageTablePlan.compile BootPageTablePlan.sampleInput with
      | .ok plan => edges.all (Edge.matchesOracle plan)
      | .error _ => false) = true := by
  native_decide

end LeanOS.SpawnBoundary
