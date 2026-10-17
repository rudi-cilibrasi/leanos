import LeanOS.SpawnAccountingOracle
import LeanOS.CompositeDispatcherResources

/-!
# The spawn family's commands, seeds and whole traces

The spawn family's commands (#489, #491) are the public child commands of
`FailStop.childGate`, the memory commands of `FailStop.memoryGate`, the kernel's
grant and revocation of spawn authority, and the dispatcher's timer switch and
capability copy.  This module holds what every boundary of the family shares:

* the canonical command words (`encodeFamily`, `decodeFamily`), with the
  hosted oracles' tags;
* the typed results as status and value words (`childStatus`,
  `memoryStatus`), with the codes of `SpawnOracle` and
  `SpawnAccountingOracle`;
* one step of the family (`familyStep`: the gate's post-state and the encoded
  result) and replay of a command list (`runFamily`);
* the family seeds (`seedState`, `familySeed`) and their invariants;
* the whole-trace theorem for every command list from every seed
  (`family_trace`).

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
the encoding of what it decodes to (`encodeFamily_decodeFamily`).

The boot path decides the family with the spawn allocator
(`LeanOS.SpawnAllocator`, #575): its thirteen words are the record of a
composite state of this family (`SpawnAllocator.Family`), and
`SpawnAllocator.familyStep_simulates` makes every decided command one
`familyStep`.

The four seeds (`seedState`) differ from the dispatcher's seed
`compositeDispatcherInitial` only in the issuers, the frame commitment, and
the spawn registry.  No authoritative conjunct reads those projections, so a
seed's authoritative invariant is the dispatcher seed's
(`compositeDispatcherInitial_authoritativeRuntimeWellFormed`); the resource
conjuncts are checked directly (`familySeed_resourceRuntimeWellFormed`).
-/
namespace LeanOS.SpawnFamily

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

/-- Busy and halted latches are `0x7e` and `0x7f`; the family's states run
under the running latch, so they never reach them. -/
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

/-! ## Seeds -/

/-- The family's kernel-owned seed: the dispatcher seed
(`compositeDispatcherInitial`), in which subject 2 is current and holds
endpoint 10 (slot 0, handle `0x30000`) and memory object 20 on frame 4 (slot
2), with the issuers past the seed's histories and frame 4 committed to
subject 2.  No spawn authority is held; the kernel grants it first, through the
kernel command. -/
def spawnSeed (plan : BootPageTablePlan.Plan) : CompositeState :=
  { compositeDispatcherInitial plan with
    issuers := { subject := { next := 3 }, object := { next := 21 } }
    frameBudgets := { commitment := fun frame => if frame = 4 then some 2 else none } }

/-- The family seeds.  The three exhaustion seeds are the main seed with one
never-reused counter at its bound; no short trace reaches a bound of
`2^64 - 1`, so they are seeds of their own. -/
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

/-! ## Replay -/

def runFamily (state : CompositeState) : List FamilyCommand → CompositeState
  | [] => state
  | command :: rest => runFamily (familyStep state command).state rest

theorem runFamily_append (state : CompositeState) (commands : List FamilyCommand)
    (command : FamilyCommand) :
    runFamily state (commands ++ [command]) =
      (familyStep (runFamily state commands) command).state := by
  induction commands generalizing state with
  | nil => rfl
  | cons first rest ih => exact ih _

open LeanOS.CompositeFootprint (Projection)

/-! ## Seeds satisfy the combined invariant -/

/-- A seed of the family: the dispatcher seed with issuers, the single frame
commitment of frame 4 to subject 2, and an empty spawn registry with some
generation counters. -/
def familySeed (plan : BootPageTablePlan.Plan) (subjectNext objectNext : Nat)
    (registry : SpawnRegistry) : CompositeState :=
  { compositeDispatcherInitial plan with
    issuers := { subject := { next := subjectNext }, object := { next := objectNext } }
    frameBudgets := { commitment := fun frame => if frame = 4 then some 2 else none }
    spawn := registry }

theorem authoritative_issuers_frameBudgets_unsupported :
    authoritativeInvariants.all
      (fun invariant => !invariant.support.contains .issuers &&
        !invariant.support.contains .frameBudgets) = true := by
  decide

theorem familySeed_authoritativeRuntimeWellFormed (plan : BootPageTablePlan.Plan)
    (subjectNext objectNext : Nat) (registry : SpawnRegistry) :
    AuthoritativeRuntimeWellFormed (familySeed plan subjectNext objectNext registry) := by
  have holds := compositeDispatcherInitial_authoritativeRuntimeWellFormed plan
  rw [authoritativeRuntimeWellFormed_iff_all] at holds ⊢
  intro invariant member
  apply invariant.dependsOn (compositeDispatcherInitial plan) _ _ (holds invariant member)
  intro projection supported
  have unsupported := List.all_eq_true.1 authoritative_issuers_frameBudgets_unsupported
    invariant member
  have spawnFree := List.all_eq_true.1 spawn_unsupported invariant
    (List.mem_append_left _ member)
  simp only [decide_eq_true_eq] at supported
  cases projection <;> try rfl
  all_goals simp_all

theorem dispatcherSeed_issuedSubjects (plan : BootPageTablePlan.Plan) (subject : Nat) :
    (compositeDispatcherInitial plan).lifecycle.issuedSubjects subject =
      (decide (subject = 1) || decide (subject = 2)) := rfl

theorem dispatcherSeed_issuedObject (plan : BootPageTablePlan.Plan) (object : Nat) :
    (compositeDispatcherInitial plan).virtualMemory.memory.issued object =
        (decide (object = 1) || decide (object = 2) || decide (object = 10) ||
          decide (object = 20)) ∧
      (compositeDispatcherInitial plan).virtualMemory.issuedAddressSpace object =
        (decide (object = 1) || decide (object = 2)) := ⟨rfl, rfl⟩

/-- **Every family seed satisfies the combined invariant** when its counters
bound the seed's histories and stay in the identity domain. -/
theorem familySeed_resourceRuntimeWellFormed (plan : BootPageTablePlan.Plan)
    (subjectNext objectNext : Nat) (registry : SpawnRegistry)
    (subjectBound : 3 ≤ subjectNext) (subjectDomain : subjectNext ≤ LifetimeIssuer.identityReserved)
    (objectBound : 21 ≤ objectNext) (objectDomain : objectNext ≤ LifetimeIssuer.identityReserved) :
    ResourceRuntimeWellFormed (familySeed plan subjectNext objectNext registry) := by
  refine ⟨familySeed_authoritativeRuntimeWellFormed plan subjectNext objectNext registry, ?_⟩
  rw [resourceWellFormed_iff]
  refine ⟨⟨subjectDomain, objectDomain⟩, ⟨fun subject issued => ?_, fun object issued => ?_⟩,
    fun frame subject committed => ?_, fun object frame bound unwritten => ?_⟩
  · change (compositeDispatcherInitial plan).lifecycle.issuedSubjects subject = true at issued
    rw [dispatcherSeed_issuedSubjects] at issued
    show 0 < subject ∧ subject < subjectNext
    simp only [Bool.or_eq_true, decide_eq_true_eq] at issued
    rcases issued with rfl | rfl <;> exact ⟨by decide, Nat.lt_of_lt_of_le (by decide) subjectBound⟩
  · change ((compositeDispatcherInitial plan).virtualMemory.memory.issued object ||
      (compositeDispatcherInitial plan).virtualMemory.issuedAddressSpace object) = true at issued
    rw [(dispatcherSeed_issuedObject plan object).1,
      (dispatcherSeed_issuedObject plan object).2] at issued
    show 0 < object ∧ object < objectNext
    simp only [Bool.or_eq_true, decide_eq_true_eq] at issued
    rcases issued with (((rfl | rfl) | rfl) | rfl) | (rfl | rfl) <;>
      exact ⟨by decide, Nat.lt_of_lt_of_le (by decide) objectBound⟩
  · change (if frame = 4 then some 2 else none) = some subject at committed
    by_cases four : frame = 4
    · subst four
      simp only [↓reduceIte, Option.some.injEq] at committed
      subst committed
      refine ⟨List.mem_singleton.2 rfl, fun reserved => ?_, rfl⟩
      cases reserved
    · simp [four] at committed
  · change (if object = 20 then some 4 else none) = some frame at bound
    by_cases twenty : object = 20
    · subst twenty
      simp only [↓reduceIte, Option.some.injEq] at bound
      subst bound
      exact ⟨rfl, fun _ _ => rfl⟩
    · simp [twenty] at bound

theorem familySeed_childAccounting (plan : BootPageTablePlan.Plan) (subjectNext objectNext : Nat)
    (registry : SpawnRegistry) (empty : ∀ parent slot, registry.children parent slot = none) :
    ChildAccountingWellFormed (familySeed plan subjectNext objectNext registry) :=
  childAccounting_of_empty _ empty

theorem familySeed_spawnTree (plan : BootPageTablePlan.Plan) (subjectNext objectNext : Nat)
    (registry : SpawnRegistry) (empty : ∀ parent slot, registry.children parent slot = none)
    (noAuthority : ∀ subject, registry.authority subject = none)
    (noParents : ∀ child, registry.parent child = none) :
    SpawnTreeWellFormed (familySeed plan subjectNext objectNext registry) :=
  spawnTree_of_empty _ empty noAuthority noParents

/-- Each of the four seeds is a family seed. -/
theorem seedState_familySeed (plan : BootPageTablePlan.Plan) (seed : Seed) :
    ∃ subjectNext objectNext registry,
      seedState plan seed = familySeed plan subjectNext objectNext registry ∧
      3 ≤ subjectNext ∧ subjectNext ≤ LifetimeIssuer.identityReserved ∧
      21 ≤ objectNext ∧ objectNext ≤ LifetimeIssuer.identityReserved ∧
      (∀ parent slot, registry.children parent slot = none) ∧
      (∀ subject, registry.authority subject = none) ∧
      (∀ child, registry.parent child = none) := by
  have reserved : 21 ≤ LifetimeIssuer.identityReserved := by
    unfold LifetimeIssuer.identityReserved LifetimeIssuer.identityRadix
    decide
  cases seed with
  | main =>
      exact ⟨3, 21, {}, rfl, by omega, by omega, by omega, reserved,
        fun _ _ => rfl, fun _ => rfl, fun _ => rfl⟩
  | subjectsExhausted =>
      exact ⟨LifetimeIssuer.identityReserved, 21, {}, rfl, by omega, Nat.le_refl _, by omega,
        reserved, fun _ _ => rfl, fun _ => rfl, fun _ => rfl⟩
  | objectsExhausted =>
      exact ⟨3, LifetimeIssuer.identityReserved, {}, rfl, by omega, by omega, reserved,
        Nat.le_refl _, fun _ _ => rfl, fun _ => rfl, fun _ => rfl⟩
  | controlsExhausted =>
      exact ⟨3, 21, { nextChildGeneration := CapabilityHandle.generationReserved }, rfl,
        by omega, by omega, by omega, reserved, fun _ _ => rfl, fun _ => rfl, fun _ => rfl⟩

/-! ## Every command list is an admissible child trace -/

theorem runFamily_runChildSteps (state : CompositeState) (commands : List FamilyCommand) :
    runFamily state commands = runChildSteps state (commands.map FamilyCommand.toStep) := by
  induction commands generalizing state with
  | nil => rfl
  | cons command rest ih =>
      simp only [runFamily, List.map_cons, runChildSteps]
      rw [familyStep_state]
      exact ih _

/-- Every family command is admissible in every state: child and memory steps
need no premise, and the switch and the copy are unconditional composite
steps. -/
theorem toStep_admissible (state : CompositeState) (command : FamilyCommand) :
    command.toStep.Admissible state := by
  cases command with
  | child operation => trivial
  | memory operation => trivial
  | switch => exact CompositeStep.admissible_of_unconditional _ _ rfl
  | copy => exact CompositeStep.admissible_of_unconditional _ _ rfl

theorem admissibleAlong_family (state : CompositeState) (commands : List FamilyCommand) :
    AdmissibleAlongChild state (commands.map FamilyCommand.toStep) := by
  induction commands generalizing state with
  | nil => trivial
  | cons command rest ih => exact ⟨toStep_admissible state command, ih _⟩

/-- **The whole-trace theorem for every command list.**  Every state the spawn
family reaches from a seed satisfies the authoritative, resource, child-accounting,
and spawn-tree invariants; frame usage is within limit; every parent's live
children are within its subject budget, and its usage plus its children's
limits within its entitlement; no frame outside the seed's commitment is
committed; and no subject identity was created twice or reused along the
replayed path. -/
theorem family_trace (plan : BootPageTablePlan.Plan) (start : Seed)
    (commands : List FamilyCommand) :
    let state := runFamily (seedState plan start) commands
    let seed := seedState plan start
    let steps := commands.map FamilyCommand.toStep
    ResourceRuntimeWellFormed state ∧ ChildAccountingWellFormed state ∧
      SpawnTreeWellFormed state ∧
      (createdAlongChild seed steps).Nodup ∧
      (∀ identity, identity ∈ createdAlongChild seed steps →
        seed.lifecycle.issuedSubjects identity = false) ∧
      (∀ subject, state.budgetUsage subject ≤ state.budgetLimit subject) ∧
      (∀ frame, (state.frameBudgets.commitment frame).isSome = true →
        (seed.frameBudgets.commitment frame).isSome = true) ∧
      (∀ parent capability, state.spawn.authority parent = some capability →
        childCount state parent ≤ capability.subjectBudget) ∧
      (∀ parent, state.budgetUsage parent + childLimits state parent ≤
        entitlement state parent) := by
  intro state seed steps
  obtain ⟨subjectNext, objectNext, registry, seedEq, subjectBound, subjectDomain, objectBound,
    objectDomain, empty, noAuthority, noParents⟩ := seedState_familySeed plan start
  have holds : ResourceRuntimeWellFormed seed := by
    simp only [seed, seedEq]
    exact familySeed_resourceRuntimeWellFormed plan subjectNext objectNext registry subjectBound
      subjectDomain objectBound objectDomain
  have accounting : ChildAccountingWellFormed seed := by
    simp only [seed, seedEq]
    exact familySeed_childAccounting plan subjectNext objectNext registry empty
  have tree : SpawnTreeWellFormed seed := by
    simp only [seed, seedEq]
    exact familySeed_spawnTree plan subjectNext objectNext registry empty noAuthority noParents
  obtain ⟨final, finalAccounting, finalTree, nodup, fresh, _, _, usage, _, committed, budget,
    entitled, _, _⟩ :=
    child_resource_trace seed steps holds accounting tree (admissibleAlong_family _ _)
  have stateEq : state = runChildSteps seed steps := runFamily_runChildSteps _ _
  rw [stateEq]
  exact ⟨final, finalAccounting, finalTree, nodup, fresh, usage, committed, budget, entitled⟩

end LeanOS.SpawnFamily
