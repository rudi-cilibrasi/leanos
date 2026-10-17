import LeanOS.SpawnAllocatorWordsEncode
import LeanOS.SpawnAllocatorSeeds

/-!
# The spawn allocator's boot exports refine the composite (#575)

The kernel holds thirteen words.  The theorems below say what those words and
the generated `SpawnAllocatorBoot` exports of `LeanOS.SpawnAllocatorWords` mean.

* `family_bounded`: every `Family` state's record is bounded, so its words are
  canonical and decode back to it (`encode_canonical`, `decode_encode`).
* `registersCanonical_iff`: the register check is exactly decoding to a
  syscall command; `syscallTag_not_kernel`: no number names a kernel
  command.
* `syscall_refines`: on the words of any `Family` state, a syscall that is
  not refused runs exactly one `childGate` or `memoryGate` step of the
  composite (`familyStep`) on that state, with the parent as the actor: the
  reply carries the gate's status, the value word is the gate's, the
  successor words are the words of the gate's post-state, and the post-state
  is again a `Family` state.
* `syscall_rollback`: on a refusal or a rejection every word is kept and the
  value is zero.
* `kernel_refines`: the same for the kernel's own commands, including its
  grant and revocation of spawn authority.
* `seed_refines` and `syscallTrace_refines`: the seed words are the words of
  the family seed, so along every sequence of syscalls the kernel's words are
  the words of the composite state the same commands reach.
-/
namespace LeanOS.SpawnAllocatorBoot

open LeanOS
open LeanOS.FailStop
open LeanOS.SpawnAllocator
open LeanOS.SpawnAllocatorWords
open LeanOS.SpawnBoundary
open LeanOS.CompositeDispatcher (CommandWords)

set_option linter.unusedSimpArgs false

/-! ## Family records are bounded -/

/-- **Every family state's record is bounded.** -/
theorem family_bounded (state : CompositeState) (family : Family state) :
    Bounded (abstraction state) := by
  have issuers := ((resourceWellFormed_iff state).1 family.resources.2).1
  obtain ⟨subjectDomain, objectDomain⟩ := issuers
  have reserved : LifetimeIssuer.identityReserved < 2 ^ 64 := by
    unfold LifetimeIssuer.identityReserved LifetimeIssuer.identityRadix; decide
  have capability := family.capabilityBound
  have control := family.controlBound
  obtain ⟨generationPositive, generationBound⟩ := family.generationBound
  have frames := family.frameBound
  have generationReserved : CapabilityHandle.generationReserved = 2 ^ 48 - 1 := rfl
  refine ⟨?_, ?_, ?_, ?_, generationPositive, generationBound, ?_, ?_, ?_, rfl, ?_, ?_, frames⟩
  · show state.issuers.subject.next < 2 ^ 64
    have : state.issuers.subject.next ≤ LifetimeIssuer.identityReserved := subjectDomain
    omega
  · show state.issuers.object.next < 2 ^ 64
    have : state.issuers.object.next ≤ LifetimeIssuer.identityReserved := objectDomain
    omega
  · show state.capabilities.nextIdentity < 2 ^ 64
    rw [generationReserved] at capability
    omega
  · show state.spawn.nextChildGeneration < 2 ^ 64
    rw [generationReserved] at control
    omega
  · intro generation held
    change (state.spawn.authority parent).map SpawnCapability.generation = some generation at held
    cases found : state.spawn.authority parent with
    | none => rw [found] at held; cases held
    | some capability =>
        rw [found] at held
        simp only [Option.map_some, Option.some.injEq] at held
        subst held
        obtain ⟨_, positive, below⟩ := family.authority capability found
        exact ⟨positive, by omega⟩
  · show subjectBudget state parent ≤ childCapacity
    unfold subjectBudget
    cases found : state.spawn.authority parent with
    | none => decide
    | some capability => exact (family.authority capability found).1
  · show ((List.range childCapacity).map _).length = childCapacity
    simp
  · intro entry member
    rw [abstraction_children] at member
    obtain ⟨slot, _, mapped⟩ := List.mem_map.1 member
    cases found : state.spawn.children parent slot with
    | none => rw [found] at mapped; cases mapped
    | some child =>
        rw [found] at mapped
        simp only [Option.map_some, Option.some.injEq] at mapped
        subst mapped
        obtain ⟨_, positive, _⟩ := family.childLive slot child found
        obtain ⟨_, below, _⟩ := family.accounting.entries parent slot child found
        exact ⟨positive, Nat.lt_of_lt_of_le below control⟩
  · intro identity member
    have memoryEq : (abstraction state).memory = [memoryIn state 2, memoryIn state 3] := rfl
    rw [memoryEq] at member
    have bound : ∀ slot, (slot = 2 ∨ slot = 3) → memoryIn state slot = some identity →
        0 < identity ∧ identity < wordBound := by
      intro slot which held
      unfold memoryIn at held
      rcases family.memory slot which with empty | ⟨found, _, foundHeld, kind, _, positive, _⟩
      · rw [empty] at held; cases held
      · rw [foundHeld] at held
        simp only [kind, ↓reduceIte, Option.some.injEq] at held
        subst held
        have below := ((family_runtime state family).2.2.2.1.1 parent slot found
          foundHeld).2.2.2.2.1
        rw [generationReserved] at capability
        exact ⟨positive, by show found.identity < 2 ^ 64; omega⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with held | held
    · exact bound 2 (Or.inl rfl) held.symm
    · exact bound 3 (Or.inr rfl) held.symm

/-! ## Numbers and registers -/

/-- The command words of a syscall: the number's tag, RBX, RCX, RDX, and a
zero fourth argument. -/
def syscallWords (number rbx rcx rdx : UInt64) : CommandWords :=
  { tag := syscallTag number, arg0 := rbx, arg1 := rcx, arg2 := rdx, arg3 := 0 }

def syscallTags : List UInt64 := [0x7001, 0x7101, 0x7201, 0x7301, 0x7401]

theorem syscallTag_cases (number : UInt64) :
    syscallTag number = 0 ∨ syscallTag number ∈ syscallTags := by
  unfold syscallTag
  repeat' split
  all_goals simp [syscallTags]

/-- **No syscall number names a kernel command**: neither the grant nor the
revocation of spawn authority. -/
theorem syscallTag_not_kernel (number : UInt64) :
    syscallTag number ≠ SpawnAllocatorWords.grantAuthorityTag ∧ syscallTag number ≠ SpawnAllocatorWords.revokeAuthorityTag := by
  rcases syscallTag_cases number with zero | member
  · rw [zero]; decide
  · simp only [syscallTags, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with h | h | h | h | h <;> rw [h] <;> decide

/-- **The register check is exactly decoding.**  For a syscall number, the
registers pass exactly when the command words decode, and then they decode to
a syscall command. -/
theorem registersCanonical_iff (number rbx rcx rdx : UInt64) (named : syscallTag number ≠ 0) :
    registersCanonical (syscallTag number) rbx rcx rdx = true ↔
      ∃ command, decodeCommand (syscallWords number rbx rcx rdx) = .ok command ∧
        command.isSyscall = true := by
  rcases syscallTag_cases number with zero | member
  · exact absurd zero named
  simp only [syscallTags, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with tag | tag | tag | tag | tag
  · simp only [registersCanonical, syscallWords, tag, decodeCommand, SpawnAllocatorWords.spawnTag, SpawnAllocatorWords.grantTag,
      SpawnAllocatorWords.terminateTag, SpawnAccountingOracle.decodeChild, SpawnOracle.decodeSpawn,
      SpawnOracle.decodeRights, SpawnOracle.spawnCommandTag]
    by_cases zero : rbx = 0
    · subst zero; simp
    · by_cases wide : 64 ≤ rdx
      · have : ¬ rdx < 64 := by
          intro small
          rw [UInt64.le_iff_toNat_le] at wide
          rw [UInt64.lt_iff_toNat_lt] at small
          simp at wide small
          omega
        simp [zero, wide, this]
      · have small : rdx < 64 := by
          rw [UInt64.le_iff_toNat_le] at wide
          rw [UInt64.lt_iff_toNat_lt]
          simp at wide ⊢
          omega
        simp [zero, wide, small, Command.isSyscall]
  · simp only [registersCanonical, syscallWords, tag, decodeCommand, SpawnAllocatorWords.spawnTag, SpawnAllocatorWords.grantTag,
      SpawnAllocatorWords.terminateTag, SpawnAccountingOracle.decodeChild, SpawnOracle.spawnCommandTag,
      SpawnAccountingOracle.grantFramesTag, SpawnAccountingOracle.terminateChildTag]
    by_cases reserved : rdx = 0
    · subst reserved
      by_cases zero : rcx = 0
      · subst zero; simp
      · simp [zero, Command.isSyscall]
    · simp [reserved]
  · simp only [registersCanonical, syscallWords, tag, decodeCommand, SpawnAllocatorWords.spawnTag, SpawnAllocatorWords.grantTag,
      SpawnAllocatorWords.terminateTag, SpawnAccountingOracle.decodeChild, SpawnOracle.spawnCommandTag,
      SpawnAccountingOracle.grantFramesTag, SpawnAccountingOracle.terminateChildTag]
    by_cases first : rcx = 0
    · subst first
      by_cases second : rdx = 0
      · subst second
        simp [Command.isSyscall]
      · simp [second]
    · simp [first]
  · simp only [registersCanonical, syscallWords, tag, decodeCommand, SpawnAllocatorWords.spawnTag, SpawnAllocatorWords.grantTag,
      SpawnAllocatorWords.terminateTag, SpawnAllocatorWords.allocateTag]
    by_cases first : rcx = 0
    · subst first
      by_cases second : rdx = 0
      · subst second
        simp [Command.isSyscall]
      · simp [second]
    · simp [first]
  · simp only [registersCanonical, syscallWords, tag, decodeCommand, SpawnAllocatorWords.spawnTag, SpawnAllocatorWords.grantTag,
      SpawnAllocatorWords.terminateTag, SpawnAllocatorWords.allocateTag, SpawnAllocatorWords.releaseTag]
    by_cases first : rcx = 0
    · subst first
      by_cases second : rdx = 0
      · subst second
        simp [Command.isSyscall]
      · simp [second]
    · simp [first]

/-! ## The exports on a `Words` record -/

/-- Word `index` of a record of words. -/
def Words.at (words : Words) (index : UInt64) : UInt64 :=
  wordAt index words.subjectNext words.objectNext words.capabilityNext words.controlNext
    words.authorityNext words.authority words.child0 words.child1 words.child2 words.child3
    words.memory2 words.memory3 words.frames

def refusalOf (words : Words) (actor number rbx rcx rdx : UInt64) : UInt64 :=
  refusal words.authorityNext words.child0 words.child1 words.child2 words.child3 words.frames
    actor number rbx rcx rdx

def syscallOf (words : Words) (actor number rbx rcx rdx : UInt64) : UInt64 :=
  syscall words.subjectNext words.objectNext words.capabilityNext words.controlNext
    words.authorityNext words.authority words.child0 words.child1 words.child2 words.child3
    words.memory2 words.memory3 words.frames actor number rbx rcx rdx

def syscallValueOf (words : Words) (actor number rbx rcx rdx : UInt64) : UInt64 :=
  syscallValue words.subjectNext words.objectNext words.capabilityNext words.controlNext
    words.authorityNext words.authority words.child0 words.child1 words.child2 words.child3
    words.memory2 words.memory3 words.frames actor number rbx rcx rdx

/-- The thirteen successor words of a syscall. -/
def syscallNextOf (words : Words) (actor number rbx rcx rdx : UInt64) : Words :=
  let wordAfter := fun (index : UInt64) =>
    syscallNext index words.subjectNext words.objectNext words.capabilityNext words.controlNext
      words.authorityNext words.authority words.child0 words.child1 words.child2 words.child3
      words.memory2 words.memory3 words.frames actor number rbx rcx rdx
  ⟨wordAfter 0, wordAfter 1, wordAfter 2, wordAfter 3, wordAfter 4, wordAfter 5, wordAfter 6,
    wordAfter 7, wordAfter 8, wordAfter 9, wordAfter 10, wordAfter 11, wordAfter 12⟩

def kernelOf (words : Words) (command : CommandWords) : UInt64 :=
  kernel words.subjectNext words.objectNext words.capabilityNext words.controlNext
    words.authorityNext words.authority words.child0 words.child1 words.child2 words.child3
    words.memory2 words.memory3 words.frames command.tag command.arg0 command.arg1 command.arg2
    command.arg3

def kernelValueOf (words : Words) (command : CommandWords) : UInt64 :=
  kernelValue words.subjectNext words.objectNext words.capabilityNext words.controlNext
    words.authorityNext words.authority words.child0 words.child1 words.child2 words.child3
    words.memory2 words.memory3 words.frames command.tag command.arg0 command.arg1 command.arg2
    command.arg3

/-- The thirteen successor words of a kernel command. -/
def kernelNextOf (words : Words) (command : CommandWords) : Words :=
  let wordAfter := fun (index : UInt64) =>
    kernelNext index words.subjectNext words.objectNext words.capabilityNext words.controlNext
      words.authorityNext words.authority words.child0 words.child1 words.child2 words.child3
      words.memory2 words.memory3 words.frames command.tag command.arg0 command.arg1 command.arg2
      command.arg3
  ⟨wordAfter 0, wordAfter 1, wordAfter 2, wordAfter 3, wordAfter 4, wordAfter 5, wordAfter 6,
    wordAfter 7, wordAfter 8, wordAfter 9, wordAfter 10, wordAfter 11, wordAfter 12⟩

/-- What a syscall that is not refused checked. -/
theorem refusalOf_zero (words : Words) (actor number rbx rcx rdx : UInt64)
    (admitted : refusalOf words actor number rbx rcx rdx = 0) :
    Canonical words = true ∧ actor = 2 ∧ syscallTag number ≠ 0 ∧
      registersCanonical (syscallTag number) rbx rcx rdx = true := by
  unfold refusalOf refusal at admitted
  by_cases canonicalWords : Canonical words = true
  · have canonicalRaw : canonical words.authorityNext words.child0 words.child1 words.child2
        words.child3 words.frames = true := canonicalWords
    simp only [canonicalRaw, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at admitted
    by_cases parentActor : actor = 2
    · simp only [parentActor, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at admitted
      by_cases named : syscallTag number = 0
      · simp [named] at admitted
      · simp only [named, beq_iff_eq, ↓reduceIte] at admitted
        by_cases registers : registersCanonical (syscallTag number) rbx rcx rdx = true
        · exact ⟨canonicalWords, parentActor, named, registers⟩
        · simp [registers] at admitted
    · have : (actor != 2) = true := by simpa using parentActor
      simp [this] at admitted
  · have canonicalRaw : canonical words.authorityNext words.child0 words.child1 words.child2
        words.child3 words.frames = false := by simpa [Canonical] using canonicalWords
    simp [canonicalRaw] at admitted

/-- An admitted syscall runs the generated step functions on its command
words. -/
theorem syscall_code (words : Words) (actor number rbx rcx rdx : UInt64)
    (admitted : refusalOf words actor number rbx rcx rdx = 0) :
    syscallOf words actor number rbx rcx rdx =
        replyOf (codeReply words (syscallWords number rbx rcx rdx)) ∧
      syscallValueOf words actor number rbx rcx rdx = codeValue words (syscallWords number rbx rcx rdx) ∧
      syscallNextOf words actor number rbx rcx rdx = codeNext words (syscallWords number rbx rcx rdx) := by
  have zero : refusal words.authorityNext words.child0 words.child1 words.child2 words.child3
      words.frames actor number rbx rcx rdx = 0 := admitted
  refine ⟨?_, ?_, ?_⟩
  · simp only [syscallOf, syscall, zero, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    rfl
  · simp only [syscallValueOf, syscallValue, zero, bne_self_eq_false, Bool.false_eq_true,
      ↓reduceIte]
    rfl
  · simp only [syscallNextOf, syscallNext, zero, bne_self_eq_false, Bool.false_eq_true,
      ↓reduceIte]
    rfl

/-- **Refusals keep every word.** -/
theorem syscall_refused (words : Words) (actor number rbx rcx rdx : UInt64)
    (refused : refusalOf words actor number rbx rcx rdx ≠ 0) :
    syscallOf words actor number rbx rcx rdx = refusalOf words actor number rbx rcx rdx ∧
      syscallValueOf words actor number rbx rcx rdx = 0 ∧
      syscallNextOf words actor number rbx rcx rdx = words := by
  have nonzero : (refusal words.authorityNext words.child0 words.child1 words.child2 words.child3
      words.frames actor number rbx rcx rdx != 0) = true := by simpa [refusalOf] using refused
  refine ⟨?_, ?_, ?_⟩
  · simp only [syscallOf, syscall, nonzero, ↓reduceIte]; rfl
  · simp only [syscallValueOf, syscallValue, nonzero, ↓reduceIte]
  · simp only [syscallNextOf, syscallNext, nonzero, ↓reduceIte]
    rfl

/-- The family command of an allocator command. -/
def familyCommandOf : Command → FamilyCommand
  | .child operation => .child operation
  | .memory operation => .memory operation

theorem toCommand_familyCommandOf (command : Command) :
    toCommand (familyCommandOf command) = some command := by
  cases command <;> rfl

/-! ## The syscall refines the composite -/

/-- **The spawn syscall on the words of a family state is one gate step of
that state.**  A syscall that is not refused decodes to a syscall command
(never a kernel command), runs as `familyStep` with the parent, the current
subject, as the actor; the reply carries the gate's status, the value word
is the gate's, the successor words are the words of the gate's post-state,
and that post-state is again a `Family` state. -/
theorem syscall_refines (state : CompositeState) (family : Family state)
    (actor number rbx rcx rdx : UInt64)
    (admitted : refusalOf (encode (abstraction state)) actor number rbx rcx rdx = 0) :
    ∃ command, decodeCommand (syscallWords number rbx rcx rdx) = .ok command ∧
      command.isSyscall = true ∧
      actor.toNat = state.execution.core.context.currentSubject ∧
      syscallOf (encode (abstraction state)) actor number rbx rcx rdx =
        replyOf (familyStep state (familyCommandOf command)).status ∧
      syscallValueOf (encode (abstraction state)) actor number rbx rcx rdx =
        (familyStep state (familyCommandOf command)).value ∧
      syscallNextOf (encode (abstraction state)) actor number rbx rcx rdx =
        encode (abstraction (familyStep state (familyCommandOf command)).state) ∧
      Family (familyStep state (familyCommandOf command)).state := by
  obtain ⟨_, parentActor, named, registers⟩ :=
    refusalOf_zero (encode (abstraction state)) actor number rbx rcx rdx admitted
  obtain ⟨command, decoded, syscallCommand⟩ :=
    (registersCanonical_iff number rbx rcx rdx named).1 registers
  have covered := syscall_commands_covered (abstraction state) command syscallCommand
  obtain ⟨result, decided⟩ := Option.isSome_iff_exists.1 covered
  obtain ⟨reply, value, next⟩ := code_step (abstraction state) (family_bounded state family)
    (syscallWords number rbx rcx rdx) command decoded result decided
  obtain ⟨status, stepValue, abstractionEq, postFamily⟩ :=
    familyStep_simulates state family (familyCommandOf command) command result
      (toCommand_familyCommandOf command) decided
  obtain ⟨syscallReply, syscallValue', syscallNext'⟩ :=
    syscall_code (encode (abstraction state)) actor number rbx rcx rdx admitted
  refine ⟨command, decoded, syscallCommand, ?_, ?_, ?_, ?_, postFamily⟩
  · rw [family.current, parentActor]; rfl
  · rw [syscallReply, reply, status]
  · rw [syscallValue', value, stepValue]
  · rw [syscallNext', next, abstractionEq]

/-- **Rollback.**  On the words of a family state, a syscall that is refused,
or that the gate rejects, keeps every word and returns a zero value, and the
gate's post-state is the pre-state. -/
theorem syscall_rollback (state : CompositeState) (family : Family state)
    (actor number rbx rcx rdx : UInt64) :
    refusalOf (encode (abstraction state)) actor number rbx rcx rdx ≠ 0 ∨
      (∃ command, decodeCommand (syscallWords number rbx rcx rdx) = .ok command ∧
        ((familyStep state (familyCommandOf command)).status = 0x01 ∨
          (familyStep state (familyCommandOf command)).state = state ∧
          syscallNextOf (encode (abstraction state)) actor number rbx rcx rdx =
            encode (abstraction state) ∧
          syscallValueOf (encode (abstraction state)) actor number rbx rcx rdx = 0)) := by
  by_cases admitted : refusalOf (encode (abstraction state)) actor number rbx rcx rdx = 0
  · right
    obtain ⟨command, decoded, syscallCommand, _, _, value, next, _⟩ :=
      syscall_refines state family actor number rbx rcx rdx admitted
    refine ⟨command, decoded, ?_⟩
    by_cases accepted : (familyStep state (familyCommandOf command)).status = 0x01
    · exact Or.inl accepted
    · right
      have notAuthoritative : (familyCommandOf command).isAuthoritative = false := by
        cases command <;> rfl
      have same := familyStep_stutter state (familyCommandOf command) notAuthoritative accepted
      have zero : (familyStep state (familyCommandOf command)).value = 0 := by
        have covered := syscall_commands_covered (abstraction state) command syscallCommand
        obtain ⟨result, decided⟩ := Option.isSome_iff_exists.1 covered
        obtain ⟨status, stepValue, _, _⟩ :=
          familyStep_simulates state family (familyCommandOf command) command result
            (toCommand_familyCommandOf command) decided
        rw [stepValue]
        exact step_rejected_value _ command result decided (by rw [← status]; exact accepted)
      refine ⟨same, ?_, ?_⟩
      · rw [next, same]
      · rw [value, zero]
  · exact Or.inl admitted

/-! ## Kernel commands -/

/-- **A kernel command on the words of a family state is one gate step of
that state**: the status and value are the gate's, the successor words are
the words of its post-state, and the post-state is a `Family` state. -/
theorem kernel_refines (state : CompositeState) (family : Family state) (words : CommandWords)
    (command : Command) (decoded : decodeCommand words = .ok command) (result : Step)
    (decided : step (abstraction state) command = some result) :
    kernelOf (encode (abstraction state)) words = (familyStep state (familyCommandOf command)).status ∧
      kernelValueOf (encode (abstraction state)) words =
        (familyStep state (familyCommandOf command)).value ∧
      kernelNextOf (encode (abstraction state)) words =
        encode (abstraction (familyStep state (familyCommandOf command)).state) ∧
      Family (familyStep state (familyCommandOf command)).state := by
  obtain ⟨reply, value, next⟩ := code_step (abstraction state) (family_bounded state family)
    words command decoded result decided
  obtain ⟨status, stepValue, abstractionEq, postFamily⟩ :=
    familyStep_simulates state family (familyCommandOf command) command result
      (toCommand_familyCommandOf command) decided
  refine ⟨?_, ?_, ?_, postFamily⟩
  · rw [status, ← reply]; rfl
  · rw [stepValue, ← value]; rfl
  · rw [abstractionEq, ← next]; rfl

/-! ## The seed and whole traces -/

/-- The seed words. -/
def seedWords : Words :=
  ⟨seed 0, seed 1, seed 2, seed 3, seed 4, seed 5, seed 6, seed 7, seed 8, seed 9, seed 10,
    seed 11, seed 12⟩

/-- **The seed words are the words of the family seed**, for every boot
plan, and the family seed is a family state. -/
theorem seed_refines (plan : BootPageTablePlan.Plan) :
    seedWords = encode (abstraction (seedState plan .main)) ∧ Family (seedState plan .main) := by
  refine ⟨?_, seedState_family plan .main⟩
  rw [abstraction_seedState]
  decide

/-- One syscall of the kernel: the successor words and the composite state
the same command reaches (unchanged on a refusal). -/
def syscallStep (state : CompositeState) (actor number rbx rcx rdx : UInt64) : CompositeState :=
  if refusalOf (encode (abstraction state)) actor number rbx rcx rdx = 0 then
    match decodeCommand (syscallWords number rbx rcx rdx) with
    | .ok command => (familyStep state (familyCommandOf command)).state
    | .error _ => state
  else state

/-- **Every syscall keeps the kernel's words the words of a family state.**
If the kernel's words are the words of a family state, then after any syscall
they are the words of `syscallStep`, which is a family state again. -/
theorem syscall_preserves (state : CompositeState) (family : Family state)
    (actor number rbx rcx rdx : UInt64) :
    syscallNextOf (encode (abstraction state)) actor number rbx rcx rdx =
        encode (abstraction (syscallStep state actor number rbx rcx rdx)) ∧
      Family (syscallStep state actor number rbx rcx rdx) := by
  by_cases admitted : refusalOf (encode (abstraction state)) actor number rbx rcx rdx = 0
  · obtain ⟨command, decoded, _, _, _, _, next, postFamily⟩ :=
      syscall_refines state family actor number rbx rcx rdx admitted
    simp only [syscallStep, admitted, ↓reduceIte, decoded]
    exact ⟨next, postFamily⟩
  · obtain ⟨_, _, next⟩ := syscall_refused (encode (abstraction state)) actor number rbx rcx rdx
      admitted
    simp only [syscallStep, admitted, ↓reduceIte]
    exact ⟨next, family⟩

/-- A syscall's registers: the actor, the number and RBX, RCX, RDX. -/
structure SyscallInput where
  actor : UInt64
  number : UInt64
  rbx : UInt64
  rcx : UInt64
  rdx : UInt64

/-- The kernel's words after a list of syscalls. -/
def runWords (words : Words) : List SyscallInput → Words
  | [] => words
  | input :: rest =>
      runWords (syscallNextOf words input.actor input.number input.rbx input.rcx input.rdx) rest

/-- The composite state the same list of syscalls reaches. -/
def runStates (state : CompositeState) : List SyscallInput → CompositeState
  | [] => state
  | input :: rest =>
      runStates (syscallStep state input.actor input.number input.rbx input.rcx input.rdx) rest

/-- **Along every list of syscalls from the seed, the kernel's words are the
words of the family state the same gate steps reach.** -/
theorem syscallTrace_refines (plan : BootPageTablePlan.Plan) (inputs : List SyscallInput) :
    runWords seedWords inputs = encode (abstraction (runStates (seedState plan .main) inputs)) ∧
      Family (runStates (seedState plan .main) inputs) := by
  obtain ⟨seeded, seedFamily⟩ := seed_refines plan
  rw [seeded]
  generalize seedState plan .main = state at seedFamily ⊢
  induction inputs generalizing state with
  | nil => exact ⟨rfl, seedFamily⟩
  | cons input rest ih =>
      obtain ⟨next, nextFamily⟩ := syscall_preserves state seedFamily input.actor input.number
        input.rbx input.rcx input.rdx
      simp only [runWords, runStates]
      rw [next]
      exact ih _ nextFamily

/-! ## The specification the hosted vectors check -/

/-- **What a syscall should compute**, from the decoder, the allocator and
the encoding: the refusal words in order, then the allocator's step on the
decoded record. -/
def specSyscall (words : Words) (actor number rbx rcx rdx : UInt64) : UInt64 × UInt64 × Words :=
  if Canonical words = false then (0xfe20, 0, words)
  else if actor ≠ 2 then (0xfe21, 0, words)
  else if syscallTag number = 0 then (0xfe22, 0, words)
  else match decodeCommand (syscallWords number rbx rcx rdx) with
    | .error _ => (0xfe23, 0, words)
    | .ok command =>
        if command.isSyscall = false then (0xfe23, 0, words)
        else match step (decode words) command with
          | none => (0xfe24, 0, words)
          | some result => (replyOf result.status, result.value, encode result.next)

/-- **The generated syscall exports compute the specification, for every
input.** -/
theorem syscall_spec (words : Words) (actor number rbx rcx rdx : UInt64) :
    (syscallOf words actor number rbx rcx rdx, syscallValueOf words actor number rbx rcx rdx,
      syscallNextOf words actor number rbx rcx rdx) = specSyscall words actor number rbx rcx rdx := by
  by_cases admitted : refusalOf words actor number rbx rcx rdx = 0
  · obtain ⟨canonicalWords, parentActor, named, registers⟩ :=
      refusalOf_zero words actor number rbx rcx rdx admitted
    subst parentActor
    obtain ⟨command, decoded, syscallCommand⟩ :=
      (registersCanonical_iff number rbx rcx rdx named).1 registers
    obtain ⟨reply, value, next⟩ := syscall_code words 2 number rbx rcx rdx admitted
    obtain ⟨codeReplyEq, codeValueEq, codeNextEq⟩ := words_refine words
      (syscallWords number rbx rcx rdx)
    have covered := syscall_commands_covered (decode words) command syscallCommand
    obtain ⟨result, decided⟩ := Option.isSome_iff_exists.1 covered
    have specEq : specStep words (syscallWords number rbx rcx rdx) =
        (encode result.next, result.status, result.value) := by
      simp only [specStep, canonicalWords, decoded, decided]
      rfl
    rw [specEq] at codeReplyEq codeValueEq codeNextEq
    have canonicalTrue : ¬(Canonical words = false) := by simp [canonicalWords]
    simp only [specSyscall, canonicalTrue, named, decoded, syscallCommand, decided,
      ↓reduceIte, ne_eq, not_true_eq_false, Bool.true_eq_false]
    rw [reply, value, next, codeReplyEq, codeValueEq, codeNextEq]
  · obtain ⟨reply, value, next⟩ := syscall_refused words actor number rbx rcx rdx admitted
    rw [reply, value, next]
    unfold refusalOf refusal at admitted ⊢
    by_cases canonicalWords : Canonical words = true
    · have canonicalRaw : canonical words.authorityNext words.child0 words.child1 words.child2
          words.child3 words.frames = true := canonicalWords
      have canonicalTrue : ¬(Canonical words = false) := by simp [canonicalWords]
      simp only [canonicalRaw, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at admitted ⊢
      simp only [specSyscall, canonicalTrue, ↓reduceIte]
      by_cases parentActor : actor = 2
      · simp only [parentActor, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, ne_eq,
          not_true_eq_false] at admitted ⊢
        by_cases named : syscallTag number = 0
        · simp [named]
        · simp only [named, beq_iff_eq, ↓reduceIte] at admitted ⊢
          by_cases registers : registersCanonical (syscallTag number) rbx rcx rdx = true
          · simp [registers] at admitted
          · simp only [registers, Bool.not_false, ↓reduceIte]
            have notDecoded := mt (registersCanonical_iff number rbx rcx rdx named).2 registers
            cases decodedCase : decodeCommand (syscallWords number rbx rcx rdx) with
            | error reason => rfl
            | ok command =>
                have notSyscall : command.isSyscall = false := by
                  cases syscallCase : command.isSyscall
                  · rfl
                  · exact absurd ⟨command, decodedCase, syscallCase⟩ notDecoded
                simp [notSyscall]
      · have different : (actor != 2) = true := by simpa using parentActor
        simp [different, parentActor]
    · have canonicalRaw : canonical words.authorityNext words.child0 words.child1 words.child2
          words.child3 words.frames = false := by simpa [Canonical] using canonicalWords
      have canonicalFalse : Canonical words = false := by simpa using canonicalWords
      simp [canonicalRaw, specSyscall, canonicalFalse]

/-- What a kernel command should compute: `specStep`. -/
theorem kernel_spec (words : Words) (command : CommandWords) :
    (kernelOf words command, kernelValueOf words command, kernelNextOf words command) =
      ((specStep words command).2.1, (specStep words command).2.2, (specStep words command).1) := by
  obtain ⟨reply, value, next⟩ := words_refine words command
  rw [← reply, ← value, ← next]
  rfl

end LeanOS.SpawnAllocatorBoot
