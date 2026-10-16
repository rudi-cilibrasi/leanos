import LeanOS.SpawnAllocatorWordsFacts

/-!
# The fixed-width spawn allocator computes the allocator (#575)

`words_refine`: for every thirteen state words and every five command words,
the generated functions `stepReply`, `stepValue` and `stepNextWord` compute
`specStep`, which decodes the words and the command, runs
`SpawnAllocator.step`, and encodes the successor record.
-/
namespace LeanOS.SpawnAllocatorWords

open LeanOS
open LeanOS.FailStop
open LeanOS.SpawnAllocator
open LeanOS.CompositeDispatcher (CommandWords DecodeError)

set_option linter.unusedSimpArgs false

/-! ## Decoded commands -/

/-- The spawn request of command words with decoded rights. -/
def requestOf (command : CommandWords) (rights : Capability.Rights) : SpawnRequest :=
  { spawnWord := command.arg0, endpointWord := command.arg1, rights }

/-- What a decoded command is, in its words. -/
theorem decodeCommand_ok (command : CommandWords) (operation : Command)
    (decoded : decodeCommand command = .ok operation) :
    (command.tag = 0x7001 ∧ ∃ rights, SpawnOracle.decodeRights command.arg2 = .ok rights ∧
        operation = .child (.spawn (requestOf command rights))) ∨
      (command.tag = 0x7101 ∧ operation = .child (.grantFrames command.arg0 command.arg1.toNat)) ∨
      (command.tag = 0x7201 ∧ operation = .child (.terminateChild command.arg0)) ∨
      (command.tag = 0x7301 ∧ operation = .memory (.allocate command.arg0.toNat)) ∨
      (command.tag = 0x7401 ∧ operation = .memory (.release command.arg0.toNat)) ∨
      (command.tag = 0x7501 ∧
        operation = .child (.grantAuthority command.arg0.toNat command.arg1.toNat)) ∨
      (command.tag = 0x7601 ∧ operation = .child (.revokeAuthority command.arg0.toNat)) := by
  obtain ⟨tag, a0, a1, a2, a3⟩ := command
  simp only [decodeCommand, SpawnAccountingOracle.decodeChild, SpawnOracle.decodeSpawn, spawnTag,
    grantTag, terminateTag, allocateTag, releaseTag, grantAuthorityTag, revokeAuthorityTag,
    SpawnOracle.spawnCommandTag, SpawnAccountingOracle.grantFramesTag,
    SpawnAccountingOracle.terminateChildTag] at decoded
  by_cases t0 : tag = 0x7001
  · subst t0
    left
    refine ⟨rfl, ?_⟩
    by_cases r3 : a3 = 0 <;> by_cases z0 : a0 = 0 <;> simp [r3, z0] at decoded
    cases hr : SpawnOracle.decodeRights a2 with
    | error reason => simp [hr] at decoded
    | ok rights =>
        simp only [hr, Except.ok.injEq] at decoded
        exact ⟨rights, by simp [hr], by rw [← decoded]; rfl⟩
  right
  by_cases t1 : tag = 0x7101
  · subst t1
    left
    refine ⟨rfl, ?_⟩
    by_cases r2 : a2 = 0 <;> by_cases r3 : a3 = 0 <;> by_cases z1 : a1 = 0 <;>
      simp [r2, r3, z1] at decoded
    exact decoded.symm
  right
  by_cases t2 : tag = 0x7201
  · subst t2
    left
    refine ⟨rfl, ?_⟩
    by_cases r1 : a1 = 0 <;> by_cases r2 : a2 = 0 <;> by_cases r3 : a3 = 0 <;>
      simp [r1, r2, r3] at decoded
    exact decoded.symm
  right
  by_cases t3 : tag = 0x7301
  · subst t3
    left
    refine ⟨rfl, ?_⟩
    by_cases r1 : a1 = 0 <;> by_cases r2 : a2 = 0 <;> by_cases r3 : a3 = 0 <;>
      simp [r1, r2, r3] at decoded
    exact decoded.symm
  right
  by_cases t4 : tag = 0x7401
  · subst t4
    left
    refine ⟨rfl, ?_⟩
    by_cases r1 : a1 = 0 <;> by_cases r2 : a2 = 0 <;> by_cases r3 : a3 = 0 <;>
      simp [r1, r2, r3] at decoded
    exact decoded.symm
  right
  by_cases t5 : tag = 0x7501
  · subst t5
    left
    refine ⟨rfl, ?_⟩
    by_cases r2 : a2 = 0 <;> by_cases r3 : a3 = 0 <;> simp [r2, r3] at decoded
    exact decoded.symm
  right
  by_cases t6 : tag = 0x7601
  · subst t6
    refine ⟨rfl, ?_⟩
    by_cases r1 : a1 = 0 <;> by_cases r2 : a2 = 0 <;> by_cases r3 : a3 = 0 <;>
      simp [r1, r2, r3] at decoded
    exact decoded.symm
  simp [t0, t1, t2, t3, t4, t5, t6] at decoded

/-! ## The status of each command -/

theorem budget_toNat (words : Words) : (budgetW words.frames).toNat = (decode words).budget := by
  unfold budgetW; rw [toNat_and16]; rfl

theorem le_toNat (left right : UInt64) : (left ≤ right) = (left.toNat ≤ right.toNat) := by
  rw [UInt64.le_iff_toNat_le]

theorem lt_toNat (left right : UInt64) : (left < right) = (left.toNat < right.toNat) := by
  rw [UInt64.lt_iff_toNat_lt]

theorem decide_spawn (words : Words) (request : SpawnRequest)
    (rights : SpawnOracle.decodeRights (SpawnOracle.encodeRights request.rights) =
      .ok request.rights) :
    decideW words.subjectNext words.objectNext words.capabilityNext words.controlNext
        words.authorityNext words.authority words.child0 words.child1 words.child2 words.child3
        words.memory2 words.memory3 words.frames 0x7001 request.spawnWord request.endpointWord
        (SpawnOracle.encodeRights request.rights) =
      (spawnStep (decode words) request).status := by
  unfold decideW spawnStep
  simp only [beq_self_eq_true, ↓reduceIte]
  have authority : (decode words).authority = decodeAuthority words.authority := rfl
  rw [authority]
  unfold decodeAuthority
  by_cases zero : words.authority = 0
  · simp [zero, rejectWith, SpawnAccountingOracle.childSpawnErrorCode, SpawnOracle.spawnErrorCode]
  simp only [zero, beq_iff_eq, ↓reduceIte]
  by_cases stale : words.authority = request.spawnWord
  · have staleNat : ¬(words.authority.toNat ≠ request.spawnWord.toNat) := by simp [stale]
    simp only [stale, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, staleNat]
    simp only [UInt64.le_iff_toNat_le, budget_toNat, childCountW_toNat]
    by_cases full : (decode words).budget ≤ (decode words).childCount
    · simp [full, rejectWith, SpawnAccountingOracle.childSpawnErrorCode]
    simp only [full, decide_false, Bool.false_eq_true, ↓reduceIte]
    rw [freeSlotW_spec]
    by_cases none : freeSlotW words.child0 words.child1 words.child2 words.child3 = 4
    · simp [none, rejectWith, SpawnAccountingOracle.childSpawnErrorCode]
    simp only [none, beq_iff_eq, ↓reduceIte, Bool.false_eq_true]
    rw [controlAvailableW_spec, identityExhaustedW_spec, identityExhaustedW_spec,
      capabilityExhaustedW_spec]
    have controlDecoded : (decode words).controlNext = words.controlNext.toNat := rfl
    have subjectDecoded : (decode words).subjectNext = words.subjectNext.toNat := rfl
    have objectDecoded : (decode words).objectNext = words.objectNext.toNat := rfl
    have capabilityDecoded : (decode words).capabilityNext = words.capabilityNext.toNat := rfl
    rw [controlDecoded, subjectDecoded, objectDecoded, capabilityDecoded]
    by_cases control : controlAvailable words.controlNext.toNat = false
    · simp [control, rejectWith, SpawnAccountingOracle.childSpawnErrorCode]
    simp only [Bool.not_eq_false] at control
    simp only [control, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    by_cases subjects : identityExhausted words.subjectNext.toNat = true
    · simp [subjects, rejectWith, SpawnAccountingOracle.childSpawnErrorCode,
        SpawnOracle.spawnErrorCode]
    simp only [Bool.not_eq_true] at subjects
    simp only [subjects, Bool.false_eq_true, ↓reduceIte]
    by_cases objects : identityExhausted words.objectNext.toNat = true
    · simp [objects, rejectWith, SpawnAccountingOracle.childSpawnErrorCode,
        SpawnOracle.spawnErrorCode]
    simp only [Bool.not_eq_true] at objects
    simp only [objects, Bool.false_eq_true, ↓reduceIte]
    by_cases capabilities : capabilityExhausted words.capabilityNext.toNat = true
    · simp [capabilities, rejectWith, SpawnAccountingOracle.childSpawnErrorCode,
        SpawnOracle.spawnErrorCode, SpawnOracle.addressSpaceErrorCode]
    simp only [Bool.not_eq_true] at capabilities
    simp only [capabilities, Bool.false_eq_true, ↓reduceIte]
    have endpoint := resolveEndpointW_spec words request.endpointWord
    cases resolved : (decode words).resolveEndpoint request.endpointWord with
    | some denial =>
        rw [resolved] at endpoint
        have nonzero : SpawnOracle.handleErrorCode denial ≠ 0 := by
          cases denial <;> (try rename_i reason; cases reason) <;> decide
        simp [endpoint, nonzero, rejectWith, SpawnAccountingOracle.childSpawnErrorCode,
          SpawnOracle.spawnErrorCode]
    | none =>
        rw [resolved] at endpoint
        simp only [endpoint, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
        rw [rightsValidW_spec _ _ rights]
        simp only [ne_eq, not_true_eq_false, ↓reduceIte, Bool.true_eq_false]
        by_cases valid : Capability.rightsValid .endpoint request.rights = true
        · simp [valid, acceptWith]
        · simp only [Bool.not_eq_true] at valid
          simp [valid, rejectWith, SpawnAccountingOracle.childSpawnErrorCode,
            SpawnOracle.spawnErrorCode]
  · have staleNat : words.authority.toNat ≠ request.spawnWord.toNat :=
      fun eq => stale (UInt64.toNat_inj.1 eq)
    have staleBne : (words.authority != request.spawnWord) = true := by simpa using stale
    simp [staleBne, staleNat, rejectWith, SpawnAccountingOracle.childSpawnErrorCode,
      SpawnOracle.spawnErrorCode]

theorem decide_grant (words : Words) (control frames : UInt64) (a2 : UInt64) :
    decideW words.subjectNext words.objectNext words.capabilityNext words.controlNext
        words.authorityNext words.authority words.child0 words.child1 words.child2 words.child3
        words.memory2 words.memory3 words.frames 0x7101 control frames a2 =
      (grantStep (decode words) control frames.toNat).status := by
  unfold decideW grantStep
  simp only [show (0x7101 : UInt64) ≠ 0x7001 from by decide, beq_iff_eq, beq_self_eq_true,
    ↓reduceIte, Bool.false_eq_true]
  have resolved := resolveControlW_spec words control
  cases result : (decode words).resolveControl control with
  | error denial =>
      rw [result] at resolved
      have nonzero : SpawnAccountingOracle.controlDenialCode denial ≠ 0 := by
        cases denial <;> (try rename_i reason; cases reason) <;> decide
      simp [resolved, nonzero, rejectWith, SpawnAccountingOracle.frameGrantErrorCode]
  | ok found =>
      obtain ⟨slot, entry⟩ := found
      rw [result] at resolved
      simp only [resolved, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
      simp only [UInt64.lt_iff_toNat_lt, availableW_toNat]
      by_cases short : (decode words).available < frames.toNat
      · simp [short, rejectWith, SpawnAccountingOracle.frameGrantErrorCode]
      · simp [short, acceptWith]

theorem decide_terminate (words : Words) (control a1 a2 : UInt64) :
    decideW words.subjectNext words.objectNext words.capabilityNext words.controlNext
        words.authorityNext words.authority words.child0 words.child1 words.child2 words.child3
        words.memory2 words.memory3 words.frames 0x7201 control a1 a2 =
      (terminateStep (decode words) control).status := by
  unfold decideW terminateStep
  simp only [show (0x7201 : UInt64) ≠ 0x7001 from by decide,
    show (0x7201 : UInt64) ≠ 0x7101 from by decide, beq_iff_eq, beq_self_eq_true,
    ↓reduceIte, Bool.false_eq_true]
  have resolved := resolveControlW_spec words control
  cases result : (decode words).resolveControl control with
  | error denial =>
      rw [result] at resolved
      have nonzero : SpawnAccountingOracle.controlDenialCode denial ≠ 0 := by
        cases denial <;> (try rename_i reason; cases reason) <;> decide
      simp [resolved, nonzero, rejectWith]
  | ok found =>
      obtain ⟨slot, entry⟩ := found
      rw [result] at resolved
      simp [resolved, acceptWith]

theorem memoryWordAt_zero_iff (words : Words) (slot : UInt64) :
    memoryWordAt slot words.memory2 words.memory3 = 0 ↔ (decode words).memoryAt slot.toNat = none := by
  rw [← memoryWordAt_spec]
  unfold decodeMemory
  by_cases zero : memoryWordAt slot words.memory2 words.memory3 = 0 <;> simp [zero]

theorem decide_allocate (words : Words) (slot a1 a2 : UInt64) :
    decideW words.subjectNext words.objectNext words.capabilityNext words.controlNext
        words.authorityNext words.authority words.child0 words.child1 words.child2 words.child3
        words.memory2 words.memory3 words.frames 0x7301 slot a1 a2 =
      (allocateStep (decode words) slot.toNat).status := by
  unfold decideW allocateStep
  simp only [show (0x7301 : UInt64) ≠ 0x7001 from by decide,
    show (0x7301 : UInt64) ≠ 0x7101 from by decide, show (0x7301 : UInt64) ≠ 0x7201 from by decide,
    beq_iff_eq, beq_self_eq_true, ↓reduceIte, Bool.false_eq_true]
  have reserved : CapabilityHandle.slotReserved = 0xffff := slotReserved_value
  simp only [Bool.or_eq_true, decide_eq_true_eq, UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt,
    reserved, parentSlots, memoryBase, show (0xffff : UInt64).toNat = 0xffff from rfl,
    show (4 : UInt64).toNat = 4 from rfl, show (2 : UInt64).toNat = 2 from rfl]
  by_cases range : 0xffff ≤ slot.toNat ∨ 4 ≤ slot.toNat
  · simp [range, rejectWith, memoryCode]
  simp only [range, ↓reduceIte]
  rw [capabilityExhaustedW_spec]
  by_cases capabilities : capabilityExhausted words.capabilityNext.toNat = true
  · simp [capabilities, decode, rejectWith, memoryCode]
  simp only [Bool.not_eq_true] at capabilities
  simp only [capabilities, Bool.false_eq_true, ↓reduceIte, decode]
  have occupiedIff := memoryWordAt_zero_iff words slot
  by_cases low : slot.toNat < 2
  · simp [low, rejectWith, memoryCode]
  simp only [low, false_or]
  by_cases empty : memoryWordAt slot words.memory2 words.memory3 = 0
  · have none := occupiedIff.1 empty
    have noneDecoded : State.memoryAt (decode words) slot.toNat = Option.none := none
    simp only [bne_iff_ne, ne_eq, empty, not_true_eq_false, decide_false, Bool.false_eq_true,
      ↓reduceIte]
    simp only [decode] at noneDecoded
    simp only [noneDecoded, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
    rw [identityExhaustedW_spec]
    by_cases objects : identityExhausted words.objectNext.toNat = true
    · simp [objects, rejectWith, memoryCode]
    simp only [Bool.not_eq_true] at objects
    simp only [objects, Bool.false_eq_true, ↓reduceIte]
    have available := availableW_toNat words
    by_cases zero : (decode words).available = 0
    · have zeroWord : availableW words.frames words.memory2 words.memory3 = 0 :=
        UInt64.toNat_inj.1 (by rw [available, zero]; rfl)
      simp only [decode] at zero
      simp [zeroWord, zero, rejectWith, memoryCode]
    · have nonzeroWord : availableW words.frames words.memory2 words.memory3 ≠ 0 :=
        fun eq => zero (by rw [← available, eq]; rfl)
      simp only [decode] at zero
      simp [nonzeroWord, zero, acceptWith]
  · have some : (State.memoryAt (decode words) slot.toNat).isSome = true := by
      cases held : (decode words).memoryAt slot.toNat with
      | none => exact absurd (occupiedIff.2 held) empty
      | some _ => rfl
    simp only [decode] at some
    simp [empty, some, rejectWith, memoryCode]

theorem decide_release (words : Words) (slot a1 a2 : UInt64) :
    decideW words.subjectNext words.objectNext words.capabilityNext words.controlNext
        words.authorityNext words.authority words.child0 words.child1 words.child2 words.child3
        words.memory2 words.memory3 words.frames 0x7401 slot a1 a2 =
      (releaseStep (decode words) slot.toNat).status := by
  unfold decideW releaseStep
  simp only [show (0x7401 : UInt64) ≠ 0x7001 from by decide,
    show (0x7401 : UInt64) ≠ 0x7101 from by decide, show (0x7401 : UInt64) ≠ 0x7201 from by decide,
    show (0x7401 : UInt64) ≠ 0x7301 from by decide,
    beq_iff_eq, beq_self_eq_true, ↓reduceIte, Bool.false_eq_true]
  simp only [UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt, parentSlots, memoryBase,
    show (4 : UInt64).toNat = 4 from rfl, show (2 : UInt64).toNat = 2 from rfl]
  by_cases range : 4 ≤ slot.toNat
  · simp [range, rejectWith, memoryCode]
  simp only [range, decide_false, Bool.false_eq_true, ↓reduceIte]
  by_cases low : slot.toNat < 2
  · simp [low, rejectWith, memoryCode]
  simp only [low, decide_false, Bool.false_eq_true, ↓reduceIte]
  have occupiedIff := memoryWordAt_zero_iff words slot
  by_cases empty : memoryWordAt slot words.memory2 words.memory3 = 0
  · have none := occupiedIff.1 empty
    simp [empty, none, rejectWith, memoryCode]
  · cases held : (decode words).memoryAt slot.toNat with
    | none => exact absurd (occupiedIff.2 held) empty
    | some identity => simp [empty, acceptWith]

/-- The reply of a decided command: its status, or `uncoveredWord`. -/
def statusOf : Option Step → UInt64
  | none => uncoveredWord
  | some result => result.status

theorem decide_grantAuthority (words : Words) (subject budget a2 : UInt64) :
    decideW words.subjectNext words.objectNext words.capabilityNext words.controlNext
        words.authorityNext words.authority words.child0 words.child1 words.child2 words.child3
        words.memory2 words.memory3 words.frames 0x7501 subject budget a2 =
      statusOf (grantAuthorityStep (decode words) subject.toNat budget.toNat) := by
  unfold decideW grantAuthorityStep
  simp only [show (0x7501 : UInt64) ≠ 0x7001 from by decide,
    show (0x7501 : UInt64) ≠ 0x7101 from by decide, show (0x7501 : UInt64) ≠ 0x7201 from by decide,
    show (0x7501 : UInt64) ≠ 0x7301 from by decide, show (0x7501 : UInt64) ≠ 0x7401 from by decide,
    beq_iff_eq, beq_self_eq_true, ↓reduceIte, Bool.false_eq_true]
  have count := childCountW_toNat words
  have authorityNext : (decode words).authorityNext = words.authorityNext.toNat := rfl
  by_cases isParent : subject = 2
  · subst isParent
    simp only [↓reduceIte, show (2 : UInt64).toNat = parent from rfl]
    simp only [Bool.and_eq_true, decide_eq_true_eq, UInt64.le_iff_toNat_le, count,
      show (64 : UInt64).toNat = childSlots from rfl]
    by_cases allowed : budget.toNat ≤ childSlots ∧ (decode words).childCount ≤ budget.toNat
    · simp only [allowed, and_self, ↓reduceIte]
      simp only [Bool.or_eq_true, decide_eq_true_eq, UInt64.lt_iff_toNat_lt, beq_iff_eq,
        show (4 : UInt64).toNat = childCapacity from rfl, authorityNext, wordBound]
      by_cases outside : childCapacity < budget.toNat ∨
          words.authorityNext = maxWord
      · have outsideNat : childCapacity < budget.toNat ∨
            18446744073709551615 ≤ words.authorityNext.toNat := by
          rcases outside with big | full
          · exact Or.inl big
          · right; rw [full]; decide
        simp [outside, outsideNat, statusOf]
      · have insideNat : ¬(childCapacity < budget.toNat ∨
            18446744073709551615 ≤ words.authorityNext.toNat) := by
          simp only [not_or] at outside ⊢
          refine ⟨outside.1, ?_⟩
          have : words.authorityNext.toNat ≠ 2 ^ 64 - 1 := by
            intro eq
            apply outside.2
            apply UInt64.toNat_inj.1
            rw [eq]; rfl
          have := words.authorityNext.toNat_lt
          omega
        simp [outside, insideNat, statusOf, acceptWith]
    · simp [allowed, statusOf, authorityRejected]
  · have notParent : subject.toNat ≠ parent := by
      intro eq; apply isParent; apply UInt64.toNat_inj.1; rw [eq]; rfl
    simp only [isParent, ↓reduceIte, notParent]
    by_cases isBystander : subject = 1
    · subst isBystander
      simp only [↓reduceIte, show (1 : UInt64).toNat = bystander from rfl,
        UInt64.le_iff_toNat_le, show (64 : UInt64).toNat = childSlots from rfl]
      by_cases small : budget.toNat ≤ childSlots
      · simp [small, statusOf]
      · simp [small, statusOf, authorityRejected]
    · have notBystander : subject.toNat ≠ bystander := by
        intro eq; apply isBystander; apply UInt64.toNat_inj.1; rw [eq]; rfl
      simp [isBystander, notBystander, statusOf, authorityRejected]

theorem decide_revoke (words : Words) (subject a1 a2 : UInt64) :
    decideW words.subjectNext words.objectNext words.capabilityNext words.controlNext
        words.authorityNext words.authority words.child0 words.child1 words.child2 words.child3
        words.memory2 words.memory3 words.frames 0x7601 subject a1 a2 =
      (revokeAuthorityStep (decode words) subject.toNat).status := by
  unfold decideW revokeAuthorityStep
  simp only [show (0x7601 : UInt64) ≠ 0x7001 from by decide,
    show (0x7601 : UInt64) ≠ 0x7101 from by decide, show (0x7601 : UInt64) ≠ 0x7201 from by decide,
    show (0x7601 : UInt64) ≠ 0x7301 from by decide, show (0x7601 : UInt64) ≠ 0x7401 from by decide,
    show (0x7601 : UInt64) ≠ 0x7501 from by decide,
    beq_iff_eq, ↓reduceIte, Bool.false_eq_true]
  split <;> rfl

/-- **The status of every decoded command.** -/
theorem decideW_spec (words : Words) (command : CommandWords) (operation : Command)
    (decoded : decodeCommand command = .ok operation) :
    decideW words.subjectNext words.objectNext words.capabilityNext words.controlNext
        words.authorityNext words.authority words.child0 words.child1 words.child2 words.child3
        words.memory2 words.memory3 words.frames command.tag command.arg0 command.arg1
        command.arg2 =
      statusOf (step (decode words) operation) := by
  rcases decodeCommand_ok command operation decoded with
    ⟨tag, rights, decodedRights, rfl⟩ | ⟨tag, rfl⟩ | ⟨tag, rfl⟩ | ⟨tag, rfl⟩ | ⟨tag, rfl⟩ |
      ⟨tag, rfl⟩ | ⟨tag, rfl⟩ <;> rw [tag]
  · have encoded := SpawnOracle.encodeRights_decodeRights _ _ decodedRights
    have := decide_spawn words (requestOf command rights)
      (by simp only [requestOf]; rw [SpawnOracle.decodeRights_encodeRights])
    simp only [requestOf] at this
    rw [encoded] at this
    simp only [step, statusOf, requestOf]
    exact this
  · simp only [step, statusOf]; exact decide_grant words _ _ _
  · simp only [step, statusOf]; exact decide_terminate words _ _ _
  · simp only [step, statusOf]; exact decide_allocate words _ _ _
  · simp only [step, statusOf]; exact decide_release words _ _ _
  · simp only [step]; exact decide_grantAuthority words _ _ _
  · simp only [step, statusOf]; exact decide_revoke words _ _ _

/-! ## The reply word -/

theorem errorWord_ne_zero (reason : DecodeError) : CompositeDispatcher.errorWord reason ≠ 0 := by
  cases reason <;> decide

theorem canonical_words (words : Words) :
    canonical words.authorityNext words.child0 words.child1 words.child2 words.child3
      words.frames = Canonical words := rfl

/-- **The reply word is the specification's.** -/
theorem codeReply_spec (words : Words) (command : CommandWords) :
    codeReply words command = (specStep words command).2.1 := by
  unfold codeReply stepReply specStep
  rw [canonical_words]
  by_cases canonicalWords : Canonical words = true
  · simp only [canonicalWords, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rw [commandErrorW_spec]
    cases decoded : decodeCommand command with
    | error reason =>
        simp [errorWord_ne_zero reason]
    | ok operation =>
        simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
        rw [decideW_spec words command operation decoded]
        cases step (decode words) operation <;> rfl
  · simp only [Bool.not_eq_true] at canonicalWords
    simp [canonicalWords]

/-- Exactly the accepted commands have reply `0x01`. -/
theorem codeReply_accepted (words : Words) (command : CommandWords)
    (accepted : codeReply words command = 0x01) :
    Canonical words = true ∧ ∃ operation result, decodeCommand command = .ok operation ∧
      step (decode words) operation = some result ∧ result.status = 0x01 := by
  rw [codeReply_spec] at accepted
  unfold specStep at accepted
  by_cases canonicalWords : Canonical words = true
  · refine ⟨canonicalWords, ?_⟩
    simp only [canonicalWords, Bool.true_eq_false, ↓reduceIte] at accepted
    cases decoded : decodeCommand command with
    | error reason =>
        rw [decoded] at accepted
        cases reason <;> simp [CompositeDispatcher.errorWord] at accepted
    | ok operation =>
        rw [decoded] at accepted
        simp only at accepted
        cases result : step (decode words) operation with
        | none =>
            rw [result] at accepted
            simp [uncoveredWord] at accepted
        | some found =>
            rw [result] at accepted
            exact ⟨operation, found, rfl, result, accepted⟩
  · simp only [Bool.not_eq_true] at canonicalWords
    simp [canonicalWords, stateErrorWord] at accepted

end LeanOS.SpawnAllocatorWords
