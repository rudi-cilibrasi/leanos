import LeanOS.SpawnAllocatorWords

/-!
# The thirteen words, read as the allocator record

Component lemmas for `LeanOS.SpawnAllocatorWordsRefinement`: on canonical
words, each fixed-width helper of `LeanOS.SpawnAllocatorWords` computes the
corresponding reading of the decoded record (`decode`).
-/
namespace LeanOS.SpawnAllocatorWords

open LeanOS
open LeanOS.FailStop
open LeanOS.SpawnAllocator
open LeanOS.CompositeDispatcher (CommandWords DecodeError)

set_option linter.unusedSimpArgs false

/-! ## Arithmetic -/

theorem toNat_shr16 (word : UInt64) : (word >>> 16).toNat = word.toNat / 65536 := by
  rw [UInt64.toNat_shiftRight]
  simp [Nat.shiftRight_eq_div_pow]

theorem toNat_shr32 (word : UInt64) : (word >>> 32).toNat = word.toNat / 2 ^ 32 := by
  rw [UInt64.toNat_shiftRight]
  simp [Nat.shiftRight_eq_div_pow]

theorem toNat_and16 (word : UInt64) : (word &&& 0xffff).toNat = word.toNat % 65536 := by
  rw [UInt64.toNat_and]
  have := Nat.and_two_pow_sub_one_eq_mod word.toNat 16
  simpa using this

theorem toNat_shl16 (word : UInt64) (small : word.toNat < 2 ^ 48) :
    (word <<< 16).toNat = word.toNat * 65536 := by
  rw [UInt64.toNat_shiftLeft]
  simp only [Nat.shiftLeft_eq]
  have : word.toNat * 2 ^ 16 < 2 ^ 64 := by omega
  simp
  omega

theorem beq_toNat (left right : UInt64) : (left == right) = decide (left.toNat = right.toNat) := by
  by_cases same : left = right
  · subst same; simp
  · have : left.toNat ≠ right.toNat := fun eq => same (UInt64.toNat_inj.1 eq)
    simp [same, this]

theorem eq_toNat (left right : UInt64) : (left = right) ↔ left.toNat = right.toNat :=
  UInt64.toNat_inj.symm

theorem toNat_add_of_lt (left right : UInt64) (fits : left.toNat + right.toNat < 2 ^ 64) :
    (left + right).toNat = left.toNat + right.toNat := by
  rw [UInt64.toNat_add]; omega

theorem toNat_ofNat_lt {value : Nat} (small : value < 2 ^ 64) : (UInt64.ofNat value).toNat = value := by
  rw [UInt64.toNat_ofNat']; omega

theorem ofNat_toNat (word : UInt64) : UInt64.ofNat word.toNat = word := UInt64.ofNat_toNat

/-! ## Canonical words -/

/-- The facts canonical words carry. -/
structure CanonicalFacts (words : Words) : Prop where
  authorityNext : words.authorityNext ≠ 0
  child0 : childCanonical words.child0 = true
  child1 : childCanonical words.child1 = true
  child2 : childCanonical words.child2 = true
  child3 : childCanonical words.child3 = true
  framesHigh : words.frames.toNat < 2 ^ 32
  budget : words.frames.toNat % 65536 ≤ 4
  frames : words.frames.toNat / 65536 + words.child0.toNat % 65536 + words.child1.toNat % 65536 +
    words.child2.toNat % 65536 + words.child3.toNat % 65536 < 65536

theorem canonicalFacts (words : Words) (canonicalWords : Canonical words = true) :
    CanonicalFacts words := by
  simp only [Canonical, canonical, Bool.and_eq_true] at canonicalWords
  obtain ⟨⟨⟨⟨⟨⟨⟨w4, c0⟩, c1⟩, c2⟩, c3⟩, high⟩, budget⟩, frames⟩ := canonicalWords
  simp only [bne_iff_ne, ne_eq] at w4
  simp only [beq_iff_eq] at high
  simp only [decide_eq_true_eq] at budget frames
  refine ⟨w4, c0, c1, c2, c3, ?_, ?_, ?_⟩
  · have := congrArg UInt64.toNat high
    rw [toNat_shr32] at this
    simp at this
    exact this
  · rw [UInt64.le_iff_toNat_le, toNat_and16] at budget
    simpa using budget
  · rw [UInt64.lt_iff_toNat_lt] at frames
    simp only [chargeOf] at frames
    have shr := toNat_shr16 words.frames
    have a0 := toNat_and16 words.child0
    have a1 := toNat_and16 words.child1
    have a2 := toNat_and16 words.child2
    have a3 := toNat_and16 words.child3
    have b0 := Nat.mod_lt words.child0.toNat (by decide : 0 < 65536)
    have b1 := Nat.mod_lt words.child1.toNat (by decide : 0 < 65536)
    have b2 := Nat.mod_lt words.child2.toNat (by decide : 0 < 65536)
    have b3 := Nat.mod_lt words.child3.toNat (by decide : 0 < 65536)
    have bf : words.frames.toNat / 65536 < 2 ^ 48 := by
      have := words.frames.toNat_lt; omega
    have s1 := toNat_add_of_lt (words.frames >>> 16) (chargeOf words.child0)
      (by rw [shr]; simp only [chargeOf]; rw [a0]; omega)
    have s2 := toNat_add_of_lt (words.frames >>> 16 + chargeOf words.child0) (chargeOf words.child1)
      (by rw [s1, shr]; simp only [chargeOf]; rw [a0, a1]; omega)
    have s3 := toNat_add_of_lt (words.frames >>> 16 + chargeOf words.child0 + chargeOf words.child1)
      (chargeOf words.child2) (by rw [s2, s1, shr]; simp only [chargeOf]; rw [a0, a1, a2]; omega)
    have s4 := toNat_add_of_lt
      (words.frames >>> 16 + chargeOf words.child0 + chargeOf words.child1 + chargeOf words.child2)
      (chargeOf words.child3)
      (by rw [s3, s2, s1, shr]; simp only [chargeOf]; rw [a0, a1, a2, a3]; omega)
    simp only [chargeOf] at s1 s2 s3 s4
    rw [s4, s3, s2, s1, shr, a0, a1, a2, a3] at frames
    simpa using frames

/-- A canonical child word: zero, or a generation in `1 .. 2^48 - 2`. -/
theorem childCanonical_facts {word : UInt64} (canonicalWord : childCanonical word = true) :
    word = 0 ∨ (0 < word.toNat / 65536 ∧ word.toNat / 65536 < CapabilityHandle.generationReserved) := by
  simp only [childCanonical, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, bne_iff_ne, ne_eq,
    decide_eq_true_eq] at canonicalWord
  rcases canonicalWord with zero | ⟨nonzero, small⟩
  · exact Or.inl zero
  · right
    rw [UInt64.lt_iff_toNat_lt, toNat_shr16] at small
    have : (word >>> 16).toNat ≠ 0 := fun eq => nonzero (UInt64.toNat_inj.1 (by simpa using eq))
    rw [toNat_shr16] at this
    unfold CapabilityHandle.generationReserved CapabilityHandle.generationRadix
    simp [generationLimit] at small
    omega

/-! ## Reading the decoded record -/

theorem decode_childAt (words : Words) (slot : Nat) :
    (decode words).childAt slot =
      if slot = 0 then decodeChild words.child0 else if slot = 1 then decodeChild words.child1
      else if slot = 2 then decodeChild words.child2 else if slot = 3 then decodeChild words.child3
      else none := by
  unfold State.childAt decode
  rcases slot with _ | _ | _ | _ | slot <;> simp

theorem decode_memoryAt (words : Words) (slot : Nat) :
    (decode words).memoryAt slot =
      if slot = 2 then decodeMemory words.memory2 else if slot = 3 then decodeMemory words.memory3
      else none := by
  unfold State.memoryAt decode memoryBase
  rcases slot with _ | _ | _ | _ | slot <;> simp

theorem occupied_toNat (word : UInt64) :
    (occupied word).toNat = if (decodeChild word).isSome then 1 else 0 := by
  unfold occupied decodeChild
  by_cases zero : word = 0 <;> simp [zero]

theorem occupied_memory_toNat (word : UInt64) :
    (occupied word).toNat = if (decodeMemory word).isSome then 1 else 0 := by
  unfold occupied decodeMemory
  by_cases zero : word = 0 <;> simp [zero]

theorem occupied_le (word : UInt64) : (occupied word).toNat ≤ 1 := by
  unfold occupied; split <;> simp

theorem childCountW_toNat (words : Words) :
    (childCountW words.child0 words.child1 words.child2 words.child3).toNat =
      (decode words).childCount := by
  have o0 := occupied_le words.child0
  have o1 := occupied_le words.child1
  have o2 := occupied_le words.child2
  have o3 := occupied_le words.child3
  unfold childCountW
  have s1 := toNat_add_of_lt (occupied words.child0) (occupied words.child1) (by omega)
  have s2 := toNat_add_of_lt (occupied words.child0 + occupied words.child1)
    (occupied words.child2) (by rw [s1]; omega)
  have s3 := toNat_add_of_lt (occupied words.child0 + occupied words.child1 + occupied words.child2)
    (occupied words.child3) (by rw [s2, s1]; omega)
  rw [s3, s2, s1]
  simp only [occupied_toNat, State.childCount, decode, List.countP_cons, List.countP_nil]
  split <;> split <;> split <;> split <;> simp_all

theorem memoryUsedW_toNat (words : Words) :
    (occupied words.memory2 + occupied words.memory3).toNat = (decode words).memoryUsed := by
  have o2 := occupied_le words.memory2
  have o3 := occupied_le words.memory3
  rw [toNat_add_of_lt _ _ (by omega)]
  simp only [occupied_memory_toNat, State.memoryUsed, decode, List.countP_cons, List.countP_nil]
  split <;> split <;> simp_all

theorem availableW_toNat (words : Words) :
    (availableW words.frames words.memory2 words.memory3).toNat = (decode words).available := by
  have used := memoryUsedW_toNat words
  unfold availableW State.available parentFramesW
  have frames : (decode words).parentFrames = (words.frames >>> 16).toNat := by
    rw [toNat_shr16]; rfl
  split
  · next le =>
    rw [UInt64.toNat_sub_of_le _ _ le, used, frames]
  · next notLe =>
    rw [UInt64.le_iff_toNat_le, used] at notLe
    rw [frames, show (0 : UInt64).toNat = 0 from rfl]
    omega

theorem freeSlotW_spec (words : Words) :
    (decode words).freeSlot =
      if freeSlotW words.child0 words.child1 words.child2 words.child3 = 4 then none
      else some (freeSlotW words.child0 words.child1 words.child2 words.child3).toNat := by
  unfold State.freeSlot freeSlotW decode decodeChild
  by_cases z0 : words.child0 = 0
  · simp [z0, List.findIdx?_cons]
  by_cases z1 : words.child1 = 0
  · simp [z0, z1, List.findIdx?_cons]
  by_cases z2 : words.child2 = 0
  · simp [z0, z1, z2, List.findIdx?_cons]
  by_cases z3 : words.child3 = 0
  · simp [z0, z1, z2, z3, List.findIdx?_cons]
  · simp [z0, z1, z2, z3, List.findIdx?_cons]

theorem childWordAt_spec (words : Words) (slot : UInt64) :
    decodeChild (childWordAt slot words.child0 words.child1 words.child2 words.child3) =
      (decode words).childAt slot.toNat := by
  rw [decode_childAt]
  unfold childWordAt
  by_cases s0 : slot = 0
  · subst s0; simp
  by_cases s1 : slot = 1
  · subst s1; simp
  by_cases s2 : slot = 2
  · subst s2; simp
  by_cases s3 : slot = 3
  · subst s3; simp
  have n0 : slot.toNat ≠ 0 := fun eq => s0 (UInt64.toNat_inj.1 (by simpa using eq))
  have n1 : slot.toNat ≠ 1 := fun eq => s1 (UInt64.toNat_inj.1 (by simpa using eq))
  have n2 : slot.toNat ≠ 2 := fun eq => s2 (UInt64.toNat_inj.1 (by simpa using eq))
  have n3 : slot.toNat ≠ 3 := fun eq => s3 (UInt64.toNat_inj.1 (by simpa using eq))
  simp [s0, s1, s2, s3, n0, n1, n2, n3, decodeChild]

theorem memoryWordAt_spec (words : Words) (slot : UInt64) :
    decodeMemory (memoryWordAt slot words.memory2 words.memory3) =
      (decode words).memoryAt slot.toNat := by
  rw [decode_memoryAt]
  unfold memoryWordAt
  by_cases s2 : slot = 2
  · subst s2; simp
  by_cases s3 : slot = 3
  · subst s3; simp
  have n2 : slot.toNat ≠ 2 := fun eq => s2 (UInt64.toNat_inj.1 (by simpa using eq))
  have n3 : slot.toNat ≠ 3 := fun eq => s3 (UInt64.toNat_inj.1 (by simpa using eq))
  simp [s2, s3, n2, n3, decodeMemory]

/-! ## Counters -/

theorem toNat_ne_of_ne {word : UInt64} {value : Nat} (small : value < 2 ^ 64)
    (different : word ≠ UInt64.ofNat value) : word.toNat ≠ value := by
  intro eq
  apply different
  apply UInt64.toNat_inj.1
  rw [eq, toNat_ofNat_lt small]

theorem identityExhaustedW_spec (next : UInt64) :
    identityExhaustedW next = identityExhausted next.toNat := by
  have bound := next.toNat_lt
  by_cases zero : next = 0
  · subst zero; rfl
  by_cases full : next = 0xffffffffffffffff
  · subst full; rfl
  have n0 : next.toNat ≠ 0 := toNat_ne_of_ne (by decide) zero
  have nf : next.toNat ≠ 0xffffffffffffffff := toNat_ne_of_ne (by decide) full
  have lhs : identityExhaustedW next = false := by
    simp [identityExhaustedW, zero, full, maxWord]
  have rhs : identityExhausted next.toNat = false := by
    simp only [identityExhausted, Bool.or_eq_false_iff, decide_eq_false_iff_not]
    unfold LifetimeIssuer.identityReserved LifetimeIssuer.identityRadix
    omega
  rw [lhs, rhs]

theorem capabilityExhaustedW_spec (next : UInt64) :
    capabilityExhaustedW next = capabilityExhausted next.toNat := by
  by_cases zero : next = 0
  · subst zero; rfl
  have n0 : next.toNat ≠ 0 := toNat_ne_of_ne (by decide) zero
  have reserved : CapabilityHandle.generationReserved = generationLimit.toNat := by
    unfold CapabilityHandle.generationReserved CapabilityHandle.generationRadix generationLimit
    rfl
  have zeroBeq : (next == 0) = false := by simpa using zero
  simp only [capabilityExhaustedW, capabilityExhausted, reserved, zeroBeq, n0, beq_iff_eq,
    decide_false, Bool.false_or, decide_eq_decide, UInt64.le_iff_toNat_le]

theorem controlAvailableW_spec (next : UInt64) :
    controlAvailableW next = controlAvailable next.toNat := by
  by_cases zero : next = 0
  · subst zero; rfl
  have n0 : next.toNat ≠ 0 := toNat_ne_of_ne (by decide) zero
  have reserved : CapabilityHandle.generationReserved = generationLimit.toNat := by
    unfold CapabilityHandle.generationReserved CapabilityHandle.generationRadix generationLimit
    rfl
  have positive : 0 < next.toNat := Nat.pos_of_ne_zero n0
  have zeroBne : (next != 0) = true := by simpa using zero
  simp only [controlAvailableW, controlAvailable, reserved, zeroBne, positive, bne_iff_ne, ne_eq,
    not_false_eq_true, decide_true, Bool.true_and, decide_eq_decide, UInt64.lt_iff_toNat_lt]

/-! ## Handles -/

theorem slot_toNat (word : UInt64) : (word &&& 0xffff).toNat = word.toNat % CapabilityHandle.slotRadix := by
  rw [toNat_and16]; rfl

theorem identity_toNat (word : UInt64) :
    (word >>> 16).toNat = word.toNat / CapabilityHandle.slotRadix := by
  rw [toNat_shr16]; rfl

theorem slotReserved_value : CapabilityHandle.slotReserved = 65535 := by
  unfold CapabilityHandle.slotReserved CapabilityHandle.slotRadix; rfl

theorem generationLimit_toNat : generationLimit.toNat = CapabilityHandle.generationReserved := by
  unfold generationLimit CapabilityHandle.generationReserved CapabilityHandle.generationRadix; rfl

theorem decodeMemory_some_iff (word : UInt64) (identity : Nat) :
    decodeMemory word = some identity ↔ word ≠ 0 ∧ word.toNat = identity := by
  unfold decodeMemory
  by_cases zero : word = 0 <;> simp [zero]

theorem resolveEndpointW_spec (words : Words) (word : UInt64) :
    resolveEndpointW words.memory2 words.memory3 word =
      match (decode words).resolveEndpoint word with
      | none => 0
      | some denial => SpawnOracle.handleErrorCode denial := by
  have memory := memoryWordAt_spec words (word &&& 0xffff)
  rw [slot_toNat] at memory
  unfold resolveEndpointW State.resolveEndpoint CapabilityHandle.decode
  simp only [beq_toNat, slot_toNat, identity_toNat, generationLimit_toNat,
    UInt64.le_iff_toNat_le]
  generalize hs : word.toNat % CapabilityHandle.slotRadix = slot at memory ⊢
  generalize hi : word.toNat / CapabilityHandle.slotRadix = identity
  rw [slotReserved_value]
  by_cases reservedSlot : slot = 65535
  · subst reservedSlot; simp [SpawnOracle.handleErrorCode]
  simp only [reservedSlot, show ((0xffff : UInt64).toNat) = 65535 from rfl, decide_false,
    Bool.false_eq_true, ↓reduceIte]
  by_cases reservedGeneration : identity = 0 ∨ identity = CapabilityHandle.generationReserved
  · rcases reservedGeneration with zero | full
    · subst zero; simp [SpawnOracle.handleErrorCode]
    · subst full; simp [SpawnOracle.handleErrorCode]
  simp only [not_or] at reservedGeneration
  simp only [reservedGeneration, show ((0 : UInt64).toNat) = 0 from rfl, decide_false,
    Bool.or_false, Bool.false_eq_true, ↓reduceIte, or_self]
  by_cases out : 4 ≤ slot
  · simp [out, parentSlots, SpawnOracle.handleErrorCode]
  have outNat : ¬parentSlots ≤ slot := by unfold parentSlots; omega
  simp only [show ((4 : UInt64).toNat) = 4 from rfl, out, decide_false, Bool.false_eq_true,
    ↓reduceIte, outNat]
  by_cases s0 : slot = 0
  · subst s0
    by_cases same : identity = 3 <;>
      simp [same, endpointIdentity, SpawnOracle.handleErrorCode]
  simp only [show ((0 : UInt64).toNat) = 0 from rfl, s0, decide_false, Bool.false_eq_true,
    ↓reduceIte]
  by_cases s1 : slot = 1
  · subst s1
    by_cases same : identity = 4 <;>
      simp [same, spaceIdentity, SpawnOracle.handleErrorCode]
  simp only [show ((1 : UInt64).toNat) = 1 from rfl, s1, decide_false, Bool.false_eq_true,
    ↓reduceIte]
  cases held : (decode words).memoryAt slot with
  | none =>
      rw [held] at memory
      have zero : memoryWordAt (word &&& 0xffff) words.memory2 words.memory3 = 0 := by
        unfold decodeMemory at memory
        split at memory
        · assumption
        · cases memory
      simp [zero, SpawnOracle.handleErrorCode]
  | some value =>
      rw [held] at memory
      obtain ⟨nonzero, eq⟩ := (decodeMemory_some_iff _ _).1 memory
      have nonzeroNat : (memoryWordAt (word &&& 0xffff) words.memory2 words.memory3).toNat ≠ 0 :=
        fun z => nonzero (UInt64.toNat_inj.1 (by simpa using z))
      rw [eq] at nonzeroNat
      simp only [eq, show ((0 : UInt64).toNat) = 0 from rfl, nonzeroNat, decide_false,
        Bool.false_eq_true, ↓reduceIte]
      by_cases same : identity = value <;> simp [same, SpawnOracle.handleErrorCode]

theorem decodeChild_some_iff (word : UInt64) (entry : ChildRecord) :
    decodeChild word = some entry ↔
      word ≠ 0 ∧ entry.generation = word.toNat / 65536 ∧ entry.charge = word.toNat % 65536 := by
  unfold decodeChild
  by_cases zero : word = 0
  · simp [zero]
  · simp only [zero, ↓reduceIte, Option.some.injEq, ne_eq, not_false_eq_true, true_and]
    constructor
    · rintro rfl; exact ⟨rfl, rfl⟩
    · rintro ⟨g, c⟩; cases entry; simp_all

theorem decodeChild_none_iff (word : UInt64) : decodeChild word = none ↔ word = 0 := by
  unfold decodeChild
  by_cases zero : word = 0 <;> simp [zero]

theorem resolveControlW_spec (words : Words) (word : UInt64) :
    resolveControlW words.child0 words.child1 words.child2 words.child3 word =
      match (decode words).resolveControl word with
      | .ok _ => 0
      | .error denial => SpawnAccountingOracle.controlDenialCode denial := by
  have child := childWordAt_spec words (word &&& 0xffff)
  rw [slot_toNat] at child
  unfold resolveControlW State.resolveControl CapabilityHandle.decode generationOf
  simp only [beq_toNat, slot_toNat, identity_toNat, generationLimit_toNat]
  generalize hs : word.toNat % CapabilityHandle.slotRadix = slot at child ⊢
  generalize hi : word.toNat / CapabilityHandle.slotRadix = identity
  generalize hw : childWordAt (word &&& 0xffff) words.child0 words.child1 words.child2
    words.child3 = childWord at child ⊢
  rw [slotReserved_value]
  by_cases reservedSlot : slot = 65535
  · subst reservedSlot; simp [SpawnAccountingOracle.controlDenialCode]
  simp only [reservedSlot, show ((0xffff : UInt64).toNat) = 65535 from rfl, decide_false,
    Bool.false_eq_true, ↓reduceIte]
  by_cases reservedGeneration : identity = 0 ∨ identity = CapabilityHandle.generationReserved
  · rcases reservedGeneration with zero | full
    · subst zero; simp [SpawnAccountingOracle.controlDenialCode]
    · subst full; simp [SpawnAccountingOracle.controlDenialCode]
  simp only [not_or] at reservedGeneration
  simp only [reservedGeneration, show ((0 : UInt64).toNat) = 0 from rfl, decide_false,
    Bool.or_false, Bool.false_eq_true, ↓reduceIte, or_self]
  cases held : (decode words).childAt slot with
  | none =>
      rw [held, decodeChild_none_iff] at child
      subst child
      simp [SpawnAccountingOracle.controlDenialCode]
  | some entry =>
      rw [held] at child
      obtain ⟨nonzero, generation, _⟩ := (decodeChild_some_iff _ _).1 child
      have nonzeroNat : childWord.toNat ≠ 0 :=
        fun z => nonzero (UInt64.toNat_inj.1 (by simpa using z))
      simp only [show ((0 : UInt64).toNat) = 0 from rfl, nonzeroNat, decide_false,
        Bool.false_eq_true, ↓reduceIte, toNat_shr16, ← generation]
      have slotRadix : CapabilityHandle.slotRadix = 65536 := rfl
      rw [slotRadix, ← generation]
      by_cases same : entry.generation = identity <;>
        simp [same, SpawnAccountingOracle.controlDenialCode]

/-- What an accepted control word names, in words. -/
theorem resolveControl_words (words : Words) (word : UInt64) (slot : Nat) (entry : ChildRecord)
    (resolved : (decode words).resolveControl word = .ok (slot, entry)) :
    slot = (word &&& 0xffff).toNat ∧
      decodeChild (childWordAt (word &&& 0xffff) words.child0 words.child1 words.child2
        words.child3) = some entry := by
  obtain ⟨decoded, held⟩ := resolveControl_ok resolved
  unfold CapabilityHandle.decode at decoded
  dsimp only at decoded
  split at decoded
  · cases decoded
  split at decoded
  · cases decoded
  simp only [Except.ok.injEq, CapabilityHandle.Handle.mk.injEq] at decoded
  have slotEq : slot = (word &&& 0xffff).toNat := by rw [slot_toNat]; exact decoded.1.symm
  refine ⟨slotEq, ?_⟩
  rw [childWordAt_spec, ← slotEq]
  exact held

/-! ## Rights and command words -/

def rightsAgree (index : Nat) : Bool :=
  match SpawnOracle.decodeRights (UInt64.ofNat index) with
  | .ok rights => rightsValidW (UInt64.ofNat index) == Capability.rightsValid .endpoint rights
  | .error _ => true

theorem rightsAgree_all : (List.range 64).all rightsAgree = true := by decide

theorem rightsValidW_spec (word : UInt64) (rights : Capability.Rights)
    (decoded : SpawnOracle.decodeRights word = .ok rights) :
    rightsValidW word = Capability.rightsValid .endpoint rights := by
  have small : word.toNat < 64 := by
    unfold SpawnOracle.decodeRights at decoded
    split at decoded
    · cases decoded
    · next bound =>
      rw [UInt64.le_iff_toNat_le] at bound
      simp at bound
      omega
  have := List.all_eq_true.1 rightsAgree_all word.toNat (List.mem_range.2 small)
  simp only [rightsAgree, UInt64.ofNat_toNat, decoded, beq_iff_eq] at this
  exact this

theorem commandErrorW_spec (command : CommandWords) :
    commandErrorW command.tag command.arg0 command.arg1 command.arg2 command.arg3 =
      match decodeCommand command with
      | .ok _ => 0
      | .error reason => CompositeDispatcher.errorWord reason := by
  obtain ⟨tag, a0, a1, a2, a3⟩ := command
  unfold commandErrorW decodeCommand SpawnAccountingOracle.decodeChild SpawnOracle.decodeSpawn
    SpawnOracle.decodeRights
  simp only [spawnTag, grantTag, terminateTag, allocateTag, releaseTag, grantAuthorityTag,
    revokeAuthorityTag, SpawnOracle.spawnCommandTag, SpawnAccountingOracle.grantFramesTag,
    SpawnAccountingOracle.terminateChildTag]
  by_cases t0 : tag = 0x7001
  · subst t0
    by_cases r3 : a3 = 0 <;> by_cases z0 : a0 = 0 <;> by_cases big : 64 ≤ a2 <;>
      simp [r3, z0, big, CompositeDispatcher.errorWord]
  by_cases t1 : tag = 0x7101
  · subst t1
    by_cases r2 : a2 = 0 <;> by_cases r3 : a3 = 0 <;> by_cases z1 : a1 = 0 <;>
      simp [r2, r3, z1, CompositeDispatcher.errorWord]
  by_cases t2 : tag = 0x7201
  · subst t2
    by_cases r1 : a1 = 0 <;> by_cases r2 : a2 = 0 <;> by_cases r3 : a3 = 0 <;>
      simp [r1, r2, r3, CompositeDispatcher.errorWord]
  by_cases t3 : tag = 0x7301
  · subst t3
    by_cases r1 : a1 = 0 <;> by_cases r2 : a2 = 0 <;> by_cases r3 : a3 = 0 <;>
      simp [r1, r2, r3, CompositeDispatcher.errorWord]
  by_cases t4 : tag = 0x7401
  · subst t4
    by_cases r1 : a1 = 0 <;> by_cases r2 : a2 = 0 <;> by_cases r3 : a3 = 0 <;>
      simp [r1, r2, r3, CompositeDispatcher.errorWord]
  by_cases t5 : tag = 0x7501
  · subst t5
    by_cases r2 : a2 = 0 <;> by_cases r3 : a3 = 0 <;>
      simp [r2, r3, CompositeDispatcher.errorWord]
  by_cases t6 : tag = 0x7601
  · subst t6
    by_cases r1 : a1 = 0 <;> by_cases r2 : a2 = 0 <;> by_cases r3 : a3 = 0 <;>
      simp [r1, r2, r3, CompositeDispatcher.errorWord]
  simp [t0, t1, t2, t3, t4, t5, t6, CompositeDispatcher.errorWord]

/-! ## Encoding and decoding -/

theorem entryCharge_decodeChild (word : UInt64) :
    SpawnAllocator.entryCharge (decodeChild word) = word.toNat % 65536 := by
  unfold SpawnAllocator.entryCharge decodeChild
  by_cases zero : word = 0
  · subst zero; simp
  · simp [zero]

theorem decode_chargeSum (words : Words) :
    (decode words).chargeSum = words.child0.toNat % 65536 + words.child1.toNat % 65536 +
      words.child2.toNat % 65536 + words.child3.toNat % 65536 := by
  simp only [State.chargeSum, decode, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    entryCharge_decodeChild]
  omega

theorem decodeChild_bounded {word : UInt64} (canonicalWord : childCanonical word = true)
    {entry : ChildRecord} (decoded : decodeChild word = some entry) :
    0 < entry.generation ∧ entry.generation < CapabilityHandle.generationReserved := by
  obtain ⟨nonzero, generation, _⟩ := (decodeChild_some_iff _ _).1 decoded
  rcases childCanonical_facts canonicalWord with zero | facts
  · exact absurd zero nonzero
  · rw [generation]; exact facts

/-- **Canonical words decode to a bounded record.** -/
theorem decode_bounded (words : Words) (canonicalWords : Canonical words = true) :
    Bounded (decode words) := by
  have facts := canonicalFacts words canonicalWords
  refine ⟨words.subjectNext.toNat_lt, words.objectNext.toNat_lt, words.capabilityNext.toNat_lt,
    words.controlNext.toNat_lt, ?_, words.authorityNext.toNat_lt, ?_, facts.budget, rfl, rfl, ?_,
    ?_, ?_⟩
  · have : words.authorityNext.toNat ≠ 0 :=
      fun z => facts.authorityNext (UInt64.toNat_inj.1 (by simpa using z))
    show 0 < words.authorityNext.toNat
    omega
  · intro generation held
    simp only [decode, decodeAuthority] at held
    split at held
    · cases held
    · next nonzero =>
      simp only [Option.some.injEq] at held
      subst held
      have : words.authority.toNat ≠ 0 := fun z => nonzero (UInt64.toNat_inj.1 (by simpa using z))
      exact ⟨Nat.pos_of_ne_zero this, words.authority.toNat_lt⟩
  · intro entry member
    simp only [decode, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with m | m | m | m
    · exact decodeChild_bounded facts.child0 m.symm
    · exact decodeChild_bounded facts.child1 m.symm
    · exact decodeChild_bounded facts.child2 m.symm
    · exact decodeChild_bounded facts.child3 m.symm
  · intro identity member
    simp only [decode, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with m | m <;>
    · obtain ⟨nonzero, eq⟩ := (decodeMemory_some_iff _ _).1 m.symm
      have : identity ≠ 0 := by
        rw [← eq]; exact fun z => nonzero (UInt64.toNat_inj.1 (by simpa using z))
      exact ⟨Nat.pos_of_ne_zero this, by rw [← eq]; exact UInt64.toNat_lt _⟩
  · rw [decode_chargeSum]
    have := facts.frames
    show words.frames.toNat / 65536 + _ < 2 ^ 16
    omega

theorem encodeChild_decodeChild (word : UInt64) : encodeChild (decodeChild word) = word := by
  unfold encodeChild decodeChild
  by_cases zero : word = 0
  · subst zero; rfl
  · simp only [zero, ↓reduceIte]
    apply UInt64.toNat_inj.1
    rw [toNat_ofNat_lt (by have := word.toNat_lt; omega)]
    omega

theorem encodeMemory_decodeMemory (word : UInt64) : encodeMemory (decodeMemory word) = word := by
  unfold encodeMemory decodeMemory
  by_cases zero : word = 0
  · subst zero; rfl
  · simp [zero]

theorem encodeAuthority_decodeAuthority (word : UInt64) :
    encodeAuthority (decodeAuthority word) = word := by
  unfold encodeAuthority decodeAuthority
  by_cases zero : word = 0
  · subst zero; rfl
  · simp [zero]

/-- **Canonical words are the encoding of what they decode to.** -/
theorem encode_decode (words : Words) (canonicalWords : Canonical words = true) :
    encode (decode words) = words := by
  have facts := canonicalFacts words canonicalWords
  have frames : UInt64.ofNat ((decode words).budget + (decode words).parentFrames * 65536) =
      words.frames := by
    apply UInt64.toNat_inj.1
    simp only [decode]
    rw [toNat_ofNat_lt (by have := facts.framesHigh; omega)]
    omega
  simp only [encode, frames]
  rw [decode_childAt, decode_childAt, decode_childAt, decode_childAt, decode_memoryAt,
    decode_memoryAt]
  simp only [↓reduceIte, encodeChild_decodeChild, encodeMemory_decodeMemory,
    show (1 : Nat) ≠ 0 from by decide, show (2 : Nat) ≠ 0 from by decide,
    show (3 : Nat) ≠ 0 from by decide, show (2 : Nat) ≠ 1 from by decide,
    show (3 : Nat) ≠ 1 from by decide, show (3 : Nat) ≠ 2 from by decide]
  simp [decode, encodeAuthority_decodeAuthority, encodeChild_decodeChild,
    encodeMemory_decodeMemory]

end LeanOS.SpawnAllocatorWords
