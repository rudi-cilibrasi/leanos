import LeanOS.SpawnAllocatorWordsNext

/-!
# Bounded records encode exactly (#575)

`encode_decode` (`LeanOS.SpawnAllocatorWordsFacts`) reads canonical words as
the encoding of their record.  This module is the other direction: a bounded
record encodes to canonical words (`encode_canonical`) that decode to the same
record (`decode_encode`).  So a kernel that holds the thirteen words of a
bounded record holds exactly that record, and the generated functions run on
it are the allocator's step on it (`code_step`).
-/
namespace LeanOS.SpawnAllocatorWords

open LeanOS
open LeanOS.SpawnAllocator
open LeanOS.CompositeDispatcher (CommandWords)

set_option linter.unusedSimpArgs false

theorem generationReserved_value : CapabilityHandle.generationReserved = 2 ^ 48 - 1 := rfl

theorem wordBound_value : wordBound = 2 ^ 64 := rfl

theorem frameBound_value : SpawnAllocator.frameBound = 2 ^ 16 := rfl

/-- The record's four child entries, by position. -/
theorem children_four {state : State} (bounded : Bounded state) :
    state.children = [state.childAt 0, state.childAt 1, state.childAt 2, state.childAt 3] := by
  have length := bounded.childrenLength
  unfold childCapacity at length
  match children : state.children, length with
  | [first, second, third, fourth], _ =>
      simp [State.childAt, children]

/-- The record's two memory entries, by parent slot. -/
theorem memory_two {state : State} (bounded : Bounded state) :
    state.memory = [state.memoryAt 2, state.memoryAt 3] := by
  have length := bounded.memoryLength
  unfold memoryCapacity parentSlots memoryBase at length
  match memory : state.memory, length with
  | [first, second], _ =>
      simp [State.memoryAt, memory, memoryBase]

theorem childAt_mem {state : State} {slot : Nat} {entry : ChildRecord}
    (held : state.childAt slot = some entry) : some entry ∈ state.children := by
  unfold State.childAt at held
  cases found : state.children[slot]? with
  | none => rw [found] at held; cases held
  | some inner =>
      rw [found] at held
      simp only [Option.join_some] at held
      subst held
      exact List.mem_of_getElem? found

theorem memoryAt_mem {state : State} {slot : Nat} {identity : Nat}
    (held : state.memoryAt slot = some identity) : some identity ∈ state.memory := by
  unfold State.memoryAt at held
  split at held
  · cases held
  · cases found : state.memory[slot - memoryBase]? with
    | none => rw [found] at held; cases held
    | some inner =>
        rw [found] at held
        simp only [Option.join_some] at held
        subst held
        exact List.mem_of_getElem? found

theorem charge_le_chargeSum {state : State} {entry : ChildRecord}
    (member : some entry ∈ state.children) : entry.charge ≤ state.chargeSum := by
  unfold State.chargeSum
  have sumLe : ∀ (values : List (Option ChildRecord)), some entry ∈ values →
      entry.charge ≤ (values.map SpawnAllocator.entryCharge).sum := by
    intro values
    induction values with
    | nil => intro inside; cases inside
    | cons head tail ih =>
        intro inside
        simp only [List.map_cons, List.sum_cons]
        rcases List.mem_cons.1 inside with same | rest
        · subst same; simp [SpawnAllocator.entryCharge]
        · have := ih rest; omega
  exact sumLe state.children member

/-- One child entry of a bounded record encodes exactly. -/
theorem decodeChild_encodeChild {state : State} (bounded : Bounded state) (slot : Nat) :
    decodeChild (encodeChild (state.childAt slot)) = state.childAt slot ∧
      childCanonical (encodeChild (state.childAt slot)) = true ∧
      (encodeChild (state.childAt slot)).toNat % 65536 = SpawnAllocator.entryCharge (state.childAt slot) := by
  cases held : state.childAt slot with
  | none => exact ⟨rfl, rfl, rfl⟩
  | some entry =>
      have member := childAt_mem held
      obtain ⟨positive, below⟩ := bounded.childRecords entry member
      have charge := charge_le_chargeSum member
      have frames := bounded.frames
      rw [generationReserved_value] at below
      rw [frameBound_value] at frames
      have fits : entry.generation * 65536 + entry.charge < 2 ^ 64 := by omega
      have value : (encodeChild (some entry)).toNat = entry.generation * 65536 + entry.charge := by
        simp only [encodeChild]; exact toNat_ofNat_lt fits
      have nonzero : encodeChild (some entry) ≠ 0 := by
        intro zero
        have := congrArg UInt64.toNat zero
        rw [value] at this
        simp at this
        omega
      have generationEq : (entry.generation * 65536 + entry.charge) / 65536 = entry.generation := by
        omega
      have chargeEq : (entry.generation * 65536 + entry.charge) % 65536 = entry.charge := by omega
      refine ⟨?_, ?_, ?_⟩
      · simp only [decodeChild, nonzero, ↓reduceIte, value, generationEq, chargeEq]
      · simp only [childCanonical, Bool.or_eq_true, beq_iff_eq, nonzero, false_or,
          Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq]
        constructor
        · intro shifted
          have := congrArg UInt64.toNat shifted
          rw [toNat_shr16, value] at this
          simp at this
          omega
        · rw [UInt64.lt_iff_toNat_lt, toNat_shr16, value]
          simp [generationLimit]
          omega
      · rw [value]
        simp [SpawnAllocator.entryCharge]
        omega

/-- One memory entry of a bounded record encodes exactly. -/
theorem decodeMemory_encodeMemory {state : State} (bounded : Bounded state) (slot : Nat) :
    decodeMemory (encodeMemory (state.memoryAt slot)) = state.memoryAt slot := by
  cases held : state.memoryAt slot with
  | none => rfl
  | some identity =>
      obtain ⟨positive, below⟩ := bounded.memoryRecords identity (memoryAt_mem held)
      have value : (encodeMemory (some identity)).toNat = identity := by
        simp only [encodeMemory]; exact toNat_ofNat_lt below
      have nonzero : encodeMemory (some identity) ≠ 0 := by
        intro zero
        have := congrArg UInt64.toNat zero
        rw [value] at this
        simp at this
        omega
      simp only [decodeMemory, nonzero, ↓reduceIte, value]

theorem decodeAuthority_encodeAuthority {state : State} (bounded : Bounded state) :
    decodeAuthority (encodeAuthority state.authority) = state.authority := by
  cases held : state.authority with
  | none => rfl
  | some generation =>
      obtain ⟨positive, below⟩ := bounded.authority generation held
      have value : (encodeAuthority (some generation)).toNat = generation := by
        simp only [encodeAuthority]; exact toNat_ofNat_lt below
      have nonzero : encodeAuthority (some generation) ≠ 0 := by
        intro zero
        have := congrArg UInt64.toNat zero
        rw [value] at this
        simp at this
        omega
      simp only [decodeAuthority, nonzero, ↓reduceIte, value]

theorem frames_toNat {state : State} (bounded : Bounded state) :
    (UInt64.ofNat (state.budget + state.parentFrames * 65536)).toNat =
      state.budget + state.parentFrames * 65536 := by
  have budget := bounded.budget
  have frames := bounded.frames
  unfold childCapacity at budget
  rw [frameBound_value] at frames
  exact toNat_ofNat_lt (by omega)

/-- **A bounded record's words decode to it.** -/
theorem decode_encode (state : State) (bounded : Bounded state) : decode (encode state) = state := by
  have budget := bounded.budget
  unfold childCapacity at budget
  have framesValue := frames_toNat bounded
  have children := children_four bounded
  have memory := memory_two bounded
  obtain ⟨child0, _, _⟩ := decodeChild_encodeChild bounded 0
  obtain ⟨child1, _, _⟩ := decodeChild_encodeChild bounded 1
  obtain ⟨child2, _, _⟩ := decodeChild_encodeChild bounded 2
  obtain ⟨child3, _, _⟩ := decodeChild_encodeChild bounded 3
  have memory2 := decodeMemory_encodeMemory bounded 2
  have memory3 := decodeMemory_encodeMemory bounded 3
  have authority := decodeAuthority_encodeAuthority bounded
  cases state with
  | mk subjectNext objectNext capabilityNext controlNext authorityNext authorityValue budgetValue
      childrenValue memoryValue parentFrames =>
    simp only [decode, encode] at *
    simp only [State.mk.injEq]
    refine ⟨toNat_ofNat_lt bounded.subjectNext, toNat_ofNat_lt bounded.objectNext,
      toNat_ofNat_lt bounded.capabilityNext, toNat_ofNat_lt bounded.controlNext,
      toNat_ofNat_lt bounded.authorityNext, authority, ?_, ?_, ?_, ?_⟩
    · rw [framesValue]; omega
    · rw [child0, child1, child2, child3]; exact children.symm
    · rw [memory2, memory3]; exact memory.symm
    · rw [framesValue]; omega

/-- **A bounded record's words are canonical.** -/
theorem encode_canonical (state : State) (bounded : Bounded state) :
    Canonical (encode state) = true := by
  have budget := bounded.budget
  have frames := bounded.frames
  unfold childCapacity at budget
  rw [frameBound_value] at frames
  have framesValue := frames_toNat bounded
  obtain ⟨_, canonical0, charge0⟩ := decodeChild_encodeChild bounded 0
  obtain ⟨_, canonical1, charge1⟩ := decodeChild_encodeChild bounded 1
  obtain ⟨_, canonical2, charge2⟩ := decodeChild_encodeChild bounded 2
  obtain ⟨_, canonical3, charge3⟩ := decodeChild_encodeChild bounded 3
  have chargeSum : state.chargeSum = SpawnAllocator.entryCharge (state.childAt 0) +
      SpawnAllocator.entryCharge (state.childAt 1) + SpawnAllocator.entryCharge (state.childAt 2) +
      SpawnAllocator.entryCharge (state.childAt 3) := by
    unfold State.chargeSum
    rw [children_four bounded]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    omega
  have authorityNonzero : UInt64.ofNat state.authorityNext ≠ 0 := by
    intro zero
    have := congrArg UInt64.toNat zero
    rw [toNat_ofNat_lt bounded.authorityNext] at this
    have := bounded.authorityPositive
    simp at *
    omega
  have high : (UInt64.ofNat (state.budget + state.parentFrames * 65536) >>> 32 == 0) = true := by
    simp only [beq_iff_eq]
    apply UInt64.toNat_inj.1
    rw [toNat_shr32, framesValue]
    simp
    omega
  have low : decide (UInt64.ofNat (state.budget + state.parentFrames * 65536) &&& 0xffff ≤ 4) =
      true := by
    simp only [decide_eq_true_eq]
    rw [UInt64.le_iff_toNat_le, toNat_and16, framesValue]
    simp
    omega
  have sumLt : (UInt64.ofNat (state.budget + state.parentFrames * 65536) >>> 16) +
      chargeOf (encodeChild (state.childAt 0)) + chargeOf (encodeChild (state.childAt 1)) +
      chargeOf (encodeChild (state.childAt 2)) + chargeOf (encodeChild (state.childAt 3)) <
      0x10000 := by
    simp only [chargeOf]
    rw [UInt64.lt_iff_toNat_lt]
    have shr := toNat_shr16 (UInt64.ofNat (state.budget + state.parentFrames * 65536))
    rw [framesValue] at shr
    have a0 := toNat_and16 (encodeChild (state.childAt 0))
    have a1 := toNat_and16 (encodeChild (state.childAt 1))
    have a2 := toNat_and16 (encodeChild (state.childAt 2))
    have a3 := toNat_and16 (encodeChild (state.childAt 3))
    rw [charge0] at a0
    rw [charge1] at a1
    rw [charge2] at a2
    rw [charge3] at a3
    have quotient : (state.budget + state.parentFrames * 65536) / 65536 = state.parentFrames := by
      omega
    rw [quotient] at shr
    have s1 := toNat_add_of_lt (UInt64.ofNat (state.budget + state.parentFrames * 65536) >>> 16) (encodeChild (state.childAt 0) &&& 0xffff)
      (by rw [shr, a0]; omega)
    have s2 := toNat_add_of_lt ((UInt64.ofNat (state.budget + state.parentFrames * 65536) >>> 16) + (encodeChild (state.childAt 0) &&& 0xffff))
      (encodeChild (state.childAt 1) &&& 0xffff) (by rw [s1, shr, a0, a1]; omega)
    have s3 := toNat_add_of_lt ((UInt64.ofNat (state.budget + state.parentFrames * 65536) >>> 16) + (encodeChild (state.childAt 0) &&& 0xffff) +
      (encodeChild (state.childAt 1) &&& 0xffff)) (encodeChild (state.childAt 2) &&& 0xffff) (by rw [s2, s1, shr, a0, a1, a2]; omega)
    have s4 := toNat_add_of_lt ((UInt64.ofNat (state.budget + state.parentFrames * 65536) >>> 16) + (encodeChild (state.childAt 0) &&& 0xffff) +
      (encodeChild (state.childAt 1) &&& 0xffff) + (encodeChild (state.childAt 2) &&& 0xffff)) (encodeChild (state.childAt 3) &&& 0xffff)
      (by rw [s3, s2, s1, shr, a0, a1, a2, a3]; omega)
    rw [s4, s3, s2, s1, shr, a0, a1, a2, a3]
    simp
    omega
  have sum : decide ((UInt64.ofNat (state.budget + state.parentFrames * 65536) >>> 16) +
      chargeOf (encodeChild (state.childAt 0)) + chargeOf (encodeChild (state.childAt 1)) +
      chargeOf (encodeChild (state.childAt 2)) + chargeOf (encodeChild (state.childAt 3)) <
      0x10000) = true := decide_eq_true sumLt
  have authority : (UInt64.ofNat state.authorityNext != 0) = true := by
    simpa using authorityNonzero
  simp only [Canonical, canonical, encode, authority, canonical0, canonical1, canonical2,
    canonical3, high, low, sum, Bool.and_self]
  simp only [Bool.true_and, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨by simpa using low, by simpa using sumLt⟩

/-- **The generated functions on a bounded record's words are the
allocator's step.**  For every bounded record and every command words that
decode to a command the allocator decides, the reply, value and successor
words are the step's status, value and the encoding of its successor. -/
theorem code_step (state : State) (bounded : Bounded state) (command : CommandWords)
    (operation : Command) (decoded : decodeCommand command = .ok operation) (result : Step)
    (decided : step state operation = some result) :
    codeReply (encode state) command = result.status ∧
      codeValue (encode state) command = result.value ∧
      codeNext (encode state) command = encode result.next := by
  obtain ⟨reply, value, next⟩ := words_refine (encode state) command
  have spec : specStep (encode state) command = (encode result.next, result.status, result.value) := by
    simp only [specStep, encode_canonical state bounded, decoded, decode_encode state bounded,
      decided]
    rfl
  rw [spec] at reply value next
  exact ⟨reply, value, next⟩

end LeanOS.SpawnAllocatorWords
