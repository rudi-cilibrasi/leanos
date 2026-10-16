import LeanOS.SpawnAllocatorWordsRefinement

/-!
# The successor words and the value word (#575)

Completes `words_refine`: the value word and every successor word computed by
the generated functions are the specification's.
-/
namespace LeanOS.SpawnAllocatorWords

open LeanOS
open LeanOS.FailStop
open LeanOS.SpawnAllocator
open LeanOS.CompositeDispatcher (CommandWords DecodeError)

set_option linter.unusedSimpArgs false

/-! ## Arithmetic of the encodings -/

theorem ofNat_add_toNat (word : UInt64) (count : Nat) :
    UInt64.ofNat (word.toNat + count) = word + UInt64.ofNat count := by
  apply UInt64.toNat_inj.1
  rw [UInt64.toNat_ofNat', UInt64.toNat_add, UInt64.toNat_ofNat']
  omega

theorem shiftLeft16_toNat (word : UInt64) : (word <<< 16).toNat = word.toNat * 65536 % 2 ^ 64 := by
  rw [UInt64.toNat_shiftLeft]
  have : (16 : UInt64).toNat % 64 = 16 := rfl
  rw [this, Nat.shiftLeft_eq]

theorem encodeChild_fresh (word : UInt64) :
    encodeChild (some ⟨word.toNat, 0⟩) = word <<< 16 := by
  apply UInt64.toNat_inj.1
  unfold encodeChild
  rw [UInt64.toNat_ofNat', shiftLeft16_toNat]
  dsimp only
  omega

theorem encodeChild_charge (word frames : UInt64) :
    encodeChild (some ⟨word.toNat / 65536, word.toNat % 65536 + frames.toNat⟩) =
      word + frames := by
  apply UInt64.toNat_inj.1
  simp only [encodeChild, UInt64.toNat_ofNat', UInt64.toNat_add]
  have := Nat.div_add_mod word.toNat 65536
  omega

theorem encodeAuthority_toNat (word : UInt64) :
    encodeAuthority (some word.toNat) = word := by
  simp [encodeAuthority]

theorem encodeMemory_toNat (word : UInt64) : encodeMemory (some word.toNat) = word := by
  simp [encodeMemory]

theorem frames_word (budget frames : UInt64) :
    UInt64.ofNat (budget.toNat + frames.toNat * 65536) = budget + (frames <<< 16) := by
  apply UInt64.toNat_inj.1
  rw [UInt64.toNat_ofNat', UInt64.toNat_add, shiftLeft16_toNat]
  omega

/-! ## The successor words of an accepted command -/

/-- The generated successor words of an accepted command. -/
theorem codeNext_accepted (words : Words) (command : CommandWords)
    (accepted : codeReply words command = 0x01) :
    codeNext words command =
      { subjectNext := if command.tag == 0x7001 then words.subjectNext + 1 else words.subjectNext
        objectNext := if command.tag == 0x7001 || command.tag == 0x7301 then words.objectNext + 1
          else words.objectNext
        capabilityNext := if command.tag == 0x7001 then words.capabilityNext + 2
          else if command.tag == 0x7301 then words.capabilityNext + 1 else words.capabilityNext
        controlNext := if command.tag == 0x7001 then words.controlNext + 1 else words.controlNext
        authorityNext := if command.tag == 0x7501 then words.authorityNext + 1
          else words.authorityNext
        authority := if command.tag == 0x7501 then words.authorityNext
          else if command.tag == 0x7601 && command.arg0 == 2 then 0 else words.authority
        child0 := nextChild 0 words.controlNext words.child0 words.child1 words.child2 words.child3
          command.tag command.arg0 command.arg1 words.child0
        child1 := nextChild 1 words.controlNext words.child0 words.child1 words.child2 words.child3
          command.tag command.arg0 command.arg1 words.child1
        child2 := nextChild 2 words.controlNext words.child0 words.child1 words.child2 words.child3
          command.tag command.arg0 command.arg1 words.child2
        child3 := nextChild 3 words.controlNext words.child0 words.child1 words.child2 words.child3
          command.tag command.arg0 command.arg1 words.child3
        memory2 := nextMemory 2 words.capabilityNext command.tag command.arg0 words.memory2
        memory3 := nextMemory 3 words.capabilityNext command.tag command.arg0 words.memory3
        frames := nextFrames words.child0 words.child1 words.child2 words.child3 words.frames
          command.tag command.arg0 command.arg1 } := by
  have reply : stepReply words.subjectNext words.objectNext words.capabilityNext
      words.controlNext words.authorityNext words.authority words.child0 words.child1 words.child2
      words.child3 words.memory2 words.memory3 words.frames command.tag command.arg0 command.arg1
      command.arg2 command.arg3 = 0x01 := accepted
  simp only [codeNext, stepNextWord, reply, beq_self_eq_true, Bool.true_and]
  simp

/-- The generated successor words of a command that is not accepted: the
words themselves. -/
theorem codeNext_unaccepted (words : Words) (command : CommandWords)
    (unaccepted : codeReply words command ≠ 0x01) : codeNext words command = words := by
  have different : stepReply words.subjectNext words.objectNext words.capabilityNext
      words.controlNext words.authorityNext words.authority words.child0 words.child1 words.child2
      words.child3 words.memory2 words.memory3 words.frames command.tag command.arg0 command.arg1
      command.arg2 command.arg3 ≠ 0x01 := unaccepted
  have reply : (stepReply words.subjectNext words.objectNext words.capabilityNext
      words.controlNext words.authorityNext words.authority words.child0 words.child1 words.child2
      words.child3 words.memory2 words.memory3 words.frames command.tag command.arg0 command.arg1
      command.arg2 command.arg3 == 0x01) = false := by
    simpa using different
  simp only [codeNext, stepNextWord, reply, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  simp

/-! ## Fields of the decoded record -/

theorem decoded_childWord (words : Words) (index : Nat) (word : UInt64)
    (which : (index = 0 ∧ word = words.child0) ∨ (index = 1 ∧ word = words.child1) ∨
      (index = 2 ∧ word = words.child2) ∨ (index = 3 ∧ word = words.child3)) :
    encodeChild ((decode words).childAt index) = word := by
  rw [decode_childAt]
  rcases which with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp [encodeChild_decodeChild]

theorem decoded_memoryWord2 (words : Words) :
    encodeMemory ((decode words).memoryAt 2) = words.memory2 := by
  rw [decode_memoryAt]; simp [encodeMemory_decodeMemory]

theorem decoded_memoryWord3 (words : Words) :
    encodeMemory ((decode words).memoryAt 3) = words.memory3 := by
  rw [decode_memoryAt]; simp [encodeMemory_decodeMemory]

theorem decoded_frames (words : Words) (canonicalWords : Canonical words = true) :
    UInt64.ofNat ((decode words).budget + (decode words).parentFrames * 65536) = words.frames := by
  have := congrArg Words.frames (encode_decode words canonicalWords)
  simpa [encode] using this

theorem freeSlotW_le (c0 c1 c2 c3 : UInt64) : (freeSlotW c0 c1 c2 c3).toNat ≤ 4 := by
  unfold freeSlotW
  repeat' split
  all_goals decide

/-! ## Spawn -/

theorem spawn_words (words : Words) (canonicalWords : Canonical words = true) (slot : Nat)
    (free : (decode words).freeSlot = some slot) (command : CommandWords)
    (tag : command.tag = 0x7001) :
    encode (spawned (decode words) slot) =
        { subjectNext := words.subjectNext + 1
          objectNext := words.objectNext + 1
          capabilityNext := words.capabilityNext + 2
          controlNext := words.controlNext + 1
          authorityNext := words.authorityNext
          authority := words.authority
          child0 := nextChild 0 words.controlNext words.child0 words.child1 words.child2
            words.child3 command.tag command.arg0 command.arg1 words.child0
          child1 := nextChild 1 words.controlNext words.child0 words.child1 words.child2
            words.child3 command.tag command.arg0 command.arg1 words.child1
          child2 := nextChild 2 words.controlNext words.child0 words.child1 words.child2
            words.child3 command.tag command.arg0 command.arg1 words.child2
          child3 := nextChild 3 words.controlNext words.child0 words.child1 words.child2
            words.child3 command.tag command.arg0 command.arg1 words.child3
          memory2 := words.memory2
          memory3 := words.memory3
          frames := words.frames } ∧
      SpawnAllocator.controlWord slot (decode words).controlNext =
        freeSlotW words.child0 words.child1 words.child2 words.child3 + (words.controlNext <<< 16) := by
  obtain ⟨inRange, _⟩ := freeSlot_some free
  have slotEq : slot = (freeSlotW words.child0 words.child1 words.child2 words.child3).toNat := by
    rw [freeSlotW_spec] at free
    split at free
    · cases free
    · simp only [Option.some.injEq] at free; exact free.symm
  have childAt := fun index => childAt_set (next := spawned (decode words) slot) rfl inRange index
  have child : ∀ index : Nat, ∀ word : UInt64, (index = 0 ∧ word = words.child0) ∨
      (index = 1 ∧ word = words.child1) ∨ (index = 2 ∧ word = words.child2) ∨
      (index = 3 ∧ word = words.child3) →
      encodeChild ((spawned (decode words) slot).childAt index) =
        nextChild (UInt64.ofNat index) words.controlNext words.child0 words.child1 words.child2
          words.child3 command.tag command.arg0 command.arg1 word := by
    intro index word which
    rw [childAt index]
    unfold nextChild
    simp only [tag, beq_self_eq_true, ↓reduceIte]
    by_cases same : slot = index
    · have : freeSlotW words.child0 words.child1 words.child2 words.child3 = UInt64.ofNat index := by
        apply UInt64.toNat_inj.1
        rw [← slotEq, same, toNat_ofNat_lt]
        rcases which with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> decide
      simp only [same, ↓reduceIte, this, beq_self_eq_true]
      exact encodeChild_fresh words.controlNext
    · have : (freeSlotW words.child0 words.child1 words.child2 words.child3 ==
          UInt64.ofNat index) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]
        intro eq
        apply same
        rw [slotEq, eq, toNat_ofNat_lt]
        rcases which with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> decide
      simp only [same, ↓reduceIte, this, Bool.false_eq_true]
      exact decoded_childWord words index word which
  have frames := decoded_frames words canonicalWords
  refine ⟨?_, ?_⟩
  · simp only [encode, spawned_subjectNext, spawned_objectNext, spawned_capabilityNext,
      spawned_controlNext, spawned_authorityNext, spawned_authority, spawned_budget,
      spawned_parentFrames, spawned_memoryAt, decoded_memoryWord2, decoded_memoryWord3, frames]
    apply Words.ext
    · exact ofNat_add_toNat _ _
    · exact ofNat_add_toNat _ _
    · exact ofNat_add_toNat _ _
    · exact ofNat_add_toNat _ _
    · exact UInt64.ofNat_toNat
    · exact encodeAuthority_decodeAuthority _
    · exact child 0 _ (Or.inl ⟨rfl, rfl⟩)
    · exact child 1 _ (Or.inr (Or.inl ⟨rfl, rfl⟩))
    · exact child 2 _ (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
    · exact child 3 _ (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))
    · rfl
    · rfl
    · rfl
  · have small := freeSlotW_le words.child0 words.child1 words.child2 words.child3
    unfold SpawnAllocator.controlWord
    apply UInt64.toNat_inj.1
    rw [UInt64.toNat_ofNat', UInt64.toNat_add, shiftLeft16_toNat, ← slotEq]
    show (slot + words.controlNext.toNat * 65536) % 2 ^ 64 = _
    omega

/-! ## Grant and termination -/

theorem childWordAt_index (words : Words) (index : UInt64) (word : UInt64)
    (which : (index = 0 ∧ word = words.child0) ∨ (index = 1 ∧ word = words.child1) ∨
      (index = 2 ∧ word = words.child2) ∨ (index = 3 ∧ word = words.child3)) :
    childWordAt index words.child0 words.child1 words.child2 words.child3 = word := by
  rcases which with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl

theorem which_toNat {words : Words} {index : Nat} {word : UInt64}
    (which : (index = 0 ∧ word = words.child0) ∨ (index = 1 ∧ word = words.child1) ∨
      (index = 2 ∧ word = words.child2) ∨ (index = 3 ∧ word = words.child3)) :
    (UInt64.ofNat index).toNat = index := by
  rcases which with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> rfl

theorem which_ofNat {words : Words} {index : Nat} {word : UInt64}
    (which : (index = 0 ∧ word = words.child0) ∨ (index = 1 ∧ word = words.child1) ∨
      (index = 2 ∧ word = words.child2) ∨ (index = 3 ∧ word = words.child3)) :
    (UInt64.ofNat index = 0 ∧ word = words.child0) ∨ (UInt64.ofNat index = 1 ∧ word = words.child1) ∨
      (UInt64.ofNat index = 2 ∧ word = words.child2) ∨ (UInt64.ofNat index = 3 ∧ word = words.child3) := by
  rcases which with ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩
  · exact Or.inl ⟨rfl, h⟩
  · exact Or.inr (Or.inl ⟨rfl, h⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨rfl, h⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨rfl, h⟩))

/-- The successor of a child-table update of `slot`, in words: the named
slot's word becomes `updated`, every other slot keeps its word. -/
theorem child_update (words : Words) (next : SpawnAllocator.State) (slot : Nat) (entry : Option ChildRecord)
    (children : next.children = (decode words).children.set slot entry)
    (inRange : slot < (decode words).children.length) (control : UInt64)
    (slotEq : slot = (control &&& 0xffff).toNat) (updated : UInt64 → UInt64)
    (named : ∀ word, decodeChild word ≠ none →
      childWordAt (control &&& 0xffff) words.child0 words.child1 words.child2 words.child3 = word →
      encodeChild entry = updated word)
    (held : (decode words).childAt slot ≠ none)
    (index : Nat) (word : UInt64)
    (which : (index = 0 ∧ word = words.child0) ∨ (index = 1 ∧ word = words.child1) ∨
      (index = 2 ∧ word = words.child2) ∨ (index = 3 ∧ word = words.child3)) :
    encodeChild (next.childAt index) =
      if (control &&& 0xffff) == UInt64.ofNat index then updated word else word := by
  rw [childAt_set children inRange index]
  by_cases same : slot = index
  · have eqWord : (control &&& 0xffff) = UInt64.ofNat index := by
      apply UInt64.toNat_inj.1; rw [← slotEq, same, which_toNat which]
    simp only [same, ↓reduceIte, eqWord, beq_self_eq_true]
    apply named word
    · have := childWordAt_spec words (UInt64.ofNat index)
      rw [childWordAt_index words _ word (which_ofNat which), which_toNat which, ← same] at this
      rw [this]; exact held
    · rw [eqWord]; exact childWordAt_index words _ word (which_ofNat which)
  · have ne : ((control &&& 0xffff) == UInt64.ofNat index) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]
      intro eq; apply same; rw [slotEq, eq, which_toNat which]
    simp only [same, ↓reduceIte, ne, Bool.false_eq_true]
    exact decoded_childWord words index word which

theorem parentFramesW_toNat (words : Words) :
    (parentFramesW words.frames).toNat = (decode words).parentFrames := by
  unfold parentFramesW; rw [toNat_shr16]; rfl

theorem budgetW_toNat (words : Words) : (budgetW words.frames).toNat = (decode words).budget :=
  budget_toNat words

theorem frames_of (budget frames : UInt64) (budgetValue framesValue : Nat)
    (budgetEq : budget.toNat = budgetValue) (framesEq : frames.toNat = framesValue) :
    UInt64.ofNat (budgetValue + framesValue * 65536) = budget + (frames <<< 16) := by
  rw [← budgetEq, ← framesEq]; exact frames_word budget frames

/-! ## Every accepted command -/

theorem codeValue_accepted (words : Words) (command : CommandWords)
    (accepted : codeReply words command = 0x01) :
    codeValue words command =
      if command.tag == 0x7001 then
        freeSlotW words.child0 words.child1 words.child2 words.child3 + (words.controlNext <<< 16)
      else if command.tag == 0x7101 then command.arg1
      else if command.tag == 0x7201 then
        chargeOf (childWordAt (command.arg0 &&& 0xffff) words.child0 words.child1 words.child2
          words.child3)
      else if command.tag == 0x7501 then words.authorityNext
      else 0 := by
  have reply : stepReply words.subjectNext words.objectNext words.capabilityNext
      words.controlNext words.authorityNext words.authority words.child0 words.child1 words.child2
      words.child3 words.memory2 words.memory3 words.frames command.tag command.arg0 command.arg1
      command.arg2 command.arg3 = 0x01 := accepted
  simp only [codeValue, stepValue, reply, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]

/-- The successor words the generated functions compute for an accepted
command (`codeNext_accepted`). -/
def acceptedWords (words : Words) (command : CommandWords) : Words :=
  { subjectNext := if command.tag == 0x7001 then words.subjectNext + 1 else words.subjectNext
    objectNext := if command.tag == 0x7001 || command.tag == 0x7301 then words.objectNext + 1
      else words.objectNext
    capabilityNext := if command.tag == 0x7001 then words.capabilityNext + 2
      else if command.tag == 0x7301 then words.capabilityNext + 1 else words.capabilityNext
    controlNext := if command.tag == 0x7001 then words.controlNext + 1 else words.controlNext
    authorityNext := if command.tag == 0x7501 then words.authorityNext + 1
      else words.authorityNext
    authority := if command.tag == 0x7501 then words.authorityNext
      else if command.tag == 0x7601 && command.arg0 == 2 then 0 else words.authority
    child0 := nextChild 0 words.controlNext words.child0 words.child1 words.child2 words.child3
      command.tag command.arg0 command.arg1 words.child0
    child1 := nextChild 1 words.controlNext words.child0 words.child1 words.child2 words.child3
      command.tag command.arg0 command.arg1 words.child1
    child2 := nextChild 2 words.controlNext words.child0 words.child1 words.child2 words.child3
      command.tag command.arg0 command.arg1 words.child2
    child3 := nextChild 3 words.controlNext words.child0 words.child1 words.child2 words.child3
      command.tag command.arg0 command.arg1 words.child3
    memory2 := nextMemory 2 words.capabilityNext command.tag command.arg0 words.memory2
    memory3 := nextMemory 3 words.capabilityNext command.tag command.arg0 words.memory3
    frames := nextFrames words.child0 words.child1 words.child2 words.child3 words.frames
      command.tag command.arg0 command.arg1 }

theorem grant_refines (words : Words)
    (command : CommandWords) (tag : command.tag = 0x7101) (slot : Nat) (entry : ChildRecord)
    (resolved : (decode words).resolveControl command.arg0 = .ok (slot, entry))
    (enough : command.arg1.toNat ≤ (decode words).available) :
    acceptedWords words command = encode (granted (decode words) slot entry command.arg1.toNat) := by
  obtain ⟨slotEq, entryWord⟩ := resolveControl_words words command.arg0 slot entry resolved
  obtain ⟨_, held⟩ := resolveControl_ok resolved
  obtain ⟨inRange, _⟩ := childAt_some held
  have availableLe := available_le (decode words)
  have child := child_update words (granted (decode words) slot entry command.arg1.toNat) slot
    (some { entry with charge := entry.charge + command.arg1.toNat }) rfl inRange
    command.arg0 slotEq (fun word => word + command.arg1)
    (by
      intro word _ named
      rw [named] at entryWord
      obtain ⟨_, generation, charge⟩ := (decodeChild_some_iff _ _).1 entryWord
      have := encodeChild_charge word command.arg1
      rw [← generation, ← charge] at this
      exact this)
    (by rw [held]; simp)
  have frames : nextFrames words.child0 words.child1 words.child2 words.child3 words.frames
      0x7101 command.arg0 command.arg1 =
      UInt64.ofNat ((decode words).budget + ((decode words).parentFrames - command.arg1.toNat) * 65536) := by
    simp only [nextFrames, beq_self_eq_true, ↓reduceIte]
    refine (frames_of _ _ _ _ (budgetW_toNat words) ?_).symm
    rw [UInt64.toNat_sub_of_le, parentFramesW_toNat]
    rw [UInt64.le_iff_toNat_le, parentFramesW_toNat]
    omega
  have n0 : ((0x7101 : UInt64) == 0x7001) = false := by decide
  have n3 : ((0x7101 : UInt64) == 0x7301) = false := by decide
  have n5 : ((0x7101 : UInt64) == 0x7501) = false := by decide
  have n6 : ((0x7101 : UInt64) == 0x7601) = false := by decide
  apply Words.ext
  · simp only [acceptedWords, encode, tag, n0, Bool.false_eq_true, ↓reduceIte, granted_subjectNext]
    exact UInt64.ofNat_toNat.symm
  · simp only [acceptedWords, encode, tag, n0, n3, Bool.false_or, Bool.false_eq_true, ↓reduceIte,
      granted_objectNext]
    exact UInt64.ofNat_toNat.symm
  · simp only [acceptedWords, encode, tag, n0, n3, Bool.false_eq_true, ↓reduceIte,
      granted_capabilityNext]
    exact UInt64.ofNat_toNat.symm
  · simp only [acceptedWords, encode, tag, n0, Bool.false_eq_true, ↓reduceIte, granted_controlNext]
    exact UInt64.ofNat_toNat.symm
  · simp only [acceptedWords, encode, tag, n5, Bool.false_eq_true, ↓reduceIte,
      granted_authorityNext]
    exact UInt64.ofNat_toNat.symm
  · simp only [acceptedWords, encode, tag, n5, n6, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
      granted_authority]
    exact (encodeAuthority_decodeAuthority _).symm
  · simp only [acceptedWords, encode, tag]
    rw [child 0 _ (Or.inl ⟨rfl, rfl⟩)]; simp [nextChild]
  · simp only [acceptedWords, encode, tag]
    rw [child 1 _ (Or.inr (Or.inl ⟨rfl, rfl⟩))]; simp [nextChild]
  · simp only [acceptedWords, encode, tag]
    rw [child 2 _ (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))]; simp [nextChild]
  · simp only [acceptedWords, encode, tag]
    rw [child 3 _ (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))]; simp [nextChild]
  · simp only [acceptedWords, encode, tag, granted_memoryAt, nextMemory]
    simp [decoded_memoryWord2]
  · simp only [acceptedWords, encode, tag, granted_memoryAt, nextMemory]
    simp [decoded_memoryWord3]
  · simp only [acceptedWords, encode, tag, granted_budget, granted_parentFrames]
    exact frames

theorem terminate_refines (words : Words) (command : CommandWords) (tag : command.tag = 0x7201)
    (slot : Nat) (entry : ChildRecord)
    (resolved : (decode words).resolveControl command.arg0 = .ok (slot, entry)) :
    acceptedWords words command = encode (terminated (decode words) slot entry) ∧
      chargeOf (childWordAt (command.arg0 &&& 0xffff) words.child0 words.child1 words.child2
        words.child3) = UInt64.ofNat entry.charge := by
  obtain ⟨slotEq, entryWord⟩ := resolveControl_words words command.arg0 slot entry resolved
  obtain ⟨_, held⟩ := resolveControl_ok resolved
  obtain ⟨inRange, _⟩ := childAt_some held
  obtain ⟨_, _, charge⟩ := (decodeChild_some_iff _ _).1 entryWord
  have chargeWord : (chargeOf (childWordAt (command.arg0 &&& 0xffff) words.child0
      words.child1 words.child2 words.child3)).toNat = entry.charge := by
    unfold chargeOf; rw [toNat_and16, charge]
  have chargeSmall : entry.charge < 65536 := by rw [charge]; omega
  have child := child_update words (terminated (decode words) slot entry) slot none rfl
    inRange command.arg0 slotEq (fun _ => 0) (fun _ _ _ => rfl) (by rw [held]; simp)
  have frames : nextFrames words.child0 words.child1 words.child2 words.child3 words.frames
      0x7201 command.arg0 command.arg1 =
      UInt64.ofNat ((decode words).budget + ((decode words).parentFrames + entry.charge) * 65536) := by
    have n1 : ((0x7201 : UInt64) == 0x7101) = false := by decide
    simp only [nextFrames, n1, Bool.false_eq_true, beq_self_eq_true, ↓reduceIte]
    refine (frames_of _ _ _ _ (budgetW_toNat words) ?_).symm
    have small : (parentFramesW words.frames).toNat < 2 ^ 48 := by
      rw [parentFramesW_toNat]; show words.frames.toNat / 65536 < _
      have := words.frames.toNat_lt; omega
    have chargeLt : (chargeOf (childWordAt (command.arg0 &&& 0xffff) words.child0 words.child1
        words.child2 words.child3)).toNat < 65536 := by rw [chargeWord]; exact chargeSmall
    have fits := toNat_add_of_lt (parentFramesW words.frames) (chargeOf (childWordAt
      (command.arg0 &&& 0xffff) words.child0 words.child1 words.child2 words.child3))
      (by omega)
    rw [fits, chargeWord, parentFramesW_toNat]
  have n0 : ((0x7201 : UInt64) == 0x7001) = false := by decide
  have n3 : ((0x7201 : UInt64) == 0x7301) = false := by decide
  have n5 : ((0x7201 : UInt64) == 0x7501) = false := by decide
  have n6 : ((0x7201 : UInt64) == 0x7601) = false := by decide
  refine ⟨?_, UInt64.toNat_inj.1 (by rw [chargeWord, toNat_ofNat_lt (by omega)])⟩
  apply Words.ext
  · simp only [acceptedWords, encode, tag, n0, Bool.false_eq_true, ↓reduceIte,
      terminated_subjectNext]
    exact UInt64.ofNat_toNat.symm
  · simp only [acceptedWords, encode, tag, n0, n3, Bool.false_or, Bool.false_eq_true, ↓reduceIte,
      terminated_objectNext]
    exact UInt64.ofNat_toNat.symm
  · simp only [acceptedWords, encode, tag, n0, n3, Bool.false_eq_true, ↓reduceIte,
      terminated_capabilityNext]
    exact UInt64.ofNat_toNat.symm
  · simp only [acceptedWords, encode, tag, n0, Bool.false_eq_true, ↓reduceIte,
      terminated_controlNext]
    exact UInt64.ofNat_toNat.symm
  · simp only [acceptedWords, encode, tag, n5, Bool.false_eq_true, ↓reduceIte,
      terminated_authorityNext]
    exact UInt64.ofNat_toNat.symm
  · simp only [acceptedWords, encode, tag, n5, n6, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
      terminated_authority]
    exact (encodeAuthority_decodeAuthority _).symm
  · simp only [acceptedWords, encode, tag]
    rw [child 0 _ (Or.inl ⟨rfl, rfl⟩)]; simp [nextChild]
  · simp only [acceptedWords, encode, tag]
    rw [child 1 _ (Or.inr (Or.inl ⟨rfl, rfl⟩))]; simp [nextChild]
  · simp only [acceptedWords, encode, tag]
    rw [child 2 _ (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))]; simp [nextChild]
  · simp only [acceptedWords, encode, tag]
    rw [child 3 _ (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))]; simp [nextChild]
  · simp only [acceptedWords, encode, tag, terminated_memoryAt, nextMemory]
    simp [decoded_memoryWord2]
  · simp only [acceptedWords, encode, tag, terminated_memoryAt, nextMemory]
    simp [decoded_memoryWord3]
  · simp only [acceptedWords, encode, tag, terminated_budget, terminated_parentFrames]
    exact frames

theorem memoryAt_update {next state : SpawnAllocator.State} {slot : Nat} {entry : Option Nat}
    (memory : next.memory = state.memory.set (slot - memoryBase) entry)
    (low : memoryBase ≤ slot) (inRange : slot - memoryBase < state.memory.length)
    (other : Nat) (otherLow : memoryBase ≤ other) :
    next.memoryAt other = if slot = other then entry else state.memoryAt other := by
  unfold State.memoryAt
  simp only [Nat.not_lt.2 otherLow, ↓reduceIte, memory, List.getElem?_set]
  by_cases same : slot = other
  · subst same; simp [inRange]
  · have : slot - memoryBase ≠ other - memoryBase := by unfold memoryBase at *; omega
    simp [same, this]

theorem memory_update (words : Words) (next : SpawnAllocator.State) (slot : Nat)
    (entry : Option Nat) (memory : next.memory = (decode words).memory.set (slot - memoryBase) entry)
    (low : memoryBase ≤ slot) (range : slot < parentSlots) (command : CommandWords)
    (slotEq : slot = command.arg0.toNat) (updated : UInt64) (named : encodeMemory entry = updated)
    (index : Nat) (word : UInt64)
    (which : (index = 2 ∧ word = words.memory2) ∨ (index = 3 ∧ word = words.memory3)) :
    encodeMemory (next.memoryAt index) =
      if command.arg0 == UInt64.ofNat index then updated else word := by
  have inRange : slot - memoryBase < (decode words).memory.length := by
    simp only [decode, List.length_cons, List.length_nil]
    unfold memoryBase parentSlots at *; omega
  have indexLow : memoryBase ≤ index := by
    unfold memoryBase; rcases which with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> decide
  rw [memoryAt_update memory low inRange index indexLow]
  have indexNat : (UInt64.ofNat index).toNat = index := by
    rcases which with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> rfl
  by_cases same : slot = index
  · have eq : command.arg0 = UInt64.ofNat index := by
      apply UInt64.toNat_inj.1; rw [indexNat, ← slotEq, same]
    simp [same, eq, named]
  · have ne : (command.arg0 == UInt64.ofNat index) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]
      intro eq; apply same; rw [slotEq, eq, indexNat]
    simp only [same, ↓reduceIte, ne, Bool.false_eq_true]
    rcases which with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact decoded_memoryWord2 words
    · exact decoded_memoryWord3 words

/-- The fields a command leaves alone, for the per-field proofs below. -/
theorem acceptedWords_fields (words : Words) (command : CommandWords) :
    (acceptedWords words command).child0 = nextChild 0 words.controlNext words.child0 words.child1
        words.child2 words.child3 command.tag command.arg0 command.arg1 words.child0 ∧
      (acceptedWords words command).child1 = nextChild 1 words.controlNext words.child0
        words.child1 words.child2 words.child3 command.tag command.arg0 command.arg1 words.child1 ∧
      (acceptedWords words command).child2 = nextChild 2 words.controlNext words.child0
        words.child1 words.child2 words.child3 command.tag command.arg0 command.arg1 words.child2 ∧
      (acceptedWords words command).child3 = nextChild 3 words.controlNext words.child0
        words.child1 words.child2 words.child3 command.tag command.arg0 command.arg1 words.child3 :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem nextChild_other (index controlNext c0 c1 c2 c3 tag a0 a1 current : UInt64)
    (n0 : (tag == 0x7001) = false) (n1 : (tag == 0x7101) = false) (n2 : (tag == 0x7201) = false) :
    nextChild index controlNext c0 c1 c2 c3 tag a0 a1 current = current := by
  simp [nextChild, n0, n1, n2]

theorem decoded_childWords (words : Words) :
    encodeChild ((decode words).childAt 0) = words.child0 ∧
      encodeChild ((decode words).childAt 1) = words.child1 ∧
      encodeChild ((decode words).childAt 2) = words.child2 ∧
      encodeChild ((decode words).childAt 3) = words.child3 :=
  ⟨decoded_childWord words 0 _ (Or.inl ⟨rfl, rfl⟩),
    decoded_childWord words 1 _ (Or.inr (Or.inl ⟨rfl, rfl⟩)),
    decoded_childWord words 2 _ (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))),
    decoded_childWord words 3 _ (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))⟩

theorem allocate_refines (words : Words) (canonicalWords : Canonical words = true)
    (command : CommandWords) (tag : command.tag = 0x7301) (low : memoryBase ≤ command.arg0.toNat)
    (range : command.arg0.toNat < parentSlots) :
    acceptedWords words command = encode (allocated (decode words) command.arg0.toNat) := by
  have memory := fun index word which => memory_update words
    (allocated (decode words) command.arg0.toNat) command.arg0.toNat
    (some (decode words).capabilityNext) rfl low range command rfl words.capabilityNext
    (encodeMemory_toNat _) index word which
  have frames := decoded_frames words canonicalWords
  have n0 : ((0x7301 : UInt64) == 0x7001) = false := by decide
  have n1 : ((0x7301 : UInt64) == 0x7101) = false := by decide
  have n2 : ((0x7301 : UInt64) == 0x7201) = false := by decide
  have n4 : ((0x7301 : UInt64) == 0x7401) = false := by decide
  have n5 : ((0x7301 : UInt64) == 0x7501) = false := by decide
  have n6 : ((0x7301 : UInt64) == 0x7601) = false := by decide
  obtain ⟨d0, d1, d2, d3⟩ := decoded_childWords words
  apply Words.ext
  · simp only [acceptedWords, encode, tag, n0, Bool.false_eq_true, ↓reduceIte,
      allocated_subjectNext]
    exact UInt64.ofNat_toNat.symm
  · simp only [acceptedWords, encode, tag, n0, beq_self_eq_true, Bool.or_true, ↓reduceIte,
      allocated_objectNext]
    exact (ofNat_add_toNat _ _).symm
  · simp only [acceptedWords, encode, tag, n0, beq_self_eq_true, Bool.false_eq_true, ↓reduceIte,
      allocated_capabilityNext]
    exact (ofNat_add_toNat _ _).symm
  · simp only [acceptedWords, encode, tag, n0, Bool.false_eq_true, ↓reduceIte,
      allocated_controlNext]
    exact UInt64.ofNat_toNat.symm
  · simp only [acceptedWords, encode, tag, n5, Bool.false_eq_true, ↓reduceIte,
      allocated_authorityNext]
    exact UInt64.ofNat_toNat.symm
  · simp only [acceptedWords, encode, tag, n5, n6, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
      allocated_authority]
    exact (encodeAuthority_decodeAuthority _).symm
  · simp only [acceptedWords, encode, tag, allocated_childAt, nextChild_other _ _ _ _ _ _ _ _ _ _
      n0 n1 n2, d0]
  · simp only [acceptedWords, encode, tag, allocated_childAt, nextChild_other _ _ _ _ _ _ _ _ _ _
      n0 n1 n2, d1]
  · simp only [acceptedWords, encode, tag, allocated_childAt, nextChild_other _ _ _ _ _ _ _ _ _ _
      n0 n1 n2, d2]
  · simp only [acceptedWords, encode, tag, allocated_childAt, nextChild_other _ _ _ _ _ _ _ _ _ _
      n0 n1 n2, d3]
  · simp only [acceptedWords, encode, tag]
    rw [memory 2 _ (Or.inl ⟨rfl, rfl⟩)]
    simp [nextMemory]
  · simp only [acceptedWords, encode, tag]
    rw [memory 3 _ (Or.inr ⟨rfl, rfl⟩)]
    simp [nextMemory]
  · simp only [acceptedWords, encode, tag, allocated_budget, allocated_parentFrames, frames]
    simp [nextFrames, n1, n2, n5, n6]

theorem release_refines (words : Words) (canonicalWords : Canonical words = true)
    (command : CommandWords) (tag : command.tag = 0x7401) (low : memoryBase ≤ command.arg0.toNat)
    (range : command.arg0.toNat < parentSlots) :
    acceptedWords words command = encode (released (decode words) command.arg0.toNat) := by
  have memory := fun index word which => memory_update words
    (released (decode words) command.arg0.toNat) command.arg0.toNat none rfl low range command rfl
    0 rfl index word which
  have frames := decoded_frames words canonicalWords
  have n0 : ((0x7401 : UInt64) == 0x7001) = false := by decide
  have n1 : ((0x7401 : UInt64) == 0x7101) = false := by decide
  have n2 : ((0x7401 : UInt64) == 0x7201) = false := by decide
  have n3 : ((0x7401 : UInt64) == 0x7301) = false := by decide
  have n5 : ((0x7401 : UInt64) == 0x7501) = false := by decide
  have n6 : ((0x7401 : UInt64) == 0x7601) = false := by decide
  obtain ⟨d0, d1, d2, d3⟩ := decoded_childWords words
  apply Words.ext
  · simp only [acceptedWords, encode, tag, n0, Bool.false_eq_true, ↓reduceIte,
      released_subjectNext]
    exact UInt64.ofNat_toNat.symm
  · simp only [acceptedWords, encode, tag, n0, n3, Bool.or_false, Bool.false_eq_true, ↓reduceIte,
      released_objectNext]
    exact UInt64.ofNat_toNat.symm
  · simp only [acceptedWords, encode, tag, n0, n3, Bool.false_eq_true, ↓reduceIte,
      released_capabilityNext]
    exact UInt64.ofNat_toNat.symm
  · simp only [acceptedWords, encode, tag, n0, Bool.false_eq_true, ↓reduceIte,
      released_controlNext]
    exact UInt64.ofNat_toNat.symm
  · simp only [acceptedWords, encode, tag, n5, Bool.false_eq_true, ↓reduceIte,
      released_authorityNext]
    exact UInt64.ofNat_toNat.symm
  · simp only [acceptedWords, encode, tag, n5, n6, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
      released_authority]
    exact (encodeAuthority_decodeAuthority _).symm
  · simp only [acceptedWords, encode, tag, released_childAt, nextChild_other _ _ _ _ _ _ _ _ _ _
      n0 n1 n2, d0]
  · simp only [acceptedWords, encode, tag, released_childAt, nextChild_other _ _ _ _ _ _ _ _ _ _
      n0 n1 n2, d1]
  · simp only [acceptedWords, encode, tag, released_childAt, nextChild_other _ _ _ _ _ _ _ _ _ _
      n0 n1 n2, d2]
  · simp only [acceptedWords, encode, tag, released_childAt, nextChild_other _ _ _ _ _ _ _ _ _ _
      n0 n1 n2, d3]
  · simp only [acceptedWords, encode, tag]
    rw [memory 2 _ (Or.inl ⟨rfl, rfl⟩)]
    simp [nextMemory, n3]
  · simp only [acceptedWords, encode, tag]
    rw [memory 3 _ (Or.inr ⟨rfl, rfl⟩)]
    simp [nextMemory, n3]
  · simp only [acceptedWords, encode, tag, released_budget, released_parentFrames, frames]
    simp [nextFrames, n1, n2, n5, n6]

theorem grantAuthority_refines (words : Words) (command : CommandWords)
    (tag : command.tag = 0x7501) :
    acceptedWords words command = encode (authorized (decode words) command.arg1.toNat) := by
  have n0 : ((0x7501 : UInt64) == 0x7001) = false := by decide
  have n1 : ((0x7501 : UInt64) == 0x7101) = false := by decide
  have n2 : ((0x7501 : UInt64) == 0x7201) = false := by decide
  have n3 : ((0x7501 : UInt64) == 0x7301) = false := by decide
  have n4 : ((0x7501 : UInt64) == 0x7401) = false := by decide
  obtain ⟨d0, d1, d2, d3⟩ := decoded_childWords words
  apply Words.ext
  · simp only [acceptedWords, encode, tag, n0, Bool.false_eq_true, ↓reduceIte,
      authorized_subjectNext]
    exact UInt64.ofNat_toNat.symm
  · simp only [acceptedWords, encode, tag, n0, n3, Bool.or_false, Bool.false_eq_true, ↓reduceIte,
      authorized_objectNext]
    exact UInt64.ofNat_toNat.symm
  · simp only [acceptedWords, encode, tag, n0, n3, Bool.false_eq_true, ↓reduceIte,
      authorized_capabilityNext]
    exact UInt64.ofNat_toNat.symm
  · simp only [acceptedWords, encode, tag, n0, Bool.false_eq_true, ↓reduceIte,
      authorized_controlNext]
    exact UInt64.ofNat_toNat.symm
  · simp only [acceptedWords, encode, tag, beq_self_eq_true, ↓reduceIte, authorized_authorityNext]
    exact (ofNat_add_toNat _ _).symm
  · simp only [acceptedWords, encode, tag, beq_self_eq_true, ↓reduceIte, authorized_authority]
    simp [encodeAuthority, decode]
  · simp only [acceptedWords, encode, tag, authorized_childAt, nextChild_other _ _ _ _ _ _ _ _ _ _
      n0 n1 n2, d0]
  · simp only [acceptedWords, encode, tag, authorized_childAt, nextChild_other _ _ _ _ _ _ _ _ _ _
      n0 n1 n2, d1]
  · simp only [acceptedWords, encode, tag, authorized_childAt, nextChild_other _ _ _ _ _ _ _ _ _ _
      n0 n1 n2, d2]
  · simp only [acceptedWords, encode, tag, authorized_childAt, nextChild_other _ _ _ _ _ _ _ _ _ _
      n0 n1 n2, d3]
  · simp only [acceptedWords, encode, tag, authorized_memoryAt, decoded_memoryWord2]
    simp [nextMemory, n3, n4]
  · simp only [acceptedWords, encode, tag, authorized_memoryAt, decoded_memoryWord3]
    simp [nextMemory, n3, n4]
  · simp only [acceptedWords, encode, tag, authorized_budget, authorized_parentFrames]
    simp only [nextFrames, n1, n2, Bool.false_eq_true, beq_self_eq_true, ↓reduceIte]
    exact (frames_of command.arg1 (parentFramesW words.frames) command.arg1.toNat
      (decode words).parentFrames rfl (parentFramesW_toNat words)).symm

theorem revoke_refines (words : Words) (canonicalWords : Canonical words = true)
    (command : CommandWords) (tag : command.tag = 0x7601) :
    acceptedWords words command =
      encode (if command.arg0.toNat = parent then { decode words with authority := none, budget := 0 }
        else decode words) := by
  have n0 : ((0x7601 : UInt64) == 0x7001) = false := by decide
  have n1 : ((0x7601 : UInt64) == 0x7101) = false := by decide
  have n2 : ((0x7601 : UInt64) == 0x7201) = false := by decide
  have n3 : ((0x7601 : UInt64) == 0x7301) = false := by decide
  have n4 : ((0x7601 : UInt64) == 0x7401) = false := by decide
  have n5 : ((0x7601 : UInt64) == 0x7501) = false := by decide
  have frames := decoded_frames words canonicalWords
  obtain ⟨d0, d1, d2, d3⟩ := decoded_childWords words
  by_cases isParent : command.arg0 = 2
  · have parentNat : command.arg0.toNat = parent := by rw [isParent]; rfl
    simp only [parentNat, ↓reduceIte]
    apply Words.ext
    · simp only [acceptedWords, encode, tag, n0, Bool.false_eq_true, ↓reduceIte]
      exact UInt64.ofNat_toNat.symm
    · simp only [acceptedWords, encode, tag, n0, n3, Bool.or_false, Bool.false_eq_true,
        ↓reduceIte]
      exact UInt64.ofNat_toNat.symm
    · simp only [acceptedWords, encode, tag, n0, n3, Bool.false_eq_true, ↓reduceIte]
      exact UInt64.ofNat_toNat.symm
    · simp only [acceptedWords, encode, tag, n0, Bool.false_eq_true, ↓reduceIte]
      exact UInt64.ofNat_toNat.symm
    · simp only [acceptedWords, encode, tag, n5, Bool.false_eq_true, ↓reduceIte]
      exact UInt64.ofNat_toNat.symm
    · simp [acceptedWords, encode, tag, n5, isParent, encodeAuthority]
    · simp only [acceptedWords, encode, tag, nextChild_other _ _ _ _ _ _ _ _ _ _ n0 n1 n2]
      exact d0.symm
    · simp only [acceptedWords, encode, tag, nextChild_other _ _ _ _ _ _ _ _ _ _ n0 n1 n2]
      exact d1.symm
    · simp only [acceptedWords, encode, tag, nextChild_other _ _ _ _ _ _ _ _ _ _ n0 n1 n2]
      exact d2.symm
    · simp only [acceptedWords, encode, tag, nextChild_other _ _ _ _ _ _ _ _ _ _ n0 n1 n2]
      exact d3.symm
    · simp only [acceptedWords, encode, tag]
      simp only [nextMemory, n3, n4, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      exact (decoded_memoryWord2 words).symm
    · simp only [acceptedWords, encode, tag]
      simp only [nextMemory, n3, n4, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      exact (decoded_memoryWord3 words).symm
    · simp only [acceptedWords, encode, tag]
      simp only [nextFrames, n1, n2, n5, isParent, Bool.false_eq_true, beq_self_eq_true,
        Bool.and_self, ↓reduceIte]
      have := frames_of 0 (parentFramesW words.frames) 0 (decode words).parentFrames rfl
        (parentFramesW_toNat words)
      simpa using this.symm
  · have notParent : command.arg0.toNat ≠ parent := by
      intro eq; apply isParent; apply UInt64.toNat_inj.1; rw [eq]; rfl
    have notParentBeq : (command.arg0 == 2) = false := by simpa using isParent
    simp only [notParent, ↓reduceIte]
    rw [encode_decode words canonicalWords]
    apply Words.ext
    · simp [acceptedWords, tag, n0]
    · simp [acceptedWords, tag, n0, n3]
    · simp [acceptedWords, tag, n0, n3]
    · simp [acceptedWords, tag, n0]
    · simp [acceptedWords, tag, n5]
    · simp [acceptedWords, tag, n5, notParentBeq]
    · simp [acceptedWords, tag, nextChild_other _ _ _ _ _ _ _ _ _ _ n0 n1 n2]
    · simp [acceptedWords, tag, nextChild_other _ _ _ _ _ _ _ _ _ _ n0 n1 n2]
    · simp [acceptedWords, tag, nextChild_other _ _ _ _ _ _ _ _ _ _ n0 n1 n2]
    · simp [acceptedWords, tag, nextChild_other _ _ _ _ _ _ _ _ _ _ n0 n1 n2]
    · simp [acceptedWords, tag, nextMemory, n3, n4]
    · simp [acceptedWords, tag, nextMemory, n3, n4]
    · simp [acceptedWords, tag, nextFrames, n1, n2, n5, notParentBeq]

/-! ## The refinement -/

theorem codeNext_acceptedWords (words : Words) (command : CommandWords)
    (accepted : codeReply words command = 0x01) :
    codeNext words command = acceptedWords words command :=
  codeNext_accepted words command accepted

/-- The words of an accepted command are the specification's. -/
theorem accepted_refines (words : Words) (command : CommandWords)
    (accepted : codeReply words command = 0x01) :
    codeNext words command = (specStep words command).1 ∧
      codeValue words command = (specStep words command).2.2 := by
  obtain ⟨canonicalWords, operation, result, decoded, stepped, status⟩ :=
    codeReply_accepted words command accepted
  have spec : specStep words command = (encode result.next, result.status, result.value) := by
    simp [specStep, canonicalWords, decoded, stepped]
  rw [spec, codeNext_acceptedWords words command accepted,
    codeValue_accepted words command accepted]
  have acc := step_accepted (decode words) operation result stepped status
  rcases decodeCommand_ok command operation decoded with
    ⟨tag, rights, _, rfl⟩ | ⟨tag, rfl⟩ | ⟨tag, rfl⟩ | ⟨tag, rfl⟩ | ⟨tag, rfl⟩ | ⟨tag, rfl⟩ |
      ⟨tag, rfl⟩
  · cases acc with
    | spawn _ slot _ _ free =>
        obtain ⟨enc, val⟩ := spawn_words words canonicalWords slot free command tag
        refine ⟨?_, by simp only [acceptWith, tag, beq_self_eq_true, ↓reduceIte]; exact val.symm⟩
        simp only [acceptWith]
        rw [enc]
        apply Words.ext <;> simp [acceptedWords, tag, nextMemory, nextFrames]
  · cases acc with
    | grant _ _ slot entry resolved enough =>
        have n0 : ((0x7101 : UInt64) == 0x7001) = false := by decide
        refine ⟨grant_refines words command tag slot entry resolved enough, ?_⟩
        simp only [acceptWith, tag, n0, Bool.false_eq_true, beq_self_eq_true, ↓reduceIte]
        exact UInt64.ofNat_toNat.symm
  · cases acc with
    | terminate _ slot entry resolved =>
        have n0 : ((0x7201 : UInt64) == 0x7001) = false := by decide
        have n1 : ((0x7201 : UInt64) == 0x7101) = false := by decide
        obtain ⟨next, value⟩ := terminate_refines words command tag slot entry resolved
        refine ⟨next, ?_⟩
        simp only [acceptWith, tag, n0, n1, Bool.false_eq_true, beq_self_eq_true, ↓reduceIte]
        exact value
  · cases acc with
    | allocate _ range low =>
        refine ⟨allocate_refines words canonicalWords command tag low range, ?_⟩
        simp [acceptWith, tag]
  · cases acc with
    | release _ _ range low =>
        refine ⟨release_refines words canonicalWords command tag low range, ?_⟩
        simp [acceptWith, tag]
  · simp only [step] at stepped
    obtain ⟨_, _, _, _, eq⟩ := grantAuthorityStep_accepted _ _ _ result stepped status
    subst eq
    refine ⟨grantAuthority_refines words command tag, ?_⟩
    simp only [acceptWith, tag]
    simp [decode]
  · simp only [step, Option.some.injEq] at stepped
    subst stepped
    have n0 : ((0x7601 : UInt64) == 0x7001) = false := by decide
    have n1 : ((0x7601 : UInt64) == 0x7101) = false := by decide
    have n2 : ((0x7601 : UInt64) == 0x7201) = false := by decide
    have n5 : ((0x7601 : UInt64) == 0x7501) = false := by decide
    simp only
    refine ⟨?_, ?_⟩
    · rw [revoke_refines words canonicalWords command tag]
      unfold revokeAuthorityStep
      split <;> rfl
    · simp only [tag, n0, n1, n2, n5, Bool.false_eq_true, ↓reduceIte]
      unfold revokeAuthorityStep
      split <;> rfl

/-- **The generated functions compute the allocator, for every input.**  For
all thirteen state words and five command words, `stepReply`, `stepValue` and
`stepNextWord` return exactly the reply, value and successor words of
`specStep`: decode the words, run `SpawnAllocator.step`, encode the
successor. -/
theorem words_refine (words : Words) (command : CommandWords) :
    codeReply words command = (specStep words command).2.1 ∧
      codeValue words command = (specStep words command).2.2 ∧
      codeNext words command = (specStep words command).1 := by
  refine ⟨codeReply_spec words command, ?_⟩
  by_cases accepted : codeReply words command = 0x01
  · obtain ⟨next, value⟩ := accepted_refines words command accepted
    exact ⟨value, next⟩
  · have value : codeValue words command = 0 := by
      have different : stepReply words.subjectNext words.objectNext words.capabilityNext
          words.controlNext words.authorityNext words.authority words.child0 words.child1
          words.child2 words.child3 words.memory2 words.memory3 words.frames command.tag
          command.arg0 command.arg1 command.arg2 command.arg3 ≠ 0x01 := accepted
      simp [codeValue, stepValue, different]
    rw [value, codeNext_unaccepted words command accepted]
    have reply := codeReply_spec words command
    rw [reply] at accepted
    unfold specStep at accepted ⊢
    by_cases canonicalWords : Canonical words = true
    · simp only [canonicalWords, Bool.true_eq_false, ↓reduceIte] at accepted ⊢
      cases decoded : decodeCommand command with
      | error reason => simp
      | ok operation =>
          rw [decoded] at accepted
          simp only at accepted ⊢
          cases stepped : step (decode words) operation with
          | none => simp
          | some result =>
              rw [stepped] at accepted
              simp only at accepted ⊢
              rw [step_rejected_unchanged _ _ _ stepped accepted,
                step_rejected_value _ _ _ stepped accepted, encode_decode words canonicalWords]
              exact ⟨rfl, rfl⟩
    · simp only [Bool.not_eq_true] at canonicalWords
      simp [canonicalWords]

end LeanOS.SpawnAllocatorWords
