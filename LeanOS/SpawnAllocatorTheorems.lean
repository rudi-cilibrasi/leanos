import LeanOS.SpawnAllocator

/-!
# The spawn allocator's theorems (#575)

General theorems about `LeanOS.SpawnAllocator.step`: they hold for every
record and every command, not for a list of states.

* **Accounting.**  `step_frames_conserved`: the frames of the parent and its
  children never change in number.  `step_valid`: the representation is
  closed under steps (`Bounded`), the parent's memory stays within its frames,
  the children stay within the subject budget, and every recorded generation
  was issued.
* **Rollback.**  `SpawnAllocator.step_rejected_unchanged`.
* **Stale handles.**  `step_retired_forever`, `retired_rejected`,
  `terminate_retires`.
* **Inheritance exactness and confinement at the allocator.**  `spawn_exact`,
  `step_confined`.
* **Exhaustion.**  `spawn_subjects_exhausted`, `spawn_objects_exhausted`,
  `spawn_controls_exhausted`, `spawn_capabilities_exhausted`,
  `spawn_budget_exhausted`, `grant_frames_exhausted`,
  `allocate_frames_exhausted`, `allocate_capabilities_exhausted`,
  `allocate_objects_exhausted`: each counter at its bound is a typed rejection
  with the record unchanged, from any record.
-/
namespace LeanOS.SpawnAllocator

open LeanOS
open LeanOS.FailStop
open LeanOS.SpawnOracle
open LeanOS.SpawnAccountingOracle

set_option linter.unusedSimpArgs false

/-! ## The accepted steps -/

/-- What an accepted step did, command by command. -/
inductive Accepted (state : State) : Command → Step → Prop where
  | spawn (request : SpawnRequest) (slot : Nat)
      (authority : state.authority = some request.spawnWord.toNat)
      (room : state.childCount < state.budget)
      (free : state.freeSlot = some slot)
      (control : controlAvailable state.controlNext = true)
      (subjects : identityExhausted state.subjectNext = false)
      (objects : identityExhausted state.objectNext = false)
      (capabilities : capabilityExhausted state.capabilityNext = false)
      (endpoint : state.resolveEndpoint request.endpointWord = none)
      (rights : Capability.rightsValid .endpoint request.rights = true) :
      Accepted state (.child (.spawn request))
        (acceptWith (spawned state slot) (controlWord slot state.controlNext))
  | grant (control : UInt64) (frames slot : Nat) (entry : ChildRecord)
      (resolved : state.resolveControl control = .ok (slot, entry))
      (enough : frames ≤ state.available) :
      Accepted state (.child (.grantFrames control frames))
        (acceptWith (granted state slot entry frames) (UInt64.ofNat frames))
  | terminate (control : UInt64) (slot : Nat) (entry : ChildRecord)
      (resolved : state.resolveControl control = .ok (slot, entry)) :
      Accepted state (.child (.terminateChild control))
        (acceptWith (terminated state slot entry) (UInt64.ofNat entry.charge))
  | grantAuthority (budget : Nat) (small : budget ≤ childCapacity)
      (covers : state.childCount ≤ budget) (fits : state.authorityNext + 1 < wordBound) :
      Accepted state (.child (.grantAuthority parent budget))
        (acceptWith (authorized state budget) (UInt64.ofNat state.authorityNext))
  | revokeParent :
      Accepted state (.child (.revokeAuthority parent))
        (acceptWith { state with authority := none, budget := 0 } 0)
  | revokeOther (subject : Nat) (other : subject ≠ parent) :
      Accepted state (.child (.revokeAuthority subject)) (acceptWith state 0)
  | allocate (slot : Nat) (range : slot < parentSlots) (low : memoryBase ≤ slot)
      (empty : state.memoryAt slot = none)
      (capabilities : capabilityExhausted state.capabilityNext = false)
      (objects : identityExhausted state.objectNext = false)
      (frames : 0 < state.available) :
      Accepted state (.memory (.allocate slot)) (acceptWith (allocated state slot) 0)
  | release (slot identity : Nat) (range : slot < parentSlots) (low : memoryBase ≤ slot)
      (held : state.memoryAt slot = some identity) :
      Accepted state (.memory (.release slot)) (acceptWith (released state slot) 0)

/-- **Every accepted step is one of the cases of `Accepted`.** -/
theorem step_accepted (state : State) (command : Command) (result : Step)
    (decided : step state command = some result) (accepted : result.status = 0x01) :
    Accepted state command result := by
  rcases command with (request | ⟨control, frames⟩ | control | ⟨subject, budget⟩ | subject) |
    (slot | slot) <;>
    simp only [step, Option.some.injEq] at decided
  · subst decided
    obtain ⟨slot, authority, room, free, control, subjects, objects, capabilities, endpoint, rights,
      eq⟩ := spawnStep_accepted state request accepted
    rw [eq]
    exact .spawn request slot authority room free control subjects objects capabilities endpoint
      rights
  · subst decided
    obtain ⟨slot, entry, resolved, enough, eq⟩ := grantStep_accepted state control frames accepted
    rw [eq]
    exact .grant control frames slot entry resolved enough
  · subst decided
    obtain ⟨slot, entry, resolved, eq⟩ := terminateStep_accepted state control accepted
    rw [eq]
    exact .terminate control slot entry resolved
  · obtain ⟨isParent, small, covers, fits, eq⟩ :=
      grantAuthorityStep_accepted state subject budget result decided accepted
    subst isParent eq
    exact .grantAuthority budget small covers fits
  · subst decided
    unfold revokeAuthorityStep
    by_cases isParent : subject = parent
    · subst isParent
      simp only [↓reduceIte]
      exact .revokeParent
    · simp only [isParent, ↓reduceIte]
      exact .revokeOther subject isParent
  · subst decided
    obtain ⟨range, low, empty, capabilities, objects, frames, eq⟩ :=
      allocateStep_accepted state slot accepted
    rw [eq]
    exact .allocate slot range low empty capabilities objects frames
  · subst decided
    obtain ⟨identity, range, low, held, eq⟩ := releaseStep_accepted state slot accepted
    rw [eq]
    exact .release slot identity range low held

/-- Every step is a rejection that returns the record, or an accepted case. -/
theorem step_cases (state : State) (command : Command) (result : Step)
    (decided : step state command = some result) :
    (result.status ≠ 0x01 ∧ result.next = state) ∨ Accepted state command result := by
  by_cases accepted : result.status = 0x01
  · exact Or.inr (step_accepted state command result decided accepted)
  · exact Or.inl ⟨accepted, step_rejected_unchanged state command result decided accepted⟩

/-! ## Accounting -/

/-- The parent's frames and the frames charged to its children. -/
def State.frames (state : State) : Nat := state.parentFrames + state.chargeSum

theorem spawned_chargeSum (state : State) (slot : Nat) (free : state.freeSlot = some slot) :
    (spawned state slot).chargeSum = state.chargeSum := by
  obtain ⟨inRange, empty⟩ := freeSlot_some free
  have := chargeSum_set (next := spawned state slot) rfl inRange
  simp only [empty, entryCharge, Option.map_none, Option.getD_none, Option.map_some,
    Option.getD_some, Nat.add_zero] at this
  exact this

theorem granted_chargeSum (state : State) (slot : Nat) (entry : ChildRecord) (frames : Nat)
    (found : state.childAt slot = some entry) :
    (granted state slot entry frames).chargeSum = state.chargeSum + frames := by
  obtain ⟨inRange, held⟩ := childAt_some found
  have := chargeSum_set (next := granted state slot entry frames) rfl inRange
  simp only [held, entryCharge, Option.map_some, Option.getD_some] at this
  omega

theorem terminated_chargeSum (state : State) (slot : Nat) (entry : ChildRecord)
    (found : state.childAt slot = some entry) :
    (terminated state slot entry).chargeSum + entry.charge = state.chargeSum := by
  obtain ⟨inRange, held⟩ := childAt_some found
  have := chargeSum_set (next := terminated state slot entry) rfl inRange
  simp only [held, entryCharge, Option.map_some, Option.getD_some, Option.map_none,
    Option.getD_none, Nat.add_zero] at this
  exact this

theorem available_le (state : State) : state.available ≤ state.parentFrames := by
  unfold State.available; omega

/-- **Frames are conserved.**  No step creates or destroys a frame of the
parent's family: a grant moves frames from the parent to a child, and a
termination moves them back. -/
theorem step_frames_conserved (state : State) (command : Command) (result : Step)
    (decided : step state command = some result) : result.next.frames = state.frames := by
  rcases step_cases state command result decided with ⟨_, same⟩ | accepted
  · rw [same]
  cases accepted with
  | spawn request slot _ _ free =>
      simp only [acceptWith, State.frames]
      rw [spawned_chargeSum state slot free]
      rfl
  | grant control frames slot entry resolved enough =>
      simp only [acceptWith, State.frames]
      rw [granted_chargeSum state slot entry frames (resolveControl_ok resolved).2]
      have := available_le state
      simp only [granted]
      omega
  | terminate control slot entry resolved =>
      simp only [acceptWith, State.frames]
      have := terminated_chargeSum state slot entry (resolveControl_ok resolved).2
      simp only [terminated] at this ⊢
      omega
  | grantAuthority => rfl
  | revokeParent => rfl
  | revokeOther => rfl
  | allocate => rfl
  | release => rfl

/-! ## The representation and the invariants are closed under steps -/

/-- The allocator invariant: the representation, the parent's memory within
its frames, the children within the subject budget, and every recorded
generation issued. -/
structure Valid (state : State) : Prop where
  bounded : Bounded state
  memoryWithin : state.memoryUsed ≤ state.parentFrames
  budgetWithin : ∀ generation, state.authority = some generation →
    state.childCount ≤ state.budget
  issued : ∀ entry, some entry ∈ state.children → entry.generation < state.controlNext

theorem identityExhausted_false {next : Nat} (live : identityExhausted next = false) :
    0 < next ∧ next + 1 < wordBound := by
  simp only [identityExhausted, Bool.or_eq_false_iff, decide_eq_false_iff_not, Nat.not_le]
    at live
  unfold LifetimeIssuer.identityReserved LifetimeIssuer.identityRadix at live
  unfold wordBound
  omega

theorem capabilityExhausted_false {next : Nat} (live : capabilityExhausted next = false) :
    0 < next ∧ next < CapabilityHandle.generationReserved := by
  simp only [capabilityExhausted, Bool.or_eq_false_iff, decide_eq_false_iff_not, Nat.not_le]
    at live
  omega

theorem controlAvailable_true {next : Nat} (available : controlAvailable next = true) :
    0 < next ∧ next < CapabilityHandle.generationReserved := by
  simpa [controlAvailable] using available

theorem generationReserved_lt : CapabilityHandle.generationReserved + 2 < wordBound := by
  unfold CapabilityHandle.generationReserved CapabilityHandle.generationRadix wordBound
  decide

theorem mem_set_cases {α : Type} {values : List α} {index : Nat} {value item : α}
    (member : item ∈ values.set index value) : item ∈ values ∨ item = value :=
  List.mem_or_eq_of_mem_set member

theorem memoryAt_none_index {state : State} {slot : Nat} (bounded : Bounded state)
    (range : slot < parentSlots) (low : memoryBase ≤ slot) (empty : state.memoryAt slot = none) :
    ∃ inRange : slot - memoryBase < state.memory.length, state.memory[slot - memoryBase] = none := by
  have inRange : slot - memoryBase < state.memory.length := by
    rw [bounded.memoryLength]
    unfold memoryCapacity parentSlots memoryBase at *
    omega
  refine ⟨inRange, ?_⟩
  unfold State.memoryAt at empty
  simp only [Nat.not_lt.2 low, ↓reduceIte] at empty
  rw [List.getElem?_eq_getElem inRange] at empty
  simpa using empty

theorem spawned_valid (state : State) (slot : Nat) (valid : Valid state)
    (room : state.childCount < state.budget) (free : state.freeSlot = some slot)
    (control : controlAvailable state.controlNext = true)
    (subjects : identityExhausted state.subjectNext = false)
    (objects : identityExhausted state.objectNext = false)
    (capabilities : capabilityExhausted state.capabilityNext = false) :
    Valid (spawned state slot) := by
  obtain ⟨bounded, memoryWithin, budgetWithin, issued⟩ := valid
  obtain ⟨inRange, empty⟩ := freeSlot_some free
  obtain ⟨controlPositive, controlBounded⟩ := controlAvailable_true control
  have subjectFits := (identityExhausted_false subjects).2
  have objectFits := (identityExhausted_false objects).2
  have capabilityBounded := (capabilityExhausted_false capabilities).2
  have reserved := generationReserved_lt
  have count := childCount_set (next := spawned state slot) rfl inRange
  simp only [empty, Option.isSome_none, Option.isSome_some, Bool.false_eq_true, ↓reduceIte]
    at count
  have sum := spawned_chargeSum state slot free
  refine ⟨⟨?_, ?_, ?_, ?_, bounded.authorityPositive, bounded.authorityNext, bounded.authority,
    bounded.budget, ?_, bounded.memoryLength, ?_, bounded.memoryRecords, ?_⟩,
    memoryWithin, ?_, ?_⟩
  · exact subjectFits
  · exact objectFits
  · simp only [spawned]; omega
  · simp only [spawned]; omega
  · simp only [spawned, List.length_set]; exact bounded.childrenLength
  · intro entry member
    rcases mem_set_cases member with old | new
    · exact bounded.childRecords entry old
    · simp only [Option.some.injEq] at new
      subst new
      exact ⟨controlPositive, controlBounded⟩
  · have := bounded.frames
    simp only [spawned] at sum ⊢
    rw [sum]
    exact this
  · intro generation held
    simp only [spawned] at count ⊢
    omega
  · intro entry member
    rcases mem_set_cases member with old | new
    · exact Nat.lt_succ_of_lt (issued entry old)
    · simp only [Option.some.injEq] at new
      subst new
      simp [spawned]

theorem granted_valid (state : State) (slot : Nat) (entry : ChildRecord) (frames : Nat)
    (valid : Valid state) (found : state.childAt slot = some entry)
    (enough : frames ≤ state.available) :
    Valid (granted state slot entry frames) := by
  obtain ⟨bounded, memoryWithin, budgetWithin, issued⟩ := valid
  obtain ⟨inRange, held⟩ := childAt_some found
  have entryMember : some entry ∈ state.children := by
    rw [← held]; exact List.getElem_mem inRange
  have count := childCount_set (next := granted state slot entry frames) rfl inRange
  simp only [held, Option.isSome_some, ↓reduceIte] at count
  have sum := granted_chargeSum state slot entry frames found
  have availableLe : state.available ≤ state.parentFrames - state.memoryUsed := Nat.le_refl _
  refine ⟨⟨bounded.subjectNext, bounded.objectNext, bounded.capabilityNext, bounded.controlNext,
    bounded.authorityPositive, bounded.authorityNext, bounded.authority, bounded.budget, ?_,
    bounded.memoryLength, ?_, bounded.memoryRecords, ?_⟩, ?_, ?_, ?_⟩
  · simp only [granted, List.length_set]; exact bounded.childrenLength
  · intro record member
    rcases mem_set_cases member with old | new
    · exact bounded.childRecords record old
    · simp only [Option.some.injEq] at new
      subst new
      exact bounded.childRecords entry entryMember
  · have := bounded.frames
    simp only [granted_parentFrames]
    rw [sum]
    unfold State.available at enough
    omega
  · simp only [granted_parentFrames, granted_memoryUsed]
    unfold State.available at enough
    omega
  · intro generation authority
    have := budgetWithin generation (by simpa using authority)
    simp only [granted_budget]
    omega
  · intro record member
    rcases mem_set_cases member with old | new
    · exact issued record old
    · simp only [Option.some.injEq] at new
      subst new
      exact issued entry entryMember

theorem terminated_valid (state : State) (slot : Nat) (entry : ChildRecord)
    (valid : Valid state) (found : state.childAt slot = some entry) :
    Valid (terminated state slot entry) := by
  obtain ⟨bounded, memoryWithin, budgetWithin, issued⟩ := valid
  obtain ⟨inRange, held⟩ := childAt_some found
  have count := childCount_set (next := terminated state slot entry) rfl inRange
  simp only [held, Option.isSome_some, Option.isSome_none, ↓reduceIte, Bool.false_eq_true]
    at count
  have sum := terminated_chargeSum state slot entry found
  refine ⟨⟨bounded.subjectNext, bounded.objectNext, bounded.capabilityNext, bounded.controlNext,
    bounded.authorityPositive, bounded.authorityNext, bounded.authority, bounded.budget, ?_,
    bounded.memoryLength, ?_, bounded.memoryRecords, ?_⟩, ?_, ?_, ?_⟩
  · simp only [terminated, List.length_set]; exact bounded.childrenLength
  · intro record member
    rcases mem_set_cases member with old | new
    · exact bounded.childRecords record old
    · cases new
  · have := bounded.frames
    simp only [terminated_parentFrames]
    omega
  · simp only [terminated_parentFrames, terminated_memoryUsed]; omega
  · intro generation authority
    have := budgetWithin generation (by simpa using authority)
    simp only [terminated_budget]
    omega
  · intro record member
    rcases mem_set_cases member with old | new
    · exact issued record old
    · cases new

theorem allocated_valid (state : State) (slot : Nat) (valid : Valid state)
    (range : slot < parentSlots) (low : memoryBase ≤ slot) (empty : state.memoryAt slot = none)
    (capabilities : capabilityExhausted state.capabilityNext = false)
    (objects : identityExhausted state.objectNext = false) (frames : 0 < state.available) :
    Valid (allocated state slot) := by
  obtain ⟨bounded, memoryWithin, budgetWithin, issued⟩ := valid
  obtain ⟨inRange, emptyAt⟩ := memoryAt_none_index bounded range low empty
  have used := memoryUsed_set (next := allocated state slot) rfl inRange
  simp only [emptyAt, Option.isSome_none, Option.isSome_some, Bool.false_eq_true, ↓reduceIte]
    at used
  obtain ⟨capabilityPositive, capabilityBounded⟩ := capabilityExhausted_false capabilities
  have objectFits := (identityExhausted_false objects).2
  have reserved := generationReserved_lt
  refine ⟨⟨bounded.subjectNext, ?_, ?_, bounded.controlNext, bounded.authorityPositive,
    bounded.authorityNext, bounded.authority, bounded.budget, bounded.childrenLength, ?_,
    bounded.childRecords, ?_, bounded.frames⟩, ?_, budgetWithin, issued⟩
  · exact objectFits
  · simp only [allocated]; omega
  · simp only [allocated, List.length_set]; exact bounded.memoryLength
  · intro identity member
    rcases mem_set_cases member with old | new
    · exact bounded.memoryRecords identity old
    · simp only [Option.some.injEq] at new
      subst new
      exact ⟨capabilityPositive, by omega⟩
  · simp only [allocated] at used ⊢
    unfold State.available at frames
    omega

theorem released_valid (state : State) (slot identity : Nat) (valid : Valid state)
    (held : state.memoryAt slot = some identity) : Valid (released state slot) := by
  obtain ⟨bounded, memoryWithin, budgetWithin, issued⟩ := valid
  obtain ⟨_, inRange, heldAt⟩ := memoryAt_some held
  have used := memoryUsed_set (next := released state slot) rfl inRange
  simp only [heldAt, Option.isSome_none, Option.isSome_some, Bool.false_eq_true, ↓reduceIte]
    at used
  refine ⟨⟨bounded.subjectNext, bounded.objectNext, bounded.capabilityNext, bounded.controlNext,
    bounded.authorityPositive, bounded.authorityNext, bounded.authority, bounded.budget,
    bounded.childrenLength, ?_, bounded.childRecords, ?_, bounded.frames⟩, ?_, budgetWithin,
    issued⟩
  · simp only [released, List.length_set]; exact bounded.memoryLength
  · intro record member
    rcases mem_set_cases member with old | new
    · exact bounded.memoryRecords record old
    · cases new
  · simp only [released] at used ⊢
    omega

/-- **The allocator invariant is closed under every step.** -/
theorem step_valid (state : State) (command : Command) (result : Step) (valid : Valid state)
    (decided : step state command = some result) : Valid result.next := by
  rcases step_cases state command result decided with ⟨_, same⟩ | accepted
  · rw [same]; exact valid
  cases accepted with
  | spawn request slot authority room free control subjects objects capabilities =>
      exact spawned_valid state slot valid room free control subjects objects capabilities
  | grant control frames slot entry resolved enough =>
      exact granted_valid state slot entry frames valid (resolveControl_ok resolved).2 enough
  | terminate control slot entry resolved =>
      exact terminated_valid state slot entry valid (resolveControl_ok resolved).2
  | grantAuthority budget small covers fits =>
      obtain ⟨bounded, memoryWithin, _, issued⟩ := valid
      refine ⟨⟨bounded.subjectNext, bounded.objectNext, bounded.capabilityNext,
        bounded.controlNext, Nat.succ_pos _, fits, ?_, small, bounded.childrenLength,
        bounded.memoryLength, bounded.childRecords, bounded.memoryRecords, bounded.frames⟩,
        memoryWithin, fun _ _ => covers, issued⟩
      intro generation held
      simp only [acceptWith, authorized_authority, Option.some.injEq] at held
      subst held
      exact ⟨bounded.authorityPositive, bounded.authorityNext⟩
  | revokeParent =>
      obtain ⟨bounded, memoryWithin, _, issued⟩ := valid
      refine ⟨⟨bounded.subjectNext, bounded.objectNext, bounded.capabilityNext,
        bounded.controlNext, bounded.authorityPositive, bounded.authorityNext, ?_, Nat.zero_le _,
        bounded.childrenLength, bounded.memoryLength, bounded.childRecords,
        bounded.memoryRecords, bounded.frames⟩, memoryWithin, ?_, issued⟩
      · intro generation held; cases held
      · intro generation held; cases held
  | revokeOther => exact valid
  | allocate slot range low empty capabilities objects frames =>
      exact allocated_valid state slot valid range low empty capabilities objects frames
  | release slot identity range low held =>
      exact released_valid state slot identity valid held

/-! ## Stale control words -/

/-- A control word is **retired**: it decodes, its generation was issued, and
its slot holds no entry of that generation. -/
def Retired (state : State) (word : UInt64) : Prop :=
  ∃ handle : CapabilityHandle.Handle, CapabilityHandle.decode word = .ok handle ∧
    handle.identity < state.controlNext ∧
    ∀ entry, state.childAt handle.slot = some entry → entry.generation ≠ handle.identity

/-- A retired word names no child: grant and termination reject it with the
record unchanged. -/
theorem retired_resolve (state : State) (word : UInt64) (retired : Retired state word) :
    state.resolveControl word = .error .stale := by
  obtain ⟨handle, decoded, _, stale⟩ := retired
  unfold State.resolveControl
  rw [decoded]
  simp only
  cases found : state.childAt handle.slot with
  | none => rfl
  | some entry => simp [stale entry found]

theorem retired_rejected (state : State) (word : UInt64) (frames : Nat)
    (retired : Retired state word) :
    grantStep state word frames =
        rejectWith state (frameGrantErrorCode (.control .stale)) ∧
      terminateStep state word = rejectWith state (controlDenialCode .stale) := by
  have resolved := retired_resolve state word retired
  exact ⟨by simp [grantStep, resolved], by simp [terminateStep, resolved]⟩

theorem step_controlNext_mono (state : State) (command : Command) (result : Step)
    (decided : step state command = some result) : state.controlNext ≤ result.next.controlNext := by
  rcases step_cases state command result decided with ⟨_, same⟩ | accepted
  · rw [same]; exact Nat.le_refl _
  cases accepted <;> simp [acceptWith]

/-- **A retired word is retired forever**: every later step, accepted or
rejected, keeps it retired. -/
theorem step_retired_forever (state : State) (command : Command) (result : Step) (word : UInt64)
    (decided : step state command = some result)
    (retired : Retired state word) : Retired result.next word := by
  obtain ⟨handle, decoded, issuedBefore, stale⟩ := retired
  have mono := step_controlNext_mono state command result decided
  refine ⟨handle, decoded, Nat.lt_of_lt_of_le issuedBefore mono, ?_⟩
  rcases step_cases state command result decided with ⟨_, same⟩ | accepted
  · rw [same]; exact stale
  cases accepted with
  | spawn request slot _ _ free =>
      intro entry found
      obtain ⟨inRange, _⟩ := freeSlot_some free
      simp only [acceptWith] at found
      rw [childAt_set (next := spawned state slot) rfl inRange] at found
      split at found
      · simp only [Option.some.injEq] at found
        subst found
        exact Nat.ne_of_gt issuedBefore
      · exact stale entry found
  | grant control frames slot record resolved =>
      intro entry found
      obtain ⟨_, held⟩ := resolveControl_ok resolved
      obtain ⟨inRange, _⟩ := childAt_some held
      simp only [acceptWith] at found
      rw [childAt_set (next := granted state slot record frames) rfl inRange] at found
      split at found
      · next same =>
        simp only [Option.some.injEq] at found
        subst found same
        exact stale record held
      · exact stale entry found
  | terminate control slot record resolved =>
      intro entry found
      obtain ⟨_, held⟩ := resolveControl_ok resolved
      obtain ⟨inRange, _⟩ := childAt_some held
      simp only [acceptWith] at found
      rw [childAt_set (next := terminated state slot record) rfl inRange] at found
      split at found
      · cases found
      · exact stale entry found
  | grantAuthority => exact stale
  | revokeParent => exact stale
  | revokeOther => exact stale
  | allocate => exact stale
  | release => exact stale

/-- **Termination retires its control word.** -/
theorem terminate_retires (state : State) (control : UInt64) (slot : Nat) (entry : ChildRecord)
    (valid : Valid state) (resolved : state.resolveControl control = .ok (slot, entry)) :
    Retired (terminated state slot entry) control := by
  obtain ⟨decoded, held⟩ := resolveControl_ok resolved
  obtain ⟨inRange, heldAt⟩ := childAt_some held
  have member : some entry ∈ state.children := by rw [← heldAt]; exact List.getElem_mem inRange
  refine ⟨{ slot, identity := entry.generation }, decoded, valid.issued entry member, ?_⟩
  intro record found
  rw [childAt_set (next := terminated state slot entry) rfl inRange] at found
  simp at found

/-! ## Inheritance exactness and confinement at the allocator -/

/-- **An accepted spawn records exactly one child.**  The first free slot gets
the fresh generation and charge zero; the value word is its control word; the
subject, object and control counters advance by one and the capability
counter by two (the child's address-space root and its endpoint); every other
entry, the parent's memory, its frames, and its spawn authority are
unchanged. -/
theorem spawn_exact (state : State) (request : SpawnRequest) (result : Step)
    (decided : step state (.child (.spawn request)) = some result) (accepted : result.status = 0x01) :
    ∃ slot, state.freeSlot = some slot ∧
      result.next.childAt slot = some { generation := state.controlNext, charge := 0 } ∧
      result.value = controlWord slot state.controlNext ∧
      (∀ other, other ≠ slot → result.next.childAt other = state.childAt other) ∧
      result.next.subjectNext = state.subjectNext + 1 ∧
      result.next.objectNext = state.objectNext + 1 ∧
      result.next.capabilityNext = state.capabilityNext + 2 ∧
      result.next.controlNext = state.controlNext + 1 ∧
      result.next.memory = state.memory ∧ result.next.parentFrames = state.parentFrames ∧
      result.next.authority = state.authority ∧ result.next.budget = state.budget ∧
      result.next.authorityNext = state.authorityNext := by
  cases step_accepted state _ result decided accepted with
  | spawn _ slot _ _ free =>
      obtain ⟨inRange, _⟩ := freeSlot_some free
      refine ⟨slot, free, ?_, rfl, fun other ne => ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      · simp only [acceptWith]
        rw [childAt_set (next := spawned state slot) rfl inRange]
        simp
      · simp only [acceptWith]
        rw [childAt_set (next := spawned state slot) rfl inRange]
        simp [Ne.symm ne]

/-- **Confinement at the allocator.**  A grant or termination changes only the
entry its control word names, besides the parent's frames; a memory command
and a kernel command change no child entry. -/
theorem step_confined (state : State) (command : Command) (result : Step)
    (decided : step state command = some result) :
    (∀ control frames slot entry, (command = .child (.grantFrames control frames) ∨
        command = .child (.terminateChild control)) →
      state.resolveControl control = .ok (slot, entry) →
      ∀ other, other ≠ slot → result.next.childAt other = state.childAt other) ∧
    (∀ operation, command = .memory operation → result.next.children = state.children) ∧
    (∀ subject budget, (command = .child (.grantAuthority subject budget) ∨
        command = .child (.revokeAuthority subject)) →
      result.next.children = state.children ∧ result.next.memory = state.memory ∧
        result.next.parentFrames = state.parentFrames) := by
  rcases step_cases state command result decided with ⟨_, same⟩ | accepted
  · rw [same]; exact ⟨fun _ _ _ _ _ _ _ _ => rfl, fun _ _ => rfl, fun _ _ _ => ⟨rfl, rfl, rfl⟩⟩
  cases accepted with
  | spawn =>
      refine ⟨?_, ?_, ?_⟩
      · intro _ _ _ _ is; rcases is with is | is <;> cases is
      · intro _ is; cases is
      · intro _ _ is; rcases is with is | is <;> cases is
  | grant control frames slot entry resolved =>
      refine ⟨?_, ?_, ?_⟩
      · intro control' frames' slot' entry' is resolved' other ne
        rcases is with is | is
        · simp only [Command.child.injEq, ChildOperation.grantFrames.injEq] at is
          obtain ⟨rfl, rfl⟩ := is
          rw [resolved] at resolved'
          simp only [Except.ok.injEq, Prod.mk.injEq] at resolved'
          obtain ⟨rfl, rfl⟩ := resolved'
          obtain ⟨inRange, _⟩ := childAt_some (resolveControl_ok resolved).2
          simp only [acceptWith]
          rw [childAt_set (next := granted state slot entry frames) rfl inRange]
          simp [Ne.symm ne]
        · cases is
      · intro _ is; cases is
      · intro _ _ is; rcases is with is | is <;> cases is
  | terminate control slot entry resolved =>
      refine ⟨?_, ?_, ?_⟩
      · intro control' frames' slot' entry' is resolved' other ne
        rcases is with is | is
        · cases is
        · simp only [Command.child.injEq, ChildOperation.terminateChild.injEq] at is
          subst is
          rw [resolved] at resolved'
          simp only [Except.ok.injEq, Prod.mk.injEq] at resolved'
          obtain ⟨rfl, rfl⟩ := resolved'
          obtain ⟨inRange, _⟩ := childAt_some (resolveControl_ok resolved).2
          simp only [acceptWith]
          rw [childAt_set (next := terminated state slot entry) rfl inRange]
          simp [Ne.symm ne]
      · intro _ is; cases is
      · intro _ _ is; rcases is with is | is <;> cases is
  | grantAuthority =>
      refine ⟨?_, ?_, fun _ _ _ => ⟨rfl, rfl, rfl⟩⟩
      · intro _ _ _ _ is; rcases is with is | is <;> cases is
      · intro _ is; cases is
  | revokeParent =>
      refine ⟨?_, ?_, fun _ _ _ => ⟨rfl, rfl, rfl⟩⟩
      · intro _ _ _ _ is; rcases is with is | is <;> cases is
      · intro _ is; cases is
  | revokeOther =>
      exact ⟨fun _ _ _ _ _ _ _ _ => rfl, fun _ _ => rfl, fun _ _ _ => ⟨rfl, rfl, rfl⟩⟩
  | allocate =>
      refine ⟨?_, fun _ _ => rfl, ?_⟩
      · intro _ _ _ _ is; rcases is with is | is <;> cases is
      · intro _ _ is; rcases is with is | is <;> cases is
  | release =>
      refine ⟨?_, fun _ _ => rfl, ?_⟩
      · intro _ _ _ _ is; rcases is with is | is <;> cases is
      · intro _ _ is; rcases is with is | is <;> cases is

/-! ## Exhaustion, from any record -/

/-- The prefix of a spawn that reaches the counters: the parent presents its
current spawn generation, it is within its subject budget, and a slot is
free. -/
structure SpawnReaches (state : State) (request : SpawnRequest) (slot : Nat) : Prop where
  authority : state.authority = some request.spawnWord.toNat
  room : state.childCount < state.budget
  free : state.freeSlot = some slot

theorem spawn_budget_exhausted (state : State) (request : SpawnRequest)
    (authority : state.authority = some request.spawnWord.toNat)
    (full : state.budget ≤ state.childCount) :
    spawnStep state request = rejectWith state (childSpawnErrorCode .subjectBudgetExhausted) := by
  simp [spawnStep, authority, full]

theorem spawn_controls_exhausted (state : State) (request : SpawnRequest) (slot : Nat)
    (reaches : SpawnReaches state request slot) (exhausted : controlAvailable state.controlNext = false) :
    spawnStep state request =
      rejectWith state (childSpawnErrorCode .controlGenerationExhausted) := by
  simp [spawnStep, reaches.authority, Nat.not_le.2 reaches.room, reaches.free, exhausted]

theorem spawn_subjects_exhausted (state : State) (request : SpawnRequest) (slot : Nat)
    (reaches : SpawnReaches state request slot) (control : controlAvailable state.controlNext = true)
    (exhausted : identityExhausted state.subjectNext = true) :
    spawnStep state request = rejectWith state (childSpawnErrorCode (.spawn .identityExhausted)) := by
  simp [spawnStep, reaches.authority, Nat.not_le.2 reaches.room, reaches.free, control, exhausted]

theorem spawn_objects_exhausted (state : State) (request : SpawnRequest) (slot : Nat)
    (reaches : SpawnReaches state request slot) (control : controlAvailable state.controlNext = true)
    (subjects : identityExhausted state.subjectNext = false)
    (exhausted : identityExhausted state.objectNext = true) :
    spawnStep state request =
      rejectWith state (childSpawnErrorCode (.spawn .addressSpaceIdentityExhausted)) := by
  simp [spawnStep, reaches.authority, Nat.not_le.2 reaches.room, reaches.free, control, subjects,
    exhausted]

theorem spawn_capabilities_exhausted (state : State) (request : SpawnRequest) (slot : Nat)
    (reaches : SpawnReaches state request slot) (control : controlAvailable state.controlNext = true)
    (subjects : identityExhausted state.subjectNext = false)
    (objects : identityExhausted state.objectNext = false)
    (exhausted : capabilityExhausted state.capabilityNext = true) :
    spawnStep state request =
      rejectWith state
        (childSpawnErrorCode (.spawn (.addressSpaceRejected .generationExhausted))) := by
  simp [spawnStep, reaches.authority, Nat.not_le.2 reaches.room, reaches.free, control, subjects,
    objects, exhausted]

theorem grant_frames_exhausted (state : State) (control : UInt64) (frames slot : Nat)
    (entry : ChildRecord) (resolved : state.resolveControl control = .ok (slot, entry))
    (short : state.available < frames) :
    grantStep state control frames =
      rejectWith state (frameGrantErrorCode .frameBudgetExhausted) := by
  simp [grantStep, resolved, short]

theorem allocate_capabilities_exhausted (state : State) (slot : Nat)
    (range : slot < parentSlots) (exhausted : capabilityExhausted state.capabilityNext = true) :
    allocateStep state slot = rejectWith state (memoryCode .capabilityIdentityExhausted) := by
  have notReserved : ¬CapabilityHandle.slotReserved ≤ slot := by
    unfold CapabilityHandle.slotReserved CapabilityHandle.slotRadix parentSlots at *
    omega
  simp [allocateStep, notReserved, Nat.not_le.2 range, exhausted]

theorem allocate_objects_exhausted (state : State) (slot : Nat)
    (range : slot < parentSlots) (low : memoryBase ≤ slot) (empty : state.memoryAt slot = none)
    (capabilities : capabilityExhausted state.capabilityNext = false)
    (exhausted : identityExhausted state.objectNext = true) :
    allocateStep state slot = rejectWith state (memoryCode .objectIdentityExhausted) := by
  have notReserved : ¬CapabilityHandle.slotReserved ≤ slot := by
    unfold CapabilityHandle.slotReserved CapabilityHandle.slotRadix parentSlots at *
    omega
  simp [allocateStep, notReserved, Nat.not_le.2 range, capabilities, Nat.not_lt.2 low, empty,
    exhausted]

theorem allocate_frames_exhausted (state : State) (slot : Nat)
    (range : slot < parentSlots) (low : memoryBase ≤ slot) (empty : state.memoryAt slot = none)
    (capabilities : capabilityExhausted state.capabilityNext = false)
    (objects : identityExhausted state.objectNext = false) (none : state.available = 0) :
    allocateStep state slot = rejectWith state (memoryCode .frameBudgetExhausted) := by
  have notReserved : ¬CapabilityHandle.slotReserved ≤ slot := by
    unfold CapabilityHandle.slotReserved CapabilityHandle.slotRadix parentSlots at *
    omega
  simp [allocateStep, notReserved, Nat.not_le.2 range, capabilities, Nat.not_lt.2 low, empty,
    objects, none]

end LeanOS.SpawnAllocator
