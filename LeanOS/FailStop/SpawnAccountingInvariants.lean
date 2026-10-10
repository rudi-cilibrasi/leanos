import LeanOS.FailStop.SpawnAccounting

/-!
# Fail-stop composite: the spawn accounting invariant

`ChildAccountingWellFormed` is the accounting invariant of the public spawn
family (`ChildOperation`):

- every child-table entry lies in the table, has a generation below the
  never-reused counter, names a child other than the parent and an issued
  subject, and **the child's whole entitlement (its own frames plus what it
  charged to its own children) is within the charge its parent recorded**;
- no child appears in two entries;
- a subject never issued has an empty child table;
- **a parent holding a spawn capability has at most its subject budget of
  children** (`childCount`).

`ChildOperation.apply_preserves` and `CompositeStep.childAccounting` prove
that every step keeps it, together with the combined resource invariant
`ResourceRuntimeWellFormed`.

The frame arithmetic is exact: a frame grant moves frames from the parent to
the child and its charge (`grantFrames_limits`), and a child termination
moves every frame of the child back to the parent (`releaseChild_limits`).
-/
namespace LeanOS.FailStop

open LeanOS
set_option linter.unusedSimpArgs false

/-! ## Frame limits as counts -/

theorem budgetLimit_countP (state : CompositeState) (subject : Nat) :
    state.budgetLimit subject = state.virtualMemory.memory.allocator.frames.countP
      (fun frame => decide (state.frameBudgets.commitment frame = some subject)) := by
  unfold CompositeState.budgetLimit FrameBudget.limit FrameBudget.budgetFrames
    CompositeState.budgetState
  exact List.countP_eq_length_filter.symm

/-- Moving frames from `parent` to `child` moves exactly their count. -/
theorem countP_move (frames : List Nat) (commit : Nat → Option Nat) (moved : Nat → Bool)
    (parent child : Nat) (ne : child ≠ parent)
    (fromParent : ∀ frame, frame ∈ frames → moved frame = true → commit frame = some parent) :
    frames.countP (fun frame => decide
        ((if moved frame = true then some child else commit frame) = some parent)) +
        frames.countP moved =
        frames.countP (fun frame => decide (commit frame = some parent)) ∧
      frames.countP (fun frame => decide
        ((if moved frame = true then some child else commit frame) = some child)) =
        frames.countP (fun frame => decide (commit frame = some child)) +
          frames.countP moved ∧
      ∀ other, other ≠ parent → other ≠ child →
        frames.countP (fun frame => decide
          ((if moved frame = true then some child else commit frame) = some other)) =
          frames.countP (fun frame => decide (commit frame = some other)) := by
  induction frames with
  | nil => simp
  | cons head rest ih =>
      obtain ⟨ih1, ih2, ih3⟩ :=
        ih (fun frame member => fromParent frame (List.mem_cons_of_mem _ member))
      by_cases hmoved : moved head = true
      · have hcommit := fromParent head List.mem_cons_self hmoved
        refine ⟨?_, ?_, fun other ne1 ne2 => ?_⟩
        · simp only [List.countP_cons, Option.some.injEq, ne, Ne.symm ne, ↓reduceIte, decide_true,
            decide_false, Bool.false_eq_true, hmoved, hcommit]; omega
        · simp only [List.countP_cons, Option.some.injEq, ne, Ne.symm ne, ↓reduceIte, decide_true,
            decide_false, Bool.false_eq_true, hmoved, hcommit]; omega
        · have := ih3 other ne1 ne2
          simp only [List.countP_cons, Option.some.injEq, ne, Ne.symm ne, ↓reduceIte, decide_true,
              decide_false, Bool.false_eq_true, hmoved, hcommit, Ne.symm ne1, Ne.symm ne2]; omega
      · have unmoved : moved head = false := by simpa using hmoved
        refine ⟨?_, ?_, fun other ne1 ne2 => ?_⟩
        · simp only [List.countP_cons, Option.some.injEq, ne, Ne.symm ne, ↓reduceIte, decide_true,
            decide_false, Bool.false_eq_true, unmoved]; omega
        · simp only [List.countP_cons, Option.some.injEq, ne, Ne.symm ne, ↓reduceIte, decide_true,
            decide_false, Bool.false_eq_true, unmoved]; omega
        · have := ih3 other ne1 ne2
          simp only [List.countP_cons, Option.some.injEq, ne, Ne.symm ne, ↓reduceIte, decide_true,
              decide_false, Bool.false_eq_true, unmoved]; omega

/-- Returning a child's frames to its parent moves exactly the child's
count. -/
theorem countP_return (frames : List Nat) (commit : Nat → Option Nat) (parent child : Nat)
    (ne : child ≠ parent) :
    frames.countP (fun frame => decide
        ((if commit frame = some child then some parent else commit frame) = some parent)) =
        frames.countP (fun frame => decide (commit frame = some parent)) +
          frames.countP (fun frame => decide (commit frame = some child)) ∧
      frames.countP (fun frame => decide
        ((if commit frame = some child then some parent else commit frame) = some child)) = 0 ∧
      ∀ other, other ≠ parent → other ≠ child →
        frames.countP (fun frame => decide
          ((if commit frame = some child then some parent else commit frame) = some other)) =
          frames.countP (fun frame => decide (commit frame = some other)) := by
  induction frames with
  | nil => simp
  | cons head rest ih =>
      obtain ⟨ih1, ih2, ih3⟩ := ih
      by_cases hchild : commit head = some child
      · refine ⟨?_, ?_, fun other ne1 ne2 => ?_⟩
        · simp only [List.countP_cons, Option.some.injEq, ne, Ne.symm ne, ↓reduceIte, decide_true,
            decide_false, Bool.false_eq_true, hchild]; omega
        · simp only [List.countP_cons, Option.some.injEq, ne, Ne.symm ne, ↓reduceIte, decide_true,
            decide_false, Bool.false_eq_true, hchild]; omega
        · have := ih3 other ne1 ne2
          simp only [List.countP_cons, Option.some.injEq, ne, Ne.symm ne, ↓reduceIte, decide_true,
              decide_false, Bool.false_eq_true, hchild, Ne.symm ne1, Ne.symm ne2]; omega
      · refine ⟨?_, ?_, fun other ne1 ne2 => ?_⟩
        · by_cases hparent : commit head = some parent
          · simp only [List.countP_cons, Option.some.injEq, ne, Ne.symm ne, ↓reduceIte, decide_true,
              decide_false, Bool.false_eq_true, hchild, hparent]; omega
          · simp only [List.countP_cons, Option.some.injEq, ne, Ne.symm ne, ↓reduceIte, decide_true,
              decide_false, Bool.false_eq_true, hchild, hparent]; omega
        · simp only [List.countP_cons, Option.some.injEq, ne, Ne.symm ne, ↓reduceIte, decide_true,
            decide_false, Bool.false_eq_true, hchild]; omega
        · have := ih3 other ne1 ne2
          simp only [List.countP_cons, Option.some.injEq, ne, Ne.symm ne, ↓reduceIte, decide_true,
              decide_false, Bool.false_eq_true, hchild]; omega

/-! ## Child-table updates -/

/-- A child-table change at one slot changes the parent's count and charge by
exactly that slot's change, and no other parent's. -/
theorem childTable_update (before after : CompositeState) (parent slot : Nat)
    (inRange : slot < childSlots)
    (same : ∀ candidate candidateSlot, ¬(candidate = parent ∧ candidateSlot = slot) →
      after.spawn.children candidate candidateSlot = before.spawn.children candidate candidateSlot) :
    childCharge after parent + entryCharge (before.spawn.children parent slot) =
        childCharge before parent + entryCharge (after.spawn.children parent slot) ∧
      childCount after parent + entryCount (before.spawn.children parent slot) =
        childCount before parent + entryCount (after.spawn.children parent slot) ∧
      ∀ other, other ≠ parent →
        childCharge after other = childCharge before other ∧
          childCount after other = childCount before other := by
  refine ⟨?_, ?_, fun other ne => ⟨?_, ?_⟩⟩
  · exact slotSum_update (fun i => entryCharge (before.spawn.children parent i))
      (fun i => entryCharge (after.spawn.children parent i)) slot inRange
      fun candidateSlot ne' => by
        simp only [same parent candidateSlot (fun h => ne' h.2)]
  · exact slotSum_update (fun i => entryCount (before.spawn.children parent i))
      (fun i => entryCount (after.spawn.children parent i)) slot inRange
      fun candidateSlot ne' => by
        simp only [same parent candidateSlot (fun h => ne' h.2)]
  · exact slotSum_congr (fun i => entryCharge (before.spawn.children other i))
      (fun i => entryCharge (after.spawn.children other i)) fun candidateSlot => by
        simp only [same other candidateSlot (fun h => ne h.1)]
  · exact slotSum_congr (fun i => entryCount (before.spawn.children other i))
      (fun i => entryCount (after.spawn.children other i)) fun candidateSlot => by
        simp only [same other candidateSlot (fun h => ne h.1)]

theorem childTable_congr {before after : CompositeState}
    (same : after.spawn.children = before.spawn.children) (parent : Nat) :
    childCharge after parent = childCharge before parent ∧
      childCount after parent = childCount before parent := by
  simp [childCharge, childCount, same]

theorem slotSum_mono (f g : Nat → Nat) (le : ∀ slot, f slot ≤ g slot) : slotSum f ≤ slotSum g := by
  simp only [slotSum]
  induction List.range childSlots with
  | nil => simp
  | cons head rest ih => simp only [List.map_cons, List.sum_cons]; have := le head; omega

theorem list_sum_zero (values : List Nat) : (values.map fun _ => 0).sum = 0 := by
  induction values with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem slotSum_zero : slotSum (fun _ => 0) = 0 := list_sum_zero _

/-! ## The accounting invariant -/

/-- Some entry of some child table names `subject`. -/
def ChargedChild (state : CompositeState) (subject : Nat) : Prop :=
  ∃ parent slot entry, state.spawn.children parent slot = some entry ∧ entry.child = subject

structure ChildAccountingWellFormed (state : CompositeState) : Prop where
  entries : ∀ parent slot entry, state.spawn.children parent slot = some entry →
    slot < childSlots ∧ entry.generation < state.spawn.nextChildGeneration ∧
      entry.child ≠ parent ∧ state.lifecycle.issuedSubjects entry.child = true ∧
      entitlement state entry.child ≤ entry.charge
  unique : ∀ parent slot entry parent' slot' entry',
    state.spawn.children parent slot = some entry →
    state.spawn.children parent' slot' = some entry' →
    entry.child = entry'.child → parent = parent' ∧ slot = slot'
  fresh : ∀ subject slot, state.lifecycle.issuedSubjects subject = false →
    state.spawn.children subject slot = none
  budget : ∀ parent capability, state.spawn.authority parent = some capability →
    childCount state parent ≤ capability.subjectBudget

/-- An empty child table satisfies the invariant. -/
theorem childAccounting_of_empty (state : CompositeState)
    (empty : ∀ parent slot, state.spawn.children parent slot = none) :
    ChildAccountingWellFormed state := by
  have zero : ∀ parent, childCount state parent = 0 := by
    intro parent
    have := slotSum_congr (fun _ => 0) (fun slot => entryCount (state.spawn.children parent slot))
      (fun slot => by simp [entryCount, empty])
    rw [slotSum_zero] at this
    exact this
  refine ⟨fun parent slot entry found => ?_, fun parent slot entry _ _ _ found => ?_,
    fun subject slot _ => empty subject slot, fun parent capability _ => ?_⟩
  · rw [empty] at found; cases found
  · rw [empty] at found; cases found
  · rw [zero]; exact Nat.zero_le _

/-- What the invariant implies for a parent: its own usage plus every
child's frame limit is within its entitlement. -/
def childLimits (state : CompositeState) (parent : Nat) : Nat :=
  slotSum fun slot => ((state.spawn.children parent slot).map
    fun entry => state.budgetLimit entry.child).getD 0

/-- **Children's budgets plus the parent's usage never exceed the parent's
entitlement.**  The frames committed to the parent's children together with
the frames the parent itself uses are within the frames committed to the
parent plus what it charged to its children. -/
theorem usage_add_childLimits_le (state : CompositeState) (accounting : ChildAccountingWellFormed state)
    (parent : Nat) :
    state.budgetUsage parent + childLimits state parent ≤ entitlement state parent := by
  have usage := (budget_conservation state).1 parent
  have children : childLimits state parent ≤ childCharge state parent := by
    apply slotSum_mono
    intro slot
    cases found : state.spawn.children parent slot with
    | none => simp
    | some entry =>
        have := (accounting.entries parent slot entry found).2.2.2.2
        simp only [Option.map_some, Option.getD_some, entryCharge]
        simp only [entitlement] at this
        omega
  simp only [entitlement]
  omega

/-! ## Resource invariant for new commitments -/

theorem frameBudgets_unsupported :
    authoritativeInvariants.all (fun invariant => !invariant.support.contains .frameBudgets) =
      true := by
  decide

/-- Replacing the frame commitment keeps the combined invariant when the new
commitment satisfies the budget agreement. -/
theorem withFrameBudgets_resourceRuntimeWellFormed {state : CompositeState}
    (holds : ResourceRuntimeWellFormed state) (budgets : FrameBudgets)
    (agreement : ∀ frame subject, budgets.commitment frame = some subject →
      frame ∈ state.virtualMemory.memory.allocator.frames ∧
        ¬FrameAllocator.IsReserved state.virtualMemory.memory.allocator frame ∧
        state.lifecycle.issuedSubjects subject = true) :
    ResourceRuntimeWellFormed { state with frameBudgets := budgets } := by
  obtain ⟨authoritative, resource⟩ := holds
  refine ⟨?_, ?_⟩
  · rw [authoritativeRuntimeWellFormed_iff_all] at authoritative ⊢
    intro invariant member
    apply invariant.dependsOn state _ _ (authoritative invariant member)
    intro projection supported
    cases projection <;> try rfl
    have := List.all_eq_true.1 frameBudgets_unsupported invariant member
    simp only [decide_eq_true_eq] at supported
    simp [supported] at this
  · rw [resourceWellFormed_iff] at resource ⊢
    obtain ⟨issuersHold, agreementHold, _, scrubHold⟩ := resource
    exact ⟨issuersHold, agreementHold, agreement, scrubHold⟩

/-! ## Facts about the stages -/

theorem spawnAuthorize_live {state : CompositeState} {word : UInt64}
    (authorized : spawnAuthorize state word = none) :
    state.capabilities.subjects (spawnParent state) = true ∧
      ∃ capability, state.spawn.authority (spawnParent state) = some capability := by
  unfold spawnAuthorize at authorized
  split at authorized
  · next live =>
    refine ⟨live, ?_⟩
    split at authorized
    · cases authorized
    · next capability found => exact ⟨capability, found⟩
  · cases authorized

theorem live_issued {state : CompositeState} (holds : RuntimeWellFormed state) {subject : Nat}
    (live : state.capabilities.subjects subject = true) :
    state.lifecycle.issuedSubjects subject = true := by
  rw [holds.1.2.2.2.1] at live
  exact holds.2.2.1.1 subject live

theorem subjectBudget_of_authority {state : CompositeState} {parent : Nat}
    {capability : SpawnCapability} (found : state.spawn.authority parent = some capability) :
    subjectBudget state parent = capability.subjectBudget := by
  simp [subjectBudget, found]

/-- The #489 spawn keeps the child table, its generation counter, and the
spawn-authority table. -/
theorem spawn_childTable (state : CompositeState) (request : SpawnRequest)
    (child addressSpace : Nat)
    (spawned : (spawn state request).result = .spawned child addressSpace) :
    (spawn state request).state.spawn.children = state.spawn.children ∧
      (spawn state request).state.spawn.nextChildGeneration = state.spawn.nextChildGeneration ∧
      (spawn state request).state.spawn.authority = state.spawn.authority := by
  obtain ⟨_, issued, _, _, _, _, _, _, _, stateEq⟩ :=
    spawn_spawned_stages state request child addressSpace spawned
  obtain ⟨_, _, created, eq⟩ := issueSubject_issued state child issued
  rw [stateEq]
  simp [recordSpawn, installCopiedCapabilities, spawnSpaced, installCreatedAddressSpace, eq,
    applyOperation, created, installCreatedSubject]

/-- The #489 spawn keeps every subject's frame limit. -/
theorem spawn_budgetLimit (state : CompositeState) (request : SpawnRequest)
    (child addressSpace : Nat)
    (spawned : (spawn state request).result = .spawned child addressSpace) (subject : Nat) :
    (spawn state request).state.budgetLimit subject = state.budgetLimit subject := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, budgets, _, allocator, _, _⟩ :=
    spawn_keeps state request child addressSpace spawned
  exact (budget_eq_of_allocator budgets allocator subject).2


theorem childCharge_empty {state : CompositeState} {parent : Nat}
    (empty : ∀ slot, state.spawn.children parent slot = none) : childCharge state parent = 0 := by
  have := slotSum_congr (fun _ => 0) (fun slot => entryCharge (state.spawn.children parent slot))
    (fun slot => by simp [entryCharge, empty])
  rw [slotSum_zero] at this
  exact this

/-! ## Composite steps keep the accounting -/

/-- No issued-lifecycle, authoritative, or invalidation step writes the spawn
projection. -/
theorem CompositeStep.apply_spawn (state : CompositeState) (step : CompositeStep) :
    (step.apply state).spawn = state.spawn := by
  obtain ⟨lifecycle, authoritative, invalidation⟩ := footprints_unread_spawn
  cases step with
  | lifecycle operation =>
      exact lifecycleGate_frames state operation .spawn
        (operation.footprint.unread_is_untouched .spawn (lifecycle operation))
  | authoritative operation =>
      exact authoritativeGate_frames state operation .spawn
        (operation.footprint.unread_is_untouched .spawn (authoritative operation))
  | invalidation operation =>
      exact InvalidationOperation.apply_frames state operation .spawn
        (operation.footprint.unread_is_untouched .spawn (invalidation operation))

/-- A transition that keeps the spawn record, the frame commitment, and the
allocator, and only grows the subject history, keeps the accounting
invariant and every entitlement. -/
theorem childAccounting_of_kept {before after : CompositeState}
    (accounting : ChildAccountingWellFormed before)
    (spawnSame : after.spawn = before.spawn)
    (budgets : after.frameBudgets = before.frameBudgets)
    (allocator : after.virtualMemory.memory.allocator = before.virtualMemory.memory.allocator)
    (grows : ∀ subject, before.lifecycle.issuedSubjects subject = true →
      after.lifecycle.issuedSubjects subject = true) :
    ChildAccountingWellFormed after ∧
      ∀ subject, entitlement after subject = entitlement before subject := by
  have children : after.spawn.children = before.spawn.children := by rw [spawnSame]
  have same : ∀ subject, entitlement after subject = entitlement before subject := by
    intro subject
    simp only [entitlement, (budget_eq_of_allocator budgets allocator subject).2,
      (childTable_congr children subject).1]
  refine ⟨⟨fun parent slot entry found => ?_,
    fun parent slot entry parent' slot' entry' f1 f2 eq => ?_,
    fun subject slot unissued => ?_, fun parent capability found => ?_⟩, same⟩
  · rw [children] at found
    obtain ⟨inRange, generation, ne, issued, bound⟩ := accounting.entries parent slot entry found
    refine ⟨inRange, by rw [spawnSame]; exact generation, ne, grows _ issued, ?_⟩
    rw [same]; exact bound
  · rw [children] at f1 f2
    exact accounting.unique parent slot entry parent' slot' entry' f1 f2 eq
  · rw [children]
    apply accounting.fresh
    cases h : before.lifecycle.issuedSubjects subject with
    | false => rfl
    | true => rw [grows subject h] at unissued; cases unissued
  · rw [spawnSame] at found
    rw [(childTable_congr children parent).2]
    exact accounting.budget parent capability found

/-- **Every composite step keeps the accounting.**  An admissible issued
lifecycle, authoritative, or invalidation step keeps the accounting
invariant and every subject's entitlement. -/
theorem CompositeStep.childAccounting (state : CompositeState) (step : CompositeStep)
    (holds : ResourceRuntimeWellFormed state) (admissible : step.Admissible state)
    (accounting : ChildAccountingWellFormed state) :
    ChildAccountingWellFormed (step.apply state) ∧
      ∀ subject, entitlement (step.apply state) subject = entitlement state subject := by
  have grows := step.admissible_grows state holds admissible
  exact childAccounting_of_kept accounting (step.apply_spawn state) grows.1 grows.2.2.1.2.2.1
    grows.2.2.2

/-! ## Charged spawn keeps the accounting -/

theorem spawnCharged_preserves (state : CompositeState) (request : SpawnRequest)
    (running : state.execution.mode = .running) (holds : ResourceRuntimeWellFormed state)
    (accounting : ChildAccountingWellFormed state) :
    ResourceRuntimeWellFormed (spawnCharged state request).state ∧
      ChildAccountingWellFormed (spawnCharged state request).state ∧
      ∀ subject, entitlement (spawnCharged state request).state subject =
        entitlement state subject := by
  rcases spawnCharged_result state request with ⟨child, addressSpace, control, result⟩ |
    ⟨reason, result⟩
  · obtain ⟨slot, authorized, room, free, _, spawned, _, stateEq⟩ :=
      spawnCharged_spawned state request child addressSpace control result
    rw [stateEq]
    have runtime := holds.1.left
    obtain ⟨parentLive, capability, capabilityFound⟩ := spawnAuthorize_live authorized
    have parentIssued := live_issued runtime parentLive
    obtain ⟨inRange, slotFree⟩ := freeChildSlot_some free
    obtain ⟨childrenEq, nextEq, authorityEq⟩ :=
      spawn_childTable state request child addressSpace spawned
    have ne := (spawn_parent_ne_child state request child addressSpace runtime spawned).1
    have unissued := (spawn_fresh_identity state request child addressSpace holds spawned).2.1
    have issuedEq :=
      (spawn_keeps state request child addressSpace spawned).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    have limitZero : state.budgetLimit child = 0 := by
      have := (spawn_child_starts_empty state request child addressSpace holds spawned).1
      rwa [spawn_budgetLimit state request child addressSpace spawned] at this
    have postChildren : ∀ candidate candidateSlot,
        (installChild (spawn state request).state (spawnParent state) slot child).spawn.children
          candidate candidateSlot =
        if candidate = spawnParent state ∧ candidateSlot = slot then
          some { child, generation := state.spawn.nextChildGeneration, charge := 0 }
        else state.spawn.children candidate candidateSlot := by
      intro candidate candidateSlot
      simp only [installChild, childrenEq, nextEq]
    have postNext :
        (installChild (spawn state request).state (spawnParent state) slot
          child).spawn.nextChildGeneration = state.spawn.nextChildGeneration + 1 := by
      simp only [installChild, nextEq]
    have postAuthority :
        (installChild (spawn state request).state (spawnParent state) slot child).spawn.authority =
          state.spawn.authority := by
      simp only [installChild, authorityEq]
    have postIssued :
        (installChild (spawn state request).state (spawnParent state) slot
          child).lifecycle.issuedSubjects =
          SubjectLifecycle.setBool state.lifecycle.issuedSubjects child true := issuedEq
    have postLimit : ∀ subject,
        (installChild (spawn state request).state (spawnParent state) slot child).budgetLimit
          subject = state.budgetLimit subject :=
      fun subject => spawn_budgetLimit state request child addressSpace spawned subject
    have resourcePost : ResourceRuntimeWellFormed
        (installChild (spawn state request).state (spawnParent state) slot child) :=
      withSpawn_resourceRuntimeWellFormed
        (spawn_preserves_resourceRuntimeWellFormed state request running holds) _
    generalize installChild (spawn state request).state (spawnParent state) slot child = post
      at postChildren postNext postAuthority postIssued postLimit resourcePost ⊢
    have update := childTable_update state post (spawnParent state) slot inRange
      (fun candidate candidateSlot ne' => by rw [postChildren]; simp [ne'])
    have newSlot : post.spawn.children (spawnParent state) slot =
        some { child, generation := state.spawn.nextChildGeneration, charge := 0 } := by
      rw [postChildren]; simp
    rw [newSlot, slotFree] at update
    obtain ⟨chargeParent, countParent, others⟩ := update
    simp only [entryCharge, entryCount, Option.map_some, Option.getD_some, Option.map_none,
      Option.getD_none, Option.isSome_some, Option.isSome_none, ↓reduceIte,
      Bool.false_eq_true] at chargeParent countParent
    have chargeSame : ∀ subject, childCharge post subject = childCharge state subject := by
      intro subject
      by_cases h : subject = spawnParent state
      · rw [h]; exact Nat.add_right_cancel chargeParent
      · exact (others subject h).1
    have entitlementSame : ∀ subject, entitlement post subject = entitlement state subject := by
      intro subject
      simp only [entitlement, postLimit, chargeSame]
    have issuedGrows : ∀ subject, state.lifecycle.issuedSubjects subject = true →
        post.lifecycle.issuedSubjects subject = true := by
      intro subject h
      rw [postIssued]; simp only [SubjectLifecycle.setBool]; split <;> simp_all
    have childEmpty : ∀ candidateSlot, state.spawn.children child candidateSlot = none :=
      fun candidateSlot => accounting.fresh child candidateSlot unissued
    have entitlementChild : entitlement state child = 0 := by
      simp only [entitlement, limitZero, childCharge_empty childEmpty]
    have oldNotChild : ∀ parent candidateSlot entry,
        state.spawn.children parent candidateSlot = some entry → entry.child ≠ child := by
      intro parent candidateSlot entry found same
      have issuedEntry := (accounting.entries parent candidateSlot entry found).2.2.2.1
      rw [same] at issuedEntry
      exact absurd (issuedEntry.symm.trans unissued) (by decide)
    refine ⟨?_, ⟨fun parent candidateSlot entry found => ?_,
      fun parent candidateSlot entry parent' candidateSlot' entry' f1 f2 eq => ?_,
      fun subject candidateSlot unissuedPost => ?_, fun parent cap found => ?_⟩,
      entitlementSame⟩
    · exact resourcePost
    · rw [postChildren] at found
      split at found
      · next h =>
        obtain ⟨rfl, rfl⟩ := h
        simp only [Option.some.injEq] at found
        subst found
        refine ⟨inRange, by simp only [postNext]; omega, Ne.symm ne, ?_, ?_⟩
        · rw [postIssued]; simp [SubjectLifecycle.setBool]
        · rw [entitlementSame, entitlementChild]; exact Nat.zero_le _
      · obtain ⟨slotBound, generation, entryNe, issued, bound⟩ :=
          accounting.entries parent candidateSlot entry found
        exact ⟨slotBound, by rw [postNext]; omega, entryNe, issuedGrows _ issued,
          by rw [entitlementSame]; exact bound⟩
    · rw [postChildren] at f1 f2
      split at f1 <;> split at f2
      · next h1 h2 => exact ⟨h1.1.trans h2.1.symm, h1.2.trans h2.2.symm⟩
      · simp only [Option.some.injEq] at f1
        subst f1
        exact absurd eq.symm (oldNotChild _ _ _ f2)
      · simp only [Option.some.injEq] at f2
        subst f2
        exact absurd eq (oldNotChild _ _ _ f1)
      · exact accounting.unique _ _ _ _ _ _ f1 f2 eq
    · rw [postChildren]
      have subjectUnissued : state.lifecycle.issuedSubjects subject = false := by
        cases h : state.lifecycle.issuedSubjects subject with
        | false => rfl
        | true => rw [issuedGrows subject h] at unissuedPost; cases unissuedPost
      have notParent : subject ≠ spawnParent state := by
        intro same; rw [same, parentIssued] at subjectUnissued; cases subjectUnissued
      simp only [notParent, false_and, ↓reduceIte]
      exact accounting.fresh subject candidateSlot subjectUnissued
    · rw [postAuthority] at found
      by_cases h : parent = spawnParent state
      · subst h
        rw [capabilityFound] at found
        simp only [Option.some.injEq] at found
        subst found
        rw [subjectBudget_of_authority capabilityFound] at room
        omega
      · rw [(others parent h).2]
        exact accounting.budget parent cap found
  · rw [spawnCharged_rejected_unchanged state request _ result]
    exact ⟨holds, accounting, fun _ => rfl⟩

/-! ## Frame grants keep the accounting -/

theorem mem_availableFrames {state : CompositeState} {parent frame : Nat}
    (member : frame ∈ availableFrames state parent) :
    frame ∈ state.virtualMemory.memory.allocator.frames ∧
      state.frameBudgets.commitment frame = some parent ∧
      state.virtualMemory.memory.allocator.status frame = .free := by
  simp only [availableFrames, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at member
  exact ⟨member.1, member.2.1, member.2.2⟩

/-- **A frame grant moves frames, it never creates them.**  The frames moved
were free frames committed to the parent; the parent's limit drops by
exactly their count, the child's grows by exactly their count, and every
other subject's limit is unchanged. -/
theorem grantFrames_limits (state : CompositeState) (parent child : Nat) (moved : List Nat)
    (ne : child ≠ parent)
    (fromParent : ∀ frame, frame ∈ moved → frame ∈ availableFrames state parent) :
    let after := { state with frameBudgets := moveFrames state.frameBudgets moved child }
    after.budgetLimit parent + movedCount state moved = state.budgetLimit parent ∧
      after.budgetLimit child = state.budgetLimit child + movedCount state moved ∧
      ∀ other, other ≠ parent → other ≠ child →
        after.budgetLimit other = state.budgetLimit other := by
  intro after
  have source : ∀ frame, frame ∈ state.virtualMemory.memory.allocator.frames →
      moved.contains frame = true → state.frameBudgets.commitment frame = some parent := by
    intro frame _ contained
    exact (mem_availableFrames (fromParent frame (by simpa using contained))).2.1
  obtain ⟨parentEq, childEq, otherEq⟩ := countP_move state.virtualMemory.memory.allocator.frames
    state.frameBudgets.commitment moved.contains parent child ne source
  refine ⟨?_, ?_, fun other ne1 ne2 => ?_⟩
  · rw [budgetLimit_countP, budgetLimit_countP]; exact parentEq
  · rw [budgetLimit_countP, budgetLimit_countP]; exact childEq
  · rw [budgetLimit_countP, budgetLimit_countP]; exact otherEq other ne1 ne2

theorem grantFrames_preserves (state : CompositeState) (word : UInt64) (frames : Nat)
    (holds : ResourceRuntimeWellFormed state) (accounting : ChildAccountingWellFormed state) :
    ResourceRuntimeWellFormed (grantFrames state word frames).state ∧
      ChildAccountingWellFormed (grantFrames state word frames).state ∧
      ∀ subject, entitlement (grantFrames state word frames).state subject ≤
        entitlement state subject ∨
        ∃ parent slot entry, state.spawn.children parent slot = some entry ∧
          entry.child = subject := by
  rcases grantFrames_result state word frames with ⟨child, moved, result⟩ | ⟨reason, result⟩
  · obtain ⟨slot, entry, resolved, childEq, childLive, _, movedEq, stateEq⟩ :=
      grantFrames_granted state word frames child moved result
    obtain ⟨parentLive, _, found⟩ := resolveControl_ok resolved
    obtain ⟨inRange, _, entryNe, _, entryBound⟩ :=
      accounting.entries (spawnParent state) slot entry found
    rw [childEq] at entryNe entryBound
    have runtime := holds.1.left
    have childIssued := live_issued runtime childLive
    have source : ∀ frame,
        frame ∈ grantedFrames state (spawnParent state) frames →
          frame ∈ availableFrames state (spawnParent state) :=
      fun frame member => List.mem_of_mem_take (by simpa [grantedFrames] using member)
    obtain ⟨limitParent, limitChild, limitOther⟩ :=
      grantFrames_limits state (spawnParent state) child _ entryNe source
    rw [← movedEq] at limitParent limitChild
    have resourcePost : ResourceRuntimeWellFormed (grantFrames state word frames).state := by
      rw [stateEq]
      apply withFrameBudgets_resourceRuntimeWellFormed
        (withSpawn_resourceRuntimeWellFormed holds _)
      intro frame subject committed
      simp only [moveFrames] at committed
      split at committed
      · next contained =>
        simp only [Option.some.injEq] at committed
        subst committed
        obtain ⟨member, _, free⟩ := mem_availableFrames (source frame (by simpa using contained))
        refine ⟨member, ?_, childIssued⟩
        simp [FrameAllocator.IsReserved, free]
      · exact ((resourceWellFormed_iff state).1 holds.2).2.2.1 frame subject committed
    rw [stateEq] at resourcePost ⊢
    generalize hpost : ({ setChildEntry state (spawnParent state) slot
          (some (chargeEntry entry moved)) with
        frameBudgets := moveFrames state.frameBudgets
          (grantedFrames state (spawnParent state) frames) child } : CompositeState) =
      post at resourcePost
    have postChildren : ∀ candidate candidateSlot, post.spawn.children candidate candidateSlot =
        if candidate = spawnParent state ∧ candidateSlot = slot then
          some (chargeEntry entry moved)
        else state.spawn.children candidate candidateSlot := by
      intro candidate candidateSlot; rw [← hpost]; rfl
    have postSpawn : post.spawn.nextChildGeneration = state.spawn.nextChildGeneration ∧
        post.spawn.authority = state.spawn.authority := by
      rw [← hpost]; exact ⟨rfl, rfl⟩
    have postIssued : post.lifecycle.issuedSubjects = state.lifecycle.issuedSubjects := by
      rw [← hpost]; rfl
    have postLimitParent : post.budgetLimit (spawnParent state) + moved =
        state.budgetLimit (spawnParent state) := by rw [← hpost]; exact limitParent
    have postLimitChild : post.budgetLimit child = state.budgetLimit child + moved := by
      rw [← hpost]; exact limitChild
    have postLimitOther : ∀ other, other ≠ spawnParent state → other ≠ child →
        post.budgetLimit other = state.budgetLimit other := by
      intro other ne1 ne2; rw [← hpost]; exact limitOther other ne1 ne2
    clear hpost
    have update := childTable_update state post (spawnParent state) slot inRange
      (fun candidate candidateSlot ne' => by rw [postChildren]; simp [ne'])
    have newSlot : post.spawn.children (spawnParent state) slot =
        some (chargeEntry entry moved) := by
      rw [postChildren]; simp
    rw [newSlot, found] at update
    obtain ⟨chargeParent, countParent, others⟩ := update
    simp only [entryCharge, entryCount, Option.map_some, Option.getD_some,
      Option.isSome_some, ↓reduceIte, chargeEntry] at chargeParent countParent
    have entitlementParent : entitlement post (spawnParent state) =
        entitlement state (spawnParent state) := by
      simp only [entitlement]; omega
    have entitlementChild : entitlement post child = entitlement state child + moved := by
      simp only [entitlement, postLimitChild, (others child entryNe).1]; omega
    have entitlementOther : ∀ other, other ≠ spawnParent state → other ≠ child →
        entitlement post other = entitlement state other := by
      intro other ne1 ne2
      simp only [entitlement, postLimitOther other ne1 ne2, (others other ne1).1]
    have countSame : ∀ subject, childCount post subject = childCount state subject := by
      intro subject
      by_cases h : subject = spawnParent state
      · rw [h]; exact Nat.add_right_cancel countParent
      · exact (others subject h).2
    -- every entry of the post-state comes from an entry of the pre-state with the same child
    have backward : ∀ parent candidateSlot entry',
        post.spawn.children parent candidateSlot = some entry' →
          ∃ old, state.spawn.children parent candidateSlot = some old ∧ old.child = entry'.child ∧
            old.generation = entry'.generation ∧
            (¬(parent = spawnParent state ∧ candidateSlot = slot) → old = entry') := by
      intro parent candidateSlot entry' found'
      rw [postChildren] at found'
      split at found'
      · next h =>
        obtain ⟨rfl, rfl⟩ := h
        simp only [Option.some.injEq] at found'
        subst found'
        exact ⟨entry, found, rfl, rfl, fun h => absurd ⟨rfl, rfl⟩ h⟩
      · next h => exact ⟨entry', found', rfl, rfl, fun _ => rfl⟩
    refine ⟨resourcePost, ⟨fun parent candidateSlot entry' found' => ?_,
      fun parent candidateSlot entry' parent' candidateSlot' entry'' f1 f2 eq => ?_,
      fun subject candidateSlot unissued => ?_, fun parent cap found' => ?_⟩, fun subject => ?_⟩
    · obtain ⟨old, oldFound, oldChild, oldGeneration, oldSame⟩ :=
        backward parent candidateSlot entry' found'
      obtain ⟨slotBound, generation, oldNe, issued, bound⟩ :=
        accounting.entries parent candidateSlot old oldFound
      refine ⟨slotBound, by rw [postSpawn.1, ← oldGeneration]; exact generation,
        by rw [← oldChild]; exact oldNe, by rw [postIssued, ← oldChild]; exact issued, ?_⟩
      by_cases here : parent = spawnParent state ∧ candidateSlot = slot
      · obtain ⟨rfl, rfl⟩ := here
        rw [newSlot] at found'
        simp only [Option.some.injEq] at found'
        subst found'
        simp only [chargeEntry, childEq, entitlementChild]
        omega
      · have same := oldSame here
        subst same
        by_cases isParent : old.child = spawnParent state
        · rw [isParent, entitlementParent, ← isParent]; exact bound
        · have notChild : old.child ≠ child := by
            intro h
            have := accounting.unique _ _ _ _ _ _ oldFound found (by rw [h, childEq])
            exact here this
          rw [entitlementOther _ isParent notChild]; exact bound
    · obtain ⟨old1, f1', c1, _, _⟩ := backward _ _ _ f1
      obtain ⟨old2, f2', c2, _, _⟩ := backward _ _ _ f2
      exact accounting.unique _ _ _ _ _ _ f1' f2' (by rw [c1, c2, eq])
    · rw [postChildren]
      rw [postIssued] at unissued
      have notParent : ¬(subject = spawnParent state ∧ candidateSlot = slot) := by
        rintro ⟨rfl, rfl⟩
        rw [accounting.fresh _ _ unissued] at found; cases found
      simp only [notParent, ↓reduceIte]
      exact accounting.fresh subject candidateSlot unissued
    · rw [postSpawn.2] at found'
      rw [countSame]
      exact accounting.budget parent cap found'
    · by_cases isChild : subject = child
      · exact Or.inr ⟨spawnParent state, slot, entry, found, isChild ▸ childEq⟩
      · left
        by_cases isParent : subject = spawnParent state
        · rw [isParent, entitlementParent]; exact Nat.le_refl _
        · rw [entitlementOther subject isParent isChild]; exact Nat.le_refl _
  · rw [grantFrames_rejected_unchanged state word frames _ result]
    exact ⟨holds, accounting, fun _ => Or.inl (Nat.le_refl _)⟩

/-! ## Child termination keeps the accounting -/

/-! ### Reclaiming the child's memory -/

theorem reclaimable_facts {state : CompositeState} {child frame : Nat}
    (reclaim : reclaimable state child frame = true) :
    state.frameBudgets.commitment frame = some child ∧
      ∃ object, state.virtualMemory.memory.allocator.status frame = .owned object ∧
        state.capabilities.objects object = false := by
  simp only [reclaimable, Bool.and_eq_true, beq_iff_eq] at reclaim
  refine ⟨reclaim.1, ?_⟩
  have owned := reclaim.2
  split at owned
  · next object found => exact ⟨object, found, by simpa using owned⟩
  · cases owned

/-- A frame owned by a live object is never reclaimed. -/
theorem not_reclaimable_of_live {state : CompositeState} {child frame object : Nat}
    (owned : state.virtualMemory.memory.allocator.status frame = .owned object)
    (live : state.capabilities.objects object = true) :
    reclaimable state child frame = false := by
  cases reclaim : reclaimable state child frame with
  | false => rfl
  | true =>
      obtain ⟨_, other, owned', dead⟩ := reclaimable_facts reclaim
      rw [owned] at owned'
      cases owned'
      rw [live] at dead; cases dead

/-- **Reclaiming keeps the combined invariant.**  Only frames owned by dead
objects are freed, so no mapping, capability, or unwritten lifetime loses its
frame. -/
theorem reclaimChildFrames_preserves (state : CompositeState) (child : Nat)
    (holds : ResourceRuntimeWellFormed state) :
    ResourceRuntimeWellFormed (reclaimChildFrames state child) := by
  obtain ⟨⟨runtime, deferred, publication⟩, resource⟩ := holds
  obtain ⟨hcoherent, hexecution, hlifecycle, hcapabilities, hvirtual, hipc,
    hscheduler, hpreemption, hresumable, htransfers, hhalted, _hlivePlan,
    hblockingCoherent, hdevices⟩ := runtime
  obtain ⟨hexecutionCoherent, hschedulerCoherent, hpreemptionCoherent,
    hcapabilitiesCoherent, hvirtualCapabilitiesCoherent, hipcVirtualCoherent,
    hipcCapabilitiesCoherent, hresumableSchedulerCoherent,
    hresumableVirtualCoherent, htransfersCoherent, hauthorityCoherent,
    hdeadMailbox, hliveSender⟩ := hcoherent
  have vmCaps : state.virtualMemory.memory.capabilities = state.capabilities :=
    hvirtualCapabilitiesCoherent.trans hcapabilitiesCoherent.symm
  let vm' := reclaimedVirtualMemory state child
  have vmDef : vm' = reclaimedVirtualMemory state child := rfl
  -- A bound object whose frame it owns keeps both after reclaiming, when live.
  have keepLive : ∀ object frame, state.virtualMemory.memory.binding object = some frame →
      FrameAllocator.IsOwnedBy state.virtualMemory.memory.allocator frame object →
      state.capabilities.objects object = true →
      vm'.memory.binding object = some frame ∧
        FrameAllocator.IsOwnedBy vm'.memory.allocator frame object := by
    intro object frame bound owned live
    have keep := not_reclaimable_of_live (child := child) owned live
    refine ⟨by simp [vmDef, reclaimedVirtualMemory, bound, keep], ?_⟩
    simp only [vmDef, reclaimedVirtualMemory, FrameAllocator.IsOwnedBy, keep,
      Bool.false_eq_true, ↓reduceIte]
    exact owned
  have hvirtual' : VirtualMapping.LifecycleWellFormed vm' := by
    obtain ⟨⟨hownerLive, hmappings⟩, hcaps, haddressSpaces, hownedAddressSpaces⟩ := hvirtual
    refine ⟨⟨hownerLive, ?_⟩, hcaps, haddressSpaces, hownedAddressSpaces⟩
    intro space page mapping held
    obtain ⟨subject, frame, howner, hperm, hbinding, hframe, hread, hwrite⟩ :=
      hmappings space page mapping held
    have live : state.capabilities.objects mapping.object = true := by
      have permits : mapping.permissions.read = true ∨ mapping.permissions.write = true := by
        simp only [VirtualMapping.Permissions.nonempty, Bool.or_eq_true] at hperm
        exact hperm
      rcases permits with readable | writable
      · obtain ⟨_, capability, heldCap, sameObject, _⟩ := hread readable
        have := (hcapabilities.1 _ _ _ (by rw [← vmCaps]; exact heldCap)).2.1
        rw [sameObject] at this; exact this
      · obtain ⟨_, capability, heldCap, sameObject, _⟩ := hwrite writable
        have := (hcapabilities.1 _ _ _ (by rw [← vmCaps]; exact heldCap)).2.1
        rw [sameObject] at this; exact this
    obtain ⟨bound', owned'⟩ := keepLive _ _ hbinding hframe live
    exact ⟨subject, frame, howner, hperm, bound', owned', hread, hwrite⟩
  have hresumable' : ResumablePreemption.WellFormed
      { state.resumable with
        translations := { state.resumable.translations with virtual := vm' } } := by
    obtain ⟨hsched, hcapacity, hunique, hvalid, habsent, hreadyAgree, htranslation, hagree,
      hkindsAgree, htlb⟩ := hresumable
    refine ⟨hsched, hcapacity, hunique, hvalid, habsent, hreadyAgree, ?_, ?_, hkindsAgree, htlb⟩
    · have owner := htranslation.1
      rw [hresumableVirtualCoherent] at owner
      exact ⟨by simpa [vmDef, reclaimedVirtualMemory] using owner, htranslation.2⟩
    · have caps := hagree.1
      rw [hresumableVirtualCoherent] at caps
      exact ⟨by simpa [vmDef, reclaimedVirtualMemory] using caps, hvirtual'⟩
  refine ⟨⟨⟨?_, ?_, hlifecycle, hcapabilities, hvirtual', ⟨hvirtual', hipc.2⟩, hscheduler,
    hpreemption, hresumable', htransfers, hhalted, by simp [reclaimChildFrames],
    hblockingCoherent, hdevices⟩, deferred, publication⟩, ?_⟩
  · refine ⟨hexecutionCoherent, hschedulerCoherent, hpreemptionCoherent, hcapabilitiesCoherent,
      by simpa [reclaimChildFrames, reclaimedVirtualMemory] using hvirtualCapabilitiesCoherent,
      rfl, hipcCapabilitiesCoherent, hresumableSchedulerCoherent, rfl, htransfersCoherent,
      hauthorityCoherent, hdeadMailbox, hliveSender⟩
  · obtain ⟨hcore, _, hmode⟩ := hexecution
    exact ⟨hcore, by simp [reclaimChildFrames], hmode⟩
  · obtain ⟨issuersHold, agreementHold, budgetHold, scrubHold⟩ :=
      (resourceWellFormed_iff state).1 resource
    rw [resourceWellFormed_iff]
    refine ⟨issuersHold, ?_, ?_, ?_⟩
    · simpa [issuerAgreementInvariant, reclaimChildFrames, reclaimedVirtualMemory,
        CompositeState.lifecycleRuntime, BoundedLifecycle.issuedObject] using agreementHold
    · intro frame subject committed
      obtain ⟨member, unreserved, issued⟩ := budgetHold frame subject committed
      refine ⟨member, ?_, issued⟩
      show ¬FrameAllocator.IsReserved vm'.memory.allocator frame
      simp only [vmDef, reclaimedVirtualMemory, FrameAllocator.IsReserved]
      split
      · simp
      · exact unreserved
    · intro object frame bound unwritten
      change vm'.memory.binding object = some frame at bound
      simp only [vmDef, reclaimedVirtualMemory] at bound
      cases boundOld : state.virtualMemory.memory.binding object with
      | none => simp [boundOld] at bound
      | some oldFrame =>
          simp only [boundOld] at bound
          split at bound
          · cases bound
          · next keep =>
            have same : oldFrame = frame := by simpa using bound
            subst same
            obtain ⟨owned, initial⟩ := scrubHold object oldFrame boundOld unwritten
            refine ⟨?_, ?_⟩
            · show FrameAllocator.IsOwnedBy vm'.memory.allocator oldFrame object
              simp only [vmDef, reclaimedVirtualMemory, FrameAllocator.IsOwnedBy]
              simp only [Bool.not_eq_true] at keep
              simp only [keep, Bool.false_eq_true, ↓reduceIte]
              exact owned
            · intro offset inFrame
              show (if reclaimable state child oldFrame = true ∧ offset < FrameScrub.frameBytes then
                FrameScrub.initialByte else state.scrub.bytes oldFrame offset) = _
              simp only [Bool.not_eq_true] at keep
              simp only [keep, Bool.false_eq_true, false_and, ↓reduceIte]
              exact initial offset inFrame

/-- **Reclaiming frees the child's dead memory.**  Every frame committed to
the child that backs a dead object is free, its object's binding is gone, and
it holds only initial bytes; the commitment and the frame list are kept. -/
theorem reclaimChildFrames_reclaims (state : CompositeState) (child frame object : Nat)
    (committed : state.frameBudgets.commitment frame = some child)
    (owned : state.virtualMemory.memory.allocator.status frame = .owned object)
    (dead : state.capabilities.objects object = false) :
    (reclaimChildFrames state child).virtualMemory.memory.allocator.status frame = .free ∧
      ((reclaimChildFrames state child).virtualMemory.memory.binding object = none ∨
        state.virtualMemory.memory.binding object ≠ some frame) ∧
      (∀ offset, offset < FrameScrub.frameBytes →
        (reclaimChildFrames state child).scrub.bytes frame offset = FrameScrub.initialByte) ∧
      (reclaimChildFrames state child).frameBudgets = state.frameBudgets ∧
      (reclaimChildFrames state child).virtualMemory.memory.allocator.frames =
        state.virtualMemory.memory.allocator.frames := by
  have reclaim : reclaimable state child frame = true := by
    simp [reclaimable, committed, owned, dead]
  refine ⟨by simp [reclaimChildFrames, reclaimedVirtualMemory, reclaim], ?_, ?_, rfl, rfl⟩
  · by_cases bound : state.virtualMemory.memory.binding object = some frame
    · left; simp [reclaimChildFrames, reclaimedVirtualMemory, bound, reclaim]
    · right; exact bound
  · intro offset inFrame
    simp [reclaimChildFrames, reclaim, inFrame]

/-- **Returning a child's frames.**  Every frame committed to the child is
committed to the parent: the parent's limit grows by exactly the child's, the
child's becomes zero, and every other subject's is unchanged. -/
theorem releaseChild_limits (state : CompositeState) (parent slot child : Nat)
    (ne : child ≠ parent) :
    (releaseChild state parent slot child).budgetLimit parent =
        state.budgetLimit parent + state.budgetLimit child ∧
      (releaseChild state parent slot child).budgetLimit child = 0 ∧
      ∀ other, other ≠ parent → other ≠ child →
        (releaseChild state parent slot child).budgetLimit other = state.budgetLimit other := by
  obtain ⟨parentEq, childEq, otherEq⟩ := countP_return state.virtualMemory.memory.allocator.frames
    state.frameBudgets.commitment parent child ne
  refine ⟨?_, ?_, fun other ne1 ne2 => ?_⟩
  · rw [budgetLimit_countP, budgetLimit_countP, budgetLimit_countP]; exact parentEq
  · rw [budgetLimit_countP]; exact childEq
  · rw [budgetLimit_countP, budgetLimit_countP]; exact otherEq other ne1 ne2

/-- The composite termination of a child keeps the combined invariant, every
resource history, and the spawn record. -/
theorem terminatedChild_facts (state : CompositeState) (child : Nat)
    (holds : ResourceRuntimeWellFormed state) :
    ResourceRuntimeWellFormed (terminatedChild state child) ∧
      ResourceHistoryAgrees state (terminatedChild state child) ∧
      (terminatedChild state child).spawn = state.spawn := by
  have notCreate : ∀ subject, (AuthoritativeOperation.ordinary (.terminateSubject child)) ≠
      .ordinary (.createSubject subject) := by
    intro subject h; cases h
  exact ⟨authoritativeGate_preserves_resourceRuntimeWellFormed state _ notCreate holds,
    authoritativeGate_historyAgrees state _ holds.1 notCreate,
    authoritativeGate_frames state _ .spawn
      ((AuthoritativeOperation.ordinary (.terminateSubject child)).footprint.unread_is_untouched
        .spawn (footprints_unread_spawn.2.1 _))⟩

theorem terminateChild_preserves (state : CompositeState) (word : UInt64)
    (holds : ResourceRuntimeWellFormed state) (accounting : ChildAccountingWellFormed state) :
    ResourceRuntimeWellFormed (terminateChild state word).state ∧
      ChildAccountingWellFormed (terminateChild state word).state ∧
      ∀ subject, entitlement (terminateChild state word).state subject ≤
        entitlement state subject ∨
        ∃ parent slot entry, state.spawn.children parent slot = some entry ∧
          entry.child = subject := by
  rcases terminateChild_result state word with ⟨child, returned, result⟩ | ⟨reason, result⟩
  · obtain ⟨slot, entry, resolved, childEq, _, stateEq⟩ :=
      terminateChild_terminated state word child returned result
    obtain ⟨parentLive, _, found⟩ := resolveControl_ok resolved
    obtain ⟨inRange, _, entryNe, _, entryBound⟩ :=
      accounting.entries (spawnParent state) slot entry found
    rw [childEq] at entryNe entryBound
    have parentIssued := live_issued holds.1.left parentLive
    obtain ⟨holdsT, agreesT, spawnT⟩ := terminatedChild_facts state child holds
    obtain ⟨_, budgetsT, _, issuedT, _, _, allocatorT, _⟩ := agreesT
    have limitsT : ∀ subject, (terminatedChild state child).budgetLimit subject =
        state.budgetLimit subject :=
      fun subject => (budget_eq_of_allocator budgetsT allocatorT subject).2
    obtain ⟨limitParent, limitChild, limitOther⟩ :=
      releaseChild_limits (terminatedChild state child) (spawnParent state) slot child entryNe
    rw [limitsT, limitsT] at limitParent
    have resourcePost : ResourceRuntimeWellFormed
        (releaseChild (terminatedChild state child) (spawnParent state) slot child) := by
      have holdsR := reclaimChildFrames_preserves (terminatedChild state child) child holdsT
      have spawned := withSpawn_resourceRuntimeWellFormed holdsR
        { (terminatedChild state child).spawn with
          children := fun candidate candidateSlot =>
            if candidate = spawnParent state ∧ candidateSlot = slot then none
            else (terminatedChild state child).spawn.children candidate candidateSlot
          parent := fun candidate => if candidate = child then none
            else (terminatedChild state child).spawn.parent candidate
          addressSpace := fun candidate => if candidate = child then none
            else (terminatedChild state child).spawn.addressSpace candidate }
      apply withFrameBudgets_resourceRuntimeWellFormed spawned
      intro frame subject committed
      simp only [returnFrames] at committed
      have agreement := ((resourceWellFormed_iff _).1 holdsR.2).2.2.1
      split at committed
      · next fromChild =>
        simp only [Option.some.injEq] at committed
        subst committed
        obtain ⟨member, reserved, _⟩ := agreement frame child fromChild
        refine ⟨member, reserved, ?_⟩
        show (terminatedChild state child).lifecycle.issuedSubjects (spawnParent state) = true
        rw [issuedT]; exact parentIssued
      · exact agreement frame subject committed
    rw [stateEq]
    generalize hpost : releaseChild (terminatedChild state child) (spawnParent state) slot child =
      post at resourcePost limitParent limitChild limitOther
    have postChildren : ∀ candidate candidateSlot, post.spawn.children candidate candidateSlot =
        if candidate = spawnParent state ∧ candidateSlot = slot then none
        else state.spawn.children candidate candidateSlot := by
      intro candidate candidateSlot; rw [← hpost]; simp only [releaseChild, spawnT]
    have postSpawn : post.spawn.nextChildGeneration = state.spawn.nextChildGeneration ∧
        post.spawn.authority = state.spawn.authority := by
      rw [← hpost]; simp [releaseChild, spawnT]
    have postIssued : post.lifecycle.issuedSubjects = state.lifecycle.issuedSubjects := by
      rw [← hpost]; exact issuedT
    clear hpost
    have update := childTable_update state post (spawnParent state) slot inRange
      (fun candidate candidateSlot ne' => by rw [postChildren]; simp [ne'])
    have cleared : post.spawn.children (spawnParent state) slot = none := by
      rw [postChildren]; simp
    rw [cleared, found] at update
    obtain ⟨chargeParent, countParent, others⟩ := update
    simp only [entryCharge, entryCount, Option.map_some, Option.getD_some, Option.map_none,
      Option.getD_none, Option.isSome_some, Option.isSome_none, ↓reduceIte,
      Bool.false_eq_true] at chargeParent countParent
    have childWithin : state.budgetLimit child ≤ entry.charge := by
      simp only [entitlement] at entryBound; omega
    have entitlementParent : entitlement post (spawnParent state) ≤
        entitlement state (spawnParent state) := by
      simp only [entitlement]; omega
    have entitlementOther : ∀ other, other ≠ spawnParent state → other ≠ child →
        entitlement post other = entitlement state other := by
      intro other ne1 ne2
      simp only [entitlement, limitOther other ne1 ne2, limitsT, (others other ne1).1]
    have forward : ∀ parent candidateSlot entry',
        post.spawn.children parent candidateSlot = some entry' →
          ¬(parent = spawnParent state ∧ candidateSlot = slot) ∧
            state.spawn.children parent candidateSlot = some entry' := by
      intro parent candidateSlot entry' found'
      rw [postChildren] at found'
      split at found'
      · cases found'
      · next h => exact ⟨h, found'⟩
    refine ⟨resourcePost, ⟨fun parent candidateSlot entry' found' => ?_,
      fun parent candidateSlot entry' parent' candidateSlot' entry'' f1 f2 eq => ?_,
      fun subject candidateSlot unissued => ?_, fun parent cap found' => ?_⟩, fun subject => ?_⟩
    · obtain ⟨here, oldFound⟩ := forward parent candidateSlot entry' found'
      obtain ⟨slotBound, generation, oldNe, issued, bound⟩ :=
        accounting.entries parent candidateSlot entry' oldFound
      refine ⟨slotBound, by rw [postSpawn.1]; exact generation, oldNe,
        by rw [postIssued]; exact issued, ?_⟩
      have notChild : entry'.child ≠ child := by
        intro h
        exact here (accounting.unique _ _ _ _ _ _ oldFound found (by rw [h, childEq]))
      by_cases isParent : entry'.child = spawnParent state
      · rw [isParent] at bound ⊢; omega
      · rw [entitlementOther _ isParent notChild]; exact bound
    · exact accounting.unique _ _ _ _ _ _ (forward _ _ _ f1).2 (forward _ _ _ f2).2 eq
    · rw [postChildren]
      rw [postIssued] at unissued
      split
      · rfl
      · exact accounting.fresh subject candidateSlot unissued
    · rw [postSpawn.2] at found'
      have bound := accounting.budget parent cap found'
      by_cases h : parent = spawnParent state
      · rw [h] at bound ⊢
        simp only [Nat.add_zero] at countParent
        rw [← countParent] at bound
        exact Nat.le_of_succ_le bound
      · rw [(others parent h).2]; exact bound
    · by_cases isChild : subject = child
      · exact Or.inr ⟨spawnParent state, slot, entry, found, isChild ▸ childEq⟩
      · left
        by_cases isParent : subject = spawnParent state
        · rw [isParent]; exact entitlementParent
        · rw [entitlementOther subject isParent isChild]; exact Nat.le_refl _
  · rw [terminateChild_rejected_unchanged state word _ result]
    exact ⟨holds, accounting, fun _ => Or.inl (Nat.le_refl _)⟩

/-! ## Spawn authority keeps the accounting -/

theorem grantBudgetedAuthority_preserves (state : CompositeState) (subject budget : Nat)
    (holds : ResourceRuntimeWellFormed state) (accounting : ChildAccountingWellFormed state) :
    ResourceRuntimeWellFormed (grantBudgetedAuthority state subject budget).state ∧
      ChildAccountingWellFormed (grantBudgetedAuthority state subject budget).state ∧
      ∀ candidate, entitlement (grantBudgetedAuthority state subject budget).state candidate =
        entitlement state candidate := by
  unfold grantBudgetedAuthority
  split
  · next admitted =>
    obtain ⟨_, _, covered, _⟩ := admitted
    refine ⟨withSpawn_resourceRuntimeWellFormed holds _, ?_, fun _ => rfl⟩
    refine ⟨accounting.entries, accounting.unique, accounting.fresh,
      fun parent capability found => ?_⟩
    simp only at found
    split at found
    · next same =>
      subst same
      simp only [Option.some.injEq] at found
      subst found
      exact covered
    · exact accounting.budget parent capability found
  · exact ⟨holds, accounting, fun _ => rfl⟩

theorem revokeSpawnAuthority_preserves (state : CompositeState) (subject : Nat)
    (holds : ResourceRuntimeWellFormed state) (accounting : ChildAccountingWellFormed state) :
    ResourceRuntimeWellFormed (revokeSpawnAuthority state subject) ∧
      ChildAccountingWellFormed (revokeSpawnAuthority state subject) ∧
      ∀ candidate, entitlement (revokeSpawnAuthority state subject) candidate =
        entitlement state candidate := by
  refine ⟨withSpawn_resourceRuntimeWellFormed holds _, ⟨accounting.entries, accounting.unique,
    accounting.fresh, fun parent capability found => ?_⟩, fun _ => rfl⟩
  simp only [revokeSpawnAuthority] at found
  split at found
  · cases found
  · exact accounting.budget parent capability found

/-! ## Every step of the family -/

/-- **Every step of the public spawn family keeps both invariants**, and no
subject's entitlement grows except a child receiving a frame slice, whose
entitlement stays within the charge its parent recorded. -/
theorem childGate_preserves (state : CompositeState) (operation : ChildOperation)
    (holds : ResourceRuntimeWellFormed state) (accounting : ChildAccountingWellFormed state) :
    ResourceRuntimeWellFormed (childGate state operation).state ∧
      ChildAccountingWellFormed (childGate state operation).state ∧
      ∀ subject, entitlement (childGate state operation).state subject ≤
        entitlement state subject ∨ ChargedChild state subject := by
  cases hmode : state.execution.mode <;> simp only [childGate, hmode]
  case running =>
    cases operation with
    | spawn request =>
        obtain ⟨h1, h2, h3⟩ := spawnCharged_preserves state request hmode holds accounting
        exact ⟨h1, h2, fun subject => Or.inl (Nat.le_of_eq (h3 subject))⟩
    | grantFrames control frames =>
        obtain ⟨h1, h2, h3⟩ := grantFrames_preserves state control frames holds accounting
        refine ⟨h1, h2, fun subject => ?_⟩
        rcases h3 subject with le | ⟨parent, slot, entry, found, eq⟩
        · exact Or.inl le
        · exact Or.inr ⟨parent, slot, entry, found, eq⟩
    | terminateChild control =>
        obtain ⟨h1, h2, h3⟩ := terminateChild_preserves state control holds accounting
        refine ⟨h1, h2, fun subject => ?_⟩
        rcases h3 subject with le | ⟨parent, slot, entry, found, eq⟩
        · exact Or.inl le
        · exact Or.inr ⟨parent, slot, entry, found, eq⟩
    | grantAuthority subject budget =>
        obtain ⟨h1, h2, h3⟩ := grantBudgetedAuthority_preserves state subject budget holds
          accounting
        exact ⟨h1, h2, fun candidate => Or.inl (Nat.le_of_eq (h3 candidate))⟩
    | revokeAuthority subject =>
        obtain ⟨h1, h2, h3⟩ := revokeSpawnAuthority_preserves state subject holds accounting
        exact ⟨h1, h2, fun candidate => Or.inl (Nat.le_of_eq (h3 candidate))⟩
  all_goals exact ⟨holds, accounting, fun _ => Or.inl (Nat.le_refl _)⟩

end LeanOS.FailStop
