import LeanOS.QotomMadtStream

/-! Proof-side traversal of the actual scalar query. This allocating model is
not a production export. Each successful step carries the exact returned
projections; callers cannot supply replacement intermediate parsed fields. -/
namespace LeanOS.QotomMadtStreamRun

structure State where
  offset : UInt64 := 44
  recordOffset : UInt64 := 0
  kind : UInt64 := 0
  length : UInt64 := 0
  apicId : UInt64 := 0
  flags : UInt64 := 0
  count : UInt64 := 0
  admitted : UInt64 := 256
  seen0 : UInt64 := 0
  seen1 : UInt64 := 0
  seen2 : UInt64 := 0
  seen3 : UInt64 := 0
  status : UInt64 := 1
  deriving DecidableEq, Repr

def initial : State := {}

def query (state : State) (length executing : UInt64) (byte : UInt8)
    (word : UInt64) : UInt64 :=
  QotomMadtStream.byteStepQuery state.offset state.recordOffset state.kind
    state.length state.apicId state.flags state.count state.admitted
    state.seen0 state.seen1 state.seen2 state.seen3 length executing state.offset
    byte.toUInt64 word

def next (state : State) (length executing : UInt64) (byte : UInt8) : State :=
  let q := query state length executing byte
  ⟨q 3, q 4, q 5, q 6, q 7, q 8, q 9, q 10, q 11, q 12, q 13, q 14, q 1⟩

def step (state : State) (length executing : UInt64) (byte : UInt8) :
    Except UInt64 State :=
  let error := query state length executing byte 2
  if error = 0 then .ok (next state length executing byte) else .error error

def run (length executing : UInt64) : State → List UInt8 → Except UInt64 State
  | state, [] => .ok state
  | state, byte :: rest => do
      let state ← step state length executing byte
      run length executing state rest

/-- Successful steps retain exactly the scalar projections. -/
theorem step_retains_projections (state result : State) (length executing : UInt64)
    (byte : UInt8) (accepted : step state length executing byte = .ok result) :
    result = next state length executing byte := by
  dsimp only [step] at accepted
  split at accepted <;> simp_all

/-- A terminal step carries the scalar terminal count into its actual state. -/
theorem step_terminal_count (state result : State) (length executing : UInt64)
    (byte : UInt8) (accepted : step state length executing byte = .ok result)
    (terminal : result.status = 3) : result.count = 4 := by
  have retained := step_retains_projections state result length executing byte accepted
  rw [retained] at terminal ⊢
  exact QotomMadtStream.terminal_byte_count state.offset state.recordOffset state.kind
    state.length state.apicId state.flags state.count state.admitted
    state.seen0 state.seen1 state.seen2 state.seen3 length executing state.offset
    byte.toUInt64 terminal

/-- Any nonempty successful traversal with terminal status has count four. -/
theorem run_terminal_count (length executing : UInt64) (state result : State)
    (bytes : List UInt8) (nonempty : bytes ≠ [])
    (accepted : run length executing state bytes = .ok result)
    (terminal : result.status = 3) : result.count = 4 := by
  induction bytes generalizing state with
  | nil => exact False.elim (nonempty rfl)
  | cons byte rest ih =>
    cases moved : step state length executing byte with
    | error reason =>
      simp only [run, moved] at accepted
      change (Except.error reason : Except UInt64 State) = .ok result at accepted
      cases accepted
    | ok middle =>
      have tail : run length executing middle rest = .ok result := by
        simp only [run, moved] at accepted
        exact accepted
      cases rest with
      | nil =>
        have same : middle = result := by simpa [run] using tail
        subst middle
        exact step_terminal_count state result length executing byte moved terminal
      | cons nextByte remaining =>
        exact ih middle (by simp) tail

/-- Every successful step has the scalar query's zero error projection. -/
theorem step_has_no_error (state result : State) (length executing : UInt64)
    (byte : UInt8) (accepted : step state length executing byte = .ok result) :
    query state length executing byte 2 = 0 := by
  dsimp only [step] at accepted
  split at accepted <;> simp_all

/-- The traversal advances the actual scalar byte offset exactly once. -/
theorem step_advances_offset (state result : State) (length executing : UInt64)
    (byte : UInt8) (accepted : step state length executing byte = .ok result) :
    result.offset = state.offset + 1 := by
  rw [step_retains_projections state result length executing byte accepted]
  exact QotomMadtStream.successful_byte_advances_offset state.offset state.recordOffset
    state.kind state.length state.apicId state.flags state.count state.admitted
    state.seen0 state.seen1 state.seen2 state.seen3 length executing state.offset
    byte.toUInt64 (step_has_no_error state result length executing byte accepted)

/-- Successful offset advancement is exact natural-number addition, not a
wrapped machine-word increment, because the scalar query enforces its bound. -/
theorem step_advances_offset_nat (state result : State) (length executing : UInt64)
    (byte : UInt8) (accepted : step state length executing byte = .ok result) :
    result.offset.toNat = state.offset.toNat + 1 := by
  have bounds := QotomMadtStream.successful_byte_position_bounded state.offset
    state.recordOffset state.kind state.length state.apicId state.flags state.count
    state.admitted state.seen0 state.seen1 state.seen2 state.seen3 length executing
    state.offset byte.toUInt64 (step_has_no_error state result length executing byte accepted)
  have within := bounds.2.2.1
  have cap := bounds.2.2.2
  simp only [UInt64.lt_iff_toNat_lt] at within
  simp [UInt64.le_iff_toNat_le, BootTopology.maxAcpiSdtBytes] at cap
  have nowrap : state.offset.toNat + 1 < 2 ^ 64 := by omega
  rw [step_advances_offset state result length executing byte accepted]
  simp [UInt64.toNat_add, Nat.mod_eq_of_lt nowrap]

/-- A successful traversal consumes precisely the supplied list length. -/
theorem run_consumes_exact_length (length executing : UInt64) (state result : State)
    (bytes : List UInt8) (accepted : run length executing state bytes = .ok result) :
    result.offset.toNat = state.offset.toNat + bytes.length := by
  induction bytes generalizing state with
  | nil =>
    simp only [run, Except.ok.injEq] at accepted
    subst result
    simp
  | cons byte rest ih =>
    simp only [run] at accepted
    cases moved : step state length executing byte with
    | error reason =>
      rw [moved] at accepted
      change (Except.error reason : Except UInt64 State) = .ok result at accepted
      cases accepted
    | ok middle =>
      have tail : run length executing middle rest = .ok result := by
        rw [moved] at accepted
        exact accepted
      have advance := step_advances_offset_nat state middle length executing byte moved
      have remaining := ih middle tail
      simp only [List.length_cons]
      omega

/-- Splitting a byte sequence cannot replace its intermediate state: the
second segment receives exactly the first segment's successful output. -/
theorem run_append (length executing : UInt64) (state : State)
    (front back : List UInt8) :
    run length executing state (front ++ back) =
      (run length executing state front >>= fun middle =>
        run length executing middle back) := by
  induction front generalizing state with
  | nil => rfl
  | cons byte rest ih =>
    simp only [List.cons_append, run]
    cases h : step state length executing byte with
    | error reason => rfl
    | ok middle => exact ih middle

/-- Successful concatenated traversal supplies a concrete intermediate state
and successful traversals of both segments, without substituting any fields. -/
theorem run_append_success (length executing : UInt64) (state result : State)
    (front back : List UInt8)
    (accepted : run length executing state (front ++ back) = .ok result) :
    ∃ middle, run length executing state front = .ok middle ∧
      run length executing middle back = .ok result := by
  rw [run_append] at accepted
  cases firstRun : run length executing state front with
  | error reason =>
    rw [firstRun] at accepted
    change (Except.error reason : Except UInt64 State) = .ok result at accepted
    cases accepted
  | ok middle =>
    refine ⟨middle, rfl, ?_⟩
    rw [firstRun] at accepted
    exact accepted

/-- A successful nonempty run exposes its actual first transition and tail. -/
theorem run_cons_success (length executing : UInt64) (state result : State)
    (byte : UInt8) (rest : List UInt8)
    (accepted : run length executing state (byte :: rest) = .ok result) :
    ∃ middle, step state length executing byte = .ok middle ∧
      run length executing middle rest = .ok result := by
  simp only [run] at accepted
  cases moved : step state length executing byte with
  | error reason =>
    rw [moved] at accepted
    change (Except.error reason : Except UInt64 State) = .ok result at accepted
    cases accepted
  | ok middle =>
    refine ⟨middle, rfl, ?_⟩
    rw [moved] at accepted
    exact accepted

/-- Cleared partial fields mark a record boundary; inventory remains separate. -/
def AtBoundary (state : State) : Prop :=
  state.recordOffset = 0 ∧ state.kind = 0 ∧ state.length = 0 ∧
    state.apicId = 0 ∧ state.flags = 0

/-- A terminal transition clears every partial field in the carried state. -/
theorem step_terminal_boundary (state result : State) (length executing : UInt64)
    (byte : UInt8) (accepted : step state length executing byte = .ok result)
    (terminal : result.status = 3) : AtBoundary result := by
  have retained := step_retains_projections state result length executing byte accepted
  rw [retained] at terminal ⊢
  have clear := QotomMadtStream.terminal_byte_clears_record state.offset state.recordOffset
    state.kind state.length state.apicId state.flags state.count state.admitted
    state.seen0 state.seen1 state.seen2 state.seen3 length executing state.offset byte.toUInt64
  exact ⟨clear 4 terminal (by simp), clear 5 terminal (by simp),
    clear 6 terminal (by simp), clear 7 terminal (by simp), clear 8 terminal (by simp)⟩

/-- A nonempty terminal traversal ends at a genuine record boundary. -/
theorem run_terminal_boundary (length executing : UInt64) (state result : State)
    (bytes : List UInt8) (nonempty : bytes ≠ [])
    (accepted : run length executing state bytes = .ok result)
    (terminal : result.status = 3) : AtBoundary result := by
  induction bytes generalizing state with
  | nil => exact False.elim (nonempty rfl)
  | cons byte rest ih =>
    obtain ⟨middle, moved, tail⟩ := run_cons_success length executing state result byte rest accepted
    cases rest with
    | nil =>
      have same : middle = result := by simpa [run] using tail
      subst middle
      exact step_terminal_boundary state result length executing byte moved terminal
    | cons nextByte remaining =>
      exact ih middle (by simp) tail

/-- Terminal control fields come from the actual last scalar transition.
The duplicate-detection limbs require a separate traversal invariant. -/
theorem step_terminal_control_fields (state result : State) (length executing : UInt64)
    (byte : UInt8) (accepted : step state length executing byte = .ok result)
    (terminal : result.status = 3) :
    result.offset = length ∧ 44 < length ∧ length ≤ UInt64.ofNat BootTopology.maxAcpiSdtBytes ∧
      AtBoundary result ∧ result.count = 4 ∧ result.admitted = 0 ∧ executing = 0 := by
  have retained := step_retains_projections state result length executing byte accepted
  have scalarStatus : query state length executing byte 1 = 3 := by
    rw [retained] at terminal
    exact terminal
  have position := QotomMadtStream.terminal_byte_has_no_error state.offset state.recordOffset
    state.kind state.length state.apicId state.flags state.count state.admitted
    state.seen0 state.seen1 state.seen2 state.seen3 length executing state.offset
    byte.toUInt64 scalarStatus
  have bounds := QotomMadtStream.successful_byte_position_bounded state.offset state.recordOffset
    state.kind state.length state.apicId state.flags state.count state.admitted
    state.seen0 state.seen1 state.seen2 state.seen3 length executing state.offset
    byte.toUInt64 position.1
  have bsp := QotomMadtStream.terminal_byte_bsp state.offset state.recordOffset
    state.kind state.length state.apicId state.flags state.count state.admitted
    state.seen0 state.seen1 state.seen2 state.seen3 length executing state.offset
    byte.toUInt64 scalarStatus
  have low : 44 < length := by
    have atLeast := bounds.2.1
    have within := bounds.2.2.1
    simp only [UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt] at atLeast within ⊢
    omega
  refine ⟨(step_advances_offset state result length executing byte accepted).trans position.2,
    low, bounds.2.2.2, step_terminal_boundary state result length executing byte accepted terminal,
    step_terminal_count state result length executing byte accepted terminal, ?_, bsp.1⟩
  rw [retained]
  exact bsp.2

/-- A nonempty terminal traversal supplies its final control fields without
caller-provided replacements for offsets, counts or the admitted BSP ID. -/
theorem run_terminal_control_fields (length executing : UInt64) (state result : State)
    (bytes : List UInt8) (nonempty : bytes ≠ [])
    (accepted : run length executing state bytes = .ok result)
    (terminal : result.status = 3) :
    result.offset = length ∧ 44 < length ∧ length ≤ UInt64.ofNat BootTopology.maxAcpiSdtBytes ∧
      AtBoundary result ∧ result.count = 4 ∧ result.admitted = 0 ∧ executing = 0 := by
  induction bytes generalizing state with
  | nil => exact False.elim (nonempty rfl)
  | cons byte rest ih =>
    obtain ⟨middle, moved, tail⟩ := run_cons_success length executing state result byte rest accepted
    cases rest with
    | nil =>
      have same : middle = result := by simpa [run] using tail
      subst middle
      exact step_terminal_control_fields state result length executing byte moved terminal
    | cons nextByte remaining => exact ih middle (by simp) tail

/-- Lift the scalar kind-byte contract to the exact carried-state model. -/
theorem step_starts_record (state result : State) (length executing : UInt64)
    (byte : UInt8) (boundary : AtBoundary state)
    (accepted : step state length executing byte = .ok result) :
    (result.recordOffset, result.kind, result.length, result.apicId, result.flags) =
      (1, byte.toUInt64, 0, 0, 0) ∧
    (result.count, result.admitted, result.seen0, result.seen1, result.seen2, result.seen3) =
      (state.count, state.admitted, state.seen0, state.seen1, state.seen2, state.seen3) := by
  have noError := step_has_no_error state result length executing byte accepted
  have fields := boundary
  dsimp only [AtBoundary] at fields
  have error : QotomMadtStream.byteStepQuery state.offset 0 0 0 0 0 state.count
      state.admitted state.seen0 state.seen1 state.seen2 state.seen3 length executing
      state.offset byte.toUInt64 2 = 0 := by
    simpa [query, fields.1, fields.2.1, fields.2.2.1, fields.2.2.2.1,
      fields.2.2.2.2] using noError
  have scalar := QotomMadtStream.record_kind_starts_clean state.offset state.count
    state.admitted state.seen0 state.seen1 state.seen2 state.seen3 length executing
    state.offset byte.toUInt64 error
  rw [step_retains_projections state result length executing byte accepted]
  simpa [next, query, fields.1, fields.2.1, fields.2.2.1, fields.2.2.2.1,
    fields.2.2.2.2] using scalar

/-- A successful complete header derives framing from both supplied bytes,
while carrying the exact initial processor inventory through both transitions. -/
theorem run_header_retains_framing (length executing : UInt64) (state result : State)
    (kindByte lengthByte : UInt8) (boundary : AtBoundary state)
    (accepted : run length executing state [kindByte, lengthByte] = .ok result) :
    (kindByte.toUInt64 = 0 ∨ kindByte.toUInt64 = 1 ∨
      kindByte.toUInt64 = 2 ∨ kindByte.toUInt64 = 4) ∧
    lengthByte.toUInt64 = (if kindByte.toUInt64 = 0 then 8 else
      if kindByte.toUInt64 = 1 then 12 else if kindByte.toUInt64 = 2 then 10 else 6) ∧
    (result.recordOffset, result.kind, result.length, result.apicId, result.flags) =
      (2, kindByte.toUInt64, lengthByte.toUInt64, 0, 0) ∧
    (result.count, result.admitted, result.seen0, result.seen1, result.seen2, result.seen3) =
      (state.count, state.admitted, state.seen0, state.seen1, state.seen2, state.seen3) := by
  obtain ⟨middle, firstStep, tail⟩ := run_cons_success length executing state result
    kindByte [lengthByte] accepted
  obtain ⟨last, secondStep, finished⟩ := run_cons_success length executing middle result
    lengthByte [] tail
  change Except.ok last = Except.ok result at finished
  cases finished
  have middleFields := step_starts_record state middle length executing kindByte boundary firstStep
  simp only [Prod.mk.injEq] at middleFields
  have clear := boundary
  dsimp only [AtBoundary] at clear
  have firstError := step_has_no_error state middle length executing kindByte firstStep
  have supported := QotomMadtStream.record_kind_supported state.offset state.count
    state.admitted state.seen0 state.seen1 state.seen2 state.seen3 length executing
    state.offset kindByte.toUInt64 (by
      simpa [query, clear.1, clear.2.1, clear.2.2.1, clear.2.2.2.1,
        clear.2.2.2.2] using firstError)
  have secondError := step_has_no_error middle result length executing lengthByte secondStep
  have scalar := QotomMadtStream.record_length_retained middle.offset kindByte.toUInt64
    middle.count middle.admitted middle.seen0 middle.seen1 middle.seen2 middle.seen3
    length executing middle.offset lengthByte.toUInt64 supported (by
      simpa [query, middleFields.1.1, middleFields.1.2.1, middleFields.1.2.2.1,
        middleFields.1.2.2.2.1, middleFields.1.2.2.2.2] using secondError)
  refine ⟨supported, scalar.1, ?_⟩
  rw [step_retains_projections middle result length executing lengthByte secondStep]
  simpa [next, query, middleFields.1.1, middleFields.1.2.1, middleFields.1.2.2.1,
    middleFields.1.2.2.2.1, middleFields.1.2.2.2.2, middleFields.2] using scalar.2

/-- Lift successful payload framing to the state used by traversal. -/
theorem step_payload_framing (state result : State) (length executing : UInt64)
    (byte : UInt8) (pastKind : state.recordOffset ≠ 0)
    (pastLength : state.recordOffset ≠ 1)
    (incomplete : state.recordOffset + 1 ≠ state.length)
    (accepted : step state length executing byte = .ok result) :
    (result.recordOffset, result.kind, result.length) =
      (state.recordOffset + 1, state.kind, state.length) := by
  have scalar := QotomMadtStream.payload_preserves_framing state.offset state.recordOffset
    state.kind state.length state.apicId state.flags state.count state.admitted
    state.seen0 state.seen1 state.seen2 state.seen3 length executing state.offset
    byte.toUInt64 pastKind pastLength incomplete
    (step_has_no_error state result length executing byte accepted)
  rw [step_retains_projections state result length executing byte accepted]
  exact scalar

/-- Completing a record returns the actual traversal state to a boundary. -/
theorem step_completes_boundary (state result : State) (length executing : UInt64)
    (byte : UInt8) (pastLength : state.recordOffset ≠ 1)
    (nonempty : state.length ≠ 0) (complete : state.recordOffset + 1 = state.length)
    (accepted : step state length executing byte = .ok result) : AtBoundary result := by
  have clear := QotomMadtStream.completed_record_clears_partial_state state.offset
    state.recordOffset state.kind state.length state.apicId state.flags state.count
    state.admitted state.seen0 state.seen1 state.seen2 state.seen3 length executing
    state.offset byte.toUInt64
  rw [step_retains_projections state result length executing byte accepted]
  exact ⟨clear 4 pastLength nonempty complete (by simp),
    clear 5 pastLength nonempty complete (by simp),
    clear 6 pastLength nonempty complete (by simp),
    clear 7 pastLength nonempty complete (by simp),
    clear 8 pastLength nonempty complete (by simp)⟩

/-- Reaching a record boundary from inside a payload requires enough actual
input bytes to finish that payload; a short successful prefix cannot masquerade
as a complete record. This applies to every supported record kind. -/
theorem run_boundary_requires_payload (length executing : UInt64) (state result : State)
    (bytes : List UInt8) (lower : 2 ≤ state.recordOffset.toNat)
    (remaining : state.recordOffset.toNat < state.length.toNat)
    (bounded : state.length.toNat ≤ 12)
    (accepted : run length executing state bytes = .ok result)
    (boundary : AtBoundary result) :
    state.length.toNat ≤ state.recordOffset.toNat + bytes.length := by
  induction bytes generalizing state with
  | nil =>
    have same : state = result := by simpa [run] using accepted
    have zero := boundary.1
    rw [← same] at zero
    simp [zero] at lower
  | cons byte rest ih =>
    obtain ⟨middle, moved, tail⟩ := run_cons_success length executing state result byte rest accepted
    have advance : (state.recordOffset + 1).toNat = state.recordOffset.toNat + 1 := by
      have nowrap : state.recordOffset.toNat + 1 < 2 ^ 64 := by omega
      simp [UInt64.toNat_add, Nat.mod_eq_of_lt nowrap]
    by_cases complete : state.recordOffset + 1 = state.length
    · have same := congrArg UInt64.toNat complete
      simp only [List.length_cons]
      omega
    · have pastKind : state.recordOffset ≠ 0 := by intro h; simp [h] at lower
      have pastLength : state.recordOffset ≠ 1 := by intro h; simp [h] at lower
      have framing := step_payload_framing state middle length executing byte
        pastKind pastLength complete moved
      simp only [Prod.mk.injEq] at framing
      have nextOffset : middle.recordOffset.toNat = state.recordOffset.toNat + 1 := by
        rw [framing.1, advance]
      have nextLength : middle.length.toNat = state.length.toNat := congrArg UInt64.toNat framing.2.2
      have unequal : state.recordOffset.toNat + 1 ≠ state.length.toNat := by
        intro same
        apply complete
        apply UInt64.toNat.inj
        omega
      have enough := ih middle (by omega) (by omega) (by omega) tail
      simp only [List.length_cons]
      omega

/-- Consuming exactly the remaining payload returns to a boundary, independent
of processor inventory effects and the supported record kind. -/
theorem run_payload_boundary (length executing : UInt64) (state result : State)
    (bytes : List UInt8) (lower : 2 ≤ state.recordOffset.toNat)
    (remaining : state.recordOffset.toNat < state.length.toNat)
    (bounded : state.length.toNat ≤ 12)
    (exactBytes : state.recordOffset.toNat + bytes.length = state.length.toNat)
    (accepted : run length executing state bytes = .ok result) : AtBoundary result := by
  induction bytes generalizing state with
  | nil => simp only [List.length_nil] at exactBytes; omega
  | cons byte rest ih =>
    obtain ⟨middle, moved, tail⟩ := run_cons_success length executing state result byte rest accepted
    have pastKind : state.recordOffset ≠ 0 := by intro h; simp [h] at lower
    have pastLength : state.recordOffset ≠ 1 := by intro h; simp [h] at lower
    have nonempty : state.length ≠ 0 := by intro h; simp [h] at remaining
    have advance : (state.recordOffset + 1).toNat = state.recordOffset.toNat + 1 := by
      have nowrap : state.recordOffset.toNat + 1 < 2 ^ 64 := by omega
      simp [UInt64.toNat_add, Nat.mod_eq_of_lt nowrap]
    cases rest with
    | nil =>
      have complete : state.recordOffset + 1 = state.length := by
        apply UInt64.toNat.inj
        simp only [List.length_cons, List.length_nil] at exactBytes
        omega
      have boundary := step_completes_boundary state middle length executing byte pastLength nonempty complete moved
      change Except.ok middle = Except.ok result at tail
      cases tail
      exact boundary
    | cons nextByte rest =>
      have incomplete : state.recordOffset + 1 ≠ state.length := by
        intro h
        have same := congrArg UInt64.toNat h
        simp only [List.length_cons] at exactBytes
        omega
      have framing := step_payload_framing state middle length executing byte pastKind pastLength incomplete moved
      simp only [Prod.mk.injEq] at framing
      have nextOffset : middle.recordOffset.toNat = state.recordOffset.toNat + 1 := by
        rw [framing.1, advance]
      have nextLength : middle.length.toNat = state.length.toNat := congrArg UInt64.toNat framing.2.2
      exact ih middle (by omega) (by
        simp only [List.length_cons] at exactBytes
        omega) (by omega) (by
        simp only [List.length_cons] at exactBytes ⊢
        omega) tail

/-- Non-processor payload steps preserve all carried inventory fields. -/
theorem step_nonprocessor_inventory (state result : State) (length executing : UInt64)
    (byte : UInt8) (pastKind : state.recordOffset ≠ 0) (nonprocessor : state.kind ≠ 0)
    (accepted : step state length executing byte = .ok result) :
    (result.count, result.admitted, result.seen0, result.seen1, result.seen2, result.seen3) =
      (state.count, state.admitted, state.seen0, state.seen1, state.seen2, state.seen3) := by
  have scalar := QotomMadtStream.nonprocessor_preserves_inventory state.offset
    state.recordOffset state.kind state.length state.apicId state.flags state.count
    state.admitted state.seen0 state.seen1 state.seen2 state.seen3 length executing
    state.offset byte.toUInt64 pastKind nonprocessor
    (step_has_no_error state result length executing byte accepted)
  rw [step_retains_projections state result length executing byte accepted]
  exact scalar

/-- Traverse the complete remaining payload of a bounded non-processor record.
The actual resulting state is a boundary with the original inventory intact. -/
theorem run_nonprocessor_payload (length executing : UInt64) (state result : State)
    (bytes : List UInt8) (nonprocessor : state.kind ≠ 0)
    (lower : 2 ≤ state.recordOffset.toNat)
    (remaining : state.recordOffset.toNat < state.length.toNat)
    (bounded : state.length.toNat ≤ 12)
    (exactBytes : state.recordOffset.toNat + bytes.length = state.length.toNat)
    (accepted : run length executing state bytes = .ok result) :
    AtBoundary result ∧
    (result.count, result.admitted, result.seen0, result.seen1, result.seen2, result.seen3) =
      (state.count, state.admitted, state.seen0, state.seen1, state.seen2, state.seen3) := by
  induction bytes generalizing state with
  | nil => simp only [List.length_nil] at exactBytes; omega
  | cons byte rest ih =>
    obtain ⟨middle, moved, tail⟩ := run_cons_success length executing state result byte rest accepted
    have pastKind : state.recordOffset ≠ 0 := by intro h; simp [h] at lower
    have pastLength : state.recordOffset ≠ 1 := by intro h; simp [h] at lower
    have nonempty : state.length ≠ 0 := by intro h; simp [h] at remaining
    have advance : (state.recordOffset + 1).toNat = state.recordOffset.toNat + 1 := by
      have nowrap : state.recordOffset.toNat + 1 < 2 ^ 64 := by omega
      simp [UInt64.toNat_add, Nat.mod_eq_of_lt nowrap]
    have inventory := step_nonprocessor_inventory state middle length executing byte pastKind nonprocessor moved
    cases rest with
    | nil =>
      have complete : state.recordOffset + 1 = state.length := by
        apply UInt64.toNat.inj
        simp only [List.length_cons, List.length_nil] at exactBytes
        omega
      have boundary := step_completes_boundary state middle length executing byte pastLength nonempty complete moved
      change Except.ok middle = Except.ok result at tail
      cases tail
      exact ⟨boundary, inventory⟩
    | cons nextByte rest =>
      have incomplete : state.recordOffset + 1 ≠ state.length := by
        intro h
        have same := congrArg UInt64.toNat h
        simp only [List.length_cons] at exactBytes
        omega
      have framing := step_payload_framing state middle length executing byte pastKind pastLength incomplete moved
      simp only [Prod.mk.injEq] at framing
      have nextOffset : middle.recordOffset.toNat = state.recordOffset.toNat + 1 := by
        rw [framing.1, advance]
      have nextLength : middle.length.toNat = state.length.toNat := congrArg UInt64.toNat framing.2.2
      have nextKind : middle.kind ≠ 0 := by rw [framing.2.1]; exact nonprocessor
      have done := ih middle nextKind (by omega) (by
        simp only [List.length_cons] at exactBytes
        omega) (by omega) (by
        simp only [List.length_cons] at exactBytes ⊢
        omega) tail
      exact ⟨done.1, done.2.trans inventory⟩

/-- Compose the actual header and payload of an entire non-processor record. -/
theorem run_nonprocessor_record (length executing : UInt64) (state result : State)
    (kindByte lengthByte : UInt8) (payload : List UInt8) (boundary : AtBoundary state)
    (nonprocessor : kindByte.toUInt64 ≠ 0)
    (sized : payload.length + 2 = lengthByte.toNat)
    (accepted : run length executing state ([kindByte, lengthByte] ++ payload) = .ok result) :
    AtBoundary result ∧
    (result.count, result.admitted, result.seen0, result.seen1, result.seen2, result.seen3) =
      (state.count, state.admitted, state.seen0, state.seen1, state.seen2, state.seen3) := by
  obtain ⟨middle, headRun, tailRun⟩ := run_append_success length executing state result
    [kindByte, lengthByte] payload accepted
  have header := run_header_retains_framing length executing state middle kindByte lengthByte boundary headRun
  have fields := header.2.2.1
  simp only [Prod.mk.injEq] at fields
  have widths : lengthByte.toNat = 6 ∨ lengthByte.toNat = 10 ∨ lengthByte.toNat = 12 := by
    have declared := header.2.1
    rcases header.1 with h | h | h | h
    · exact (nonprocessor h).elim
    all_goals
      simp [h] at declared
      have natural := congrArg UInt64.toNat declared
      simp at natural
      omega
  have offset : middle.recordOffset.toNat = 2 := by simp [fields.1]
  have width : middle.length.toNat = lengthByte.toNat := by simp [fields.2.2.1]
  have ignored : middle.kind ≠ 0 := by rw [fields.2.1]; exact nonprocessor
  have done := run_nonprocessor_payload length executing middle result payload ignored
    (by omega) (by omega) (by omega) (by omega) tailRun
  exact ⟨done.1, done.2.trans header.2.2.2⟩

/-- Carry the exact nonterminal local-APIC payload update through the model. -/
theorem step_processor_payload (state result : State) (length executing : UInt64)
    (byte : UInt8) (kind : state.kind = 0) (width : state.length = 8)
    (lower : 2 ≤ state.recordOffset) (upper : state.recordOffset < 7)
    (accepted : step state length executing byte = .ok result) :
    (result.recordOffset, result.kind, result.length, result.apicId, result.flags) =
      (state.recordOffset + 1, 0, 8,
        if state.recordOffset = 3 then byte.toUInt64 else state.apicId,
        if 4 ≤ state.recordOffset then state.flags |||
          (byte.toUInt64 <<< ((state.recordOffset - 4) * 8)) else state.flags) ∧
    (result.count, result.admitted, result.seen0, result.seen1, result.seen2, result.seen3) =
      (state.count, state.admitted, state.seen0, state.seen1, state.seen2, state.seen3) := by
  have error := step_has_no_error state result length executing byte accepted
  have scalar := QotomMadtStream.processor_payload_fields state.offset state.recordOffset
    state.apicId state.flags state.count state.admitted state.seen0 state.seen1
    state.seen2 state.seen3 length executing state.offset byte.toUInt64 lower upper
    (by simpa [query, kind, width] using error)
  rw [step_retains_projections state result length executing byte accepted]
  simpa [next, query, kind, width] using scalar

/-- A successful processor payload prefix before its final byte preserves
the inventory and advances framing by its actual number of supplied bytes. -/
theorem run_processor_prefix_inventory (length executing : UInt64) (state result : State)
    (bytes : List UInt8) (kind : state.kind = 0) (width : state.length = 8)
    (lower : 2 ≤ state.recordOffset.toNat)
    (bounded : state.recordOffset.toNat + bytes.length ≤ 7)
    (accepted : run length executing state bytes = .ok result) :
    (result.recordOffset.toNat, result.kind, result.length) =
      (state.recordOffset.toNat + bytes.length, 0, 8) ∧
    (result.count, result.admitted, result.seen0, result.seen1, result.seen2, result.seen3) =
      (state.count, state.admitted, state.seen0, state.seen1, state.seen2, state.seen3) := by
  induction bytes generalizing state with
  | nil =>
    have same : state = result := by simpa [run] using accepted
    subst result
    exact ⟨by simp [kind, width], rfl⟩
  | cons byte rest ih =>
    obtain ⟨middle, moved, tail⟩ := run_cons_success length executing state result byte rest accepted
    have upper : state.recordOffset.toNat < 7 := by
      simp only [List.length_cons] at bounded
      omega
    have fields := step_processor_payload state middle length executing byte kind width
      (by simpa [UInt64.le_iff_toNat_le] using lower)
      (by simpa [UInt64.lt_iff_toNat_lt] using upper) moved
    have framing := fields.1
    simp only [Prod.mk.injEq] at framing
    have nextOffset : middle.recordOffset.toNat = state.recordOffset.toNat + 1 := by
      rw [framing.1]
      have nowrap : state.recordOffset.toNat + 1 < 2 ^ 64 := by omega
      simp [UInt64.toNat_add, Nat.mod_eq_of_lt nowrap]
    have done := ih middle framing.2.1 framing.2.2.1 (by omega) (by
      simp only [List.length_cons] at bounded
      omega) tail
    refine ⟨?_, done.2.trans fields.2⟩
    simpa [nextOffset, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using done.1

/-- The final carried payload byte checks the reconstructed ID and flags and
increments the actual processor count before returning to a record boundary. -/
theorem step_processor_complete (state result : State) (length executing : UInt64)
    (byte : UInt8) (kind : state.kind = 0) (width : state.length = 8)
    (position : state.recordOffset = 7)
    (accepted : step state length executing byte = .ok result) :
    AtBoundary result ∧ result.count = state.count + 1 ∧
    QotomMadtStream.processorMatches state.count state.apicId
      ((state.flags ||| (byte.toUInt64 <<< 24)) &&& 1 != 0) = true ∧
    (state.flags ||| (byte.toUInt64 <<< 24)) &&& 2 = 0 := by
  have error := step_has_no_error state result length executing byte accepted
  have scalarError : QotomMadtStream.byteStepQuery state.offset 7 0 8 state.apicId
      state.flags state.count state.admitted state.seen0 state.seen1 state.seen2
      state.seen3 length executing state.offset byte.toUInt64 2 = 0 := by
    simpa [query, kind, width, position] using error
  have guarded := QotomMadtStream.completed_processor_requires_guard state.offset
    state.apicId state.flags state.count state.admitted state.seen0 state.seen1
    state.seen2 state.seen3 length executing state.offset byte.toUInt64 scalarError
  have counted := QotomMadtStream.completed_processor_advances_count state.offset
    state.apicId state.flags state.count state.admitted state.seen0 state.seen1
    state.seen2 state.seen3 length executing state.offset byte.toUInt64 scalarError
  refine ⟨step_completes_boundary state result length executing byte
    (by simp [position]) (by simp [width]) (by simp [position, width]) accepted, ?_, guarded⟩
  rw [step_retains_projections state result length executing byte accepted]
  simpa [next, query, kind, width, position] using counted

/-- A complete local-APIC payload binds its final guard to the supplied ID
and four flag bytes, carrying every intermediate state from actual execution. -/
theorem run_processor_payload (length executing : UInt64) (state result : State)
    (uid id b0 b1 b2 b3 : UInt8)
    (start : state.recordOffset = 2 ∧ state.kind = 0 ∧ state.length = 8 ∧
      state.apicId = 0 ∧ state.flags = 0)
    (accepted : run length executing state [uid, id, b0, b1, b2, b3] = .ok result) :
    let flags := b0.toUInt64 ||| (b1.toUInt64 <<< 8) |||
      (b2.toUInt64 <<< 16) ||| (b3.toUInt64 <<< 24)
    AtBoundary result ∧ result.count = state.count + 1 ∧
    QotomMadtStream.processorMatches state.count id.toUInt64 (flags &&& 1 != 0) = true ∧
      flags &&& 2 = 0 := by
  obtain ⟨s1, m1, t1⟩ := run_cons_success length executing state result
    uid [id, b0, b1, b2, b3] accepted
  obtain ⟨s2, m2, t2⟩ := run_cons_success length executing s1 result
    id [b0, b1, b2, b3] t1
  obtain ⟨s3, m3, t3⟩ := run_cons_success length executing s2 result
    b0 [b1, b2, b3] t2
  obtain ⟨s4, m4, t4⟩ := run_cons_success length executing s3 result
    b1 [b2, b3] t3
  obtain ⟨s5, m5, t5⟩ := run_cons_success length executing s4 result
    b2 [b3] t4
  obtain ⟨s6, m6, t6⟩ := run_cons_success length executing s5 result
    b3 [] t5
  change Except.ok s6 = Except.ok result at t6
  cases t6
  have p1 := step_processor_payload state s1 length executing uid
    (by simp_all) (by simp_all) (by simp_all) (by simp_all) m1
  simp only [Prod.mk.injEq] at p1
  have p2 := step_processor_payload s1 s2 length executing id
    (by simp_all) (by simp_all) (by simp_all) (by simp_all) m2
  simp only [Prod.mk.injEq] at p2
  have p3 := step_processor_payload s2 s3 length executing b0
    (by simp_all) (by simp_all) (by simp_all) (by simp_all) m3
  simp only [Prod.mk.injEq] at p3
  have p4 := step_processor_payload s3 s4 length executing b1
    (by simp_all) (by simp_all) (by simp_all) (by simp_all) m4
  simp only [Prod.mk.injEq] at p4
  have p5 := step_processor_payload s4 s5 length executing b2
    (by simp_all) (by simp_all) (by simp_all) (by simp_all) m5
  simp only [Prod.mk.injEq] at p5
  have done := step_processor_complete s5 result length executing b3
    (by simp_all) (by simp_all) (by simp_all) m6
  simpa [start, p1, p2, p3, p4, p5] using done

/-- A complete eight-byte processor record validates its actual payload and
advances the original inventory count before restoring a clean boundary. -/
theorem run_processor_record (length executing : UInt64) (state result : State)
    (uid id b0 b1 b2 b3 : UInt8) (boundary : AtBoundary state)
    (accepted : run length executing state [0, 8, uid, id, b0, b1, b2, b3] = .ok result) :
    let flags := b0.toUInt64 ||| (b1.toUInt64 <<< 8) |||
      (b2.toUInt64 <<< 16) ||| (b3.toUInt64 <<< 24)
    AtBoundary result ∧ result.count = state.count + 1 ∧
    QotomMadtStream.processorMatches state.count id.toUInt64 (flags &&& 1 != 0) = true ∧
      flags &&& 2 = 0 := by
  obtain ⟨middle, headRun, tailRun⟩ := run_append_success length executing state result
    [0, 8] [uid, id, b0, b1, b2, b3] accepted
  have header := run_header_retains_framing length executing state middle 0 8 boundary headRun
  have fields := header.2.2.1
  have inventory := header.2.2.2
  simp only [Prod.mk.injEq] at fields inventory
  have start : middle.recordOffset = 2 ∧ middle.kind = 0 ∧ middle.length = 8 ∧
      middle.apicId = 0 ∧ middle.flags = 0 := by simpa using fields
  have done := run_processor_payload length executing middle result uid id b0 b1 b2 b3 start tailRun
  simpa [inventory.1] using done

/-- A successful complete processor record supplies exactly the typed
baseline member at its original count, using the reference decoder's fields. -/
theorem run_processor_record_typed (length executing : UInt64) (state result : State)
    (uid id b0 b1 b2 b3 : UInt8) (boundary : AtBoundary state)
    (accepted : run length executing state [0, 8, uid, id, b0, b1, b2, b3] = .ok result) :
    let value := b0.toNat + b1.toNat * 256 + b2.toNat * 65536 + b3.toNat * 16777216
    let decoded : BootTopology.Processor :=
      ⟨id.toUInt32, value % 2 == 1, (value / 2) % 2 == 1⟩
    some decoded = QotomBspTopology.processors[state.count.toNat]? ∧
      AtBoundary result ∧ result.count = state.count + 1 := by
  have record := run_processor_record length executing state result uid id b0 b1 b2 b3 boundary accepted
  have predicates := QotomMadtStream.flags_predicates_match_reference b0 b1 b2 b3
  dsimp only at record predicates ⊢
  have matched := record.2.2.1
  rw [predicates.1] at matched
  have offline : ((b0.toNat + b1.toNat * 256 + b2.toNat * 65536 +
      b3.toNat * 16777216) / 2 % 2 == 1) = false := by
    rw [← predicates.2]
    simp [record.2.2.2]
  have member := QotomMadtStream.processor_matches_typed_record state.count
    (⟨id.toUInt32,
      (b0.toNat + b1.toNat * 256 + b2.toNat * 65536 + b3.toNat * 16777216) % 2 == 1,
      ((b0.toNat + b1.toNat * 256 + b2.toNat * 65536 + b3.toNat * 16777216) / 2) % 2 == 1⟩)
    (by simpa using matched) offline
  exact ⟨member, record.1, record.2.1⟩

/-- A successful processor record advances a count below four without wrap,
so table-level record counting can use ordinary natural-number arithmetic. -/
theorem run_processor_record_count_nat (length executing : UInt64) (state result : State)
    (uid id b0 b1 b2 b3 : UInt8) (boundary : AtBoundary state)
    (accepted : run length executing state [0, 8, uid, id, b0, b1, b2, b3] = .ok result) :
    state.count.toNat < 4 ∧ result.count.toNat = state.count.toNat + 1 := by
  have record := run_processor_record length executing state result uid id b0 b1 b2 b3 boundary accepted
  have guard := (QotomMadtStream.processor_matches_iff _ _ _).mp record.2.2.1
  have bound := guard.1
  simp [UInt64.lt_iff_toNat_lt] at bound
  refine ⟨bound, ?_⟩
  have nowrap : state.count.toNat + 1 < 2 ^ 64 := by omega
  rw [record.2.1]
  simp [UInt64.toNat_add, Nat.mod_eq_of_lt nowrap]

/-- Complete processor records preserve the exact prefix inventory until
their final byte sets the next baseline bit. -/
theorem run_processor_record_seen_bits (length executing : UInt64) (state result : State)
    (uid id b0 b1 b2 b3 : UInt8) (boundary : AtBoundary state)
    (accepted : run length executing state [0, 8, uid, id, b0, b1, b2, b3] = .ok result) :
    (result.seen0, result.seen1, result.seen2, result.seen3) =
      (state.seen0 ||| ((1 : UInt64) <<< (state.count * 2)), state.seen1, state.seen2, state.seen3) := by
  obtain ⟨headerState, headRun, payloadRun⟩ := run_append_success length executing state result
    [0, 8] [uid, id, b0, b1, b2, b3] accepted
  have header := run_header_retains_framing length executing state headerState 0 8 boundary headRun
  have fields := header.2.2.1
  simp only [Prod.mk.injEq] at fields
  obtain ⟨lastState, prefixRun, finalRun⟩ := run_append_success length executing headerState result
    [uid, id, b0, b1, b2] [b3] payloadRun
  have prior := run_processor_prefix_inventory length executing headerState lastState
    [uid, id, b0, b1, b2] fields.2.1 fields.2.2.1
    (by simp [fields.1]) (by simp [fields.1]) prefixRun
  have frame := prior.1
  simp only [Prod.mk.injEq] at frame
  have position : lastState.recordOffset = 7 := by
    apply UInt64.toNat.inj
    simpa [fields.1] using frame.1
  have inventory := prior.2.trans header.2.2.2
  obtain ⟨finalState, moved, done⟩ := run_cons_success length executing lastState result b3 [] finalRun
  have same : finalState = result := by simpa [run] using done
  subst finalState
  have error := step_has_no_error lastState result length executing b3 moved
  have scalar := QotomMadtStream.completed_processor_seen_bits lastState.offset lastState.apicId
    lastState.flags lastState.count lastState.admitted lastState.seen0 lastState.seen1
    lastState.seen2 lastState.seen3 length executing lastState.offset b3.toUInt64
    (by simpa [query, position, frame.2.1, frame.2.2] using error)
  simp only [Prod.mk.injEq] at inventory
  rw [step_retains_projections lastState result length executing b3 moved]
  simpa [next, query, position, frame.2.1, frame.2.2, inventory] using scalar

/-- Duplicate-detection mask after a prefix of the four ordered processors. -/
def processorPrefixMask (count : UInt64) : UInt64 :=
  if count = 0 then 0 else if count = 1 then 1 else if count = 2 then 5
  else if count = 3 then 21 else 85

/-- The next baseline ID extends the exact mask for every admissible prefix. -/
theorem processor_prefix_mask_step (count : UInt64) (bounded : count.toNat < 4) :
    processorPrefixMask (count + 1) =
      processorPrefixMask count ||| ((1 : UInt64) <<< (count * 2)) := by
  have positions : count = 0 ∨ count = 1 ∨ count = 2 ∨ count = 3 := by
    simp only [← UInt64.toNat_inj]
    simp
    omega
  rcases positions with h | h | h | h <;> subst count <;> decide

/-- Carried bitsets equal the ordered processor prefix and have no high IDs. -/
def SeenPrefix (state : State) : Prop :=
  state.seen0 = processorPrefixMask state.count ∧ state.seen1 = 0 ∧
    state.seen2 = 0 ∧ state.seen3 = 0

/-- A byte-preserving record view for composition. The decomposition theorem
constructs this view from successful raw-byte traversal between boundaries. -/
inductive WireRecord where
  | processor (uid id b0 b1 b2 b3 : UInt8)
  | ignored (kind width : UInt8) (payload : List UInt8)
      (nonprocessor : kind.toUInt64 ≠ 0) (sized : payload.length + 2 = width.toNat)

def WireRecord.bytes : WireRecord → List UInt8
  | .processor uid id b0 b1 b2 b3 => [0, 8, uid, id, b0, b1, b2, b3]
  | .ignored kind width payload _ _ => [kind, width] ++ payload

def WireRecord.processorValue : WireRecord → Option BootTopology.Processor
  | .processor _ id b0 b1 b2 b3 =>
      let value := b0.toNat + b1.toNat * 256 + b2.toNat * 65536 + b3.toNat * 16777216
      some ⟨id.toUInt32, value % 2 == 1, (value / 2) % 2 == 1⟩
  | .ignored _ _ _ _ _ => none

/-- Reference decoder record retaining the exact admitted field semantics. -/
def WireRecord.rawValue : WireRecord → BootTopology.RawMadtRecord
  | .processor _ id b0 b1 b2 b3 =>
      let value := b0.toNat + b1.toNat * 256 + b2.toNat * 65536 + b3.toNat * 16777216
      .localApic 8 id.toUInt32 (value % 2 == 1) (value / 2 % 2 == 1)
  | .ignored kind width _ _ _ => .topologyIrrelevant kind width.toNat

/-- Every successfully streamed record decodes to its exact reference record,
and its resulting carried state is a boundary for the next record. -/
theorem run_record_reference_decode (length executing : UInt64) (state result : State)
    (record : WireRecord) (boundary : AtBoundary state)
    (accepted : run length executing state record.bytes = .ok result) :
    AtBoundary result ∧ ∀ (fuel : Nat) (rest : List UInt8)
      (decodedRest : List BootTopology.RawMadtRecord),
      BootTopology.decodeMadtBytesAux fuel rest = .ok decodedRest →
      BootTopology.decodeMadtBytesAux (fuel + 1) (record.bytes ++ rest) =
        .ok (record.rawValue :: decodedRest) := by
  cases record with
  | processor uid id b0 b1 b2 b3 =>
    have done := run_processor_record length executing state result uid id b0 b1 b2 b3 boundary accepted
    refine ⟨done.1, ?_⟩
    intro fuel rest decodedRest decoded
    simpa [WireRecord.bytes, WireRecord.rawValue] using
      BootTopology.decode_local_apic_record_cons fuel uid id b0 b1 b2 b3 rest decodedRest decoded
  | ignored kind width payload nonprocessor sized =>
    have done := run_nonprocessor_record length executing state result kind width payload
      boundary nonprocessor sized accepted
    obtain ⟨middle, headerRun, _⟩ := run_append_success length executing state result
      [kind, width] payload accepted
    have header := run_header_retains_framing length executing state middle kind width boundary headerRun
    have supported : (kind = 1 ∧ width = 12) ∨ (kind = 2 ∧ width = 10) ∨
        (kind = 4 ∧ width = 6) := by
      have declared := header.2.1
      rcases header.1 with h | h | h | h
      · exact False.elim (nonprocessor h)
      all_goals
        simp [h] at declared
        have kindNat := congrArg UInt64.toNat h
        have widthNat := congrArg UInt64.toNat declared
        simp at kindNat widthNat
        simp only [← UInt8.toNat_inj]
        simp_all
    refine ⟨done.1, ?_⟩
    intro fuel rest decodedRest decoded
    exact BootTopology.decode_irrelevant_record_cons fuel kind width payload rest
      decodedRest supported sized decoded

/-- Successful record sequences agree with the reference decoder whenever
its fuel bounds the number of records actually present. -/
theorem run_records_reference_decode (length executing : UInt64) (state result : State)
    (records : List WireRecord) (fuel : Nat) (enough : records.length ≤ fuel)
    (boundary : AtBoundary state)
    (accepted : run length executing state (records.flatMap WireRecord.bytes) = .ok result) :
    BootTopology.decodeMadtBytesAux fuel (records.flatMap WireRecord.bytes) =
      .ok (records.map WireRecord.rawValue) := by
  induction records generalizing state fuel with
  | nil => simp [BootTopology.decodeMadtBytesAux]
  | cons record rest ih =>
    cases fuel with
    | zero => simp at enough
    | succ fuel =>
      obtain ⟨middle, firstRun, tailRun⟩ := run_append_success length executing state result
        record.bytes (rest.flatMap WireRecord.bytes) accepted
      have first := run_record_reference_decode length executing state middle record boundary firstRun
      have decodedTail := ih middle fuel (by simpa using enough) first.1 tailRun
      exact first.2 fuel _ _ decodedTail

/-- The reference decoder's byte-count fuel suffices for every record view. -/
theorem records_length_le_bytes (records : List WireRecord) :
    records.length ≤ (records.flatMap WireRecord.bytes).length := by
  induction records with
  | nil => simp
  | cons record rest ih =>
    cases record <;> simp_all [WireRecord.bytes] <;> omega

/-- A correctly sized supported header and its actual payload have a
byte-preserving record view; processor fields are taken directly from the bytes. -/
theorem wire_record_of_payload (kind width : UInt8) (payload : List UInt8)
    (processorWidth : kind.toUInt64 = 0 → width.toUInt64 = 8)
    (sized : payload.length + 2 = width.toNat) :
    ∃ record : WireRecord, record.bytes = [kind, width] ++ payload := by
  by_cases processor : kind.toUInt64 = 0
  · have kindZero : kind = 0 := by
      apply UInt8.toNat.inj
      have value := congrArg UInt64.toNat processor
      simpa using value
    have widthEight : width = 8 := by
      apply UInt8.toNat.inj
      have value := congrArg UInt64.toNat (processorWidth processor)
      simpa using value
    subst kind
    subst width
    simp at sized
    rcases payload with _ | ⟨uid, tail⟩
    · simp at sized
    rcases tail with _ | ⟨id, tail⟩
    · simp at sized
    rcases tail with _ | ⟨b0, tail⟩
    · simp at sized
    rcases tail with _ | ⟨b1, tail⟩
    · simp at sized
    rcases tail with _ | ⟨b2, tail⟩
    · simp at sized
    rcases tail with _ | ⟨b3, tail⟩
    · simp at sized
    have empty : tail = [] := by
      have zero : tail.length = 0 := by
        simp only [List.length_cons] at sized
        omega
      simpa using zero
    subst tail
    exact ⟨.processor uid id b0 b1 b2 b3, rfl⟩
  · exact ⟨.ignored kind width payload processor sized, rfl⟩

/-- Any successful raw-byte traversal between record boundaries admits a
complete byte-preserving record decomposition. No parsed records are supplied
by the caller. -/
theorem run_boundary_record_decomposition (length executing : UInt64)
    (state result : State) (bytes : List UInt8) (start : AtBoundary state)
    (accepted : run length executing state bytes = .ok result)
    (finish : AtBoundary result) :
    ∃ records : List WireRecord, records.flatMap WireRecord.bytes = bytes := by
  generalize sizeEq : bytes.length = size
  induction size using Nat.strongRecOn generalizing bytes state with
  | ind size ih =>
    cases bytes with
    | nil => exact ⟨[], rfl⟩
    | cons kind rest =>
      cases rest with
      | nil =>
        obtain ⟨middle, moved, tail⟩ := run_cons_success length executing state result kind [] accepted
        have same : middle = result := by simpa [run] using tail
        have fields := step_starts_record state middle length executing kind start moved
        have one : middle.recordOffset = 1 := congrArg Prod.fst fields.1
        rw [same, finish.1] at one
        contradiction
      | cons width rest =>
        obtain ⟨headerState, headerRun, payloadRun⟩ := run_append_success length executing state result
          [kind, width] rest accepted
        have header := run_header_retains_framing length executing state headerState kind width start headerRun
        have fields := header.2.2.1
        simp only [Prod.mk.injEq] at fields
        have offset : headerState.recordOffset.toNat = 2 := by simp [fields.1]
        have declared : headerState.length.toNat = width.toNat := by simp [fields.2.2.1]
        have limits : 6 ≤ width.toNat ∧ width.toNat ≤ 12 := by
          have widthEq := header.2.1
          rcases header.1 with k | k | k | k
          all_goals
            simp [k] at widthEq
            have natural := congrArg UInt64.toNat widthEq
            simp at natural
            omega
        have enough := run_boundary_requires_payload length executing headerState result rest
          (by omega) (by omega) (by omega) payloadRun finish
        let payload := rest.take (width.toNat - 2)
        let back := rest.drop (width.toNat - 2)
        have joined : payload ++ back = rest := List.take_append_drop _ _
        have sized : payload.length + 2 = width.toNat := by
          simp only [payload, List.length_take]
          omega
        have splitRun : run length executing headerState (payload ++ back) = .ok result := by
          rw [joined]
          exact payloadRun
        obtain ⟨middle, firstRun, tailRun⟩ := run_append_success length executing headerState result payload back splitRun
        have middleBoundary := run_payload_boundary length executing headerState middle payload
          (by omega) (by omega) (by omega) (by omega) firstRun
        have smaller : back.length < size := by
          simp only [List.length_cons] at sizeEq
          have bound : back.length ≤ rest.length := by simp [back]
          omega
        obtain ⟨records, recordBytes⟩ := ih back.length smaller middle back middleBoundary tailRun rfl
        obtain ⟨record, actualBytes⟩ := wire_record_of_payload kind width payload
          (by intro zero; simpa [zero] using header.2.1) sized
        refine ⟨record :: records, ?_⟩
        simp only [List.flatMap_cons, actualBytes, recordBytes]
        simp only [joined, List.cons_append, List.nil_append]

/-- For any byte-preserving record sequence, successful traversal returns to
a boundary and advances its count by exactly the number of processor records. -/
theorem run_records_count (length executing : UInt64) (state result : State)
    (records : List WireRecord) (boundary : AtBoundary state)
    (accepted : run length executing state (records.flatMap WireRecord.bytes) = .ok result) :
    AtBoundary result ∧ result.count.toNat = state.count.toNat +
      (records.filterMap WireRecord.processorValue).length := by
  induction records generalizing state with
  | nil =>
    change Except.ok state = Except.ok result at accepted
    cases accepted
    exact ⟨boundary, by simp⟩
  | cons record rest ih =>
    obtain ⟨middle, firstRun, tailRun⟩ := run_append_success length executing state result
      record.bytes (rest.flatMap WireRecord.bytes) accepted
    cases record with
    | processor uid id b0 b1 b2 b3 =>
      have typed := run_processor_record_typed length executing state middle uid id b0 b1 b2 b3 boundary firstRun
      have count := run_processor_record_count_nat length executing state middle uid id b0 b1 b2 b3 boundary firstRun
      have tail := ih middle typed.2.1 tailRun
      refine ⟨tail.1, ?_⟩
      simp only [List.filterMap_cons, WireRecord.processorValue, List.length_cons]
      omega
    | ignored kind width payload nonprocessor sized =>
      have ignored := run_nonprocessor_record length executing state middle kind width payload boundary nonprocessor sized firstRun
      have count : middle.count = state.count := congrArg Prod.fst ignored.2
      have tail := ih middle ignored.1 tailRun
      simpa [WireRecord.processorValue, count] using tail

/-- Every processor in a successfully traversed record view occupies its
exact baseline index, retaining order through interspersed ignored records. -/
theorem run_records_members (length executing : UInt64) (state result : State)
    (records : List WireRecord) (boundary : AtBoundary state)
    (accepted : run length executing state (records.flatMap WireRecord.bytes) = .ok result) :
    ∀ (index : Nat) (processor : BootTopology.Processor),
      (records.filterMap WireRecord.processorValue)[index]? = some processor →
      some processor = QotomBspTopology.processors[state.count.toNat + index]? := by
  induction records generalizing state with
  | nil => intro index processor selected; simp at selected
  | cons record rest ih =>
    obtain ⟨middle, firstRun, tailRun⟩ := run_append_success length executing state result
      record.bytes (rest.flatMap WireRecord.bytes) accepted
    cases record with
    | processor uid id b0 b1 b2 b3 =>
      have typed := run_processor_record_typed length executing state middle uid id b0 b1 b2 b3 boundary firstRun
      have count := run_processor_record_count_nat length executing state middle uid id b0 b1 b2 b3 boundary firstRun
      have tail := ih middle typed.2.1 tailRun
      intro index processor selected
      cases index with
      | zero =>
        simp [WireRecord.processorValue] at selected
        simpa [selected] using typed.1
      | succ index =>
        have found : (rest.filterMap WireRecord.processorValue)[index]? = some processor := by
          simpa [WireRecord.processorValue] using selected
        have member := tail index processor found
        simpa [count.2, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using member
    | ignored kind width payload nonprocessor sized =>
      have ignored := run_nonprocessor_record length executing state middle kind width payload boundary nonprocessor sized firstRun
      have count : middle.count = state.count := congrArg Prod.fst ignored.2
      have tail := ih middle ignored.1 tailRun
      simpa [WireRecord.processorValue, count] using tail

/-- An initialized successful record-view traversal ending at count four has
exactly the complete typed baseline, not merely the same count or ID bitset. -/
theorem initialized_records_complete_inventory (length executing : UInt64)
    (result : State) (records : List WireRecord)
    (accepted : run length executing initial (records.flatMap WireRecord.bytes) = .ok result)
    (complete : result.count = 4) :
    records.filterMap WireRecord.processorValue = QotomBspTopology.processors := by
  have boundary : AtBoundary initial := by simp [AtBoundary, initial]
  have count := run_records_count length executing initial result records boundary accepted
  have size : (records.filterMap WireRecord.processorValue).length = 4 := by
    simpa [initial, complete] using count.2.symm
  have members := run_records_members length executing initial result records boundary accepted
  apply List.ext_getElem
  · simpa [QotomBspTopology.processors] using size
  · intro index left right
    have selected := List.getElem?_eq_getElem left
    have member := members index (records.filterMap WireRecord.processorValue)[index] selected
    simpa [initial, List.getElem?_eq_getElem right] using member

/-- Terminal success from the actual initial state supplies the count needed
for the complete record-view inventory theorem. -/
theorem initialized_terminal_records_inventory (length executing : UInt64)
    (result : State) (records : List WireRecord)
    (accepted : run length executing initial (records.flatMap WireRecord.bytes) = .ok result)
    (terminal : result.status = 3) :
    records.filterMap WireRecord.processorValue = QotomBspTopology.processors := by
  have nonempty : records.flatMap WireRecord.bytes ≠ [] := by
    intro empty
    rw [empty] at accepted
    have same : initial = result := by simpa [run] using accepted
    rw [← same] at terminal
    simp [initial] at terminal
  exact initialized_records_complete_inventory length executing result records accepted
    (run_terminal_count length executing initial result _ nonempty accepted terminal)

/-- Successful record traversal carries the exact ordered bitset invariant
through processor updates and intervening non-processor records. -/
theorem run_records_seen_prefix (length executing : UInt64) (state result : State)
    (records : List WireRecord) (boundary : AtBoundary state) (seen : SeenPrefix state)
    (accepted : run length executing state (records.flatMap WireRecord.bytes) = .ok result) :
    SeenPrefix result := by
  induction records generalizing state with
  | nil =>
    have same : state = result := by simpa [run] using accepted
    simpa [← same] using seen
  | cons record rest ih =>
    obtain ⟨middle, firstRun, tailRun⟩ := run_append_success length executing state result
      record.bytes (rest.flatMap WireRecord.bytes) accepted
    cases record with
    | processor uid id b0 b1 b2 b3 =>
      have done := run_processor_record length executing state middle uid id b0 b1 b2 b3 boundary firstRun
      have count := run_processor_record_count_nat length executing state middle uid id b0 b1 b2 b3 boundary firstRun
      have bits := run_processor_record_seen_bits length executing state middle uid id b0 b1 b2 b3 boundary firstRun
      simp only [Prod.mk.injEq] at bits
      have nextSeen : SeenPrefix middle := by
        dsimp only [SeenPrefix] at seen ⊢
        rw [bits.1, bits.2.1, bits.2.2.1, bits.2.2.2, done.2.1,
          processor_prefix_mask_step state.count count.1, seen.1]
        exact ⟨rfl, seen.2⟩
      exact ih middle done.1 nextSeen tailRun
    | ignored kind width payload nonprocessor sized =>
      have done := run_nonprocessor_record length executing state middle kind width payload
        boundary nonprocessor sized firstRun
      have inventory := done.2
      simp only [Prod.mk.injEq] at inventory
      have nextSeen : SeenPrefix middle := by
        simpa [SeenPrefix, inventory] using seen
      exact ih middle done.1 nextSeen tailRun

/-- An initialized terminal raw-byte traversal has exactly the four baseline
ID bits in its returned state, with no bits in the three upper limbs. -/
theorem initialized_terminal_seen_bits (length executing : UInt64) (result : State)
    (bytes : List UInt8) (accepted : run length executing initial bytes = .ok result)
    (terminal : result.status = 3) :
    result.seen0 = 85 ∧ result.seen1 = 0 ∧ result.seen2 = 0 ∧ result.seen3 = 0 := by
  have nonempty : bytes ≠ [] := by
    intro empty
    rw [empty] at accepted
    have same : initial = result := by simpa [run] using accepted
    rw [← same] at terminal
    simp [initial] at terminal
  have boundary := run_terminal_boundary length executing initial result bytes nonempty accepted terminal
  obtain ⟨records, exactBytes⟩ := run_boundary_record_decomposition length executing initial result
    bytes (by simp [AtBoundary, initial]) accepted boundary
  have seen := run_records_seen_prefix length executing initial result records
    (by simp [AtBoundary, initial]) (by simp [SeenPrefix, initial, processorPrefixMask])
    (by simpa [exactBytes] using accepted)
  have count := run_terminal_count length executing initial result bytes nonempty accepted terminal
  simpa [SeenPrefix, count, processorPrefixMask] using seen

/-- Terminal success over arbitrary input bytes constructs a record view
from those bytes and proves its complete ordered processor inventory. -/
theorem initialized_raw_terminal_inventory (length executing : UInt64)
    (result : State) (bytes : List UInt8)
    (accepted : run length executing initial bytes = .ok result)
    (terminal : result.status = 3) :
    ∃ records : List WireRecord, records.flatMap WireRecord.bytes = bytes ∧
      records.filterMap WireRecord.processorValue = QotomBspTopology.processors := by
  have nonempty : bytes ≠ [] := by
    intro empty
    rw [empty] at accepted
    have same : initial = result := by simpa [run] using accepted
    rw [← same] at terminal
    simp [initial] at terminal
  have boundary := run_terminal_boundary length executing initial result bytes nonempty accepted terminal
  obtain ⟨records, exactBytes⟩ := run_boundary_record_decomposition length executing initial result
    bytes (by simp [AtBoundary, initial]) accepted boundary
  refine ⟨records, exactBytes, ?_⟩
  apply initialized_terminal_records_inventory length executing result records
  · simpa [exactBytes] using accepted
  · exact terminal

/-- The authoritative normalizer preserves a bounded record view's exact
processor list, while supplying its own source/version provenance. -/
theorem records_reference_normalize (records : List WireRecord)
    (bspId executingId : UInt32)
    (bounded : (records.filterMap WireRecord.processorValue).length ≤ BootTopology.maxProcessors) :
    BootTopology.normalizeMadtRecords (records.map WireRecord.rawValue) bspId executingId =
      .ok {
        source := .acpiMadt
        version := BootTopology.snapshotVersion
        bspId
        executingId
        processors := records.filterMap WireRecord.processorValue } := by
  apply BootTopology.normalize_valid_madt_records
  · intro raw member
    obtain ⟨record, _, rfl⟩ := List.mem_map.mp member
    cases record <;> simp [WireRecord.rawValue, BootTopology.localApicRecordLength]
  · induction records with
    | nil => rfl
    | cons record rest ih =>
      have restBound : (rest.filterMap WireRecord.processorValue).length ≤ BootTopology.maxProcessors := by
        cases record <;> simp_all [WireRecord.processorValue] <;> omega
      cases record <;> simp_all [WireRecord.rawValue, WireRecord.processorValue]
  · exact bounded

/-- Terminal raw-byte stream success agrees with the authoritative entry
 decoder and normalizer, including the complete baseline snapshot. -/
theorem initialized_raw_reference_snapshot (length executing : UInt64)
    (result : State) (bytes : List UInt8)
    (accepted : run length executing initial bytes = .ok result)
    (terminal : result.status = 3) :
    ∃ records : List BootTopology.RawMadtRecord,
      BootTopology.decodeMadtBytes bytes = .ok records ∧
      BootTopology.normalizeMadtRecords records 0 0 = .ok QotomBspTopology.baseline := by
  obtain ⟨records, exactBytes, inventory⟩ := initialized_raw_terminal_inventory
    length executing result bytes accepted terminal
  have streamed : run length executing initial (records.flatMap WireRecord.bytes) = .ok result := by
    simpa [exactBytes] using accepted
  have enough : records.length ≤ bytes.length := by
    simpa [exactBytes] using records_length_le_bytes records
  have decoded := run_records_reference_decode length executing initial result records bytes.length
    enough (by simp [AtBoundary, initial]) streamed
  refine ⟨records.map WireRecord.rawValue, ?_, ?_⟩
  · simpa [BootTopology.decodeMadtBytes, exactBytes] using decoded
  · have bounded : (records.filterMap WireRecord.processorValue).length ≤ BootTopology.maxProcessors := by
      simp [inventory, QotomBspTopology.processors, BootTopology.maxProcessors]
    simpa [inventory, QotomBspTopology.baseline] using records_reference_normalize records 0 0 bounded

/-- Once the actual complete table has passed the existing envelope and fixed
header checks, terminal stream success implies the authoritative complete-table
snapshot. The stream consumes this validated table's entry bytes. -/
theorem validated_table_reference_snapshot (bytes : List UInt8)
    (table : BootTopology.ValidAcpiSdt) (result : State)
    (validated : BootTopology.validateAcpiSdt [0x41, 0x50, 0x49, 0x43] bytes = .ok table)
    (header : BootTopology.acpiMadtHeaderLength ≤ table.length)
    (accepted : run (UInt64.ofNat table.length) 0 initial
      (table.bytes.drop BootTopology.acpiMadtHeaderLength) = .ok result)
    (terminal : result.status = 3) :
    BootTopology.decodeCompleteMadtSnapshot bytes 0 0 = .ok QotomBspTopology.baseline := by
  obtain ⟨records, decoded, normalized⟩ := initialized_raw_reference_snapshot
    (UInt64.ofNat table.length) 0 result _ accepted terminal
  simp [BootTopology.decodeCompleteMadtSnapshot, validated,
    show ¬table.length < BootTopology.acpiMadtHeaderLength by omega, decoded, normalized]

/-- The actual initialized stream result supplies every finish-shape field;
acceptance then agrees exactly with the typed BSP binder on the same observation. -/
theorem initialized_terminal_finish_binding (length executing : UInt64)
    (result : State) (bytes : List UInt8) (topology : QotomBspTopology.Witness)
    (observation : QotomBspTopology.BootstrapObservation)
    (accepted : run length executing initial bytes = .ok result)
    (terminal : result.status = 3) :
    QotomMadtStream.finishQuery result.status 0 result.offset result.recordOffset
      result.kind result.length result.apicId result.flags result.count result.admitted
      result.seen0 result.seen1 result.seen2 result.seen3 length executing
      observation.cpuidEdx.toUInt64 (if observation.readAvailable then 1 else 0)
      observation.apicBase observation.executingId.toUInt64 1 = 1 ↔
    ∃ witness, QotomBspTopology.bindBootstrap topology observation = .ok witness := by
  have nonempty : bytes ≠ [] := by
    intro empty
    rw [empty] at accepted
    have same : initial = result := by simpa [run] using accepted
    rw [← same] at terminal
    simp [initial] at terminal
  have control := run_terminal_control_fields length executing initial result bytes nonempty accepted terminal
  have seen := initialized_terminal_seen_bits length executing result bytes accepted terminal
  rcases control with ⟨offset, low, high, boundary, count, admitted, bsp⟩
  rcases boundary with ⟨recordOffset, kind, width, id, flags⟩
  rcases seen with ⟨seen0, seen1, seen2, seen3⟩
  simpa [terminal, offset, recordOffset, kind, width, id, flags, count, admitted,
    seen0, seen1, seen2, seen3, bsp] using
    QotomMadtStream.finish_typed_binding_iff topology observation length low high

/-- A validated table and its actual terminal stream result construct the
topology witness consumed by the typed BSP binder. No caller-supplied topology
witness or terminal-state replacement is needed for this finish contract. -/
theorem validated_terminal_finish_binding (bytes : List UInt8)
    (table : BootTopology.ValidAcpiSdt) (result : State)
    (observation : QotomBspTopology.BootstrapObservation)
    (validated : BootTopology.validateAcpiSdt [0x41, 0x50, 0x49, 0x43] bytes = .ok table)
    (header : BootTopology.acpiMadtHeaderLength ≤ table.length)
    (accepted : run (UInt64.ofNat table.length) 0 initial
      (table.bytes.drop BootTopology.acpiMadtHeaderLength) = .ok result)
    (terminal : result.status = 3) :
    ∃ topology : QotomBspTopology.Witness,
      BootTopology.decodeCompleteMadtSnapshot bytes 0 0 = .ok topology.observed ∧
      (QotomMadtStream.finishQuery result.status 0 result.offset result.recordOffset
        result.kind result.length result.apicId result.flags result.count result.admitted
        result.seen0 result.seen1 result.seen2 result.seen3 (UInt64.ofNat table.length) 0
        observation.cpuidEdx.toUInt64 (if observation.readAvailable then 1 else 0)
        observation.apicBase observation.executingId.toUInt64 1 = 1 ↔
       ∃ witness, QotomBspTopology.bindBootstrap topology observation = .ok witness) := by
  refine ⟨⟨QotomBspTopology.baseline, rfl⟩,
    validated_table_reference_snapshot bytes table result validated header accepted terminal, ?_⟩
  exact initialized_terminal_finish_binding (UInt64.ofNat table.length) 0 result
    (table.bytes.drop BootTopology.acpiMadtHeaderLength) _ observation accepted terminal

end LeanOS.QotomMadtStreamRun
