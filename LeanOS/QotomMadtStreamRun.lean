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

end LeanOS.QotomMadtStreamRun
