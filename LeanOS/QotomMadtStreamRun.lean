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

end LeanOS.QotomMadtStreamRun
