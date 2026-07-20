import LeanOS.DMAQuarantine

/-!
# Stateful PCI DMA quarantine corpus

This issue-local corpus serializes only the finite DMA control projection.  It
does not define or approximate the global composite runtime state owned by
issues #104 and #105.  Every record carries the complete canonical pre-state,
operation, post-state, and typed result encodings so continuity is observable.
-/
namespace LeanOS.DMAQuarantineCorpus

open LeanOS.DMAQuarantine

def corpusVersion : UInt64 := 1
def controlWords : Nat := snapshotWords * 2 + 1
def operationWords : Nat := snapshotWords + 1

def fatalReasonTag : FatalReason → UInt64
  | .controlSnapshotChanged => 1
  | .invalidControlSnapshot => 2

def runtimeModeTag : RuntimeMode → UInt64
  | .running => 0
  | .halted reason => fatalReasonTag reason

/-- The control projection consists of the boot-accepted snapshot, latest
observation, and fatal latch.  The modeled memory projection is deliberately
outside this issue-local codec. -/
def encodeControlState (state : RuntimeState) : Option (List UInt64) :=
  match encodeSnapshot state.accepted.snapshot, encodeSnapshot state.observed with
  | some accepted, some observed =>
      some (accepted ++ observed ++ [runtimeModeTag state.mode])
  | _, _ => none

/-- Public operations have a fixed width.  Ordinary operations contain no
BDF, assignment, or Command-register word; their tail is canonically zero. -/
def encodeOperation : PublicOperation → Option (List UInt64)
  | .ordinary => some (0 :: List.replicate snapshotWords 0)
  | .observeControl snapshot =>
      (encodeSnapshot snapshot).map fun words => 1 :: words

def encodeRuntimeResult : RuntimeResult → List UInt64
  | .continued => [0]
  | .fatal .controlSnapshotChanged => [1]
  | .fatal .invalidControlSnapshot => [2]
  | .alreadyHalted .controlSnapshotChanged => [3]
  | .alreadyHalted .invalidControlSnapshot => [4]

theorem encodeControlState_fixed_width state words
    (hencode : encodeControlState state = some words) :
    words.length = controlWords := by
  simp only [encodeControlState] at hencode
  cases haccepted : encodeSnapshot state.accepted.snapshot with
  | none => simp [haccepted] at hencode
  | some accepted =>
      cases hobserved : encodeSnapshot state.observed with
      | none => simp [haccepted, hobserved] at hencode
      | some observed =>
          simp [haccepted, hobserved] at hencode
          subst words
          have hacceptedLength :=
            accepted_encoding_fixed_width state.accepted.snapshot accepted haccepted
          have hobservedLength :=
            accepted_encoding_fixed_width state.observed observed hobserved
          simp [hacceptedLength, hobservedLength, controlWords]
          omega

theorem encodeOperation_fixed_width operation words
    (hencode : encodeOperation operation = some words) :
    words.length = operationWords := by
  cases operation with
  | ordinary =>
      simp [encodeOperation] at hencode
      subst words
      simp [operationWords]
  | observeControl snapshot =>
      simp only [encodeOperation] at hencode
      cases hsnapshot : encodeSnapshot snapshot with
      | none => simp [hsnapshot] at hencode
      | some encoded =>
          simp [hsnapshot] at hencode
          subst words
          have hlength := accepted_encoding_fixed_width snapshot encoded hsnapshot
          simp [hlength, operationWords]

@[simp] theorem encodeRuntimeResult_length result :
    (encodeRuntimeResult result).length = 1 := by
  cases result with
  | continued => rfl
  | fatal reason => cases reason <;> rfl
  | alreadyHalted reason => cases reason <;> rfl

structure Command where
  id : String
  operation : PublicOperation

structure Vector where
  trace : String
  step : Nat
  id : String
  preState : List UInt64
  operation : List UInt64
  postState : List UInt64
  result : List UInt64
  deriving Repr, Inhabited

private def encodedOrEmpty (encoded : Option (List UInt64)) : List UInt64 :=
  encoded.getD []

private def makeVector (trace : String) (step : Nat) (state : RuntimeState)
    (command : Command) : Vector × RuntimeState :=
  let outcome := runtimeGate state command.operation
  ({ trace, step, id := command.id,
     preState := encodedOrEmpty (encodeControlState state),
     operation := encodedOrEmpty (encodeOperation command.operation),
     postState := encodedOrEmpty (encodeControlState outcome.state),
     result := encodeRuntimeResult outcome.result }, outcome.state)

private def runTrace (trace : String) : Nat → RuntimeState → List Command → List Vector
  | _, _, [] => []
  | step, state, command :: rest =>
      let next := makeVector trace step state command
      next.1 :: runTrace trace (step + 1) next.2 rest

def changedCommands : List Command :=
  [{ id := "ordinary", operation := .ordinary },
   { id := "exact-reobserve", operation := .observeControl q35Snapshot },
   { id := "command-bit-flip", operation := .observeControl q35CommandBitFlipSnapshot },
   { id := "post-fatal-ordinary", operation := .ordinary }]

def invalidCommands : List Command :=
  [{ id := "bus-master-bit-flip", operation := .observeControl q35BusMasterBitFlipSnapshot },
   { id := "post-fatal-reobserve", operation := .observeControl q35Snapshot }]

/-- Stable trace and record order is part of DMA corpus schema version one. -/
def vectors : List Vector :=
  runTrace "changed-control" 0 q35Runtime changedCommands ++
    runTrace "invalid-control" 0 q35Runtime invalidCommands

theorem corpus_shape : vectors.length = 6 := by native_decide

theorem corpus_fixed_width :
    vectors.all fun vector =>
      vector.preState.length = controlWords &&
      vector.operation.length = operationWords &&
      vector.postState.length = controlWords && vector.result.length = 1 := by
  native_decide

theorem changed_trace_result_sequence :
    (vectors.take 4).map (·.result) = [[0], [0], [1], [3]] := by
  native_decide

theorem invalid_trace_result_sequence :
    (vectors.drop 4).map (·.result) = [[2], [4]] := by
  native_decide

theorem changed_trace_continuous :
    vectors[0]!.postState = vectors[1]!.preState ∧
    vectors[1]!.postState = vectors[2]!.preState ∧
    vectors[2]!.postState = vectors[3]!.preState := by
  native_decide

theorem invalid_trace_continuous :
    vectors[4]!.postState = vectors[5]!.preState := by
  native_decide

private def wordsText : List UInt64 → String
  | [] => ""
  | [word] => toString word
  | word :: rest => toString word ++ "," ++ wordsText rest

def line (vector : Vector) : String :=
  s!"{vector.trace}\t{vector.step}\t{vector.id}\t{wordsText vector.preState}\t{wordsText vector.operation}\t{wordsText vector.postState}\t{wordsText vector.result}"

def emit : IO Unit := do
  let revision := (← IO.getEnv "LEANOS_SOURCE_REVISION").getD "unknown"
  IO.println s!"leanos-dma-quarantine-corpus\t{corpusVersion}"
  IO.println s!"source-revision\t{revision}"
  for vector in vectors do
    IO.println (line vector)

end LeanOS.DMAQuarantineCorpus

def main : IO Unit := LeanOS.DMAQuarantineCorpus.emit
