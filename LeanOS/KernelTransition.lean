/-!
# Phase 1 kernel transition

This module defines the state machine for claims C1--C3 in ADR 0001.  At Lean
semantics, `transition` is the executable implementation as well as its
specification: there is not a second implementation hidden behind the proofs.
The model assumes sequential execution and has no devices, concurrency, memory,
or capability semantics.

`bootTransition` is the narrow fixed-width adapter selected by ADR 0002.  Its
arguments encode the phase (`0` is cold, `1` is ready) and command (`1` means
initialize), and its return value encodes only the result (`1` accepted, `0`
rejected).  `bootTransition_agrees` connects that adapter to the model for
well-formed states.  The theorem is about Lean definitions; generated C, its
ABI, foreign primitives, and the boot environment remain trusted and must be
tested separately.
-/

namespace LeanOS.KernelTransition

/-- The two phases represented by the first boot state machine. -/
inductive BootPhase where
  | cold
  | ready
  deriving DecidableEq, Repr

/-- Explicit kernel state for the Phase 1 transition. -/
structure State where
  phase : BootPhase
  generation : UInt64
  deriving DecidableEq, Repr

/-- Commands understood by the Phase 1 transition. -/
inductive Command where
  | initialize
  | unsupported
  deriving DecidableEq, Repr

/-- Whether a command was accepted by the state machine. -/
inductive Result where
  | accepted
  | rejected
  deriving DecidableEq, Repr

/-- A transition makes both its result and resulting state explicit. -/
structure Outcome where
  state : State
  result : Result
  deriving DecidableEq, Repr

/-- The kernel begins cold, before its one initialization transition. -/
def initialState : State :=
  { phase := .cold, generation := 0 }

/--
A state is well formed when its scalar generation agrees with its boot phase.
-/
def WellFormed (state : State) : Prop :=
  match state.phase with
  | .cold => state.generation = 0
  | .ready => state.generation = 1

/--
Initialize a cold kernel exactly once.  Every other input is rejected and
leaves the supplied state unchanged, making this a total operation.
-/
def transition (state : State) (command : Command) : Outcome :=
  match state.phase, command with
  | .cold, .initialize =>
      { state := { phase := .ready, generation := 1 }, result := .accepted }
  | _, _ => { state := state, result := .rejected }

/-- Initialization establishes a well-formed initial state. -/
theorem initialState_wellFormed : WellFormed initialState := by
  rfl

/-- Claim C1: evaluation of the transition is deterministic. -/
theorem transition_deterministic (state : State) (command : Command)
    (first second : Outcome) (hfirst : transition state command = first)
    (hsecond : transition state command = second) : first = second := by
  rw [← hfirst, ← hsecond]

/-- Claim C2: every transition preserves the named invariant. -/
theorem transition_preserves_wellFormed (state : State) (command : Command)
    (hstate : WellFormed state) : WellFormed (transition state command).state := by
  cases state with
  | mk phase generation =>
      cases phase <;> cases command <;> simp_all [transition, WellFormed]

/-- Claim C3: rejection leaves the modeled state unchanged. -/
theorem rejected_state_unchanged (state : State) (command : Command)
    (hrejected : (transition state command).result = .rejected) :
    (transition state command).state = state := by
  cases state with
  | mk phase generation =>
      cases phase <;> cases command <;> simp_all [transition]

/-- Decode the fixed-width command accepted by the boot adapter. -/
def decodeCommand (command : UInt64) : Command :=
  if command == 1 then .initialize else .unsupported

/-- Encode a well-formed modeled phase for the boot adapter. -/
def encodeState (state : State) : UInt64 :=
  match state.phase with
  | .cold => 0
  | .ready => 1

/-- Encode the modeled result for the serial/boot boundary. -/
def encodeResult (result : Result) : UInt64 :=
  match result with
  | .accepted => 1
  | .rejected => 0

/--
Allocation-free scalar entry point for issue #6: accept initialization only
from the encoded cold state.  Invalid state or command encodings return the
rejection code.  The modeled transition above specifies the resulting state.
-/
@[export leanos_boot_transition]
def bootTransition (state command : UInt64) : UInt64 :=
  if state == 0 && command == 1 then 1 else 0

/-- The fixed-width entry point agrees with the explicit model on valid state. -/
theorem bootTransition_agrees (state : State) (command : UInt64)
    (_hstate : WellFormed state) :
    bootTransition (encodeState state) command =
      encodeResult (transition state (decodeCommand command)).result := by
  cases state with
  | mk phase generation =>
      cases phase <;> by_cases hcommand : command = 1 <;>
        simp [bootTransition, encodeState, decodeCommand, encodeResult,
          transition, hcommand]

example : transition initialState .initialize =
    { state := { phase := .ready, generation := 1 }, result := .accepted } := by
  rfl

example : transition initialState .unsupported =
    { state := initialState, result := .rejected } := by
  rfl

example : bootTransition 0 1 = 1 := by decide
example : bootTransition 0 7 = 0 := by decide

end LeanOS.KernelTransition
