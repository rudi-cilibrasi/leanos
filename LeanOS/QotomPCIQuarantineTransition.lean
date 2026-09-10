import LeanOS.QotomPCIQuarantineObservation

/-!
Binds a validated initial inventory to a validated command/readback trace.
This checks supplied observations, not PCI execution or DMA quiescence.
-/
namespace LeanOS.QotomPCIQuarantineTransition

open PCIHeaderObservation

/-- Command and Status share dword one. Command is checked separately after
its declared word write; Status may change asynchronously. Every other raw
configuration dword must remain identical to the initial observation. -/
def stableRegisters (before after : RawHeader) : Bool :=
  before.bdf == after.bdf && before.words.eraseIdx 1 == after.words.eraseIdx 1

def stableReadback (initial : List Header)
    (step : QotomPCIQuarantineObservation.StepWitness) : Bool :=
  match initial.find? (fun header => header.raw.bdf == step.step.target) with
  | none => false
  | some before => stableRegisters before.raw step.step.readback

def stableTrace (initial : List Header)
    (trace : List QotomPCIQuarantineObservation.StepWitness) : Bool :=
  trace.all (stableReadback initial)

inductive Error where
  | initial (reason : QotomPCIInventory.Error)
  | trace (reason : QotomPCIQuarantineObservation.Error)
  | registers (index : Nat)
  deriving BEq, DecidableEq, Repr

private def checkStable (initial : List Header) :
    Nat → List QotomPCIQuarantineObservation.StepWitness → Except Error Unit
  | _, [] => .ok ()
  | index, step :: tail =>
    if stableReadback initial step then checkStable initial (index + 1) tail
    else .error (.registers index)

structure Witness where
  initial : QotomPCIInventory.Witness
  trace : QotomPCIQuarantineObservation.Witness
  stable : stableTrace initial.headers trace.steps = true

def check (initialRaw : List RawHeader)
    (steps : List QotomPCIQuarantineObservation.Step) : Except Error Witness := do
  let initial ← (QotomPCIInventory.check initialRaw).mapError Error.initial
  let trace ← (QotomPCIQuarantineObservation.check steps).mapError Error.trace
  checkStable initial.headers 0 trace.steps
  if stable : stableTrace initial.headers trace.steps = true then
    pure ⟨initial, trace, stable⟩
  else throw (.registers 0)

theorem check_preserves_inputs (initialRaw : List RawHeader)
    (steps : List QotomPCIQuarantineObservation.Step) (w : Witness)
    (accepted : check initialRaw steps = .ok w) :
    w.initial.headers.map (·.raw) = initialRaw ∧ w.trace.steps.map (·.step) = steps := by
  unfold check at accepted
  cases initialResult : QotomPCIInventory.check initialRaw with
  | error reason =>
    simp [initialResult, Except.mapError, Bind.bind, Except.bind] at accepted
  | ok initial =>
    cases traceResult : QotomPCIQuarantineObservation.check steps with
    | error reason =>
      simp [initialResult, traceResult, Except.mapError, Bind.bind, Except.bind] at accepted
    | ok trace =>
      cases stableResult : checkStable initial.headers 0 trace.steps with
      | error reason =>
        simp [initialResult, traceResult, stableResult, Except.mapError,
          Bind.bind, Except.bind] at accepted
      | ok result =>
        simp [initialResult, traceResult, stableResult, Except.mapError,
          Bind.bind, Except.bind, Pure.pure, Except.pure] at accepted
        split at accepted
        · cases accepted
          exact ⟨QotomPCIInventory.check_preserves_raw initialRaw initial initialResult,
            QotomPCIQuarantineObservation.check_preserves_trace steps trace traceResult⟩
        · contradiction

theorem witnessed_registers_stable (w : Witness)
    (step : QotomPCIQuarantineObservation.StepWitness) (member : step ∈ w.trace.steps) :
    stableReadback w.initial.headers step = true := by
  have all := w.stable
  exact (List.all_eq_true.mp all) step member

theorem witnessed_initial_count (w : Witness) : w.initial.headers.length = 15 :=
  QotomPCIInventory.witness_has_fifteen_functions w.initial

theorem witnessed_trace_count (w : Witness) : w.trace.steps.length = 15 :=
  QotomPCIQuarantineObservation.witness_has_fifteen_steps w.trace

def Error.code : Error → UInt64
  | .initial reason => 0x100000 + reason.code
  | .trace reason => 0x200000 + reason.code
  | .registers index => 0x300000 + index.toUInt64

/-- One consumed hosted array contains fifteen initial 19-word headers,
followed by fifteen 25-word write/readback records. The declared common count
must be fifteen and the physical size exactly 660 before any field is read.
This allocates Lean objects and establishes no hardware-access authority. -/
@[export leanos_qotom_pci_quarantine_transition]
def checkWords (count : UInt64) (words : Array UInt64) : UInt64 :=
  if count != 15 then 0x10000
  else if words.size != 660 then 0x10001
  else
    let initial := (List.range 15).map fun index =>
      let field := fun i => words.getD (index * 19 + i) 0
      ({ bdf := ⟨field 0, field 1, field 2⟩
         words := (List.range 16).map (fun i => field (3 + i)) } : RawHeader)
    let steps := (List.range 15).map fun index =>
      let field := fun i => words.getD (285 + index * 25 + i) 0
      ({ target := ⟨field 0, field 1, field 2⟩
         offset := field 3, width := field 4, value := field 5
         readback := ⟨⟨field 6, field 7, field 8⟩,
           (List.range 16).map (fun i => field (9 + i))⟩ } : QotomPCIQuarantineObservation.Step)
    match check initial steps with
    | .ok _ => 1
    | .error reason => reason.code

end LeanOS.QotomPCIQuarantineTransition
