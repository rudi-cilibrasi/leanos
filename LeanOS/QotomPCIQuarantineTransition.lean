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

theorem witnessed_registers_stable (w : Witness)
    (step : QotomPCIQuarantineObservation.StepWitness) (member : step ∈ w.trace.steps) :
    stableReadback w.initial.headers step = true := by
  have all := w.stable
  exact (List.all_eq_true.mp all) step member

theorem witnessed_initial_count (w : Witness) : w.initial.headers.length = 15 :=
  QotomPCIInventory.witness_has_fifteen_functions w.initial

theorem witnessed_trace_count (w : Witness) : w.trace.steps.length = 15 :=
  QotomPCIQuarantineObservation.witness_has_fifteen_steps w.trace

end LeanOS.QotomPCIQuarantineTransition
