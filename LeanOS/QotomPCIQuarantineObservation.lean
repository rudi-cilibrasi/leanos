import LeanOS.QotomPCIInventory

/-!
Checks an ordered trace of command writes and configuration readbacks against
one captured inventory. This is observation validation, not an implementation
of PCI access or a proof of DMA containment, quiescence, or enumeration.
-/
namespace LeanOS.QotomPCIQuarantineObservation

open DMAQuarantine PCIHeaderObservation

/-- Downstream endpoints first, then bus-zero endpoints, then bridges. This
order is a proposed trace contract; hardware execution remains separate. -/
def order : List QotomPCIInventory.Entry :=
  let endpoints := QotomPCIInventory.baseline.filter fun e =>
    match e.routing with | .endpoint => true | .bridge .. => false
  endpoints.filter (fun e => e.bdf.bus != 0) ++
    endpoints.filter (fun e => e.bdf.bus == 0) ++
    QotomPCIInventory.baseline.filter (fun e =>
      match e.routing with | .bridge .. => true | .endpoint => false)

/-- One recorded write followed by its recorded full-header readback.
The adapter must preserve this ordering and report every operation. -/
structure Step where
  target : BDF
  offset : UInt64
  width : UInt64
  value : UInt64
  readback : RawHeader
  deriving BEq, DecidableEq, Repr

inductive Error where
  | count
  | write (index : Nat)
  | target (index : Nat)
  | header (index : Nat) (reason : PCIHeaderObservation.Error)
  | inventory (index : Nat)
  | command (index : Nat)
  deriving BEq, DecidableEq, Repr

structure StepWitness where
  step : Step
  header : Header
  decoded : decode step.readback = .ok header
  write : step.offset = 4 ∧ step.width = 2 ∧ step.value = 0
  target : step.target = step.readback.bdf
  command : header.command = 0

def checkStep (index : Nat) (expected : QotomPCIInventory.Entry)
    (step : Step) : Except Error StepWitness :=
  if write : step.offset = 4 ∧ step.width = 2 ∧ step.value = 0 then
    if target : step.target = step.readback.bdf then
      match decoded : decode step.readback with
      | .error reason => .error (.header index reason)
      | .ok header =>
        if QotomPCIInventory.project header != expected then .error (.inventory index)
        else if command : header.command = 0 then
          .ok ⟨step, header, decoded, write, target, command⟩
        else .error (.command index)
    else .error (.target index)
  else .error (.write index)

private theorem checkStep_preserves_step (index : Nat)
    (expected : QotomPCIInventory.Entry) (step : Step) (w : StepWitness)
    (accepted : checkStep index expected step = .ok w) : w.step = step := by
  unfold checkStep at accepted
  repeat' (split at accepted <;> try contradiction)
  cases accepted
  rfl

private def checkSteps : Nat → List QotomPCIInventory.Entry → List Step →
    Except Error (List StepWitness)
  | _, [], [] => .ok []
  | index, expected :: rest, step :: tail => do
    let accepted ← checkStep index expected step
    let suffix ← checkSteps (index + 1) rest tail
    pure (accepted :: suffix)
  | _, _, _ => .error .count

private theorem checkSteps_preserves_steps (index : Nat)
    (expected : List QotomPCIInventory.Entry) (steps : List Step)
    (accepted : List StepWitness) (ok : checkSteps index expected steps = .ok accepted) :
    accepted.map (·.step) = steps := by
  induction expected generalizing index steps accepted with
  | nil =>
    cases steps with
    | nil => cases ok; rfl
    | cons step tail => contradiction
  | cons first rest ih =>
    cases steps with
    | nil => contradiction
    | cons step tail =>
      cases headResult : checkStep index first step with
      | error reason => simp [checkSteps, headResult, Bind.bind, Except.bind] at ok
      | ok head =>
        cases tailResult : checkSteps (index + 1) rest tail with
        | error reason => simp [checkSteps, headResult, tailResult, Bind.bind, Except.bind] at ok
        | ok suffix =>
          simp [checkSteps, headResult, tailResult, Bind.bind, Except.bind, Pure.pure, Except.pure] at ok
          subst accepted
          simp only [List.map_cons]
          rw [checkStep_preserves_step index first step head headResult,
            ih (index + 1) tail suffix tailResult]

structure Witness where
  steps : List StepWitness
  inventory : steps.map (fun s => QotomPCIInventory.project s.header) = order

def check (steps : List Step) : Except Error Witness := do
  if steps.length != order.length then throw .count
  let accepted ← checkSteps 0 order steps
  if inventory : accepted.map (fun s => QotomPCIInventory.project s.header) = order then
    pure ⟨accepted, inventory⟩
  else throw .count

theorem check_preserves_trace (input : List Step) (w : Witness)
    (accepted : check input = .ok w) : w.steps.map (·.step) = input := by
  unfold check at accepted
  cases decoded : checkSteps 0 order input with
  | error reason =>
    simp [decoded, Bind.bind, Except.bind] at accepted
    split at accepted <;> contradiction
  | ok steps =>
    simp [decoded, Bind.bind, Except.bind, Pure.pure, Except.pure] at accepted
    split at accepted
    · split at accepted
      · cases accepted
        exact checkSteps_preserves_steps 0 order input steps decoded
      · contradiction
    · contradiction

theorem witnessed_command_zero (w : Witness) (step : StepWitness)
    (_member : step ∈ w.steps) : step.header.command = 0 := step.command

theorem witnessed_write_is_command_word (w : Witness) (step : StepWitness)
    (_member : step ∈ w.steps) :
    step.step.offset = 4 ∧ step.step.width = 2 ∧ step.step.value = 0 := step.write

theorem order_has_fifteen_functions : order.length = 15 := by decide

theorem witness_has_fifteen_steps (w : Witness) : w.steps.length = 15 := by
  have length := congrArg List.length w.inventory
  simpa only [List.length_map, order_has_fifteen_functions] using length

end LeanOS.QotomPCIQuarantineObservation
