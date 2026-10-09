import LeanOS.Wifi.ExecRefinement

/-
The generated device-program executor (issue #494, ADR 0020): headline
theorems.

`Exec.step` is the executor's instruction step written against
named C hook primitives; `leanos_device_program_step` is its generated C
(`hardware/wifi/wifi-gen-exec.h` supplies the hooks and the step loop).
`LeanOS.Wifi.ExecRefinement` reads the hooks over a simulator machine and
proves the step is `Sim.step`; this module restates the results the
assurance argument rests on. What remains trusted: the Lean and C compilers (as for every
generated export) and that each C hook implements its reading
(`ExecRefinement.instHooksSt`); the hosted differential and its hook mutants
(`scripts/check-device-programs.sh`) are the regression test of the latter.
-/
namespace LeanOS.DeviceProgramExecutor

open LeanOS.Wifi LeanOS.Wifi.Bytecode LeanOS.Wifi.Sim LeanOS.Wifi.ExecRefinement

variable {σ : Type}

/-- The generated step, read over a machine a run can reach, is the
simulator step. -/
theorem generated_step_eq (p : Program) (d : Device σ) (m : Machine σ) (hW : WF p)
    (hI : Inv p d m) : decode (Exec.step (St.ofMachine p d m)) = Sim.step p d m :=
  step_eq p d m hW hI

/-- The generated executor's run is the simulator's run. -/
theorem generated_run_eq (p : Program) (d : Device σ) (base : UInt32)
    (hphys : ∀ s, (d.phys s 0).1 = base) (hW : WF p) (s0 : σ) (fuel : Nat) :
    ExecRefinement.run p d s0 fuel = Sim.run p d s0 fuel :=
  run_eq p d base hphys hW s0 fuel

/-- An admissible program run by the generated executor stays inside its
policy. -/
theorem generated_run_confined (π : Policy) (p : Program)
    (hp : DeviceProgramConfinement.admissible p π = true) (hW : WF p) (d : Device σ)
    (base : UInt32) (hphys : ∀ s, (d.phys s 0).1 = base) (s0 : σ) (fuel : Nat) :
    (ExecRefinement.run p (DeviceProgramConfinement.guard π d) (s0, false) fuel).2.dev.2 = false :=
  run_confined_generated π p hp hW d base hphys s0 fuel

/-- A program whose image declares its policy is held to it by the generated
executor's own checks. -/
theorem generated_run_declared_confined (π : Policy) (p : Program) (hpol : p.policy = some π)
    (hwin : p.effTarget.windowBytes.toNat ≤ π.window.toNat) (hW : WF p) (d : Device σ)
    (base : UInt32) (hphys : ∀ s, (d.phys s 0).1 = base) (s0 : σ) (fuel : Nat) :
    (ExecRefinement.run p (DeviceProgramConfinement.guard π d) (s0, false) fuel).2.dev.2 = false :=
  run_declared_confined_generated π p hpol hwin hW d base hphys s0 fuel

/-- Under the generated executor the declared descriptor map holds only
scratch pointers. -/
theorem generated_run_declared_descriptors (π : Policy) (p : Program) (hpol : p.policy = some π)
    (hW : WF p) (d : Device σ) (base : UInt32) (hphys : ∀ s, (d.phys s 0).1 = base) (s0 : σ)
    (fuel : Nat) : descOk π base (ExecRefinement.run p d s0 fuel).2.mem = true :=
  run_declared_descriptors_generated π p hpol hW d base hphys s0 fuel

end LeanOS.DeviceProgramExecutor
