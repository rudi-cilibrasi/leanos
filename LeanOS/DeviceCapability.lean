import LeanOS.Capability
import LeanOS.DeviceProgramConfinement

/-
Device programs as capability-mediated kernel services (issue #449, stage 1).

The executor stays in ring 0 but runs only on behalf of a subject that holds
a *device capability* (ADR 0022). This module layers that authority over the
existing capability model without changing it:

* `System.caps` is an unmodified `Capability.State`; capability operations act
  on it alone, so every theorem of `LeanOS.Capability` applies to it
  (`cap_step_caps`, `non_cap_step_caps`).
* The kernel grants a subject a device capability naming one admitted device
  (`grant`, kernel authority only). With it the subject may `bind` a program
  — accepted only if the program declares the device's policy and passes
  `admissible` under it — and `invoke` the bound program for a bounded number
  of steps, resuming its suspended machine. A `yield` hands one event (a key
  press) back to the subject.
* `revoke` removes the device capability, the bound program and its machine.

Every device is modelled behind the `guard` monitor of
`LeanOS.DeviceProgramConfinement`. The theorems show that only an `invoke` by
a current holder of that device's capability changes a device's state, that
invocation never touches another device or the capability state, and that
the violation flag of every device stays clear across any transition
sequence: device effects never leave the device's policy.

Not modelled: the ring-3 subjects' code, IPC delivery of the yielded events,
scheduling, and step-time accounting; the C kernel service is tested, not
proved, against this model.
-/
namespace LeanOS.DeviceCapability

open LeanOS.Capability LeanOS.Wifi.Bytecode LeanOS.Wifi.Sim LeanOS.DeviceProgramConfinement

/-- An admitted PCI function and the policy its programs must declare. -/
structure Device where
  target : Target
  policy : Policy

/-- A device capability names one admitted device. -/
structure DeviceCap where
  device : Nat
  deriving DecidableEq, Repr

/-- A subject's executor machine with its device state detached. -/
abbrev Suspended := Machine Unit

def _root_.LeanOS.Wifi.Sim.Machine.withDev {α β} (m : Machine α) (d : β) : Machine β :=
  { regs := m.regs, pc := m.pc, stack := m.stack, mem := m.mem, dev := d,
    prints := m.prints, steps := m.steps }

/-- Kernel state: capabilities, admitted devices, device capabilities, bound
programs with their suspended machines, and each device's state behind the
`guard` monitor (`.2` is the violation flag). -/
structure System (σ : Type) where
  caps : Capability.State
  devices : Nat → Option Device
  deviceCaps : SubjectId → Option DeviceCap
  bound : SubjectId → Option (Program × Suspended)
  devState : Nat → σ × Bool

inductive Transition where
  /-- Any capability-model operation. -/
  | cap (op : Capability.State → Capability.Outcome)
  /-- Kernel: give `subject` a capability for admitted device `device`. -/
  | grant (subject : SubjectId) (device : Nat)
  /-- Holder: bind `program` to its device capability. -/
  | bind (subject : SubjectId) (program : Program)
  /-- Holder: run the bound program for at most `fuel` more steps. -/
  | invoke (subject : SubjectId) (fuel : Nat)
  /-- Kernel: withdraw `subject`'s device capability and bound program. -/
  | revoke (subject : SubjectId)

inductive Reply where
  | accepted
  | ran (status : Status)
  | denied
  deriving Repr, BEq

/-- One transition over the device models `models` (each device's behaviour). -/
def step {σ} (models : Nat → Wifi.Sim.Device σ) (sys : System σ) :
    Transition → System σ × Reply
  | .cap op => ({ sys with caps := (op sys.caps).state }, .accepted)
  | .grant subject device =>
    match sys.devices device with
    | some _ => ({ sys with deviceCaps := fun s => if s = subject then some ⟨device⟩ else sys.deviceCaps s,
                            bound := fun s => if s = subject then none else sys.bound s }, .accepted)
    | none => (sys, .denied)
  | .bind subject program =>
    match sys.deviceCaps subject with
    | none => (sys, .denied)
    | some c =>
      match sys.devices c.device with
      | none => (sys, .denied)
      | some D =>
        if program.policy = some D.policy ∧ program.effTarget = D.target ∧
            admissible program D.policy = true then
          ({ sys with bound := fun s => if s = subject then some (program, { dev := () }) else sys.bound s },
            .accepted)
        else (sys, .denied)
  | .invoke subject fuel =>
    match sys.deviceCaps subject, sys.bound subject with
    | some c, some (program, m) =>
      match sys.devices c.device with
      | none => (sys, .denied)
      | some D =>
        let (status, m') := loop program (guard D.policy (models c.device)) fuel
          (m.withDev (sys.devState c.device))
        ({ sys with
            bound := fun s => if s = subject then some (program, m'.withDev ()) else sys.bound s,
            devState := fun k => if k = c.device then m'.dev else sys.devState k },
          .ran status)
    | _, _ => (sys, .denied)
  | .revoke subject =>
    ({ sys with deviceCaps := fun s => if s = subject then none else sys.deviceCaps s,
                bound := fun s => if s = subject then none else sys.bound s }, .accepted)

/-- Run a list of transitions. -/
def run {σ} (models : Nat → Wifi.Sim.Device σ) (sys : System σ) : List Transition → System σ
  | [] => sys
  | t :: ts => run models (step models sys t).1 ts

/-- The system invariant: every bound program still passes the check under
its holder's device policy, and no device's violation flag is set. -/
def Inv {σ} (sys : System σ) : Prop :=
  (∀ s program m, sys.bound s = some (program, m) →
    ∃ c D, sys.deviceCaps s = some c ∧ sys.devices c.device = some D ∧
      program.policy = some D.policy ∧ admissible program D.policy = true) ∧
  (∀ k, (sys.devState k).2 = false)

/-! ## Capability state: untouched except by capability operations -/

theorem cap_step_caps {σ} (models : Nat → Wifi.Sim.Device σ) (sys : System σ)
    (op : Capability.State → Capability.Outcome) :
    (step models sys (.cap op)).1.caps = (op sys.caps).state := rfl

theorem non_cap_step_caps {σ} (models : Nat → Wifi.Sim.Device σ) (sys : System σ)
    (t : Transition) (ht : ∀ op, t ≠ .cap op) : (step models sys t).1.caps = sys.caps := by
  cases t with
  | cap op => exact absurd rfl (ht op)
  | grant s k => simp only [step]; split <;> rfl
  | bind s p => simp only [step]; split <;> (try split) <;> (try split) <;> rfl
  | invoke s f => simp only [step]; split <;> (try split) <;> rfl
  | revoke s => rfl

/-! ## Device effects need a device capability -/

/-- Only an `invoke` by a current holder of device `k`'s capability changes
`k`'s state. -/
theorem device_state_changes_only_by_holder {σ} (models : Nat → Wifi.Sim.Device σ)
    (sys : System σ) (t : Transition) (k : Nat)
    (h : (step models sys t).1.devState k ≠ sys.devState k) :
    ∃ subject fuel, t = .invoke subject fuel ∧ sys.deviceCaps subject = some ⟨k⟩ := by
  cases t with
  | cap op => exact absurd rfl h
  | grant s d => simp only [step] at h; split at h <;> exact absurd rfl h
  | bind s p =>
    simp only [step] at h
    split at h
    · exact absurd rfl h
    · split at h
      · exact absurd rfl h
      · split at h <;> exact absurd rfl h
  | invoke s f =>
    simp only [step] at h
    split at h
    · rename_i c prog m hc hb
      split at h
      · exact absurd rfl h
      · by_cases hk : k = c.device
        · subst hk; exact ⟨s, f, rfl, hc⟩
        · simp [hk] at h
    · exact absurd rfl h
  | revoke s => exact absurd rfl h

/-- A subject without a device capability can neither bind nor invoke:
the system is unchanged and the reply is `denied`. -/
theorem no_capability_no_effect {σ} (models : Nat → Wifi.Sim.Device σ) (sys : System σ)
    (subject : SubjectId) (hnone : sys.deviceCaps subject = none) :
    (∀ program, step models sys (.bind subject program) = (sys, .denied)) ∧
    (∀ fuel, step models sys (.invoke subject fuel) = (sys, .denied)) := by
  constructor
  · intro program; simp [step, hnone]
  · intro fuel; simp [step, hnone]

/-- After `revoke`, the subject's invocations are denied. -/
theorem revoke_denies_invoke {σ} (models : Nat → Wifi.Sim.Device σ) (sys : System σ)
    (subject : SubjectId) (fuel : Nat) :
    (step models (step models sys (.revoke subject)).1 (.invoke subject fuel)).2 = .denied := by
  simp [step]

/-- Only programs admitted under the device's policy are ever bound. -/
theorem bind_accepted_admissible {σ} (models : Nat → Wifi.Sim.Device σ) (sys : System σ)
    (subject : SubjectId) (program : Program)
    (h : (step models sys (.bind subject program)).2 = .accepted) :
    ∃ c D, sys.deviceCaps subject = some c ∧ sys.devices c.device = some D ∧
      program.policy = some D.policy ∧ admissible program D.policy = true := by
  simp only [step] at h
  split at h
  · cases h
  · rename_i c hc
    split at h
    · cases h
    · rename_i D hD
      split at h
      · rename_i hp; exact ⟨c, D, hc, hD, hp.1, hp.2.2⟩
      · cases h

/-! ## Confinement is preserved by every transition -/

theorem step_inv {σ} (models : Nat → Wifi.Sim.Device σ) (sys : System σ) (hinv : Inv sys)
    (t : Transition) : Inv (step models sys t).1 := by
  obtain ⟨hb, hf⟩ := hinv
  cases t with
  | cap op => exact ⟨hb, hf⟩
  | grant subject device =>
    simp only [step]
    split
    · refine ⟨fun s program m h => ?_, hf⟩
      by_cases hs : s = subject
      · simp [hs] at h
      · simp only [hs, ite_false] at h ⊢
        exact hb s program m h
    · exact ⟨hb, hf⟩
  | bind subject program =>
    simp only [step]
    split
    · exact ⟨hb, hf⟩
    · rename_i c hc
      split
      · exact ⟨hb, hf⟩
      · rename_i D hD
        split
        · rename_i hp
          refine ⟨fun s prog m h => ?_, hf⟩
          by_cases hs : s = subject
          · subst hs; simp only [ite_true, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, -⟩ := h
            exact ⟨c, D, hc, hD, hp.1, hp.2.2⟩
          · simp only [hs, ite_false] at h; exact hb s prog m h
        · exact ⟨hb, hf⟩
  | invoke subject fuel =>
    simp only [step]
    split
    · rename_i c prog m hc hbound
      split
      · exact ⟨hb, hf⟩
      · rename_i D hD
        obtain ⟨c', D', hc', hD', hpol, hadm⟩ := hb subject prog m hbound
        rw [hc] at hc'; cases hc'
        rw [hD] at hD'; cases hD'
        simp only [admissible, Bool.and_eq_true, decide_eq_true_eq] at hadm
        have hrun := loop_flag D.policy (models c.device) prog
          (fun m hm => by
            unfold Wifi.Sim.step
            split
            · exact exec_declared_confined D.policy _ prog hpol hadm.1.1 _ _ hm
            · simpa using hm)
          fuel (m.withDev (sys.devState c.device)) (hf c.device)
        refine ⟨fun s prog' m' h => ?_, fun k => ?_⟩
        · by_cases hs : s = subject
          · subst hs
            simp only [ite_true, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, -⟩ := h
            exact ⟨c, D, hc, hD, hpol, by
              simp only [admissible, Bool.and_eq_true, decide_eq_true_eq]; exact hadm⟩
          · simp only [hs, ite_false] at h; exact hb s prog' m' h
        · by_cases hk : k = c.device
          · subst hk; simpa using hrun
          · simp only [hk, ite_false]; exact hf k
    · exact ⟨hb, hf⟩
  | revoke subject =>
    refine ⟨fun s program m h => ?_, hf⟩
    by_cases hs : s = subject
    · simp [step, hs] at h
    · simp only [step, hs, ite_false] at h ⊢; exact hb s program m h

/-- **Device confinement for the kernel service.** From a system whose
bound programs are admitted and whose device flags are clear, no sequence of
capability operations, grants, binds, invocations and revocations ever makes
a device perform an effect outside its policy. -/
theorem run_inv {σ} (models : Nat → Wifi.Sim.Device σ) :
    ∀ (ts : List Transition) (sys : System σ), Inv sys → Inv (run models sys ts)
  | [], _, h => h
  | t :: ts, sys, h => run_inv models ts _ (step_inv models sys h t)

/-- A fresh system (no device capabilities or bound programs, flags clear)
satisfies the invariant. -/
theorem initial_inv {σ} (caps : Capability.State) (devices : Nat → Option Device)
    (dev0 : Nat → σ) :
    Inv ({ caps, devices, deviceCaps := fun _ => none, bound := fun _ => none,
           devState := fun k => (dev0 k, false) } : System σ) :=
  ⟨fun _ _ _ h => by simp at h, fun _ => rfl⟩

/-- Invoking one device never changes another device's state. -/
theorem invoke_other_device_unchanged {σ} (models : Nat → Wifi.Sim.Device σ) (sys : System σ)
    (subject : SubjectId) (fuel : Nat) (c : DeviceCap) (hc : sys.deviceCaps subject = some c)
    (k : Nat) (hk : k ≠ c.device) :
    (step models sys (.invoke subject fuel)).1.devState k = sys.devState k := by
  refine Classical.byContradiction fun hne => ?_
  obtain ⟨s, f, ht, hs⟩ := device_state_changes_only_by_holder models sys _ k hne
  cases ht
  rw [hc] at hs; cases hs; exact hk rfl

/-! ## Witness: a keyboard-shaped driver delivering one event -/

/-- A one-device system: device 0 is the xHCI under its Qotom policy. -/
def witnessSystem : System Unit :=
  { caps := { subjects := fun _ => false, objects := fun _ => false, kinds := fun _ => none,
              slots := fun _ _ => none }
    devices := fun k => if k = 0 then
      some { target := LeanOS.Wifi.Bytecode.Target.mk 0 20 0 0x0f358086 0x10000,
             policy := qotomXhciPolicy } else none
    deviceCaps := fun _ => none
    bound := fun _ => none
    devState := fun _ => ((), false) }

/-- Yield the key 'A', then halt. -/
def witnessProgram : Program :=
  { words := #[⟨27 ||| 0x100, 0x41, 0, 0⟩, ⟨0, 0, 0, 0⟩], blob := .empty, sections := #[],
    target := some (LeanOS.Wifi.Bytecode.Target.mk 0 20 0 0x0f358086 0x10000),
    policy := some qotomXhciPolicy }

def witnessModels : Nat → Wifi.Sim.Device Unit := fun _ => Wifi.Sim.Device.none

def witnessReplies (ts : List Transition) : List Reply :=
  (ts.foldl (fun (acc : System Unit × List Reply) t =>
    let r := step witnessModels acc.1 t
    (r.1, acc.2 ++ [r.2])) (witnessSystem, [])).2

/- Subject 1 is granted the device, binds the program, receives the key
through a yield and then the halt; subject 2, never granted, is denied; after
revocation subject 1 is denied too. -/
#guard witnessReplies [.grant 1 0, .bind 1 witnessProgram, .invoke 1 10, .invoke 1 10,
    .invoke 2 10, .revoke 1, .invoke 1 10] ==
  [.accepted, .accepted, .ran (.yield 0x41), .ran .halt, .denied, .accepted, .denied]

end LeanOS.DeviceCapability
