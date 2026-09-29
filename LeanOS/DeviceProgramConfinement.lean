import LeanOS.Wifi.Sim
import Std.Tactic.BVDecide

/-
Static confinement of Lean device programs (issue #447).

Device programs (`LeanOS/Wifi`, `LeanOS/Usb`) are encoded into a small
register-machine bytecode and run by `hardware/wifi/wifi-exec.h` in ring 0 of
the lab kernel. This module gives each program a `Policy` — MMIO window,
configuration offsets it may read or write, the command-register bits it may
clear or set, and whether it may learn bus addresses (`physAddr`) — and a
decidable checker `admissible` over the *encoded* instruction words.

The theorems are stated against `LeanOS.Wifi.Sim`, the total reference
simulator the tests run, through `guard`: a device wrapper that latches a
violation flag whenever the simulator asks the device for an effect outside
the policy. An admitted program never sets the flag, on any device model,
from any initial registers or scratch, for any number of steps:

* MMIO accesses stay inside the policy window (direct offsets statically;
  register-indirect offsets through the simulator's window check, the C
  executor's `OFF`);
* configuration reads and writes use only allow-listed offsets below 0x100;
* the command register changes only through `cfgUpdate32` within the
  policy's clear/set masks, so a sane policy never lets a program set Bus
  Master unless it admits DMA, nor write a BAR;
* `physAddr` runs only under a DMA policy.

Version-3 images also carry the policy, and both the simulator and the C
executor enforce it dynamically; `run_declared_confined` shows that this
alone confines *any* program to its declared policy.

This is a model-level result: that `wifi-exec.h` refines `Sim.step` is
tested (`leanos-wifi-xcheck`, differential fuzzing), not proved. Where a
device may write by DMA is a separate question (issue #448).
-/
namespace LeanOS.DeviceProgramConfinement

open LeanOS.Wifi.Bytecode LeanOS.Wifi.Sim

/-! ## The checker -/

/-- Static check of one encoded instruction against `π`. Instructions
without device effects, and register-indirect MMIO (bounded dynamically by
the window), are accepted. -/
def wordOk (π : Policy) (w : Word4) : Bool :=
  match w.op &&& 0xFF with
  | 2 => cfgAllowed π.cfgRead w.b
  | 3 => cfgAllowed π.cfgWrite w.a
  | 4 => mmioOk π.window w.b 4
  | 5 => mmioOk π.window w.b 2
  | 6 => mmioOk π.window w.a 4
  | 7 => mmioOk π.window w.a 2
  | 17 => mmioOk π.window w.a 4
  | 23 => mmioOk π.window w.a 4
  | 24 => mmioOk π.window w.a 4
  | 25 => π.dma
  | 26 => π.updateOk w.a w.b w.c
  | _ => true

/-- A program is admissible under `π` when its target window fits the
policy window and every instruction word passes `wordOk`. -/
def admissible (p : Program) (π : Policy) : Bool :=
  p.effTarget.windowBytes.toNat ≤ π.window.toNat && p.words.toList.all (wordOk π)

/-- The first instruction index that `wordOk` rejects (diagnostics). -/
def firstViolation (p : Program) (π : Policy) : Option Nat :=
  (List.range p.words.size).find? fun i => !wordOk π (p.words[i]!)

/-- A policy is sane when it never lets a program write the configuration
header (identity, command/status, BARs, expansion ROM, interrupt line: offsets
0x00–0x3C) directly, never lets it set I/O Space, and lets it set Bus Master
only together with DMA. -/
def _root_.LeanOS.Wifi.Bytecode.Policy.sane (π : Policy) : Bool :=
  π.cfgWrite &&& 0xFFFF == 0 && π.cmdSet &&& ~~~(if π.dma then 0x6 else 0x2) == 0

/-! ## The monitor -/

/-- `d` with a latched flag that becomes `true` as soon as the simulator
requests any device effect outside `π`. -/
def guard {σ} (π : Policy) (d : Device σ) : Device (σ × Bool) where
  read32 s off := let r := d.read32 s.1 off; (r.1, (r.2, s.2 || !mmioOk π.window off 4))
  read16 s off := let r := d.read16 s.1 off; (r.1, (r.2, s.2 || !mmioOk π.window off 2))
  write32 s off v := (d.write32 s.1 off v, s.2 || !mmioOk π.window off 4)
  write16 s off v := (d.write16 s.1 off v, s.2 || !mmioOk π.window off 2)
  cfgRead32 s off := let r := d.cfgRead32 s.1 off; (r.1, (r.2, s.2 || !cfgAllowed π.cfgRead off))
  cfgWrite32 s off v := (d.cfgWrite32 s.1 off v, s.2 || !cfgAllowed π.cfgWrite off)
  cfgUpdate32 s off c t := (d.cfgUpdate32 s.1 off c t, s.2 || !π.updateOk off c t)
  phys s off := let r := d.phys s.1 off; (r.1, (r.2, s.2 || !π.dma))

/-- The machine a step leaves behind, whether it continues or stops. -/
def _root_.LeanOS.Wifi.Sim.Step.machine {σ} : Step σ → Machine σ
  | .next m => m
  | .stop _ m => m

/-! ## Proofs -/

theorem iter_preserve {α} (P : α → Prop) (f : Nat → α → α)
    (hf : ∀ i a, P a → P (f i a)) : ∀ i n a, P a → P (iter f i n a)
  | _, 0, _, h => h
  | i, n + 1, a, h => iter_preserve P f hf (i + 1) n (f i a) (hf i a h)

theorem mmioOk_mono {w₁ w₂ off k : UInt32} (hw : w₁.toNat ≤ w₂.toNat)
    (h : mmioOk w₁ off k = true) : mmioOk w₂ off k = true := by
  simp only [mmioOk, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
  exact ⟨Nat.le_trans h.1 hw, h.2⟩

@[simp] theorem setReg_dev {σ} (m : Machine σ) (r v : UInt32) : (m.setReg r v).dev = m.dev := rfl
@[simp] theorem setReg_stack {σ} (m : Machine σ) (r v : UInt32) :
    (m.setReg r v).stack = m.stack := rfl
@[simp] theorem Step.machine_next {σ} (m : Machine σ) : (Step.next m).machine = m := rfl
@[simp] theorem Step.machine_stop {σ} (st) (m : Machine σ) : (Step.stop st m).machine = m := rfl
@[simp] theorem Step.machine_ite {σ} (c : Prop) [Decidable c] (a b : Step σ) :
    (if c then a else b).machine = if c then a.machine else b.machine := by split <;> rfl

/-- One instruction that passes `wordOk` keeps the violation flag clear. -/
theorem exec_confined {σ} (π : Policy) (d : Device σ) (p : Program)
    (hwin : p.effTarget.windowBytes.toNat ≤ π.window.toNat)
    (w : Word4) (hwi : wordOk π w = true)
    (m : Machine (σ × Bool)) (hm : m.dev.2 = false) :
    (exec p (guard π d) w m).machine.dev.2 = false := by
  unfold exec
  dsimp only
  simp only [wordOk] at hwi
  generalize w.op &&& 0xFF = b at hwi ⊢
  split
  all_goals (try dsimp only at hwi)
  all_goals (try simp_all [guard])
  all_goals (repeat' split)
  all_goals (try simp_all)
  all_goals first
    | exact mmioOk_mono hwin ‹_›
    | exact iter_preserve (fun (s : σ × Bool) => s.2 = false) _ (by simp_all) _ _ _ hm
    | exact iter_preserve (fun (a : ByteArray × (σ × Bool)) => a.2.2 = false) _
        (by simp_all) _ _ _ hm

/-- One instruction of a program that declares `π` keeps the flag clear,
whatever the instruction: the simulator's policy checks alone suffice. -/
theorem exec_declared_confined {σ} (π : Policy) (d : Device σ) (p : Program)
    (hpol : p.policy = some π)
    (hwin : p.effTarget.windowBytes.toNat ≤ π.window.toNat)
    (w : Word4) (m : Machine (σ × Bool)) (hm : m.dev.2 = false) :
    (exec p (guard π d) w m).machine.dev.2 = false := by
  unfold exec
  dsimp only
  generalize w.op &&& 0xFF = b
  split
  all_goals (try simp_all [guard])
  all_goals (repeat' split)
  all_goals (try simp_all)
  all_goals first
    | exact mmioOk_mono hwin ‹_›
    | exact iter_preserve (fun (s : σ × Bool) => s.2 = false) _
        (by have := mmioOk_mono hwin ‹mmioOk p.effTarget.windowBytes w.a 4 = true›; simp_all)
        _ _ _ hm
    | exact iter_preserve (fun (a : ByteArray × (σ × Bool)) => a.2.2 = false) _
        (by have := mmioOk_mono hwin ‹mmioOk p.effTarget.windowBytes w.a 4 = true›; simp_all)
        _ _ _ hm

/-- Lift a per-instruction flag invariant to whole runs. -/
theorem loop_flag {σ} (π : Policy) (d : Device σ) (p : Program)
    (hstep : ∀ (m : Machine (σ × Bool)), m.dev.2 = false →
      (step p (guard π d) m).machine.dev.2 = false) :
    ∀ fuel (m : Machine (σ × Bool)), m.dev.2 = false → (loop p (guard π d) fuel m).2.dev.2 = false
  | 0, _, hm => hm
  | fuel + 1, m, hm => by
    have hs := hstep m hm
    simp only [loop]
    split <;> rename_i heq <;> rw [heq] at hs
    · exact loop_flag π d p hstep fuel _ hs
    · exact hs

/-- **Static confinement.** An admissible program, run by the simulator on
any device model from any initial machine whose flag is clear (arbitrary
registers and scratch), never requests a device effect outside its policy. -/
theorem run_confined {σ} (π : Policy) (p : Program) (hp : admissible p π = true)
    (d : Device σ) (s0 : σ) (fuel : Nat)
    (init : Machine (σ × Bool) → Machine (σ × Bool))
    (hinit : ∀ m, (init m).dev = m.dev) :
    (run p (guard π d) (s0, false) fuel init).2.dev.2 = false := by
  simp only [admissible, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hp
  refine loop_flag π d p (fun m hm => ?_) fuel _ (by simp [hinit])
  unfold step
  split
  · exact exec_confined π d p hp.1 _ (hp.2 _ (Array.getElem_mem_toList ‹_›)) _ hm
  · simpa using hm

/-- **Dynamic confinement.** Any program whose image declares `π` (with a
target window inside the policy window, which the executor checks when it
parses the header) is confined to `π` by the simulator's own checks, whether
or not it passes `admissible`. -/
theorem run_declared_confined {σ} (π : Policy) (p : Program) (hpol : p.policy = some π)
    (hwin : p.effTarget.windowBytes.toNat ≤ π.window.toNat)
    (d : Device σ) (s0 : σ) (fuel : Nat)
    (init : Machine (σ × Bool) → Machine (σ × Bool))
    (hinit : ∀ m, (init m).dev = m.dev) :
    (run p (guard π d) (s0, false) fuel init).2.dev.2 = false := by
  refine loop_flag π d p (fun m hm => ?_) fuel _ (by simp [hinit])
  unfold step
  split
  · exact exec_declared_confined π d p hpol hwin _ _ hm
  · simpa using hm

/-- The return stack never exceeds the executor's 16 entries. -/
theorem step_stack_bounded {σ} (p : Program) (d : Device σ) (m : Machine σ)
    (hm : m.stack.length ≤ 16) : (step p d m).machine.stack.length ≤ 16 := by
  unfold step
  split
  · unfold exec
    dsimp only
    generalize (p.words[m.pc]).op &&& 0xFF = b
    split
    all_goals (try simp_all)
    all_goals (repeat' split)
    all_goals (try simp_all)
    all_goals omega
  · simpa using hm

/-! ## Sane policies bound the dangerous configuration effects -/

/-- Under a sane policy an allow-listed configuration write is never to the
header (identity, command, BARs, ROM BAR). -/
theorem sane_cfgWrite_outside_header (π : Policy) (hπ : π.sane = true) (off : UInt32)
    (h : cfgAllowed π.cfgWrite off = true) : 0x40 ≤ off := by
  simp only [Policy.sane, cfgAllowed, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hπ h
  obtain ⟨⟨hlt, hal⟩, hbit⟩ := h
  bv_decide

/-- Under a sane policy an admitted command update sets Bus Master only when
the policy admits DMA, and never sets I/O Space. -/
theorem sane_update_bus_master (π : Policy) (hπ : π.sane = true) (off c s : UInt32)
    (h : π.updateOk off c s = true) :
    (s &&& 0x4 ≠ 0 → π.dma = true) ∧ s &&& 0x1 = 0 := by
  simp only [Policy.sane, Policy.updateOk, Bool.and_eq_true, beq_iff_eq] at hπ h
  cases hd : π.dma <;> simp only [hd, ite_true] at hπ <;>
    refine ⟨fun hs => ?_, ?_⟩ <;> first | rfl | bv_decide

/-! ## Admitted Qotom profiles

The widest policy each Qotom device program may declare; the lab kernel's
`lab_dev_profiles` table (`hardware/lab/qotom-wifi.c.inc`) mirrors these and
refuses images whose declared policy is wider. -/

/-- BCM43224 at 02:00.0: identity and command reads, the two BAR0 backplane
windows (0x80, 0xAC), Memory Space only — the driver moves frames by
programmed I/O, so Bus Master stays off — and no DMA. -/
def qotomBcm43224Policy : Policy where
  window := 0x4000
  cfgRead := cfgBits [0x00, 0x04]
  cfgWrite := cfgBits [0x80, 0xAC]
  cmdClear := 0xFFFF0000
  cmdSet := 0x2
  dma := false

/-- Intel xHCI at 00:14.0: identity, command and the port-routing masks
(0xD4, 0xDC) readable; port routing (0xD0, 0xD8) writable; Memory Space and
Bus Master; DMA into scratch. -/
def qotomXhciPolicy : Policy where
  window := 0x10000
  cfgRead := cfgBits [0x00, 0x04, 0xD4, 0xDC]
  cfgWrite := cfgBits [0xD0, 0xD8]
  cmdClear := 0xFFFF0000
  cmdSet := 0x6
  dma := true

theorem qotomBcm43224Policy_sane : qotomBcm43224Policy.sane = true := by decide
theorem qotomXhciPolicy_sane : qotomXhciPolicy.sane = true := by decide

/-- The WiFi policy admits no DMA and never lets a program set Bus Master. -/
theorem qotomBcm43224Policy_no_bus_master (off c s : UInt32)
    (h : qotomBcm43224Policy.updateOk off c s = true) : s &&& 0x4 = 0 := by
  have := sane_update_bus_master _ qotomBcm43224Policy_sane off c s h
  exact Classical.byContradiction fun hs => Bool.false_ne_true (this.1 hs)

/-- Header layout of the policy words in a version-3 image, as the lab
kernel's profile table reads them. -/
theorem qotomBcm43224Policy_bits :
    qotomBcm43224Policy.cfgRead = 0x3 ∧ qotomBcm43224Policy.cfgWrite = 0x80100000000 := by
  decide

theorem qotomXhciPolicy_bits :
    qotomXhciPolicy.cfgRead = 0xA0000000000003 ∧ qotomXhciPolicy.cfgWrite = 0x50000000000000 := by
  decide

end LeanOS.DeviceProgramConfinement
