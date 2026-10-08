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
  | 7 => mmioOk π.window w.a 2 && !π.sinkTouch w.a
  | 17 => mmioOk π.window w.a 4 && !π.sinkTouch w.a
  | 23 => mmioOk π.window w.a 4
  | 24 => mmioOk π.window w.a 4 && !π.sinkTouch w.a
  | 25 => π.dma
  | 26 => π.updateOk w.a w.b w.c
  | 28 => mmioOk π.window w.b 1
  | 29 => mmioOk π.window w.a 1 && !π.sinkTouch w.a
  | _ => true

/-- A program is admissible under `π` when its target window fits the
policy window, every instruction word passes `wordOk`, and — since values
written to address sinks and descriptor fields are only known at run time — a
policy with address sinks or a descriptor map is declared in the image, so the
executor checks them; the descriptor map must be one the executor accepts. -/
def admissible (p : Program) (π : Policy) : Bool :=
  p.effTarget.windowBytes.toNat ≤ π.window.toNat && p.words.toList.all (wordOk π) &&
    (((π.addrSinks.isEmpty && π.descriptors.isEmpty) || decide (p.policy = some π)) &&
      π.descWf)

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
requests any device effect outside `π`, including a write to an address
sink of a value that is not a bus address inside scratch (low dword) or not
zero (high dword). -/
def guard {σ} (π : Policy) (d : Device σ) : Device (σ × Bool) where
  read32 s off := let r := d.read32 s.1 off; (r.1, (r.2, s.2 || !mmioOk π.window off 4))
  read16 s off := let r := d.read16 s.1 off; (r.1, (r.2, s.2 || !mmioOk π.window off 2))
  write32 s off v :=
    (d.write32 s.1 off v, s.2 || !mmioOk π.window off 4 || !π.sinkOk (d.phys s.1 0).1 off v)
  write16 s off v := (d.write16 s.1 off v, s.2 || !mmioOk π.window off 2 || π.sinkTouch off)
  cfgRead32 s off := let r := d.cfgRead32 s.1 off; (r.1, (r.2, s.2 || !cfgAllowed π.cfgRead off))
  cfgWrite32 s off v := (d.cfgWrite32 s.1 off v, s.2 || !cfgAllowed π.cfgWrite off)
  cfgUpdate32 s off c t := (d.cfgUpdate32 s.1 off c t, s.2 || !π.updateOk off c t)
  phys s off := let r := d.phys s.1 off; (r.1, (r.2, s.2 || !π.dma))
  read8 s off := let r := d.read8 s.1 off; (r.1, (r.2, s.2 || !mmioOk π.window off 1))
  write8 s off v := (d.write8 s.1 off v, s.2 || !mmioOk π.window off 1 || π.sinkTouch off)

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
@[simp] theorem setReg_mem {σ} (m : Machine σ) (r v : UInt32) : (m.setReg r v).mem = m.mem := rfl
@[simp] theorem Step.machine_next {σ} (m : Machine σ) : (Step.next m).machine = m := rfl
@[simp] theorem Step.machine_stop {σ} (st) (m : Machine σ) : (Step.stop st m).machine = m := rfl
@[simp] theorem Step.machine_ite {σ} (c : Prop) [Decidable c] (a b : Step σ) :
    (if c then a else b).machine = if c then a.machine else b.machine := by split <;> rfl

/-- One instruction that passes `wordOk` keeps the violation flag clear. -/
theorem exec_confined {σ} (π : Policy) (d : Device σ) (p : Program)
    (hwin : p.effTarget.windowBytes.toNat ≤ π.window.toNat)
    (hsink : π.addrSinks = [] ∨ p.policy = some π)
    (w : Word4) (hwi : wordOk π w = true)
    (m : Machine (σ × Bool)) (hm : m.dev.2 = false) :
    (exec p (guard π d) w m).machine.dev.2 = false := by
  unfold exec
  dsimp only
  simp only [wordOk] at hwi
  generalize w.op &&& 0xFF = b at hwi ⊢
  rcases hsink with hsink | hsink
  all_goals split
  all_goals (try dsimp only at hwi)
  all_goals (try simp_all [guard, Policy.sinkOk_of_not_touch, Policy.sinkTouch_of_nil])
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
  all_goals (try simp_all [guard, Policy.sinkOk_of_not_touch])
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
  simp only [admissible, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    Bool.or_eq_true, List.isEmpty_iff] at hp
  refine loop_flag π d p (fun m hm => ?_) fuel _ (by simp [hinit])
  unfold step
  split
  · exact exec_confined π d p hp.1.1 (hp.2.1.imp And.left id) _
      (hp.1.2 _ (Array.getElem_mem_toList ‹_›)) _ hm
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

/-! ## Descriptor pointers (issue #495)

The descriptor map of a policy names the scratch fields a DMA controller
reads as bus addresses. The simulator refuses any scratch store after which a
field of the map would hold anything but zero or a bus address inside scratch
(`descOk`), and FIFO input into the map. With a fixed bus address of scratch,
the map therefore holds only scratch pointers in every reachable state. -/

/-- One instruction of a program that declares `π` keeps every descriptor
field a scratch pointer (or zero), whatever the instruction. -/
theorem exec_descOk {σ} (π : Policy) (d : Device σ) (p : Program) (hpol : p.policy = some π)
    (base : UInt32) (hphys : ∀ s, (d.phys s 0).1 = base)
    (w : Word4) (m : Machine σ) (hm : descOk π base m.mem = true) :
    descOk π base (exec p d w m).machine.mem = true := by
  unfold exec
  dsimp only
  generalize w.op &&& 0xFF = b
  split
  all_goals (try simp_all)
  all_goals (repeat' split)
  all_goals (try simp_all)

/-- Lift the descriptor invariant to whole runs. -/
theorem loop_descOk {σ} (π : Policy) (d : Device σ) (p : Program) (hpol : p.policy = some π)
    (base : UInt32) (hphys : ∀ s, (d.phys s 0).1 = base) :
    ∀ fuel (m : Machine σ), descOk π base m.mem = true →
      descOk π base (loop p d fuel m).2.mem = true
  | 0, _, hm => hm
  | fuel + 1, m, hm => by
    have hs : descOk π base (step p d m).machine.mem = true := by
      unfold step
      split
      · exact exec_descOk π d p hpol base hphys _ _ hm
      · simpa using hm
    simp only [loop]
    split <;> rename_i heq <;> rw [heq] at hs
    · exact loop_descOk π d p hpol base hphys fuel _ hs
    · exact hs

theorem get_zero (n i : Nat) : (ByteArray.mk (Array.replicate n 0)).get! i = 0 := by
  simp only [ByteArray.get!]
  rw [getElem!_def]
  split
  · rename_i h; simp only [Array.getElem?_replicate] at h; split at h <;> simp_all
  · rfl

theorem le32_zero (i : Nat) : le32 (ByteArray.mk (Array.replicate scratchBytes 0)) i = 0 := by
  simp [le32, memLoad, get_zero]
  rfl

/-- Zeroed scratch, as every executor starts, satisfies any descriptor map. -/
theorem descOk_zero (π : Policy) (base : UInt32) :
    descOk π base (ByteArray.mk (Array.replicate scratchBytes 0)) = true := by
  simp [descOk, le32_zero, ptrOk]

/-- **Descriptor pointers.** A program whose image declares `π`, run by the
simulator from zeroed scratch on any device model whose bus address of
scratch is fixed, for any number of steps, leaves every field of `π`'s
descriptor map holding zero or a bus address inside scratch. -/
theorem run_declared_descriptors {σ} (π : Policy) (p : Program) (hpol : p.policy = some π)
    (d : Device σ) (base : UInt32) (hphys : ∀ s, (d.phys s 0).1 = base) (s0 : σ) (fuel : Nat) :
    descOk π base (run p d s0 fuel).2.mem = true :=
  loop_descOk π d p hpol base hphys fuel _ (descOk_zero π base)

/-- The same for every admissible program: one whose policy has a descriptor
map must declare it. -/
theorem run_admissible_descriptors {σ} (π : Policy) (p : Program) (hp : admissible p π = true)
    (d : Device σ) (base : UInt32) (hphys : ∀ s, (d.phys s 0).1 = base) (s0 : σ) (fuel : Nat) :
    descOk π base (run p d s0 fuel).2.mem = true := by
  simp only [admissible, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true,
    List.isEmpty_iff] at hp
  rcases hp.2.1 with h | h
  · simp [descOk, h.2]
  · exact run_declared_descriptors π p h d base hphys s0 fuel

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
windows (0x80, 0xAC), Memory Space set and Bus Master cleared — the driver
moves frames by programmed I/O, so the card cannot master the bus at all
while it runs — and no DMA. -/
def qotomBcm43224Policy : Policy where
  window := 0x4000
  cfgRead := cfgBits [0x00, 0x04]
  cfgWrite := cfgBits [0x80, 0xAC]
  cmdClear := 0xFFFF0004
  cmdSet := 0x2
  dma := false

/-- Intel xHCI at 00:14.0: identity, command and the port-routing masks
(0xD4, 0xDC) readable; port routing (0xD0, 0xD8) writable; Memory Space and
Bus Master; DMA into scratch. The four registers from which the controller
finds every DMA structure — CRCR (0x98), DCBAAP (0xB0), ERSTBA (0x2030)
and ERDP (0x2038) with CAPLENGTH 0x80 and runtime base 0x2000 — are address
sinks: they only ever receive bus addresses inside scratch. The descriptor
map is the driver's `LeanOS.Usb.Xhci.descriptorMap` for the Bay Trail layout:
every pointer field the driver builds in scratch (DCBAA, scratchpad array,
ERST entry, input-context dequeue pointers, command/EP0/interrupt TRB rings)
only ever holds zero or a bus address inside scratch. -/
def qotomXhciPolicy : Policy where
  window := 0x10000
  cfgRead := cfgBits [0x00, 0x04, 0xD4, 0xDC]
  cfgWrite := cfgBits [0xD0, 0xD8]
  cmdClear := 0xFFFF0000
  cmdSet := 0x6
  dma := true
  addrSinks := [0x98, 0xB0, 0x2030, 0x2038]
  descriptors := [
    { trb := false, start := 0x20000, count := 5, stride := 8 },    -- DCBAA
    { trb := false, start := 0x20200, count := 16, stride := 8 },   -- scratchpad array
    { trb := false, start := 0x20C00, count := 1, stride := 16 },   -- ERST entry
    { trb := false, start := 0x21048, count := 31, stride := 32 },  -- input EP dequeue pointers
    { trb := true, start := 0x20400, count := 64, stride := 16 },   -- command ring
    { trb := true, start := 0x24000, count := 256, stride := 16 },  -- EP0 rings, 4 slots
    { trb := true, start := 0x25000, count := 64, stride := 16 }]   -- interrupt IN ring

/-- Intel AHCI at 00:13.0 (ABAR, 2 KiB): identity and command reads, no
configuration writes, Memory Space and Bus Master (and clearing Bus Master
again), DMA into scratch. Port 1's command-list and FIS base registers
(PxCLB 0x180, PxFB 0x188) are address sinks. -/
def qotomAhciPolicy : Policy where
  window := 0x800
  cfgRead := cfgBits [0x00, 0x04]
  cfgWrite := 0
  cmdClear := 0xFFFF0004
  cmdSet := 0x6
  dma := true
  addrSinks := [0x180, 0x188]

theorem qotomAhciPolicy_sane : qotomAhciPolicy.sane = true := by decide

/-- Realtek RTL8168E-VL at 01:00.0 (BAR2, 4 KiB): identity and command reads,
no configuration writes, Memory Space and Bus Master (and clearing Bus
Master), DMA into scratch. The transmit and high-priority ring bases (TNPDS
0x20, THPDS 0x28), the receive ring base (RDSAR 0xE4) and the tally-counter
dump address (DTCCR 0x10) are address sinks. -/
def qotomRtl8168Policy : Policy where
  window := 0x1000
  cfgRead := cfgBits [0x00, 0x04]
  cfgWrite := 0
  cmdClear := 0xFFFF0004
  cmdSet := 0x6
  dma := true
  addrSinks := [0x10, 0x20, 0x28, 0xE4]

theorem qotomRtl8168Policy_sane : qotomRtl8168Policy.sane = true := by decide

theorem qotomRtl8168Policy_bits :
    qotomRtl8168Policy.cfgRead = 0x3 ∧ qotomRtl8168Policy.cfgWrite = 0 := by
  decide

theorem qotomAhciPolicy_bits :
    qotomAhciPolicy.cfgRead = 0x3 ∧ qotomAhciPolicy.cfgWrite = 0 := by
  decide

/-- QEMU `qemu-xhci` at 00:02.0 in the q35 device lab (16 KiB BAR0):
identity and command reads, no configuration writes, Memory Space and Bus
Master, DMA into scratch; CRCR, DCBAAP, ERSTBA and ERDP in qemu-xhci's
layout (CAPLENGTH 0x40, runtime base 0x1000) are address sinks, and the
descriptor map is the driver's for qemu-xhci's layout (no scratchpads). -/
def q35XhciPolicy : Policy where
  window := 0x4000
  cfgRead := cfgBits [0x00, 0x04]
  cfgWrite := 0
  cmdClear := 0xFFFF0000
  cmdSet := 0x6
  dma := true
  addrSinks := [0x58, 0x70, 0x1030, 0x1038]
  descriptors := [
    { trb := false, start := 0x0000, count := 5, stride := 8 },     -- DCBAA
    { trb := false, start := 0x0C00, count := 1, stride := 16 },    -- ERST entry
    { trb := false, start := 0x1048, count := 31, stride := 32 },   -- input EP dequeue pointers
    { trb := true, start := 0x0400, count := 64, stride := 16 },    -- command ring
    { trb := true, start := 0x2800, count := 256, stride := 16 },   -- EP0 rings, 4 slots
    { trb := true, start := 0x3800, count := 64, stride := 16 }]    -- interrupt IN ring

theorem q35XhciPolicy_sane : q35XhciPolicy.sane = true := by decide

/-- Both xHCI descriptor maps are ones the executor accepts. -/
theorem xhciPolicies_descWf :
    qotomXhciPolicy.descWf = true ∧ q35XhciPolicy.descWf = true := by
  decide

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
