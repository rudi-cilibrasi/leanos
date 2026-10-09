import LeanOS.Wifi.Bytecode

/-
Hosted reference simulator for the device-program executor
(`hardware/wifi/wifi-exec.h`).

It interprets the *encoded* instruction words, so a program is tested in the
same form the C executor runs, and it performs the same checks in the same
order: register indices, MMIO window and alignment, configuration offsets,
blob and scratch bounds, the return stack, unknown opcodes and, for
version-3 images, the declared confinement policy. `step` is total so that
`LeanOS/DeviceProgramConfinement.lean` can prove properties of exactly the
simulator the tests run.

Device effects go through a caller-supplied model; programs that only compute
(protocol and crypto code over scratch RAM) run with `Device.none`.
-/
namespace LeanOS.Wifi.Sim

open LeanOS.Wifi.Bytecode

/-- Bus address the simulator reports for scratch byte 0 (`physAddr`). -/
def simPhysBase : UInt32 := 0x01000000

/-- Device model: MMIO and configuration space over an opaque state. -/
structure Device (σ : Type) where
  read32 : σ → UInt32 → UInt32 × σ
  read16 : σ → UInt32 → UInt16 × σ
  write32 : σ → UInt32 → UInt32 → σ
  write16 : σ → UInt32 → UInt16 → σ
  cfgRead32 : σ → UInt32 → UInt32 × σ
  cfgWrite32 : σ → UInt32 → UInt32 → σ
  /-- `cfgUpdate32 off clear set`: the executor's read-modify-write. -/
  cfgUpdate32 : σ → UInt32 → UInt32 → UInt32 → σ := fun s off clr set =>
    let (v, s) := cfgRead32 s off
    cfgWrite32 s off ((v &&& ~~~clr) ||| set)
  /-- Bus address of scratch byte `off` (`physAddr`). -/
  phys : σ → UInt32 → UInt32 × σ := fun s off => (simPhysBase + off, s)
  /-- 8-bit MMIO; models without byte registers default to the containing
  dword (read) and drop the write. -/
  read8 : σ → UInt32 → UInt8 × σ := fun s off =>
    let (v, s) := read32 s (off &&& ~~~3)
    ((v >>> (8 * (off &&& 3))).toUInt8, s)
  write8 : σ → UInt32 → UInt8 → σ := fun s _ _ => s

/-- A device that reads as zero and ignores writes. -/
def Device.none : Device Unit where
  read32 _ _ := (0, ())
  read16 _ _ := (0, ())
  write32 _ _ _ := ()
  write16 _ _ _ := ()
  cfgRead32 _ _ := (0, ())
  cfgWrite32 _ _ _ := ()

/-- How execution ended. `error` names the C executor's status
(`bad-pc`, `bad-offset`, `bad-opcode`, `stack`, `bad-blob`, `bad-mem`,
`policy`); the faulting instruction is `pc - 1` of the final machine. -/
inductive Status where
  | halt | fail (code : UInt32) | error (what : String) | stepLimit
  /-- `yield`: the program handed out `value`; `resume` continues it. -/
  | yield (value : UInt32)
  deriving Repr, BEq, Inhabited

structure Machine (σ : Type) where
  regs : Array UInt32 := Array.replicate 16 0
  pc : Nat := 0
  stack : List Nat := []
  mem : ByteArray := ByteArray.mk (Array.replicate scratchBytes 0)
  dev : σ
  prints : Array (UInt32 × UInt32) := #[]
  steps : Nat := 0

instance {σ} [Inhabited σ] : Inhabited (Machine σ) := ⟨{ dev := default }⟩

def Machine.reg {σ} (m : Machine σ) (r : UInt32) : UInt32 := m.regs.getD r.toNat 0
def Machine.setReg {σ} (m : Machine σ) (r : UInt32) (v : UInt32) : Machine σ :=
  { m with regs := m.regs.set! r.toNat v }

def memLoad (mem : ByteArray) (at_ w : Nat) : UInt32 := Id.run do
  let mut v : UInt32 := 0
  for i in [0:w] do v := v ||| ((mem.get! (at_ + i)).toUInt32 <<< (8 * i).toUInt32)
  return v

def memStore (mem : ByteArray) (at_ w : Nat) (v : UInt32) : ByteArray := Id.run do
  let mut m := mem
  for i in [0:w] do m := m.set! (at_ + i) (v >>> (8 * i).toUInt32).toUInt8
  return m

def le32 (b : ByteArray) (i : Nat) : UInt32 := memLoad b i 4

/-- Every field of `π`'s descriptor map in `mem` holds zero or a bus address
inside scratch (`ptrOk`), given the bus address `base` of scratch byte 0; a
TRB's parameter is checked only when its type makes it a pointer. -/
def descOk (π : Policy) (base : UInt32) (mem : ByteArray) : Bool :=
  π.descriptors.all fun d => (List.range d.count.toNat).all fun i =>
    let a := d.addr i
    (d.trb && !Descriptor.trbParamIsPtr (le32 mem (a + 12))) ||
      ptrOk base (le32 mem a) (le32 mem (a + 4))

/-- `iter f i n a` applies `f i`, `f (i+1)`, …, `f (i+n-1)` to `a` in order
(tail recursive; the executor's bounded inner loops). -/
def iter {α} (f : Nat → α → α) : Nat → Nat → α → α
  | _, 0, a => a
  | i, n + 1, a => iter f (i + 1) n (f i a)

/-- The MMIO window of `p` (C `OFF`): `off + w ≤ window`, `w`-aligned. -/
def mmioOk (window off w : UInt32) : Bool :=
  off.toNat + w.toNat ≤ window.toNat && off % w == 0

/-- Configuration offsets the executor accepts: dword-aligned, ≤ 0xffc. -/
def cfgOffOk (off : UInt32) : Bool := off ≤ 0xffc && off % 4 == 0

/-- Result of one instruction. -/
inductive Step (σ : Type) where
  | next (m : Machine σ)
  | stop (s : Status) (m : Machine σ)

/-- ALU sub-operation `sub` on `x` and `v`; `none` for an unknown one. -/
def aluOp (sub x v : UInt32) : Option UInt32 :=
  match sub with
  | 0 => some v | 1 => some (x + v) | 2 => some (x - v) | 3 => some (x &&& v)
  | 4 => some (x ||| v) | 5 => some (x ^^^ v)
  | 6 => some (if v ≥ 32 then 0 else x <<< v)
  | 7 => some (if v ≥ 32 then 0 else x >>> v)
  | 8 => some (x * v)
  | 9 => let k := v &&& 31; some (if k == 0 then x else (x <<< k) ||| (x >>> (32 - k)))
  | 10 => some (if v == 0 then 0 else x / v)
  | 11 => some (if v == 0 then 0 else (x.toInt32 / v.toInt32).toUInt32)
  | 12 => some (if v == 0 then x else x % v)
  | 13 => some (if v == 0 then x else (x.toInt32 % v.toInt32).toUInt32)
  | 14 => let k := if v ≥ 31 then 31 else v; some (x.toInt32 >>> k.toInt32).toUInt32
  | _ => none

/-- Branch condition `sub` on `x` and `v`; `none` for an unknown one. -/
def condOp (sub x v : UInt32) : Option Bool :=
  match sub with
  | 0 => some (x == v) | 1 => some (x != v) | 2 => some (x < v) | 3 => some (x ≥ v)
  | 4 => some (x.toInt32 < v.toInt32) | 5 => some (x.toInt32 ≥ v.toInt32)
  | _ => none

/-- Execute instruction word `w` on `m`, whose `pc` already points past it
(C `wifi_exec` switch). -/
def exec {σ} (p : Program) (d : Device σ) (w : Word4) (m : Machine σ) : Step σ :=
  let imm := w.op &&& 0x100 != 0
  let sub := w.op >>> 16
  let window := p.effTarget.windowBytes
  let val (x : UInt32) := if imm then x else m.reg x
  let bad (what : String) : Step σ := .stop (.error what) m
  -- C `REG`: register fields must name r0..r15.
  let regBad (x : UInt32) := decide (x > 15)
  let srcBad (x : UInt32) := !imm && decide (x > 15)
  let cfgR (off : UInt32) := match p.policy with | some π => cfgAllowed π.cfgRead off | none => true
  let cfgW (off : UInt32) := match p.policy with | some π => cfgAllowed π.cfgWrite off | none => true
  -- Address sinks: the executor compares against the bus address of scratch 0.
  let sinkW (off v : UInt32) := match p.policy with
    | some π => π.sinkOk (d.phys m.dev 0).1 off v | none => true
  let sinkT (off : UInt32) := match p.policy with | some π => π.sinkTouch off | none => false
  -- Descriptor map: scratch after a store must keep every pointer field in
  -- scratch (the C executor re-checks only stores that touch a region, which
  -- is equivalent while the map holds); FIFO input never lands in a region.
  let descW (mem : ByteArray) := match p.policy with
    | some π => descOk π (d.phys m.dev 0).1 mem | none => true
  let descT (at_ len : Nat) := match p.policy with
    | some π => π.descTouch at_ len | none => false
  match w.op &&& 0xFF with
  | 0 => .stop .halt m
  | 1 => .stop (.fail w.a) m
  | 2 =>
    if regBad w.a then bad "bad-opcode" else
    if !cfgOffOk w.b then bad "bad-offset" else
    if !cfgR w.b then bad "policy" else
    let (v, s) := d.cfgRead32 m.dev w.b
    .next { (m.setReg w.a v) with dev := s }
  | 3 =>
    if srcBad w.b then bad "bad-opcode" else
    if !cfgOffOk w.a then bad "bad-offset" else
    if !cfgW w.a then bad "policy" else
    .next { m with dev := d.cfgWrite32 m.dev w.a (val w.b) }
  | 4 =>
    if regBad w.a then bad "bad-opcode" else
    if !mmioOk window w.b 4 then bad "bad-offset" else
    let (v, s) := d.read32 m.dev w.b
    .next { (m.setReg w.a v) with dev := s }
  | 5 =>
    if regBad w.a then bad "bad-opcode" else
    if !mmioOk window w.b 2 then bad "bad-offset" else
    let (v, s) := d.read16 m.dev w.b
    .next { (m.setReg w.a v.toUInt32) with dev := s }
  | 6 =>
    if srcBad w.b then bad "bad-opcode" else
    if !mmioOk window w.a 4 then bad "bad-offset" else
    if !sinkW w.a (val w.b) then bad "policy" else
    .next { m with dev := d.write32 m.dev w.a (val w.b) }
  | 7 =>
    if srcBad w.b then bad "bad-opcode" else
    if !mmioOk window w.a 2 then bad "bad-offset" else
    if sinkT w.a then bad "policy" else
    .next { m with dev := d.write16 m.dev w.a (val w.b).toUInt16 }
  | 8 =>
    if regBad w.a || regBad w.b then bad "bad-opcode" else
    let off := m.reg w.b + w.c
    if !mmioOk window off 4 then bad "bad-offset" else
    let (v, s) := d.read32 m.dev off
    .next { (m.setReg w.a v) with dev := s }
  | 9 =>
    if regBad w.a || srcBad w.c then bad "bad-opcode" else
    let off := m.reg w.a + w.b
    if !mmioOk window off 4 then bad "bad-offset" else
    if !sinkW off (val w.c) then bad "policy" else
    .next { m with dev := d.write32 m.dev off (val w.c) }
  | 10 =>
    if regBad w.a || regBad w.b then bad "bad-opcode" else
    let off := m.reg w.b + w.c
    if !mmioOk window off 2 then bad "bad-offset" else
    let (v, s) := d.read16 m.dev off
    .next { (m.setReg w.a v.toUInt32) with dev := s }
  | 11 =>
    if regBad w.a || srcBad w.c then bad "bad-opcode" else
    let off := m.reg w.a + w.b
    if !mmioOk window off 2 then bad "bad-offset" else
    if sinkT off then bad "policy" else
    .next { m with dev := d.write16 m.dev off (val w.c).toUInt16 }
  | 12 =>
    if regBad w.a || srcBad w.b then bad "bad-opcode" else
    match aluOp sub (m.reg w.a) (val w.b) with
    | some r => .next (m.setReg w.a r)
    | none => bad "bad-opcode"
  | 13 =>
    if regBad w.a || srcBad w.b then bad "bad-opcode" else
    match condOp sub (m.reg w.a) (val w.b) with
    | some t => .next (if t then { m with pc := w.c.toNat } else m)
    | none => bad "bad-opcode"
  | 14 => .next { m with pc := w.a.toNat }
  | 15 => .next m
  | 16 =>
    if srcBad w.b then bad "bad-opcode" else
    .next { m with prints := m.prints.push (w.a, val w.b) }
  | 17 =>
    if w.b.toNat > p.blob.size || w.c.toNat > (p.blob.size - w.b.toNat) / 4 || w.b % 4 != 0 then
      bad "bad-blob" else
    if !mmioOk window w.a 4 then bad "bad-offset" else
    if sinkT w.a then bad "policy" else
    let dev := iter (fun i s => d.write32 s w.a (le32 p.blob (w.b.toNat + 4 * i))) 0 w.c.toNat m.dev
    .next { m with dev }
  | 18 =>
    if regBad w.a || regBad w.b then bad "bad-opcode" else
    let off := w.c.toNat + 4 * (m.reg w.b).toNat
    if w.c % 4 != 0 || off + 4 > p.blob.size then bad "bad-blob"
    else .next (m.setReg w.a (le32 p.blob off))
  | 19 => if m.stack.length ≥ 16 then bad "stack"
          else .next { m with stack := m.pc :: m.stack, pc := w.a.toNat }
  | 20 => match m.stack with
          | [] => bad "stack"
          | r :: rest => .next { m with stack := rest, pc := r }
  | 21 =>
    if regBad w.a || regBad w.b then bad "bad-opcode" else
    -- 64-bit address sum as in the C executor (no 32-bit wrap-around).
    let at_ := (m.reg w.b).toNat + w.c.toNat
    if at_ + sub.toNat > scratchBytes || (sub != 1 && sub != 2 && sub != 4) then bad "bad-mem"
    else .next (m.setReg w.a (memLoad m.mem at_ sub.toNat))
  | 22 =>
    if regBad w.a || srcBad w.c then bad "bad-opcode" else
    let at_ := (m.reg w.a).toNat + w.b.toNat
    if at_ + sub.toNat > scratchBytes || (sub != 1 && sub != 2 && sub != 4) then bad "bad-mem"
    else
      let mem := memStore m.mem at_ sub.toNat (val w.c)
      if !descW mem then bad "policy" else .next { m with mem }
  | 23 =>
    if regBad w.b || regBad w.c then bad "bad-opcode" else
    if !mmioOk window w.a 4 then bad "bad-offset" else
    let base := (m.reg w.b).toNat
    let cnt := (m.reg w.c).toNat
    if base + 4 * cnt > scratchBytes then bad "bad-mem" else
    if descT base (4 * cnt) then bad "policy" else
    let r := iter (fun i (acc : ByteArray × σ) =>
        let (v, s') := d.read32 acc.2 w.a
        (memStore acc.1 (base + 4 * i) 4 v, s')) 0 cnt (m.mem, m.dev)
    -- Outside every region the map is unchanged; re-checked for the proof.
    if !descW r.1 then bad "policy" else
    .next { m with mem := r.1, dev := r.2 }
  | 24 =>
    if regBad w.b || regBad w.c then bad "bad-opcode" else
    if !mmioOk window w.a 4 then bad "bad-offset" else
    if sinkT w.a then bad "policy" else
    let base := (m.reg w.b).toNat
    let cnt := (m.reg w.c).toNat
    if base + 4 * cnt > scratchBytes then bad "bad-mem" else
    let s := iter (fun i s => d.write32 s w.a (memLoad m.mem (base + 4 * i) 4)) 0 cnt m.dev
    .next { m with dev := s }
  | 25 =>
    if regBad w.a then bad "bad-opcode" else
    if w.b.toNat > scratchBytes then bad "bad-mem" else
    if !(p.policy.map (·.dma)).getD true then bad "policy" else
    let (v, s) := d.phys m.dev w.b
    .next { (m.setReg w.a v) with dev := s }
  | 26 =>
    if !cfgOffOk w.a then bad "bad-offset" else
    if !(p.policy.map (·.updateOk w.a w.b w.c)).getD true then bad "policy" else
    .next { m with dev := d.cfgUpdate32 m.dev w.a w.b w.c }
  | 28 =>
    if regBad w.a then bad "bad-opcode" else
    if !mmioOk window w.b 1 then bad "bad-offset" else
    let (v, s) := d.read8 m.dev w.b
    .next { (m.setReg w.a v.toUInt32) with dev := s }
  | 29 =>
    if srcBad w.b then bad "bad-opcode" else
    if !mmioOk window w.a 1 then bad "bad-offset" else
    if sinkT w.a then bad "policy" else
    .next { m with dev := d.write8 m.dev w.a (val w.b).toUInt8 }
  | 27 =>
    if srcBad w.a then bad "bad-opcode" else
    .stop (.yield (val w.a)) m
  | _ => bad "bad-opcode"

/-- One instruction of `p`. -/
def step {σ} (p : Program) (d : Device σ) (m : Machine σ) : Step σ :=
  if h : m.pc < p.words.size then
    exec p d p.words[m.pc] { m with pc := m.pc + 1, steps := m.steps + 1 }
  else .stop (.error "bad-pc") m

/-- Run at most `fuel` instructions. -/
def loop {σ} (p : Program) (d : Device σ) : Nat → Machine σ → Status × Machine σ
  | 0, m => (.stepLimit, m)
  | fuel + 1, m =>
    match step p d m with
    | .next m' => loop p d fuel m'
    | .stop s m' => (s, m')

/-- Continue a machine after `yield` until `stepLimit` total steps (the C
executor's `wifi_resume`). -/
def resume {σ} (p : Program) (d : Device σ) (stepLimit : Nat) (m : Machine σ) :
    Status × Machine σ :=
  loop p d (stepLimit - m.steps) m

/-- Run `p` on device `d` from state `s0`, at most `maxSteps` instructions. -/
def run {σ} (p : Program) (d : Device σ) (s0 : σ) (maxSteps : Nat := 100000000)
    (init : Machine σ → Machine σ := id) : Status × Machine σ :=
  loop p d maxSteps (init { dev := s0 })

end LeanOS.Wifi.Sim
