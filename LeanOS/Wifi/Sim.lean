import LeanOS.Wifi.Bytecode

/-
Hosted reference simulator for the WiFi executor (`hardware/wifi/wifi-exec.h`).

It interprets the *encoded* instruction words, so a program is tested in the
same form the C executor runs. Device effects go through a caller-supplied
model; programs that only compute (protocol and crypto code over scratch RAM)
run with `Device.none`.
-/
namespace LeanOS.Wifi.Sim

open LeanOS.Wifi.Bytecode

/-- Device model: MMIO and configuration space over an opaque state. -/
structure Device (σ : Type) where
  read32 : σ → UInt32 → UInt32 × σ
  read16 : σ → UInt32 → UInt16 × σ
  write32 : σ → UInt32 → UInt32 → σ
  write16 : σ → UInt32 → UInt16 → σ
  cfgRead32 : σ → UInt32 → UInt32 × σ
  cfgWrite32 : σ → UInt32 → UInt32 → σ

/-- A device that reads as zero and ignores writes. -/
def Device.none : Device Unit where
  read32 _ _ := (0, ())
  read16 _ _ := (0, ())
  write32 _ _ _ := ()
  write16 _ _ _ := ()
  cfgRead32 _ _ := (0, ())
  cfgWrite32 _ _ _ := ()

inductive Status where
  | halt | fail (code : UInt32) | error (what : String) | stepLimit
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

/-- One step-bounded execution loop (see `run`). -/
partial def loop {σ} [Inhabited σ] (p : Program) (d : Device σ) (maxSteps : Nat)
    (m : Machine σ) : Status × Machine σ :=
  let n := p.words.size
  if m.steps ≥ maxSteps then (.stepLimit, m) else
  if m.pc ≥ n then (.error s!"pc {m.pc}", m) else
  let w := p.words[m.pc]!
  let base := w.op &&& 0xFF
  let imm := w.op &&& 0x100 != 0
  let sub := w.op >>> 16
  let m := { m with pc := m.pc + 1, steps := m.steps + 1 }
  let val (x : UInt32) := if imm then x else m.reg x
  match base with
  | 0 => (.halt, m)
  | 1 => (.fail w.a, m)
  | 2 => let (v, s) := d.cfgRead32 m.dev w.b; loop p d maxSteps { (m.setReg w.a v) with dev := s }
  | 3 => loop p d maxSteps { m with dev := d.cfgWrite32 m.dev w.a (val w.b) }
  | 4 => let (v, s) := d.read32 m.dev w.b; loop p d maxSteps { (m.setReg w.a v) with dev := s }
  | 5 => let (v, s) := d.read16 m.dev w.b; loop p d maxSteps { (m.setReg w.a v.toUInt32) with dev := s }
  | 6 => loop p d maxSteps { m with dev := d.write32 m.dev w.a (val w.b) }
  | 7 => loop p d maxSteps { m with dev := d.write16 m.dev w.a (val w.b).toUInt16 }
  | 8 => let (v, s) := d.read32 m.dev (m.reg w.b + w.c); loop p d maxSteps { (m.setReg w.a v) with dev := s }
  | 9 => loop p d maxSteps { m with dev := d.write32 m.dev (m.reg w.a + w.b) (val w.c) }
  | 10 => let (v, s) := d.read16 m.dev (m.reg w.b + w.c); loop p d maxSteps { (m.setReg w.a v.toUInt32) with dev := s }
  | 11 => loop p d maxSteps { m with dev := d.write16 m.dev (m.reg w.a + w.b) (val w.c).toUInt16 }
  | 12 =>
    let x := m.reg w.a
    let v := val w.b
    let r := match sub with
      | 0 => v | 1 => x + v | 2 => x - v | 3 => x &&& v | 4 => x ||| v | 5 => x ^^^ v
      | 6 => if v ≥ 32 then 0 else x <<< v
      | 7 => if v ≥ 32 then 0 else x >>> v
      | 8 => x * v
      | _ => let k := v &&& 31; if k == 0 then x else (x <<< k) ||| (x >>> (32 - k))
    loop p d maxSteps (m.setReg w.a r)
  | 13 =>
    let x := m.reg w.a
    let v := val w.b
    let t := match sub with | 0 => x == v | 1 => x != v | 2 => x < v | _ => x ≥ v
    loop p d maxSteps (if t then { m with pc := w.c.toNat } else m)
  | 14 => loop p d maxSteps { m with pc := w.a.toNat }
  | 15 => loop p d maxSteps m
  | 16 => loop p d maxSteps { m with prints := m.prints.push (w.a, val w.b) }
  | 17 =>
    let dev := Id.run do
      let mut s := m.dev
      for i in [0:w.c.toNat] do s := d.write32 s w.a (le32 p.blob (w.b.toNat + 4 * i))
      return s
    loop p d maxSteps { m with dev }
  | 18 => loop p d maxSteps (m.setReg w.a (le32 p.blob (w.c.toNat + 4 * (m.reg w.b).toNat)))
  | 19 => if m.stack.length ≥ 16 then (.error "stack", m)
          else loop p d maxSteps { m with stack := m.pc :: m.stack, pc := w.a.toNat }
  | 20 => match m.stack with
          | [] => (.error "stack", m)
          | r :: rest => loop p d maxSteps { m with stack := rest, pc := r }
  | 21 =>
    let at_ := (m.reg w.b + w.c).toNat
    if at_ + sub.toNat > scratchBytes then (.error "mem", m)
    else loop p d maxSteps (m.setReg w.a (memLoad m.mem at_ sub.toNat))
  | 22 =>
    let at_ := (m.reg w.a + w.b).toNat
    if at_ + sub.toNat > scratchBytes then (.error "mem", m)
    else loop p d maxSteps { m with mem := memStore m.mem at_ sub.toNat (val w.c) }
  | 23 =>
    let base := (m.reg w.b).toNat
    let cnt := (m.reg w.c).toNat
    if base + 4 * cnt > scratchBytes then (.error "mem", m) else
    let (mem, s) := Id.run do
      let mut mem := m.mem
      let mut s := m.dev
      for i in [0:cnt] do
        let (v, s') := d.read32 s w.a
        s := s'
        mem := memStore mem (base + 4 * i) 4 v
      return (mem, s)
    loop p d maxSteps { m with mem, dev := s }
  | 24 =>
    let base := (m.reg w.b).toNat
    let cnt := (m.reg w.c).toNat
    if base + 4 * cnt > scratchBytes then (.error "mem", m) else
    let s := Id.run do
      let mut s := m.dev
      for i in [0:cnt] do s := d.write32 s w.a (memLoad m.mem (base + 4 * i) 4)
      return s
    loop p d maxSteps { m with dev := s }
  | _ => (.error s!"opcode {w.op}", m)

/-- Run `p` on device `d` from state `s0`, at most `maxSteps` instructions. -/
def run {σ} [Inhabited σ] (p : Program) (d : Device σ) (s0 : σ) (maxSteps : Nat := 100000000)
    (init : Machine σ → Machine σ := id) : Status × Machine σ :=
  loop p d maxSteps (init { dev := s0 })

end LeanOS.Wifi.Sim
