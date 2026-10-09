import LeanOS.Wifi.Bytecode

/-
The device-program executor step, generated (issue #494, ADR 0020).

`step` is one instruction of the device-program executor written against a
C-shaped interface: fixed-width scalars plus the named hook primitives of
`Hooks`. It is generic in the hook carrier `τ`, so the same definition has two
readings.

* **Generated C.** With `τ := UInt64` the hooks are the `@[extern]` C
  primitives `wifi_gen_*` (`hardware/wifi/wifi-gen-exec.h`), and
  `leanos_device_program_step` is the compiled `step`: allocation-free,
  `uint32_t`/`uint64_t` code that calls the hooks directly, with bounded inner
  loops compiled as `goto` loops (no recursion, no Lean runtime call).
* **Model.** With `τ := ExecRefinement.St σ` the hooks are interpreted over a
  simulator `Machine`, and `LeanOS.Wifi.ExecRefinement.step_eq` proves that
  `step` *is* `Sim.step` on every reachable machine, so the confinement
  theorems (`LeanOS.DeviceProgramConfinement.run_confined`, …) hold for the
  code the generated executor runs.

### The token discipline

Every hook that reads or changes mutable executor state (registers, pc,
return stack, scratch, the device) takes the *current token* and returns the
next one; the value it reads is `Hooks.val` of the returned token. In C the
token is a `uint64_t` the hooks ignore on input and use to return the value.
Because each such call consumes the token the previous call produced, the
compiler can neither reorder nor merge nor drop them: their order in C is
their order here. Hooks over the image and its policy (`window`, `blobWord`,
`polSink`, …) read immutable data and are plain functions.

The generic definitions carry `@[specialize]` so the compiler instantiates
them at the C hooks (`l_…_spec_…` functions in the generated C).
-/
namespace LeanOS.Wifi.Exec

-- Boot code has no module initializer: keep constants inline in the code.
set_option compiler.extract_closed false

/-! ## Status codes (C `enum wifi_status`) -/

def stHalt : UInt32 := 0
def stFail : UInt32 := 1
def stBadPc : UInt32 := 3
def stBadOffset : UInt32 := 4
def stBadOpcode : UInt32 := 5
def stStack : UInt32 := 6
def stBadBlob : UInt32 := 8
def stBadMem : UInt32 := 9
def stPolicy : UInt32 := 10
def stYield : UInt32 := 11
/-- The instruction completed; the executor continues with the next one. -/
def stNext : UInt32 := 12

/-- Scratch RAM bytes (`Bytecode.scratchBytes`) as a fixed-width constant. -/
def scratch32 : UInt32 := 262144

/-! ## The hook interface -/

/-- Named primitives the step is written against. In C these are the
`wifi_gen_*` functions of `hardware/wifi/wifi-gen-exec.h`; the model reading is
`LeanOS.Wifi.ExecRefinement.instHooksSt`. -/
class Hooks (τ : Type) where
  /-- The value the last hook delivered. -/
  val : τ → UInt64
  /-- The same token delivering `x` (a computed value handed on). -/
  withVal : τ → UInt64 → τ
  /-- Image constants: MMIO window bytes, blob length and blob word. -/
  window : τ → UInt32
  blobLen : τ → UInt32
  blobWord : τ → UInt32 → UInt32
  /-- Declared policy (zero fields when the image declares none). -/
  polPresent : τ → UInt32
  polDma : τ → UInt32
  polCfgRead : τ → UInt64
  polCfgWrite : τ → UInt64
  polCmdClear : τ → UInt32
  polCmdSet : τ → UInt32
  polSinks : τ → UInt32
  polSink : τ → UInt32 → UInt32
  polDescs : τ → UInt32
  polDescTrb : τ → UInt32 → UInt32
  polDescStart : τ → UInt32 → UInt32
  polDescCount : τ → UInt32 → UInt32
  polDescStride : τ → UInt32 → UInt32
  /-- Control state: `pc` names an instruction; field `i` of it; `pc + 1`
  and one more step; jump; return-stack full/empty, call and return. -/
  pcOk : τ → τ
  fetch : τ → UInt32 → τ
  advance : τ → τ
  jump : τ → UInt32 → τ
  stackFull : τ → τ
  stackEmpty : τ → τ
  call : τ → UInt32 → τ
  ret : τ → τ
  /-- Register file. -/
  regGet : τ → UInt32 → τ
  regSet : τ → UInt32 → UInt32 → τ
  /-- Scratch RAM: `w`-byte little-endian load and store (w ∈ {1, 2, 4}). -/
  memLoad : τ → UInt32 → UInt32 → τ
  memStore : τ → UInt32 → UInt32 → UInt32 → τ
  /-- Device: MMIO, configuration space, bus addresses of scratch (`phys`
  as an effect of `physAddr`, `physBase` the address of byte 0 for the
  policy checks), delay and print. -/
  mmioRead32 : τ → UInt32 → τ
  mmioRead16 : τ → UInt32 → τ
  mmioRead8 : τ → UInt32 → τ
  mmioWrite32 : τ → UInt32 → UInt32 → τ
  mmioWrite16 : τ → UInt32 → UInt32 → τ
  mmioWrite8 : τ → UInt32 → UInt32 → τ
  cfgRead : τ → UInt32 → τ
  cfgWrite : τ → UInt32 → UInt32 → τ
  cfgUpdate : τ → UInt32 → UInt32 → UInt32 → τ
  phys : τ → UInt32 → τ
  physBase : τ → τ
  delay : τ → UInt32 → τ
  print : τ → UInt32 → UInt32 → τ
  /-- End of the step: status and its code (fail code, yielded value). -/
  done : τ → UInt32 → UInt32 → τ

open Hooks

variable {τ : Type} [Hooks τ]

/-- The last value as a 32-bit word. -/
@[inline] def word (t : τ) : UInt32 := (val t).toUInt32

/-- The last value as a flag. -/
@[inline] def flag (t : τ) : Bool := val t != 0

/-! ## Fixed-width checks (equal to the simulator's, `ExecRefinement`) -/

/-- `Sim.mmioOk` without `Nat`: `off + w ≤ window`, `w`-aligned. -/
@[inline] def mmioOk (window off w : UInt32) : Bool :=
  off.toUInt64 + w.toUInt64 ≤ window.toUInt64 && off % w == 0

/-- Configuration offsets the executor accepts (`Sim.cfgOffOk`). -/
@[inline] def cfgOffOk (off : UInt32) : Bool := off ≤ 0xffc && off % 4 == 0

/-- `Bytecode.cfgAllowed`, compiled into this module. -/
@[inline] def cfgAllowed (bits : UInt64) (off : UInt32) : Bool :=
  off < 0x100 && off % 4 == 0 && (bits >>> (off / 4).toUInt64) &&& 1 == 1

/-- `Bytecode.ptrOk` without `Nat`. -/
@[inline] def ptrOk (base lo hi : UInt32) : Bool :=
  hi == 0 && (lo == 0 || lo - base < scratch32)

/-- `Bytecode.Descriptor.trbParamIsPtr`. -/
@[inline] def trbPtr (ctl : UInt32) : Bool :=
  let k := (ctl >>> 10) &&& 0x3F
  k != 0 && k != 2

/-- ALU sub-operations 0–14 (`Sim.aluOp`); `aluKnown` names the defined ones. -/
@[inline] def aluKnown (sub : UInt32) : Bool := sub ≤ 14

/-- The sub-operations are selected by a tree of `<` tests rather than a
chain of `==` tests, which C compilers may lower to a jump table (an indirect
branch the entry-stack gate rejects); likewise `cond` and `exec`. -/
def alu (sub x v : UInt32) : UInt32 :=
  if sub < 8 then
    if sub < 4 then
      if sub < 2 then (if sub < 1 then v else x + v)
      else (if sub < 3 then x - v else x &&& v)
    else if sub < 6 then (if sub < 5 then x ||| v else x ^^^ v)
    else if sub < 7 then (if v ≥ 32 then 0 else x <<< v)
    else (if v ≥ 32 then 0 else x >>> v)
  else if sub < 12 then
    if sub < 10 then
      (if sub < 9 then x * v
       else (let k := v &&& 31; if k == 0 then x else (x <<< k) ||| (x >>> (32 - k))))
    else if sub < 11 then (if v == 0 then 0 else x / v)
    else (if v == 0 then 0 else (x.toInt32 / v.toInt32).toUInt32)
  else if sub < 13 then (if v == 0 then x else x % v)
  else if sub < 14 then (if v == 0 then x else (x.toInt32 % v.toInt32).toUInt32)
  else (let k := if v ≥ 31 then 31 else v; (x.toInt32 >>> k.toInt32).toUInt32)

/-- Branch conditions 0–5 (`Sim.condOp`). -/
@[inline] def condKnown (sub : UInt32) : Bool := sub ≤ 5

def cond (sub x v : UInt32) : Bool :=
  if sub < 3 then (if sub < 1 then x == v else if sub < 2 then x != v else x < v)
  else if sub < 4 then x ≥ v else if sub < 5 then x.toInt32 < v.toInt32
  else x.toInt32 ≥ v.toInt32

/-- `Bytecode.Policy.updateOk` over the policy hooks. -/
@[inline] def updateOk (t : τ) (off clr set : UInt32) : Bool :=
  off == 0x04 && clr &&& ~~~(polCmdClear t) == 0 && set &&& ~~~(polCmdSet t) == 0

/-! ## Policy loops over the image's sink and descriptor tables -/

theorem succ_toNat_lt {i n : UInt32} (h : i < n) :
    (n.toNat - (i + 1).toNat) < n.toNat - i.toNat := by
  have hi : i.toNat < n.toNat := h
  have := n.toNat_lt
  have : (i + 1).toNat = i.toNat + 1 := by
    rw [UInt32.toNat_add]; simp only [UInt32.toNat_one]; omega
  omega

/-- Some sink from index `i` on has `off` in its 8 bytes (`Policy.sinkTouch`). -/
@[specialize] def sinkTouchFrom (t : τ) (off i : UInt32) : Bool :=
  if h : i < polSinks t then
    if off - polSink t i < 8 then true else sinkTouchFrom t off (i + 1)
  else false
termination_by (polSinks t).toNat - i.toNat
decreasing_by exact succ_toNat_lt h

/-- Some sink from index `i` on is `off` (`List.contains`). -/
@[specialize] def sinkIsFrom (t : τ) (off i : UInt32) : Bool :=
  if h : i < polSinks t then
    if polSink t i == off then true else sinkIsFrom t off (i + 1)
  else false
termination_by (polSinks t).toNat - i.toNat
decreasing_by exact succ_toNat_lt h

/-- `Policy.sinkOk`: base is the bus address of scratch byte 0. -/
@[inline] def sinkOk (t : τ) (base off v : UInt32) : Bool :=
  if !sinkTouchFrom t off 0 then true
  else if sinkIsFrom t off 0 then v - base < scratch32
  else if sinkIsFrom t (off - 4) 0 then v == 0
  else false

/-- One past descriptor `k`'s last byte (`Descriptor.limit`). -/
@[inline] def descLimit (t : τ) (k : UInt32) : UInt64 :=
  let n := polDescCount t k
  (polDescStart t k).toUInt64 + (polDescStride t k).toUInt64 * (if n == 0 then 0 else n - 1).toUInt64 +
    (if polDescTrb t k != 0 then 16 else 8)

/-- Some descriptor from index `k` on overlaps `[at, at + len)`
(`Policy.descTouch` for `len ≠ 0`). -/
@[specialize] def descTouchFrom (t : τ) (at_ len : UInt64) (k : UInt32) : Bool :=
  if h : k < polDescs t then
    if at_ < descLimit t k && (polDescStart t k).toUInt64 < at_ + len then true
    else descTouchFrom t at_ len (k + 1)
  else false
termination_by (polDescs t).toNat - k.toNat
decreasing_by exact succ_toNat_lt h

/-- `Policy.descTouch`. -/
@[inline] def descTouch (t : τ) (at_ len : UInt64) : Bool :=
  len != 0 && descTouchFrom t at_ len 0

/-- Scratch byte `j` once the pending store is applied. -/
@[inline] def byteAfter (t : τ) (j oa ow ov : UInt32) : τ :=
  if oa ≤ j && j < oa + ow then withVal t ((ov >>> (8 * (j - oa))) &&& 0xFF).toUInt64
  else memLoad t j 1

/-- The little-endian word at scratch `a` once the pending store of the low
`ow` bytes of `ov` at `oa` is applied (`ow = 0`: none). Words clear of the
pending store are one 4-byte load; a word it overlaps is assembled from byte
loads and the stored bytes, so the store itself happens only once the policy
accepts it. -/
@[inline] def wordAfter (t : τ) (a oa ow ov : UInt32) : τ :=
  if ow == 0 || a + 4 ≤ oa || oa + ow ≤ a then memLoad t a 4
  else
    let t := byteAfter t a oa ow ov
    let b0 := word t
    let t := byteAfter t (a + 1) oa ow ov
    let b1 := word t
    let t := byteAfter t (a + 2) oa ow ov
    let b2 := word t
    let t := byteAfter t (a + 3) oa ow ov
    let b3 := word t
    withVal t (b0 ||| (b1 <<< 8) ||| (b2 <<< 16) ||| (b3 <<< 24)).toUInt64

/-- Entries `i ..< count` of one descriptor hold zero or a scratch bus address
(after the pending store); the result is the flag of the returned token. -/
@[specialize] def scanEntries (t : τ) (base oa ow ov : UInt32) (trb : Bool)
    (start stride count i : UInt32) : τ :=
  if h : i < count then
    let a := start + stride * i
    let t := if trb then wordAfter t (a + 12) oa ow ov else t
    if trb && !trbPtr (word t) then scanEntries t base oa ow ov trb start stride count (i + 1)
    else
      let t := wordAfter t a oa ow ov
      let lo := word t
      let t := wordAfter t (a + 4) oa ow ov
      let hi := word t
      if ptrOk base lo hi then scanEntries t base oa ow ov trb start stride count (i + 1)
      else withVal t 0
  else withVal t 1
termination_by count.toNat - i.toNat
decreasing_by all_goals exact succ_toNat_lt h

/-- Descriptors `k ..< n` of the map hold only scratch pointers after the
pending store (`Sim.descOk` of the stored scratch); `n` is `polDescs`. -/
@[specialize] def scanDescs (t : τ) (base oa ow ov k n : UInt32) : τ :=
  if h : k < n then
    let t := scanEntries t base oa ow ov (polDescTrb t k != 0) (polDescStart t k)
      (polDescStride t k) (polDescCount t k) 0
    if flag t then scanDescs t base oa ow ov (k + 1) n else t
  else withVal t 1
termination_by n.toNat - k.toNat
decreasing_by exact succ_toNat_lt h

/-! ## Bounded transfer loops -/

/-- `blobStream32`: blob words `i ..< n` from blob offset `b` to register `off`. -/
@[specialize] def blobStream (t : τ) (off b i n : UInt32) : τ :=
  if h : i < n then blobStream (mmioWrite32 t off (blobWord t (b + 4 * i))) off b (i + 1) n
  else t
termination_by n.toNat - i.toNat
decreasing_by exact succ_toNat_lt h

/-- `fifoIn`: words `i ..< n` from register `off` into scratch at `base`. -/
@[specialize] def fifoIn (t : τ) (off base i n : UInt32) : τ :=
  if h : i < n then
    let t := mmioRead32 t off
    fifoIn (memStore t (base + 4 * i) 4 (word t)) off base (i + 1) n
  else t
termination_by n.toNat - i.toNat
decreasing_by exact succ_toNat_lt h

/-- `fifoOut`: scratch words at `base` to register `off`. -/
@[specialize] def fifoOut (t : τ) (off base i n : UInt32) : τ :=
  if h : i < n then
    let t := memLoad t (base + 4 * i) 4
    fifoOut (mmioWrite32 t off (word t)) off base (i + 1) n
  else t
termination_by n.toNat - i.toNat
decreasing_by exact succ_toNat_lt h

/-! ## One instruction -/

/-- A register field outside `r0..r15` (C `REG`). -/
@[inline] def regBad (x : UInt32) : Bool := x > 15

/-- A register source operand outside `r0..r15`. -/
@[inline] def srcBad (imm : Bool) (x : UInt32) : Bool := !imm && x > 15

/-- Register operand `x` (unless immediate): the token after reading it. -/
@[inline] def operand (t : τ) (imm : Bool) (x : UInt32) : τ := if imm then t else regGet t x

/-- The operand's value, read from the token `operand` returned. -/
@[inline] def operandVal (t : τ) (imm : Bool) (x : UInt32) : UInt32 := if imm then x else word t

@[inline] def next (t : τ) : τ := done t stNext 0

/-- Whether the instruction's source operand is an immediate. -/
@[inline] def immOf (op : UInt32) : Bool := op &&& 0x100 != 0

/-! Each opcode's effect (`Sim.exec`, check for check in the same order). -/

@[inline] def exec0 (t : τ) (_op _a _b _c : UInt32) : τ :=
  done t stHalt 0

@[inline] def exec1 (t : τ) (_op a _b _c : UInt32) : τ :=
  done t stFail a

@[inline] def exec2 (t : τ) (_op a b _c : UInt32) : τ :=
  
  if regBad a then done t stBadOpcode 0 else
  if !cfgOffOk b then done t stBadOffset 0 else
  if (polPresent t != 0) && !cfgAllowed (polCfgRead t) b then done t stPolicy 0 else
  let t := cfgRead t b
  next (regSet t a (word t))

@[inline] def exec3 (t : τ) (op a b _c : UInt32) : τ :=
  
  if srcBad (immOf op) b then done t stBadOpcode 0 else
  if !cfgOffOk a then done t stBadOffset 0 else
  if (polPresent t != 0) && !cfgAllowed (polCfgWrite t) a then done t stPolicy 0 else
  let t := operand t (immOf op) b
  next (cfgWrite t a (operandVal t (immOf op) b))

@[inline] def exec4 (t : τ) (_op a b _c : UInt32) : τ :=
  
  if regBad a then done t stBadOpcode 0 else
  if !mmioOk (Hooks.window t) b 4 then done t stBadOffset 0 else
  let t := mmioRead32 t b
  next (regSet t a (word t))

@[inline] def exec5 (t : τ) (_op a b _c : UInt32) : τ :=
  
  if regBad a then done t stBadOpcode 0 else
  if !mmioOk (Hooks.window t) b 2 then done t stBadOffset 0 else
  let t := mmioRead16 t b
  next (regSet t a (word t))

@[inline] def exec6 (t : τ) (op a b _c : UInt32) : τ :=
  
  if srcBad (immOf op) b then done t stBadOpcode 0 else
  if !mmioOk (Hooks.window t) a 4 then done t stBadOffset 0 else
  let t := operand t (immOf op) b
  let v := operandVal t (immOf op) b
  if (polPresent t != 0) then
    let t := physBase t
    if !sinkOk t (word t) a v then done t stPolicy 0 else next (mmioWrite32 t a v)
  else next (mmioWrite32 t a v)

@[inline] def exec7 (t : τ) (op a b _c : UInt32) : τ :=
  
  if srcBad (immOf op) b then done t stBadOpcode 0 else
  if !mmioOk (Hooks.window t) a 2 then done t stBadOffset 0 else
  if (polPresent t != 0) && sinkTouchFrom t a 0 then done t stPolicy 0 else
  let t := operand t (immOf op) b
  next (mmioWrite16 t a (operandVal t (immOf op) b))

@[inline] def exec8 (t : τ) (_op a b c : UInt32) : τ :=
  
  if regBad a || regBad b then done t stBadOpcode 0 else
  let t := regGet t b
  let off := word t + c
  if !mmioOk (Hooks.window t) off 4 then done t stBadOffset 0 else
  let t := mmioRead32 t off
  next (regSet t a (word t))

@[inline] def exec9 (t : τ) (op a b c : UInt32) : τ :=
  
  if regBad a || srcBad (immOf op) c then done t stBadOpcode 0 else
  let t := regGet t a
  let off := word t + b
  if !mmioOk (Hooks.window t) off 4 then done t stBadOffset 0 else
  let t := operand t (immOf op) c
  let v := operandVal t (immOf op) c
  if (polPresent t != 0) then
    let t := physBase t
    if !sinkOk t (word t) off v then done t stPolicy 0 else next (mmioWrite32 t off v)
  else next (mmioWrite32 t off v)

@[inline] def exec10 (t : τ) (_op a b c : UInt32) : τ :=
  
  if regBad a || regBad b then done t stBadOpcode 0 else
  let t := regGet t b
  let off := word t + c
  if !mmioOk (Hooks.window t) off 2 then done t stBadOffset 0 else
  let t := mmioRead16 t off
  next (regSet t a (word t))

@[inline] def exec11 (t : τ) (op a b c : UInt32) : τ :=
  
  if regBad a || srcBad (immOf op) c then done t stBadOpcode 0 else
  let t := regGet t a
  let off := word t + b
  if !mmioOk (Hooks.window t) off 2 then done t stBadOffset 0 else
  if (polPresent t != 0) && sinkTouchFrom t off 0 then done t stPolicy 0 else
  let t := operand t (immOf op) c
  next (mmioWrite16 t off (operandVal t (immOf op) c))

@[inline] def exec12 (t : τ) (op a b _c : UInt32) : τ :=
  
  if regBad a || srcBad (immOf op) b then done t stBadOpcode 0 else
  let t := operand t (immOf op) b
  let v := operandVal t (immOf op) b
  let t := regGet t a
  if aluKnown (op >>> 16) then next (regSet t a (alu (op >>> 16) (word t) v)) else done t stBadOpcode 0

@[inline] def exec13 (t : τ) (op a b c : UInt32) : τ :=
  
  if regBad a || srcBad (immOf op) b then done t stBadOpcode 0 else
  let t := operand t (immOf op) b
  let v := operandVal t (immOf op) b
  let t := regGet t a
  if condKnown (op >>> 16) then
    (if cond (op >>> 16) (word t) v then next (jump t c) else next t)
  else done t stBadOpcode 0

@[inline] def exec14 (t : τ) (_op a _b _c : UInt32) : τ :=
  next (jump t a)

@[inline] def exec15 (t : τ) (_op a _b _c : UInt32) : τ :=
  next (delay t a)

@[inline] def exec16 (t : τ) (op a b _c : UInt32) : τ :=
  
  if srcBad (immOf op) b then done t stBadOpcode 0 else
  let t := operand t (immOf op) b
  next (print t a (operandVal t (immOf op) b))

@[inline] def exec17 (t : τ) (_op a b c : UInt32) : τ :=
  
  let len := blobLen t
  if b > len || c > (len - b) / 4 || b % 4 != 0 then done t stBadBlob 0 else
  if !mmioOk (Hooks.window t) a 4 then done t stBadOffset 0 else
  if (polPresent t != 0) && sinkTouchFrom t a 0 then done t stPolicy 0 else
  next (blobStream t a b 0 c)

@[inline] def exec18 (t : τ) (_op a b c : UInt32) : τ :=
  
  if regBad a || regBad b then done t stBadOpcode 0 else
  let t := regGet t b
  let off := c.toUInt64 + 4 * (word t).toUInt64
  if c % 4 != 0 || off + 4 > (blobLen t).toUInt64 then done t stBadBlob 0
  else next (regSet t a (blobWord t off.toUInt32))

@[inline] def exec19 (t : τ) (_op a _b _c : UInt32) : τ :=
  
  let t := stackFull t
  if flag t then done t stStack 0 else next (call t a)

@[inline] def exec20 (t : τ) (_op _a _b _c : UInt32) : τ :=
  
  let t := stackEmpty t
  if flag t then done t stStack 0 else next (ret t)

@[inline] def exec21 (t : τ) (op a b c : UInt32) : τ :=
  
  if regBad a || regBad b then done t stBadOpcode 0 else
  let t := regGet t b
  let at_ := (word t).toUInt64 + c.toUInt64
  if at_ + (op >>> 16).toUInt64 > scratch32.toUInt64 || ((op >>> 16) != 1 && (op >>> 16) != 2 && (op >>> 16) != 4) then
    done t stBadMem 0
  else
    let t := memLoad t at_.toUInt32 (op >>> 16)
    next (regSet t a (word t))

@[inline] def exec22 (t : τ) (op a b c : UInt32) : τ :=
  
  if regBad a || srcBad (immOf op) c then done t stBadOpcode 0 else
  let t := regGet t a
  let at_ := (word t).toUInt64 + b.toUInt64
  if at_ + (op >>> 16).toUInt64 > scratch32.toUInt64 || ((op >>> 16) != 1 && (op >>> 16) != 2 && (op >>> 16) != 4) then
    done t stBadMem 0
  else
    let t := operand t (immOf op) c
    let v := operandVal t (immOf op) c
    if (polPresent t != 0) && descTouch t at_ (op >>> 16).toUInt64 then
      let t := physBase t
      let t := scanDescs t (word t) at_.toUInt32 (op >>> 16) v 0 (polDescs t)
      if flag t then next (memStore t at_.toUInt32 (op >>> 16) v) else done t stPolicy 0
    else next (memStore t at_.toUInt32 (op >>> 16) v)

@[inline] def exec23 (t : τ) (_op a b c : UInt32) : τ :=
  
  if regBad b || regBad c then done t stBadOpcode 0 else
  if !mmioOk (Hooks.window t) a 4 then done t stBadOffset 0 else
  let t := regGet t b
  let base := word t
  let t := regGet t c
  let cnt := word t
  if base.toUInt64 + 4 * cnt.toUInt64 > scratch32.toUInt64 then done t stBadMem 0 else
  if (polPresent t != 0) && descTouch t base.toUInt64 (4 * cnt.toUInt64) then done t stPolicy 0 else
  next (fifoIn t a base 0 cnt)

@[inline] def exec24 (t : τ) (_op a b c : UInt32) : τ :=
  
  if regBad b || regBad c then done t stBadOpcode 0 else
  if !mmioOk (Hooks.window t) a 4 then done t stBadOffset 0 else
  if (polPresent t != 0) && sinkTouchFrom t a 0 then done t stPolicy 0 else
  let t := regGet t b
  let base := word t
  let t := regGet t c
  let cnt := word t
  if base.toUInt64 + 4 * cnt.toUInt64 > scratch32.toUInt64 then done t stBadMem 0 else
  next (fifoOut t a base 0 cnt)

@[inline] def exec25 (t : τ) (_op a b _c : UInt32) : τ :=
  
  if regBad a then done t stBadOpcode 0 else
  if b > scratch32 then done t stBadMem 0 else
  if (polPresent t != 0) && polDma t == 0 then done t stPolicy 0 else
  let t := phys t b
  next (regSet t a (word t))

@[inline] def exec26 (t : τ) (_op a b c : UInt32) : τ :=
  
  if !cfgOffOk a then done t stBadOffset 0 else
  if (polPresent t != 0) && !updateOk t a b c then done t stPolicy 0 else
  next (cfgUpdate t a b c)

@[inline] def exec27 (t : τ) (op a _b _c : UInt32) : τ :=
  
  if srcBad (immOf op) a then done t stBadOpcode 0 else
  let t := operand t (immOf op) a
  done t stYield (operandVal t (immOf op) a)

@[inline] def exec28 (t : τ) (_op a b _c : UInt32) : τ :=
  
  if regBad a then done t stBadOpcode 0 else
  if !mmioOk (Hooks.window t) b 1 then done t stBadOffset 0 else
  let t := mmioRead8 t b
  next (regSet t a (word t))

@[inline] def exec29 (t : τ) (op a b _c : UInt32) : τ :=
  
  if srcBad (immOf op) b then done t stBadOpcode 0 else
  if !mmioOk (Hooks.window t) a 1 then done t stBadOffset 0 else
  if (polPresent t != 0) && sinkTouchFrom t a 0 then done t stPolicy 0 else
  let t := operand t (immOf op) b
  next (mmioWrite8 t a (operandVal t (immOf op) b))

@[inline] def execBad (t : τ) : τ := done t stBadOpcode 0

/-- Specification form of `exec`: the opcode `match` of `Sim.exec`. -/
def execMatch (t : τ) (op a b c : UInt32) : τ :=
  match op &&& 0xFF with
  | 0 => exec0 t op a b c
  | 1 => exec1 t op a b c
  | 2 => exec2 t op a b c
  | 3 => exec3 t op a b c
  | 4 => exec4 t op a b c
  | 5 => exec5 t op a b c
  | 6 => exec6 t op a b c
  | 7 => exec7 t op a b c
  | 8 => exec8 t op a b c
  | 9 => exec9 t op a b c
  | 10 => exec10 t op a b c
  | 11 => exec11 t op a b c
  | 12 => exec12 t op a b c
  | 13 => exec13 t op a b c
  | 14 => exec14 t op a b c
  | 15 => exec15 t op a b c
  | 16 => exec16 t op a b c
  | 17 => exec17 t op a b c
  | 18 => exec18 t op a b c
  | 19 => exec19 t op a b c
  | 20 => exec20 t op a b c
  | 21 => exec21 t op a b c
  | 22 => exec22 t op a b c
  | 23 => exec23 t op a b c
  | 24 => exec24 t op a b c
  | 25 => exec25 t op a b c
  | 26 => exec26 t op a b c
  | 28 => exec28 t op a b c
  | 29 => exec29 t op a b c
  | 27 => exec27 t op a b c
  | _ => execBad t

/-- Execute instruction `op a b c`, whose pc the token has already advanced:
`execMatch` dispatched by a balanced tree of `<` tests (`exec_tree`), so the
generated C has no jump table. -/
@[specialize] def exec (t : τ) (op a b c : UInt32) : τ :=
  let k := op &&& 0xFF
  if k < 30 then
    if k < 15 then
      if k < 7 then
        if k < 3 then
          if k < 1 then
            exec0 t op a b c
          else
            if k < 2 then
              exec1 t op a b c
            else
              exec2 t op a b c
        else
          if k < 5 then
            if k < 4 then
              exec3 t op a b c
            else
              exec4 t op a b c
          else
            if k < 6 then
              exec5 t op a b c
            else
              exec6 t op a b c
      else
        if k < 11 then
          if k < 9 then
            if k < 8 then
              exec7 t op a b c
            else
              exec8 t op a b c
          else
            if k < 10 then
              exec9 t op a b c
            else
              exec10 t op a b c
        else
          if k < 13 then
            if k < 12 then
              exec11 t op a b c
            else
              exec12 t op a b c
          else
            if k < 14 then
              exec13 t op a b c
            else
              exec14 t op a b c
    else
      if k < 22 then
        if k < 18 then
          if k < 16 then
            exec15 t op a b c
          else
            if k < 17 then
              exec16 t op a b c
            else
              exec17 t op a b c
        else
          if k < 20 then
            if k < 19 then
              exec18 t op a b c
            else
              exec19 t op a b c
          else
            if k < 21 then
              exec20 t op a b c
            else
              exec21 t op a b c
      else
        if k < 26 then
          if k < 24 then
            if k < 23 then
              exec22 t op a b c
            else
              exec23 t op a b c
          else
            if k < 25 then
              exec24 t op a b c
            else
              exec25 t op a b c
        else
          if k < 28 then
            if k < 27 then
              exec26 t op a b c
            else
              exec27 t op a b c
          else
            if k < 29 then
              exec28 t op a b c
            else
              exec29 t op a b c
  else execBad t

theorem exec_tree (t : τ) (op a b c : UInt32) : exec t op a b c = execMatch t op a b c := by
  unfold exec execMatch
  generalize op &&& 0xFF = k
  split
  any_goals rfl
  rename_i h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23
    h24 h25 h26 h28 h29 h27
  have : ¬ k < 30 := by
    simp only [UInt32.lt_iff_toNat_lt, ← UInt32.toNat_inj, UInt32.reduceToNat, imp_false] at *
    omega
  simp only [this, ↓reduceIte]

/-- One instruction (`Sim.step`): fetch at pc, or stop with `bad-pc`. -/
@[specialize] def step (t : τ) : τ :=
  let t := pcOk t
  if !flag t then done t stBadPc 0 else
  let t := fetch t 0
  let op := word t
  let t := fetch t 1
  let a := word t
  let t := fetch t 2
  let b := word t
  let t := fetch t 3
  exec (advance t) op a b (word t)

/-! ## The C reading -/

@[extern "wifi_gen_value"] opaque cValue (t x : UInt64) : UInt64
@[extern "wifi_gen_window"] opaque cWindow (t : UInt64) : UInt32
@[extern "wifi_gen_blob_len"] opaque cBlobLen (t : UInt64) : UInt32
@[extern "wifi_gen_blob_word"] opaque cBlobWord (t : UInt64) (off : UInt32) : UInt32
@[extern "wifi_gen_pol_present"] opaque cPolPresent (t : UInt64) : UInt32
@[extern "wifi_gen_pol_dma"] opaque cPolDma (t : UInt64) : UInt32
@[extern "wifi_gen_pol_cfg_read"] opaque cPolCfgRead (t : UInt64) : UInt64
@[extern "wifi_gen_pol_cfg_write"] opaque cPolCfgWrite (t : UInt64) : UInt64
@[extern "wifi_gen_pol_cmd_clear"] opaque cPolCmdClear (t : UInt64) : UInt32
@[extern "wifi_gen_pol_cmd_set"] opaque cPolCmdSet (t : UInt64) : UInt32
@[extern "wifi_gen_pol_sinks"] opaque cPolSinks (t : UInt64) : UInt32
@[extern "wifi_gen_pol_sink"] opaque cPolSink (t : UInt64) (i : UInt32) : UInt32
@[extern "wifi_gen_pol_descs"] opaque cPolDescs (t : UInt64) : UInt32
@[extern "wifi_gen_pol_desc_trb"] opaque cPolDescTrb (t : UInt64) (k : UInt32) : UInt32
@[extern "wifi_gen_pol_desc_start"] opaque cPolDescStart (t : UInt64) (k : UInt32) : UInt32
@[extern "wifi_gen_pol_desc_count"] opaque cPolDescCount (t : UInt64) (k : UInt32) : UInt32
@[extern "wifi_gen_pol_desc_stride"] opaque cPolDescStride (t : UInt64) (k : UInt32) : UInt32
@[extern "wifi_gen_pc_ok"] opaque cPcOk (t : UInt64) : UInt64
@[extern "wifi_gen_fetch"] opaque cFetch (t : UInt64) (i : UInt32) : UInt64
@[extern "wifi_gen_advance"] opaque cAdvance (t : UInt64) : UInt64
@[extern "wifi_gen_jump"] opaque cJump (t : UInt64) (target : UInt32) : UInt64
@[extern "wifi_gen_stack_full"] opaque cStackFull (t : UInt64) : UInt64
@[extern "wifi_gen_stack_empty"] opaque cStackEmpty (t : UInt64) : UInt64
@[extern "wifi_gen_call"] opaque cCall (t : UInt64) (target : UInt32) : UInt64
@[extern "wifi_gen_ret"] opaque cRet (t : UInt64) : UInt64
@[extern "wifi_gen_reg_get"] opaque cRegGet (t : UInt64) (r : UInt32) : UInt64
@[extern "wifi_gen_reg_set"] opaque cRegSet (t : UInt64) (r v : UInt32) : UInt64
@[extern "wifi_gen_mem_load"] opaque cMemLoad (t : UInt64) (at_ w : UInt32) : UInt64
@[extern "wifi_gen_mem_store"] opaque cMemStore (t : UInt64) (at_ w v : UInt32) : UInt64
@[extern "wifi_gen_mmio_read32"] opaque cMmioRead32 (t : UInt64) (off : UInt32) : UInt64
@[extern "wifi_gen_mmio_read16"] opaque cMmioRead16 (t : UInt64) (off : UInt32) : UInt64
@[extern "wifi_gen_mmio_read8"] opaque cMmioRead8 (t : UInt64) (off : UInt32) : UInt64
@[extern "wifi_gen_mmio_write32"] opaque cMmioWrite32 (t : UInt64) (off v : UInt32) : UInt64
@[extern "wifi_gen_mmio_write16"] opaque cMmioWrite16 (t : UInt64) (off v : UInt32) : UInt64
@[extern "wifi_gen_mmio_write8"] opaque cMmioWrite8 (t : UInt64) (off v : UInt32) : UInt64
@[extern "wifi_gen_cfg_read"] opaque cCfgRead (t : UInt64) (off : UInt32) : UInt64
@[extern "wifi_gen_cfg_write"] opaque cCfgWrite (t : UInt64) (off v : UInt32) : UInt64
@[extern "wifi_gen_cfg_update"] opaque cCfgUpdate (t : UInt64) (off clr set : UInt32) : UInt64
@[extern "wifi_gen_phys"] opaque cPhys (t : UInt64) (off : UInt32) : UInt64
@[extern "wifi_gen_phys_base"] opaque cPhysBase (t : UInt64) : UInt64
@[extern "wifi_gen_delay"] opaque cDelay (t : UInt64) (us : UInt32) : UInt64
@[extern "wifi_gen_print"] opaque cPrint (t : UInt64) (tag v : UInt32) : UInt64
@[extern "wifi_gen_done"] opaque cDone (t : UInt64) (st code : UInt32) : UInt64

/-- The C hooks: the token is the `uint64_t` each hook returns. -/
instance instHooksC : Hooks UInt64 where
  val t := t
  withVal := cValue
  window := cWindow
  blobLen := cBlobLen
  blobWord := cBlobWord
  polPresent := cPolPresent
  polDma := cPolDma
  polCfgRead := cPolCfgRead
  polCfgWrite := cPolCfgWrite
  polCmdClear := cPolCmdClear
  polCmdSet := cPolCmdSet
  polSinks := cPolSinks
  polSink := cPolSink
  polDescs := cPolDescs
  polDescTrb := cPolDescTrb
  polDescStart := cPolDescStart
  polDescCount := cPolDescCount
  polDescStride := cPolDescStride
  pcOk := cPcOk
  fetch := cFetch
  advance := cAdvance
  jump := cJump
  stackFull := cStackFull
  stackEmpty := cStackEmpty
  call := cCall
  ret := cRet
  regGet := cRegGet
  regSet := cRegSet
  memLoad := cMemLoad
  memStore := cMemStore
  mmioRead32 := cMmioRead32
  mmioRead16 := cMmioRead16
  mmioRead8 := cMmioRead8
  mmioWrite32 := cMmioWrite32
  mmioWrite16 := cMmioWrite16
  mmioWrite8 := cMmioWrite8
  cfgRead := cCfgRead
  cfgWrite := cCfgWrite
  cfgUpdate := cCfgUpdate
  phys := cPhys
  physBase := cPhysBase
  delay := cDelay
  print := cPrint
  done := cDone

/-- The generated executor step: `step` at the C hooks. The argument is the
initial token (callers pass 0); the result is the token `wifi_gen_done`
returned. The step's status and code are left in the executor state by
`wifi_gen_done`. -/
@[export leanos_device_program_step]
def deviceProgramStep (t : UInt64) : UInt64 := step t

end LeanOS.Wifi.Exec
