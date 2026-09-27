import LeanOS.Wifi.NPhyRxCal
import LeanOS.Wifi.Sim
import Std.Data.HashMap

/-! Hosted checks for `LeanOS.Wifi.NPhyRxCal` (no hardware).

Run with `lake env lean --run tests/WifiNPhyRxCal.lean`.

* Arithmetic subroutines (`wlc_phy_nbits`, `int_sqrt`, the
  `wlc_phy_calc_rx_iq_comp_nphy` coefficient math) executed by
  `LeanOS.Wifi.Sim` against Lean reference implementations of the C
  semantics, on hand-worked and pseudo-random vectors.
* The generation-time CORDIC tone against `Float` sin/cos.
* The whole `rxiqCal (qotom 6)` against a register-map device model in
  several scenarios: it halts (never `fail`s) within a step bound, leaves
  r0 = 0, and writes scratch only inside 0x5800-0x5BFF. -/

open LeanOS.Wifi LeanOS.Wifi.Bytecode LeanOS.Wifi.NPhy LeanOS.Wifi.NPhyRxCal

structure Ctx where
  failures : IO.Ref Nat

def check (ctx : Ctx) (name : String) (ok : Bool) (detail : String := "") : IO Unit := do
  if ok then
    IO.println s!"PASS {name}"
  else
    ctx.failures.modify (· + 1)
    IO.println s!"FAIL {name}{if detail.isEmpty then "" else ": " ++ detail}"

/-! ## Reference math (C semantics over `Int`) -/

def two32 : Int := 4294967296
/-- Two's-complement wrap to s32. -/
def wrapS (x : Int) : Int := let m := x % two32; if m ≥ 2147483648 then m - two32 else m
def wrapU (x : Int) : Int := x % two32
def ofS (v : UInt32) : Int := wrapS v.toNat
def toU (x : Int) : UInt32 := (wrapU x).toNat.toUInt32

/-- `wlc_phy_nbits(s32)`: bit length of |v|; |INT_MIN| overflows → 0. -/
def refNbits (v : Int) : Nat :=
  let a := if v < 0 then -v else v
  if a ≥ 2147483648 then 0 else (a.toNat).log2 + (if a == 0 then 0 else 1)

/-- `(s32) int_sqrt((unsigned long)(s32) b)` on a 64-bit kernel. -/
def refIsqrt (b : Int) : Int := if b < 0 then -1 else (b.toNat.sqrt : Int)

/-- The coefficient computation of `wlc_phy_calc_rx_iq_comp_nphy` for one
core: `none` for `-EBADE`, else `(a, b)` before masking. -/
def refIqComp (iq : Int) (ii qq : Int) : Option (Int × Int) := do
  if wrapU (ii + qq) < 2 then none
  let iqN : Int := refNbits iq
  let qqN : Int := refNbits (wrapS qq)
  let sh := (30 - iqN) % 32                    -- x86 shift-count masking
  let arsh := 10 - (30 - iqN)
  let t1 := wrapS (iq * 2 ^ sh.toNat)
  let (a0, tA) :=
    if arsh ≥ 0 then
      (wrapS (-t1 + ii / 2 ^ (1 + arsh).toNat), wrapS (ii / 2 ^ arsh.toNat))
    else
      (wrapS (-t1 + wrapU (ii * 2 ^ (-1 - arsh).toNat)), wrapS (wrapU (ii * 2 ^ (-arsh).toNat)))
  if tA == 0 then none
  let a := wrapS (Int.tdiv a0 tA)
  let brsh := qqN - 31 + 20
  let b0 := wrapS (qq * 2 ^ (31 - qqN).toNat)
  let tB := if brsh ≥ 0 then wrapS (ii / 2 ^ brsh.toNat) else wrapS (wrapU (ii * 2 ^ (-brsh).toNat))
  if tB == 0 then none
  let b1 := wrapS (Int.tdiv b0 tB)
  let b2 := wrapS (b1 - a * a)
  let b := wrapS (refIsqrt b2 - 1024)
  return (a, b)

/-! ## Running subroutines in the simulator -/

def runRegs (p : ProgM Unit) : Except String (Sim.Status × Array UInt32 × Nat) := do
  let prog ← build p
  let (st, m) := Sim.run prog Sim.Device.none () 100000
  return (st, m.regs, m.steps)

def simNbits (v : UInt32) : Option UInt32 :=
  match runRegs (do let l ← subroutine nbitsBody; li 0 v; call l; halt) with
  | .ok (.halt, r, _) => some r[0]!
  | _ => none

def simIsqrt (v : UInt32) : Option UInt32 :=
  match runRegs (do let l ← subroutine isqrtBody; li 0 v; call l; halt) with
  | .ok (.halt, r, _) => some r[0]!
  | _ => none

/-- Returns `(err, a, b)`. -/
def simIqComp (iq ii qq : UInt32) : Option (UInt32 × UInt32 × UInt32) :=
  let p : ProgM Unit := do
    let n ← subroutine nbitsBody
    let s ← subroutine isqrtBody
    let m ← subroutine (iqCompMathBody n s)
    li 1 iq; li 2 ii; li 3 qq
    call m
    halt
  match runRegs p with
  | .ok (.halt, r, _) => some (r[0]!, r[4]!, r[5]!)
  | _ => none

/-- Small LCG for reproducible pseudo-random vectors. -/
def lcg (s : UInt64) : UInt64 := s * 6364136223846793005 + 1442695040888963407

def randoms (n : Nat) (seed : UInt64) : Array UInt32 := Id.run do
  let mut s := seed
  let mut out := #[]
  for _ in [0:n] do
    s := lcg s
    let v := (s >>> 32).toUInt32
    -- vary the magnitude: shift right by 0..31
    s := lcg s
    out := out.push (v >>> ((s >>> 40).toUInt32 % 32))
  return out

def arithTests (ctx : Ctx) : IO Unit := do
  -- nbits
  let nb : Array UInt32 := #[0, 1, 2, 3, 255, 256, 0x7fffffff, 0x80000000, 0xffffffff,
    0xfffffffe, 0x40000000, 0xc0000000] ++ randoms 200 1
  let mut bad := #[]
  for v in nb do
    if simNbits v != some (refNbits (ofS v)).toUInt32 then bad := bad.push v
  check ctx s!"nbits vs reference ({nb.size} vectors)" bad.isEmpty s!"{bad}"
  check ctx "nbits hand values" (simNbits 0 == some 0 && simNbits 1 == some 1 &&
    simNbits 0x00100000 == some 21 && simNbits 0xffffffff == some 1 &&
    simNbits 0x80000000 == some 0 && simNbits 0x7fffffff == some 31)
  -- isqrt
  let sq : Array UInt32 := #[0, 1, 2, 3, 4, 15, 16, 17, 1044607, 0x3fffffff, 0x40000000,
    0x7fffffff, 0x80000000, 0xffffffff] ++ randoms 200 2
  bad := #[]
  for v in sq do
    if simIsqrt v != some (toU (refIsqrt (ofS v))) then bad := bad.push v
  check ctx s!"int_sqrt vs reference ({sq.size} vectors)" bad.isEmpty s!"{bad}"
  check ctx "int_sqrt hand values" (simIsqrt 1044607 == some 1022 &&
    simIsqrt 0x7fffffff == some 46340 && simIsqrt 0xfffffc00 == some 0xffffffff)
  -- iq comp math: hand-worked vector (ii = qq = 2^24, iq = 2^20):
  -- iq_nbits 21, arsh 1: a = (-2^29 + 2^22) / 2^23 = -63 (trunc);
  -- qq_nbits 25, brsh 14: b = 2^30 / 2^10 - 63^2 = 1044607, sqrt 1022, - 1024 = -2.
  check ctx "iq comp hand vector (a = -63, b = -2)"
    (simIqComp 0x00100000 0x01000000 0x01000000 == some (0, toU (-63), toU (-2)))
  check ctx "iq comp hand vector reference agrees"
    (refIqComp 0x00100000 0x01000000 0x01000000 == some (-63, -2))
  check ctx "iq comp rejects ii + qq < 2" ((simIqComp 5 1 0).map (·.1) == some 1)
  check ctx "iq comp rejects iq = 0 (temp = ii << 20 wraps to 0)"
    ((simIqComp 0 0x01000000 0x01000000).map (·.1) == some 1 &&
     refIqComp 0 0x01000000 0x01000000 == none)
  -- random and structured vectors
  let r1 := randoms 150 3
  let r2 := randoms 150 4
  let r3 := randoms 150 5
  let mut cases : Array (UInt32 × UInt32 × UInt32) := #[]
  for h : k in [0:r1.size] do
    cases := cases.push (r1[k], r2.getD k 0, r3.getD k 0)
  -- realistic: ii ≈ qq ≈ P, |iq| small relative to P
  for p in [0x00010000, 0x00100000, 0x01000000, 0x08000000, 0x20000000] do
    for f in [0, 1, 7, 64, 1000] do
      let pp : UInt32 := p
      cases := cases.push (pp / 1024 * f.toUInt32 / 8, pp, pp + pp / 16)
      cases := cases.push (toU (-(ofS (pp / 1024 * f.toUInt32 / 8))), pp + pp / 32, pp)
  cases := cases.push (0x7fffffff, 0x40000000, 0x40000000)   -- iq_nbits = 31
  cases := cases.push (0x80000000, 0x40000000, 0x40000000)   -- iq = INT_MIN
  let mut badc := #[]
  for (iq, ii, qq) in cases do
    let want := match refIqComp (ofS iq) ii.toNat qq.toNat with
      | none => some ((1 : UInt32), (0 : UInt32), (0 : UInt32))
      | some (a, b) => some (0, toU a, toU b)
    let got := match simIqComp iq ii qq with
      | some (1, _, _) => some (1, 0, 0)
      | g => g
    if got != want then badc := badc.push (iq, ii, qq)
  check ctx s!"iq comp vs reference ({cases.size} vectors)" badc.isEmpty
    s!"{badc.toList.take 5}"

/-! ## CORDIC tone -/

def cordicTests (ctx : Ctx) : IO Unit := do
  let mut worst : Float := 0
  for t in [0:720] do
    let (i, q) := cordicCalcIq t
    let rad := (t.toFloat) * 3.141592653589793 / 180.0
    let ei := (Float.ofInt i) / 65536.0 - Float.cos rad
    let eq := (Float.ofInt q) / 65536.0 - Float.sin rad
    worst := max worst (max ei.abs eq.abs)
  check ctx s!"cordic_calc_iq within 1e-3 of cos/sin (worst {worst})" (worst < 1e-3)
  let s := toneSamples 2000 181 20 160
  let first := s.getD 0 0
  -- theta 0: i = 181, q = 0 → (181 << 10) | 0
  check ctx "tone sample 0 = (181 << 10)" (first == ((181 : UInt32) <<< 10)) s!"{first}"
  let s1 := s.getD 1 0          -- theta 36°: i ≈ 146, q ≈ 106
  check ctx "tone sample 1 ≈ (146, 106)" ((s1 >>> 10).toNat ∈ [146, 147] && (s1 &&& 0x3ff).toNat ∈ [106, 107])
    s!"{s1 >>> 10} {s1 &&& 0x3ff}"
  check ctx "tone lengths" ((toneSamples 9500 181 82 164).size == 164 && s.size == 160)

/-! ## Device model -/

structure Dev where
  phy : Std.HashMap UInt32 UInt32 := {}
  radio : Std.HashMap UInt32 UInt32 := {}
  tbl : Std.HashMap UInt32 UInt32 := {}
  mmio : Std.HashMap UInt32 UInt32 := {}
  phyAddr : UInt32 := 0
  radioAddr : UInt32 := 0
  tblAddr : UInt32 := 0
  tblHi : UInt32 := 0
  /-- Per-core IQ estimator results: i_pwr, q_pwr, iq_prod. -/
  est : Array (UInt32 × UInt32 × UInt32) := #[(0, 0, 0), (0, 0, 0)]
  /-- The IQ estimator never finishes (0x129 bit 0 stays set). -/
  iqStuck : Bool := false
  phyWrites : Nat := 0
  radioWrites : Nat := 0
  deriving Inhabited

def Dev.estReg (d : Dev) (a : UInt32) : Option UInt32 :=
  let base : UInt32 := if a ≥ 0x134 then 0x134 else 0x12c
  if a < 0x12c || a > 0x139 || (a > 0x131 && a < 0x134) then none else
  let core := if base == 0x134 then 1 else 0
  let (ip, qp, iqp) := d.est.getD core (0, 0, 0)
  -- 0: iq lo, 1: iq hi, 2: i lo, 3: i hi, 4: q lo, 5: q hi
  let v := match (a - base).toNat with
    | 0 => iqp &&& 0xffff | 1 => iqp >>> 16
    | 2 => ip &&& 0xffff | 3 => ip >>> 16
    | 4 => qp &&& 0xffff | _ => qp >>> 16
  some v

def Dev.phyWr (d : Dev) (a v : UInt32) : Dev :=
  let d := { d with phyWrites := d.phyWrites + 1 }
  if a == 0x72 then { d with tblAddr := v }
  else if a == 0x74 then { d with tblHi := v }
  else if a == 0x73 then
    { d with tbl := d.tbl.insert d.tblAddr ((d.tblHi <<< 16) ||| v), tblAddr := d.tblAddr + 1 }
  else { d with phy := d.phy.insert a v }

def Dev.phyRd (d : Dev) (a : UInt32) : UInt32 × Dev :=
  if a == 0x73 then ((d.tbl.getD d.tblAddr 0) &&& 0xffff, d)
  else if a == 0x74 then ((d.tbl.getD d.tblAddr 0) >>> 16, { d with tblAddr := d.tblAddr + 1 })
  else if a == 0x129 then
    let v := d.phy.getD a 0
    (if d.iqStuck then v else v &&& ~~~1, d)
  else if a == 0xa4 then (0, d)
  else if a == 0x78 then (0, d)
  else if a == 0xc7 then (1, d)
  else match d.estReg a with
    | some v => (v, d)
    | none => (d.phy.getD a 0, d)

def device : Sim.Device Dev where
  read32 d off := (d.mmio.getD off 0, d)
  read16 d off :=
    if off == 0x3FE then let (v, d) := d.phyRd d.phyAddr; (v.toUInt16, d)
    else if off == 0x3FC then (d.phyAddr.toUInt16, d)
    else if off == 0x3FA then ((d.radio.getD (d.radioAddr &&& ~~~0x100) 0).toUInt16, d)
    else if off == 0x3F6 then (d.radioAddr.toUInt16, d)
    else (0, d)
  write32 d off v :=
    if off == 0x3FC then { (d.phyWr (v &&& 0xffff) (v >>> 16)) with phyAddr := v &&& 0xffff }
    else { d with mmio := d.mmio.insert off v }
  write16 d off v :=
    if off == 0x3FC then { d with phyAddr := v.toUInt32 }
    else if off == 0x3FE then d.phyWr d.phyAddr v.toUInt32
    else if off == 0x3F6 then { d with radioAddr := v.toUInt32 }
    else if off == 0x3FA then
      { d with radio := d.radio.insert d.radioAddr v.toUInt32, radioWrites := d.radioWrites + 1 }
    else d
  cfgRead32 d _ := (0, d)
  cfgWrite32 d _ _ := d

/-- Target gain in the shared slot (txgm, pga, pad, ipa per core). -/
def txGains : Array (Nat × UInt32) :=
  #[(0x5C04, 5), (0x5C06, 5), (0x5C08, 0xf), (0x5C0A, 0xe), (0x5C0C, 0x1c), (0x5C0E, 0x1b),
    (0x5C10, 0x1e), (0x5C12, 0x1d)]

def initMem (m : Sim.Machine Dev) : Sim.Machine Dev := Id.run do
  let mut mem := m.mem
  -- a recognisable pattern everywhere, so stray writes are visible
  for i in [0:scratchBytes] do mem := mem.set! i (i % 251).toUInt8
  for (a, v) in txGains do mem := Sim.memStore mem a 2 v
  return { m with mem }

structure Outcome where
  status : Sim.Status
  r0 : UInt32
  steps : Nat
  strayWrites : Nat
  prints : Array (UInt32 × UInt32)
  dev : Dev

def runCal (d0 : Dev) : Except String Outcome := do
  let prog ← build (do rxiqCal (qotom 6); halt)
  let m0 := initMem { dev := d0 }
  let (st, m) := Sim.run prog device d0 50000000 (init := initMem)
  let mut stray := 0
  for i in [0:scratchBytes] do
    if (i < 0x5800 || i ≥ 0x5C00) && m.mem.get! i != m0.mem.get! i then stray := stray + 1
  return { status := st, r0 := m.regs[0]!, steps := m.steps, strayWrites := stray,
           prints := m.prints, dev := m.dev }

def hex (v : UInt32) : String := "0x" ++ String.ofList (Nat.toDigits 16 v.toNat)

def scenario (ctx : Ctx) (name : String) (d0 : Dev) (extra : Outcome → Bool := fun _ => true) :
    IO Unit := do
  match runCal d0 with
  | .error e => check ctx s!"{name}: build" false e
  | .ok o =>
    let pr := o.prints.toList.map fun (t, v) => s!"{hex t}={hex v}"
    IO.println s!"  {name}: {o.steps} steps, {o.dev.phyWrites} PHY writes, \
      {o.dev.radioWrites} radio writes, prints {pr}"
    check ctx s!"{name}: halts, r0 = 0, scratch only in 0x5800-0x5BFF"
      (o.status == .halt && o.r0 == 0 && o.strayWrites == 0 && extra o)
      s!"{repr o.status} r0={o.r0} stray={o.strayWrites}"

def est (i q iq : UInt32) : Array (UInt32 × UInt32 × UInt32) := #[(i, q, iq), (i, q, iq)]

def calTests (ctx : Ctx) : IO Unit := do
  match build (rxiqCal (qotom 6)) with
  | .ok p => IO.println s!"  rxiqCal (qotom 6): {p.words.size} instructions, blob {p.blob.size} bytes"
  | .error e => check ctx "build" false e
  let base : Dev := { phy := ({} : Std.HashMap UInt32 UInt32).insert 0xa2 0x0033 }
  -- Moderate loopback power: the gain search walks up and runs off the table.
  scenario ctx "nominal" { base with est := est 0x00400000 0x00420000 0x00010000 }
    fun o => o.prints.any (·.1 == Tag.rxIqComp) && o.prints.any (·.1 == Tag.rccal) &&
      !o.prints.any (·.1 == Tag.compRetry)
  -- Strong power: the search walks down to entry 0 (txpwrindex -128 restore).
  scenario ctx "strong" { base with est := est 0x02000000 0x02000000 0x00100000 }
  -- No signal: every estimate is rejected; two retries, old coefficients kept.
  scenario ctx "dead" { base with est := est 0 0 0 }
    fun o => (o.prints.filter (·.1 == Tag.compRetry)).size == 6
  -- IQ estimator never completes: WARN prints, still terminates.
  scenario ctx "iq-est stuck" { base with est := est 0x00400000 0x00400000 0x1000, iqStuck := true }
    fun o => o.prints.any (·.1 == Tag.iqEstTimeout)
  -- Only core 0 receiving (rxcore_state 1): setstate path (MAC off).
  let d1 : Dev := { base with est := est 0x00400000 0x00420000 0x00010000 }
  scenario ctx "rxcore 1" { d1 with phy := d1.phy.insert 0xa2 0x0013 }

def main : IO UInt32 := do
  let ctx : Ctx := { failures := ← IO.mkRef 0 }
  arithTests ctx
  cordicTests ctx
  calTests ctx
  let n ← ctx.failures.get
  IO.println s!"{n} failure(s)"
  return if n == 0 then 0 else 1
