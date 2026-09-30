import LeanOS.Wifi.Sim

/-! Differential fuzzing of the device-program executor (issue #451).

Writes `count` random device-program images to `<dir>/NNNN.bin` and, in
`<dir>/expected.txt`, the simulator's summary line for each: status, code,
final registers, and hashes of the prints, the device-model trace and the
scratch RAM. `hardware/wifi/fuzz-runner.c` prints the same line from the C
executor with the same deterministic device model; the two files must be
identical (`scripts/check-device-programs.sh`).

Programs are raw instruction words, not `Instr` values, so they also cover
encodings the Lean encoder never produces: unknown opcodes and sub-opcodes,
out-of-range registers, misaligned and out-of-window offsets, bad blob and
scratch ranges, runaway branches, stack over/underflow, and policy
violations under random version-1, -2 and -3 headers.

usage: leanos-wifi-fuzz <dir> <count> [seed] -/

open LeanOS.Wifi.Bytecode LeanOS.Wifi

/-- xorshift32. -/
structure Rng where
  s : UInt32

def Rng.next (g : Rng) : UInt32 × Rng :=
  let x := g.s
  let x := x ^^^ (x <<< 13)
  let x := x ^^^ (x >>> 17)
  let x := x ^^^ (x <<< 5)
  (x, ⟨x⟩)

abbrev GenM := StateM Rng

def rand : GenM UInt32 := modifyGet Rng.next

/-- Uniform-ish value in `[0, n)` (`n > 0`). -/
def below (n : Nat) : GenM Nat := return (← rand).toNat % n

def pick {α} [Inhabited α] (xs : Array α) : GenM α := return xs[← below xs.size]!

def chance (percent : Nat) : GenM Bool := return (← below 100) < percent

/-- A register field: usually valid, sometimes 16–19. -/
def regField : GenM UInt32 := do
  if ← chance 2 then pure (16 + (← below 4)).toUInt32 else pure (← below 16).toUInt32

/-- An offset near the interesting boundaries of a window of `size` bytes. -/
def offsetIn (size : Nat) (align : Nat) : GenM UInt32 := do
  match ← below 40 with
  | 0 | 1 | 2 | 3 => pure (size - align).toUInt32
  | 4 => return size.toUInt32
  | 5 => pure ((← below size) + 1).toUInt32  -- often misaligned
  | 6 => pure (← rand)
  | _ => pure (((← below (size / align)) * align)).toUInt32

def cfgOffset : GenM UInt32 := do
  match ← below 5 with
  | 0 => pick #[0x00, 0x04, 0x10, 0x80, 0xAC, 0xD0, 0xD4, 0xD8, 0xDC, 0xFC, 0x100, 0x104, 0xFFC, 0x1000]
  | 1 => pure ((← below 0x1000) + 1).toUInt32
  | _ => pure ((← below 64) * 4).toUInt32

def scratchAddr : GenM UInt32 := do
  match ← below 5 with
  | 0 => pure (scratchBytes - (← below 8)).toUInt32
  | 1 => pure (← rand)
  | _ => pure (← below 4096).toUInt32

/-- One random instruction word for a program of `n` words, window `win`,
blob of `blobLen` bytes. -/
def genWord (n win blobLen : Nat) : GenM Word4 := do
  let base : UInt32 ← if ← chance 1 then pure (27 + (← below 229)).toUInt32
    else pure (← below 27).toUInt32
  let imm : UInt32 := if ← chance 50 then 0x100 else 0
  let target : GenM UInt32 := do
    if ← chance 5 then pure (n + (← below 4)).toUInt32 else pure (← below n).toUInt32
  let (sub, a, b, c) : UInt32 × UInt32 × UInt32 × UInt32 ← match base with
    | 1 => pure (0, ← rand, 0, 0)
    | 2 => pure (0, ← regField, ← cfgOffset, 0)
    | 3 => pure (0, ← cfgOffset, ← regField, 0)
    | 4 | 5 => pure (0, ← regField, ← offsetIn win (if base == 4 then 4 else 2), 0)
    | 6 | 7 => pure (0, ← offsetIn win (if base == 6 then 4 else 2), ← regField, 0)
    | 8 | 10 => pure (0, ← regField, ← regField, ← offsetIn win 4)
    | 9 | 11 => pure (0, ← regField, ← offsetIn win 4, ← regField)
    | 12 => do
      let v ← pick #[0, 1, 30, 31, 32, 33, 0x7FFFFFFF, 0x80000000, 0xFFFFFFFF]
      let src ← if ← chance 30 then pure v else regField
      pure ((← below 16).toUInt32, ← regField, src, 0)
    | 13 => do
      let v ← pick #[0, 1, 0x7FFFFFFF, 0x80000000, 0xFFFFFFFF]
      let src ← if ← chance 30 then pure v else regField
      pure ((← below 7).toUInt32, ← regField, src, ← target)
    | 14 | 19 => pure (0, ← target, 0, 0)
    | 15 => pure (0, (← below 100).toUInt32, 0, 0)
    | 16 => pure (0, ← rand, ← regField, 0)
    | 17 => pure (0, ← offsetIn win 4, ((← below (blobLen + 8)) : Nat).toUInt32,
                    ((← below 8) : Nat).toUInt32)
    | 18 => pure (0, ← regField, ← regField, ((← below (blobLen + 8)) : Nat).toUInt32)
    | 21 => pure (← pick #[1, 2, 4, 3, 0, 8], ← regField, ← regField, ← scratchAddr)
    | 22 => pure (← pick #[1, 2, 4, 3, 0, 8], ← regField, ← scratchAddr, ← regField)
    | 23 | 24 => pure (0, ← offsetIn win 4, ← regField, ← regField)
    | 25 => pure (0, ← regField, ← scratchAddr, 0)
    | 26 => pure (0, ← cfgOffset, ← pick #[0, 0xFFFF0000, 0xFFFFFFFF, ← rand],
                    ← pick #[0, 2, 4, 6, 1, ← rand])
    | _ => pure ((← below 3).toUInt32, ← rand, ← rand, ← rand)
  -- Occasionally flip the immediate flag on opcodes that ignore it, and set
  -- unused high bits, which both executors ignore.
  let noise : UInt32 := if ← chance 5 then 0x200 else 0
  return ⟨base ||| imm ||| noise ||| (sub <<< 16), a, b, c⟩

/-- Registers are only set through ALU moves; seed some useful values. -/
def preamble (win : Nat) : GenM (Array Word4) := do
  let mut ws := #[]
  for r in [0:16] do
    if ← chance 60 then
      let v ← match ← below 5 with
        | 0 => pure ((← below (win / 4)) * 4).toUInt32
        | 1 => pure (← below 64).toUInt32
        | 2 => pure (← below 4096).toUInt32
        | 3 => pick #[0, 1, 2, 4, 30, 31, 32, 0x7FFFFFFF, 0x80000000, 0xFFFFFFFF,
                      (scratchBytes - 4).toUInt32, (scratchBytes - 1).toUInt32]
        | _ => rand
      ws := ws.push ⟨12 ||| 0x100, r.toUInt32, v, 0⟩
  return ws

/-- `mov r, v` as a raw word. -/
def movW (r v : UInt32) : Word4 := ⟨12 ||| 0x100, r, v, 0⟩

/-- Short sequences that set a register to a boundary value and use it at
once, so exact edges (last scratch byte, `INT32_MIN / -1`, shift by 31) are
reached far more often than by independent random words. -/
def gadget (win : Nat) (sinks : List UInt32) : GenM (Array Word4) := do
  let r := (← below 16).toUInt32
  let q := ((r.toNat + 1 + (← below 15)) % 16).toUInt32  -- a different register
  let S := scratchBytes
  let junk ← rand
  let fifoOff := ((← below (win / 4)) * 4).toUInt32
  let nudge ← below 3  -- 0, 1, 2 → one before, at, one past the edge
  match ← below (if sinks.isEmpty then 6 else 10) with
  | 6 | 7 | 8 | 9 => do  -- address sinks: bus addresses at the scratch edges, high dwords, partial writes
    let sink ← pick sinks.toArray
    let scratchOff := (S + nudge - 1 - 4 * (← below 2)).toUInt32
    match ← below 8 with
    | 6 => pure #[movW r 0, movW q (← pick #[0, 1, 2]), ⟨24, sink + 4 * (← below 2).toUInt32, r, q⟩]
    | 7 => pure #[⟨17, sink + 4 * (← below 2).toUInt32, 0, ← pick #[0, 1]⟩]
    | 0 => pure #[⟨25, r, scratchOff, 0⟩, ⟨6, sink, r, 0⟩]
    | 1 => pure #[⟨25, r, ← pick #[0, 0x100], 0⟩, ⟨6, sink, r, 0⟩]
    | 2 => pure #[⟨6 ||| 0x100, sink + 4, ← pick #[0, 0, 1, junk], 0⟩]
    | 3 => pure #[⟨6 ||| 0x100, sink, ← pick #[0x01040000, 0x0103FFFF, 0x01040000, 0x01000000,
                    0x00FFFFFF, junk], 0⟩]
    | 4 => pure #[movW r (sink - 4 * (← below 2).toUInt32), ⟨25, q, (← below 64).toUInt32, 0⟩,
                  ⟨9, r, 4 * (← below 3).toUInt32, q⟩]
    | _ => pure #[⟨7 ||| 0x100, sink + 2 * (← below 4).toUInt32, junk, 0⟩]
  | 0 => do  -- scratch load/store ending exactly at (or one past) the end
    let w : UInt32 ← pick #[1, 2, 4]
    let base : UInt32 ← pick #[0, 1, 4096]
    let off := (S + nudge - 1 - w.toNat - base.toNat).toUInt32
    let st ← chance 50
    if st then pure #[movW r base, ⟨(22 : UInt32) ||| 0x100 ||| (w <<< (16 : UInt32)), r, off, junk⟩]
    else pure #[movW r base, ⟨(21 : UInt32) ||| (w <<< (16 : UInt32)), q, r, off⟩]
  | 1 => do  -- FIFO transfer ending exactly at (or one past) the end
    let k : UInt32 ← pick #[0, 1, 2, 7]
    let at_ := (S + nudge - 1 - 4 * k.toNat).toUInt32
    let op : UInt32 ← pick #[23, 24]
    pure #[movW r at_, movW q k, ⟨op, fifoOff, r, q⟩]
  | 2 => do  -- signed division and remainder edges
    let (x, v) : UInt32 × UInt32 ← pick #[(0x80000000, 0xFFFFFFFF), (0x80000000, 0xFFFFFFFF),
      (0x80000000, 1), (0x7FFFFFFF, 0xFFFFFFFF), (0xFFFFFFF9, 2), (7, 0xFFFFFFFE), (7, 0),
      (0x80000000, 0x80000000), (0, 0)]
    let sub : UInt32 ← pick #[10, 11, 12, 13]
    pure #[movW r x, ⟨(12 : UInt32) ||| 0x100 ||| (sub <<< (16 : UInt32)), r, v, 0⟩]
  | 3 => do  -- shifts and rotates at the width edges
    let x : UInt32 ← pick #[0x80000001, 0x7FFFFFFF, 0xC0000000, 1]
    let v : UInt32 ← pick #[0, 1, 30, 31, 32, 33, 63, 0xFFFFFFFF]
    let sub : UInt32 ← pick #[6, 7, 9, 14]
    pure #[movW r x, ⟨(12 : UInt32) ||| 0x100 ||| (sub <<< (16 : UInt32)), r, v, 0⟩]
  | 4 => do  -- physAddr at the scratch edge
    pure #[⟨25, r, (S + nudge - 1).toUInt32, 0⟩]
  | _ => do  -- register-indirect MMIO at the window edge
    let op : UInt32 ← pick #[8, 9, 10, 11]
    let w := if op == 8 || op == 9 then 4 else 2
    let off := (win + nudge - 1 - w).toUInt32
    if op == 8 || op == 10 then pure #[movW r 0, ⟨op, q, r, off⟩]
    else pure #[movW r 0, ⟨op ||| 0x100, r, off, junk⟩]

def genPolicy (win : Nat) : GenM Policy := do
  let nSinks ← below 4
  let mut sinks : List UInt32 := []
  for _ in [0:nSinks] do
    let base : UInt32 ← pick #[0, 8, 0x10, 0x98, 0xB0]
    let far ← below (win / 8)
    sinks := sinks ++ [base + (if ← chance 20 then (far * 8).toUInt32 else 0)]
  return { addrSinks := sinks
           window := ← pick #[0x4000, 0x10000]
           cfgRead := (((← rand).toUInt64 <<< 32) ||| (← rand).toUInt64)
           cfgWrite := (((← rand).toUInt64 <<< 32) ||| (← rand).toUInt64)
           cmdClear := ← pick #[0xFFFF0000, 0xFFFFFFFF, 0, ← rand]
           cmdSet := ← pick #[2, 6, 0, ← rand]
           dma := ← chance 50 }

def genProgram : GenM Program := do
  let version ← below 3
  let win ← if version == 0 then pure 0x4000 else pick #[0x1000, 0x4000, 0x10000]
  let target : Option Target := if version == 0 then none else
    some { bus := 0, dev := 20, fn := 0, id := 0x0f358086, windowBytes := win.toUInt32 }
  let mut policy : Option Policy := none
  if version == 2 then
    let π ← genPolicy win
    -- The executor rejects a target window wider than the policy window.
    policy := some { π with window := max π.window win.toUInt32 }
  let sinks := (policy.map (·.addrSinks)).getD []
  let blobLen := (← below 16) * 4
  let bytes ← (List.range blobLen).toArray.mapM fun _ => do return (← rand).toUInt8
  let blob := ByteArray.mk bytes
  let body := 8 + (← below 120)
  let pre ← preamble win
  let n := pre.size + body
  let mut words := pre
  for _ in [0:body] do
    if ← chance 12 then words := words ++ (← gadget win sinks)
    else words := words.push (← genWord n win blobLen)
  return { words, blob, sections := #[], target, policy }

def mix (a b : UInt32) : UInt32 := (a ^^^ b) * 0x01000193 + 0x9e3779b9

/-- The deterministic device model shared with `fuzz-runner.c`:
`(acc, n)` is the effect-trace hash and the read counter. -/
def model : Sim.Device (UInt32 × UInt32) where
  read32 s o :=
    let n := s.2 + 1; let v := mix n (o ^^^ 0xa5a5a5a5); (v, (mix s.1 (v ^^^ 1), n))
  read16 s o :=
    let n := s.2 + 1; let v := mix n (o ^^^ 0x3c3c3c3c); (v.toUInt16, (mix s.1 (v ^^^ 2), n))
  write32 s o v := (mix (mix s.1 (o ^^^ 3)) v, s.2)
  write16 s o v := (mix (mix s.1 (o ^^^ 4)) v.toUInt32, s.2)
  cfgRead32 s o :=
    let n := s.2 + 1; let v := mix n (o ^^^ 0x5a5a5a5a); (v, (mix s.1 (v ^^^ 5), n))
  cfgWrite32 s o v := (mix (mix s.1 (o ^^^ 6)) v, s.2)

def maxSteps : Nat := 4000

def statusCode : Sim.Status → Nat
  | .halt => 0 | .fail _ => 1 | .stepLimit => 7
  | .error "bad-pc" => 3 | .error "bad-offset" => 4 | .error "bad-opcode" => 5
  | .error "stack" => 6 | .error "bad-blob" => 8 | .error "bad-mem" => 9
  | .error "policy" => 10 | .error _ => 99

/-- The summary line `fuzz-runner.c` prints for the same image. -/
def summary (p : Program) : String := Id.run do
  let (st, m) := Sim.run p model (0, 0) maxSteps
  let code : Nat := match st with
    | .halt => 0
    | .fail c => c.toNat
    | .stepLimit => m.pc
    | .error "bad-pc" => m.pc
    | .error _ => m.pc - 1
  let prints := m.prints.foldl (fun (h : UInt32) (t, v) => mix (mix h t) v) 0
  let mut scratch : UInt32 := 0x811c9dc5
  for i in [0:scratchBytes] do
    scratch := (scratch ^^^ (m.mem.get! i).toUInt32) * 0x01000193
  let regs := (List.range 16).map fun i => toString (m.regs.getD i 0)
  return s!"{statusCode st} {code} {" ".intercalate regs} {prints} {m.dev.1} {m.dev.2} {scratch}"

def main (args : List String) : IO UInt32 := do
  let (dir, count, seed) ← match args with
    | [d, c] => pure (d, c.toNat!, 0x2545F491)
    | [d, c, s] => pure (d, c.toNat!, s.toNat!)
    | _ => IO.eprintln "usage: leanos-wifi-fuzz <dir> <count> [seed]"; return 2
  IO.FS.createDirAll dir
  let mut g : Rng := ⟨if seed == 0 then 1 else seed.toUInt32⟩
  let mut lines := #[]
  let mut statuses : Array Nat := Array.replicate 11 0
  for k in [0:count] do
    let (p, g') := genProgram.run g
    g := g'
    let name := s!"{dir}/{String.ofList (Nat.toDigits 10 (10000 + k)) |>.drop 1}.bin"
    IO.FS.writeBinFile name p.image
    let line := summary p
    lines := lines.push line
    let s := (line.splitOn " ").head!.toNat!
    statuses := statuses.modify (min s 10) (· + 1)
  IO.FS.writeFile s!"{dir}/expected.txt" ("\n".intercalate lines.toList ++ "\n")
  IO.println s!"wrote {count} programs; status histogram {statuses}"
  return 0
