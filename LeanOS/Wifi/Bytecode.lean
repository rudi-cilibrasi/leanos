/-
Lean-authored device programs for the Broadcom BCM43224 WiFi experiment.

The boot image cannot run Lean code that allocates, so the driver is written
here as a program over a deliberately small register-machine instruction set.
A hosted generator encodes the program; a runtime-free C executor (FreeBSD
userland runner or the LeanOS lab kernel) performs only the effects that an
instruction names. Every register access, ordering decision, branch and
acceptance check is authored in Lean.

Machine model:
* 16 general registers `r0..r15`, each 32 bits.
* A device window of 16 KiB (PCI BAR0) addressed by byte offset.
* PCI configuration space of the device addressed by byte offset.
* A read-only data blob, addressed by byte offset, carried with the program.
* Execution ends at `halt` (success) or `fail code` (typed rejection).
-/
namespace LeanOS.Wifi.Bytecode

/-- Register index; the encoder rejects anything outside `0..15`. -/
abbrev Reg := Nat

inductive AluOp where
  | mov | add | sub | and | or | xor | shl | shr | mul | rotl
  deriving Repr, BEq, DecidableEq

def AluOp.code : AluOp → UInt32
  | .mov => 0 | .add => 1 | .sub => 2 | .and => 3
  | .or => 4 | .xor => 5 | .shl => 6 | .shr => 7 | .mul => 8 | .rotl => 9

inductive Cond where
  | eq | ne | ltu | geu
  deriving Repr, BEq, DecidableEq

def Cond.code : Cond → UInt32
  | .eq => 0 | .ne => 1 | .ltu => 2 | .geu => 3

/-- Operand: a register or a 32-bit immediate. -/
inductive Operand where
  | reg (r : Reg)
  | imm (v : UInt32)
  deriving Repr, BEq

/-- Symbolic instruction; branch targets are labels resolved at encoding. -/
inductive Instr where
  | halt
  | fail (code : UInt32)
  | cfgRead32 (dst : Reg) (off : UInt32)
  | cfgWrite32 (off : UInt32) (src : Operand)
  | read32 (dst : Reg) (off : UInt32)
  | read16 (dst : Reg) (off : UInt32)
  | write32 (off : UInt32) (src : Operand)
  | write16 (off : UInt32) (src : Operand)
  /-- Indirect accesses: offset taken from a register plus a constant. -/
  | read32At (dst : Reg) (base : Reg) (off : UInt32)
  | write32At (base : Reg) (off : UInt32) (src : Operand)
  | read16At (dst : Reg) (base : Reg) (off : UInt32)
  | write16At (base : Reg) (off : UInt32) (src : Operand)
  | alu (op : AluOp) (dst : Reg) (src : Operand)
  | branch (c : Cond) (a : Reg) (b : Operand) (target : Nat)
  | jump (target : Nat)
  | delayUs (us : UInt32)
  /-- Emit `WIFI <tag> 0x<value>` on the executor's console. -/
  | print (tag : UInt32) (src : Operand)
  /-- Write `count` little-endian blob words starting at `blobOff` to the
  single device register `off`, in order (firmware FIFO-style upload). -/
  | blobStream32 (off : UInt32) (blobOff : UInt32) (count : UInt32)
  /-- `dst := blob32[blobOff + r(idx)*4]` (table lookup). -/
  | blobLoad32 (dst : Reg) (idx : Reg) (blobOff : UInt32)
  /-- Call and return; the executor keeps a bounded return stack (depth 16). -/
  | call (target : Nat)
  | ret
  /-- Scratch RAM (`scratchBytes`): `dst := mem[r(base) + off]` with width
  1, 2 or 4 bytes, little endian. -/
  | memLoad (width : Nat) (dst : Reg) (base : Reg) (off : UInt32)
  /-- `mem[r(base) + off] := src` (low `width` bytes, little endian). -/
  | memStore (width : Nat) (base : Reg) (off : UInt32) (src : Operand)
  /-- Receive FIFO → scratch: read `r(count)` 32-bit words from device
  register `off` into `mem[r(base)..]`. -/
  | fifoIn (off : UInt32) (base : Reg) (count : Reg)
  /-- Scratch → transmit FIFO: write `r(count)` 32-bit words from
  `mem[r(base)..]` to device register `off`. -/
  | fifoOut (off : UInt32) (base : Reg) (count : Reg)
  deriving Repr

/-- Opcode numbers shared with `hardware/wifi/wifi-exec.h`. -/
def opcode : Instr → UInt32
  | .halt => 0 | .fail _ => 1 | .cfgRead32 .. => 2 | .cfgWrite32 .. => 3
  | .read32 .. => 4 | .read16 .. => 5 | .write32 .. => 6 | .write16 .. => 7
  | .read32At .. => 8 | .write32At .. => 9 | .read16At .. => 10 | .write16At .. => 11
  | .alu .. => 12 | .branch .. => 13 | .jump .. => 14 | .delayUs .. => 15
  | .print .. => 16 | .blobStream32 .. => 17 | .blobLoad32 .. => 18
  | .call .. => 19 | .ret => 20 | .memLoad .. => 21 | .memStore .. => 22
  | .fifoIn .. => 23 | .fifoOut .. => 24

/-- Size of the executor's scratch RAM in bytes. -/
def scratchBytes : Nat := 65536

/-- Operand flag bit in the opcode word marks an immediate operand. -/
def immFlag : UInt32 := 0x100

structure Word4 where
  op : UInt32
  a : UInt32
  b : UInt32
  c : UInt32
  deriving Repr, BEq

def regOk (r : Reg) : Bool := r < 16

def operandFields : Operand → Option (UInt32 × UInt32)
  | .reg r => if regOk r then some (0, r.toUInt32) else none
  | .imm v => some (immFlag, v)

/-- Encode one instruction; `none` for an out-of-range register. -/
def encode (i : Instr) : Option Word4 :=
  let op := opcode i
  let r (x : Reg) : Option UInt32 := if regOk x then some x.toUInt32 else none
  match i with
  | .halt => some ⟨op, 0, 0, 0⟩
  | .fail code => some ⟨op, code, 0, 0⟩
  | .cfgRead32 d off => do some ⟨op, ← r d, off, 0⟩
  | .cfgWrite32 off s => do let (f, v) ← operandFields s; some ⟨op ||| f, off, v, 0⟩
  | .read32 d off => do some ⟨op, ← r d, off, 0⟩
  | .read16 d off => do some ⟨op, ← r d, off, 0⟩
  | .write32 off s => do let (f, v) ← operandFields s; some ⟨op ||| f, off, v, 0⟩
  | .write16 off s => do let (f, v) ← operandFields s; some ⟨op ||| f, off, v, 0⟩
  | .read32At d b off => do some ⟨op, ← r d, ← r b, off⟩
  | .write32At b off s => do let (f, v) ← operandFields s; some ⟨op ||| f, ← r b, off, v⟩
  | .read16At d b off => do some ⟨op, ← r d, ← r b, off⟩
  | .write16At b off s => do let (f, v) ← operandFields s; some ⟨op ||| f, ← r b, off, v⟩
  | .alu o d s => do let (f, v) ← operandFields s; some ⟨op ||| f ||| (o.code <<< 16), ← r d, v, 0⟩
  | .branch c a b t => do
      let (f, v) ← operandFields b
      some ⟨op ||| f ||| (c.code <<< 16), ← r a, v, t.toUInt32⟩
  | .jump t => some ⟨op, t.toUInt32, 0, 0⟩
  | .delayUs us => some ⟨op, us, 0, 0⟩
  | .print tag s => do let (f, v) ← operandFields s; some ⟨op ||| f, tag, v, 0⟩
  | .blobStream32 off b n => some ⟨op, off, b, n⟩
  | .blobLoad32 d idx b => do some ⟨op, ← r d, ← r idx, b⟩
  | .call t => some ⟨op, t.toUInt32, 0, 0⟩
  | .ret => some ⟨op, 0, 0, 0⟩
  | .memLoad w d b off => do
      if w != 1 && w != 2 && w != 4 then none
      some ⟨op ||| (w.toUInt32 <<< 16), ← r d, ← r b, off⟩
  | .memStore w b off s => do
      if w != 1 && w != 2 && w != 4 then none
      let (f, v) ← operandFields s
      some ⟨op ||| f ||| (w.toUInt32 <<< 16), ← r b, off, v⟩
  | .fifoIn off b n => do some ⟨op, off, ← r b, ← r n⟩
  | .fifoOut off b n => do some ⟨op, off, ← r b, ← r n⟩

/-! ## Builder

Programs are written in `ProgM`, which appends instructions, allocates labels
and records a data blob. Labels are resolved once the program is complete. -/

structure BuildState where
  code : Array Instr := #[]
  /-- label id ↦ instruction index (filled when placed). -/
  labels : Array (Option Nat) := #[]
  blob : ByteArray := ByteArray.empty
  /-- Named blob sections for diagnostics. -/
  sections : Array (String × Nat × Nat) := #[]

abbrev ProgM := StateM BuildState

def emit (i : Instr) : ProgM Unit := modify fun s => { s with code := s.code.push i }

/-- Fresh label; branch instructions carry label ids until resolution. -/
def newLabel : ProgM Nat := do
  let s ← get
  set { s with labels := s.labels.push none }
  return s.labels.size

def place (l : Nat) : ProgM Unit := modify fun s =>
  { s with labels := s.labels.set! l (some s.code.size) }

/-- Append bytes to the blob (4-byte aligned) and return their offset. -/
def addBlob (name : String) (bytes : ByteArray) : ProgM UInt32 := do
  let s ← get
  let pad := (4 - s.blob.size % 4) % 4
  let base := s.blob.size + pad
  let blob := (s.blob ++ ByteArray.mk (Array.replicate pad 0)) ++ bytes
  set { s with blob, sections := s.sections.push (name, base, bytes.size) }
  return base.toUInt32

/-- Resolve label ids in branch/jump/call targets to instruction indices. -/
def resolve (s : BuildState) : Except String (Array Instr) :=
  s.code.mapM fun i =>
    let fix (l : Nat) : Except String Nat :=
      match s.labels[l]? with
      | some (some pc) => .ok pc
      | _ => .error s!"unplaced label {l}"
    match i with
    | .branch c a b l => return .branch c a b (← fix l)
    | .jump l => return .jump (← fix l)
    | .call l => return .call (← fix l)
    | other => .ok other

structure Program where
  words : Array Word4
  blob : ByteArray
  sections : Array (String × Nat × Nat)

def build (p : ProgM Unit) : Except String Program := do
  let ((), s) := p.run {}
  let code ← resolve s
  let mut words := #[]
  for i in code, pc in [0:code.size] do
    match encode i with
    | some w => words := words.push w
    | none => throw s!"bad register at pc {pc}: {repr i}"
  return { words, blob := s.blob, sections := s.sections }

/-! ## Binary image

Layout (little endian): magic `LWIF`, version 1, instruction count, blob
length, then 16-byte instructions, then the blob. -/

def putU32 (b : ByteArray) (v : UInt32) : ByteArray :=
  b.push v.toUInt8 |>.push (v >>> 8).toUInt8 |>.push (v >>> 16).toUInt8 |>.push (v >>> 24).toUInt8

def Program.image (p : Program) : ByteArray := Id.run do
  let mut b := ByteArray.empty
  b := putU32 b 0x4649574c -- "LWIF"
  b := putU32 b 1
  b := putU32 b p.words.size.toUInt32
  b := putU32 b p.blob.size.toUInt32
  for w in p.words do
    b := putU32 (putU32 (putU32 (putU32 b w.op) w.a) w.b) w.c
  return b ++ p.blob

/-! ## Convenience combinators -/

def halt : ProgM Unit := emit .halt
def fail (code : UInt32) : ProgM Unit := emit (.fail code)
def li (d : Reg) (v : UInt32) : ProgM Unit := emit (.alu .mov d (.imm v))
def mov (d s : Reg) : ProgM Unit := emit (.alu .mov d (.reg s))
def andi (d : Reg) (v : UInt32) : ProgM Unit := emit (.alu .and d (.imm v))
def ori (d : Reg) (v : UInt32) : ProgM Unit := emit (.alu .or d (.imm v))
def addi (d : Reg) (v : UInt32) : ProgM Unit := emit (.alu .add d (.imm v))
def shri (d : Reg) (v : UInt32) : ProgM Unit := emit (.alu .shr d (.imm v))
def shli (d : Reg) (v : UInt32) : ProgM Unit := emit (.alu .shl d (.imm v))
def print (tag : UInt32) (r : Reg) : ProgM Unit := emit (.print tag (.reg r))
def printImm (tag v : UInt32) : ProgM Unit := emit (.print tag (.imm v))
def delay (us : UInt32) : ProgM Unit := emit (.delayUs us)
def w32 (off v : UInt32) : ProgM Unit := emit (.write32 off (.imm v))
def w16 (off v : UInt32) : ProgM Unit := emit (.write16 off (.imm v))
def r32 (d : Reg) (off : UInt32) : ProgM Unit := emit (.read32 d off)
def r16 (d : Reg) (off : UInt32) : ProgM Unit := emit (.read16 d off)

/-- Fail with `code` unless `r` equals `v`. -/
def expectEq (r : Reg) (v code : UInt32) : ProgM Unit := do
  let ok ← newLabel
  emit (.branch .eq r (.imm v) ok)
  print 0xEEEE r
  fail code
  place ok

/-- Structured loop helper: `body` runs until it jumps to the exit label. -/
def ifEq (r : Reg) (v : UInt32) (thenB : ProgM Unit) : ProgM Unit := do
  let skip ← newLabel
  emit (.branch .ne r (.imm v) skip)
  thenB
  place skip

/-- Poll the 32-bit register at `off` until `(value & mask) == want`, with
`tries` attempts separated by `us` microseconds; fail with `code` on timeout.
Uses scratch registers r13 (value) and r14 (counter). -/
def poll32 (off mask want tries us code : UInt32) : ProgM Unit := do
  let top ← newLabel
  let done ← newLabel
  li 14 tries
  place top
  r32 13 off
  andi 13 mask
  emit (.branch .eq 13 (.imm want) done)
  delay us
  emit (.alu .sub 14 (.imm 1))
  emit (.branch .ne 14 (.imm 0) top)
  printImm 0xEEEF off
  fail code
  place done

/-- Same as `poll32` for a 16-bit register. -/
def poll16 (off mask want tries us code : UInt32) : ProgM Unit := do
  let top ← newLabel
  let done ← newLabel
  li 14 tries
  place top
  r16 13 off
  andi 13 mask
  emit (.branch .eq 13 (.imm want) done)
  delay us
  emit (.alu .sub 14 (.imm 1))
  emit (.branch .ne 14 (.imm 0) top)
  printImm 0xEEEF off
  fail code
  place done

/-- Read-modify-write of a 32-bit register: `v := (v & mask) | set`. -/
def maskSet32 (off mask set : UInt32) : ProgM Unit := do
  r32 12 off
  andi 12 mask
  ori 12 set
  emit (.write32 off (.reg 12))

def maskSet16 (off mask set : UInt32) : ProgM Unit := do
  r16 12 off
  andi 12 mask
  ori 12 set
  emit (.write16 off (.reg 12))

end LeanOS.Wifi.Bytecode
