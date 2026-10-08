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
  /-- Unsigned and signed (two's-complement, truncating) division and
  remainder; division by zero yields 0 (quotient) or the dividend (remainder). -/
  | udiv | sdiv | urem | srem
  /-- Arithmetic (sign-propagating) shift right. -/
  | sar
  deriving Repr, BEq, DecidableEq

def AluOp.code : AluOp → UInt32
  | .mov => 0 | .add => 1 | .sub => 2 | .and => 3
  | .or => 4 | .xor => 5 | .shl => 6 | .shr => 7 | .mul => 8 | .rotl => 9
  | .udiv => 10 | .sdiv => 11 | .urem => 12 | .srem => 13 | .sar => 14

inductive Cond where
  | eq | ne | ltu | geu
  /-- Signed (two's-complement) comparisons. -/
  | lts | ges
  deriving Repr, BEq, DecidableEq

def Cond.code : Cond → UInt32
  | .eq => 0 | .ne => 1 | .ltu => 2 | .geu => 3 | .lts => 4 | .ges => 5

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
  /-- `dst := physical address of scratch byte off` (bus address for DMA
  descriptors). Executors without DMA-capable scratch report 0. -/
  | physAddr (dst : Reg) (off : UInt32)
  /-- Configuration read-modify-write done by the executor:
  `cfg[off] := (cfg[off] & ~clear) | set`. Both masks are immediates, so a
  confinement policy can bound which bits a program may change (for example
  the command register's Memory Space and Bus Master bits). -/
  | cfgUpdate32 (off : UInt32) (clear : UInt32) (set : UInt32)
  /-- Suspend and hand `src` to the executor's caller; resuming continues with
  the next instruction (a driver delivering one event at a time). -/
  | yield (src : Operand)
  /-- 8-bit MMIO (byte registers such as the RTL8168's command register). -/
  | read8 (dst : Reg) (off : UInt32)
  | write8 (off : UInt32) (src : Operand)
  deriving Repr

/-- Opcode numbers shared with `hardware/wifi/wifi-exec.h`. -/
def opcode : Instr → UInt32
  | .halt => 0 | .fail _ => 1 | .cfgRead32 .. => 2 | .cfgWrite32 .. => 3
  | .read32 .. => 4 | .read16 .. => 5 | .write32 .. => 6 | .write16 .. => 7
  | .read32At .. => 8 | .write32At .. => 9 | .read16At .. => 10 | .write16At .. => 11
  | .alu .. => 12 | .branch .. => 13 | .jump .. => 14 | .delayUs .. => 15
  | .print .. => 16 | .blobStream32 .. => 17 | .blobLoad32 .. => 18
  | .call .. => 19 | .ret => 20 | .memLoad .. => 21 | .memStore .. => 22
  | .fifoIn .. => 23 | .fifoOut .. => 24 | .physAddr .. => 25
  | .cfgUpdate32 .. => 26 | .yield _ => 27 | .read8 .. => 28 | .write8 .. => 29

/-- Size of the executor's scratch RAM in bytes. -/
def scratchBytes : Nat := 262144

/-- Operand flag bit in the opcode word marks an immediate operand. -/
def immFlag : UInt32 := 0x100

structure Word4 where
  op : UInt32
  a : UInt32
  b : UInt32
  c : UInt32
  deriving Repr, BEq, Inhabited

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
  | .physAddr d off => do some ⟨op, ← r d, off, 0⟩
  | .fifoIn off b n => do some ⟨op, off, ← r b, ← r n⟩
  | .fifoOut off b n => do some ⟨op, off, ← r b, ← r n⟩
  | .cfgUpdate32 off clr set => some ⟨op, off, clr, set⟩
  | .yield s => do let (f, v) ← operandFields s; some ⟨op ||| f, v, 0, 0⟩
  | .read8 d off => do some ⟨op, ← r d, off, 0⟩
  | .write8 off s => do let (f, v) ← operandFields s; some ⟨op ||| f, off, v, 0⟩

/-! ## Builder

Programs are written in `ProgM`, which appends instructions, allocates labels
and records a data blob. Labels are resolved once the program is complete. -/

/-- PCI function a program drives: its configuration identity dword
(vendor | device << 16), the size of its register window, and the
configuration offset of the memory BAR that locates the window (0x10–0x24;
AHCI's ABAR is 0x24). Images without a target (version 1) drive the Broadcom
BCM43224 at 02:00.0. -/
structure Target where
  bus : UInt32
  dev : UInt32
  fn : UInt32
  id : UInt32
  windowBytes : UInt32
  bar : UInt32 := 0x10
  deriving Repr, BEq, DecidableEq

/-- The target implied by version-1 images: the BCM43224 at 02:00.0. -/
def bcm43224Target : Target :=
  { bus := 2, dev := 0, fn := 0, id := 0x435314e4, windowBytes := 0x4000 }

/-- A typed scratch region whose 64-bit fields a DMA controller reads as bus
addresses (issue #495; ADR 0021). With `trb = false` the region is `count`
pointer fields at `start + stride * i` (DCBAA, scratchpad array, ERST entry,
endpoint-context dequeue pointers). With `trb = true` it is `count` 16-byte
TRBs at `start + stride * i`; a TRB's parameter (bytes 0–7) is a pointer
unless its type (control dword bits 10–15, `Descriptor.trbParamIsPtr`) is 0
(reserved: never a valid TRB) or 2 (Setup Stage: the setup packet inline).
That a layout's map names every pointer field the controller follows is an
assumption about the controller's specification, not proved. -/
structure Descriptor where
  trb : Bool
  start : UInt32
  count : UInt32
  stride : UInt32
  deriving Repr, BEq, DecidableEq, Inhabited

/-- The executor's limit on descriptors per policy. -/
def maxDescriptors : Nat := 16

/-- Bytes of one entry: a TRB or a 64-bit pointer. -/
def Descriptor.size (d : Descriptor) : Nat := if d.trb then 16 else 8

/-- Scratch offset of entry `i`. -/
def Descriptor.addr (d : Descriptor) (i : Nat) : Nat := d.start.toNat + d.stride.toNat * i

/-- One past the region's last byte. -/
def Descriptor.limit (d : Descriptor) : Nat := d.addr (d.count.toNat - 1) + d.size

/-- The executor accepts the descriptor: 1–4096 entries, all inside scratch. -/
def Descriptor.wf (d : Descriptor) : Bool :=
  1 ≤ d.count.toNat && d.count.toNat ≤ 4096 && d.limit ≤ scratchBytes

/-- A TRB whose control dword is `ctl` carries a pointer parameter: every
type except 0 (reserved) and 2 (Setup Stage, immediate data). -/
def Descriptor.trbParamIsPtr (ctl : UInt32) : Bool :=
  let t := (ctl >>> 10) &&& 0x3F
  t != 0 && t != 2

/-- A 64-bit pointer field (`lo`, `hi`) holds zero or a bus address inside
scratch, given the bus address `base` of scratch byte 0. -/
def ptrOk (base lo hi : UInt32) : Bool :=
  hi == 0 && (lo == 0 || lo - base < scratchBytes.toUInt32)

/-- Confinement policy of a device program (`LeanOS/DeviceProgramConfinement`).

Configuration offsets are dword offsets below 0x100 (the header and the
legacy capability area reachable through mechanism 1); bit `k` of a bitmap
names offset `4 * k`. The command register (0x04) is changed only through
`cfgUpdate32`, whose masks must lie inside `cmdClear` / `cmdSet`. `dma`
admits `physAddr`, the only way a program learns a bus address.

`addrSinks` names the low dwords of 64-bit MMIO registers the device
dereferences as bus addresses (for xHCI: CRCR, DCBAAP, ERSTBA, ERDP). A
program may write such a low dword only with `write32`/`write32At` and a
value inside the executor's scratch (`value - phys(0) < scratchBytes`), and
the high dword (`+ 4`) only with zero; any other write that touches a sink
is a policy violation.

`descriptors` is the typed descriptor map: scratch regions whose pointer
fields the device dereferences (`Descriptor`). Every scratch store must leave
each of them holding zero or a bus address inside scratch
(`LeanOS.Wifi.Sim.descOk`), and FIFO input into them is refused. -/
structure Policy where
  window : UInt32
  cfgRead : UInt64
  cfgWrite : UInt64
  cmdClear : UInt32
  cmdSet : UInt32
  dma : Bool
  addrSinks : List UInt32 := []
  descriptors : List Descriptor := []
  deriving Repr, BEq, DecidableEq

/-- The executor accepts the descriptor map (image header check). -/
def Policy.descWf (π : Policy) : Bool :=
  π.descriptors.length ≤ maxDescriptors && π.descriptors.all Descriptor.wf

/-- The `len` scratch bytes at `at_` overlap some descriptor region. -/
def Policy.descTouch (π : Policy) (at_ len : Nat) : Bool :=
  len != 0 && π.descriptors.any fun d => at_ < d.limit && d.start.toNat < at_ + len

/-- Bitmap of the given configuration offsets (offsets ≥ 0x100 are dropped). -/
def cfgBits (offs : List UInt32) : UInt64 :=
  offs.foldl (fun (m : UInt64) (o : UInt32) => if o < 0x100 && o % 4 == 0 then m ||| ((1 : UInt64) <<< (o / 4).toUInt64) else m) 0

/-- `off` is a dword offset below 0x100 whose bit is set in `bits`. -/
def cfgAllowed (bits : UInt64) (off : UInt32) : Bool :=
  off < 0x100 && off % 4 == 0 && (bits >>> (off / 4).toUInt64) &&& 1 == 1

/-- The write at `off` lands in some address sink's 8 bytes. -/
def Policy.sinkTouch (π : Policy) (off : UInt32) : Bool :=
  π.addrSinks.any fun s => off - s < 8

/-- A 32-bit write of `v` to `off` respects the address sinks, given the bus
address `base` of scratch byte 0: outside every sink anything goes; the low
dword takes only a bus address inside scratch and the high dword only zero. -/
def Policy.sinkOk (π : Policy) (base off v : UInt32) : Bool :=
  if !π.sinkTouch off then true
  else if π.addrSinks.contains off then v - base < scratchBytes.toUInt32
  else if π.addrSinks.contains (off - 4) then v == 0
  else false

theorem Policy.sinkOk_of_not_touch {π : Policy} {base off v : UInt32}
    (h : π.sinkTouch off = false) : π.sinkOk base off v = true := by
  simp [Policy.sinkOk, h]

theorem Policy.sinkTouch_of_nil {π : Policy} {off : UInt32} (h : π.addrSinks = []) :
    π.sinkTouch off = false := by
  simp [Policy.sinkTouch, h]

/-- Command-register update masks allowed by `π`. -/
def Policy.updateOk (π : Policy) (off clr set : UInt32) : Bool :=
  off == 0x04 && clr &&& ~~~π.cmdClear == 0 && set &&& ~~~π.cmdSet == 0

structure BuildState where
  code : Array Instr := #[]
  /-- label id ↦ instruction index (filled when placed). -/
  labels : Array (Option Nat) := #[]
  blob : ByteArray := ByteArray.empty
  /-- Named blob sections for diagnostics. -/
  sections : Array (String × Nat × Nat) := #[]
  target : Option Target := none

abbrev ProgM := StateM BuildState

/-- Declare the PCI function this program drives (version-2 image). -/
def setTarget (t : Target) : ProgM Unit := modify fun s => { s with target := some t }

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
  target : Option Target := none
  /-- Declared confinement policy (version-3 image); the executor enforces
  it and the generator only sets it after the static check passes. -/
  policy : Option Policy := none

/-- The PCI function the program drives (version-1 images: the BCM43224). -/
def Program.effTarget (p : Program) : Target := p.target.getD bcm43224Target

def build (p : ProgM Unit) : Except String Program := do
  let ((), s) := p.run {}
  let code ← resolve s
  let mut words := #[]
  for i in code, pc in [0:code.size] do
    match encode i with
    | some w => words := words.push w
    | none => throw s!"bad register at pc {pc}: {repr i}"
  return { words, blob := s.blob, sections := s.sections, target := s.target }

/-! ## Binary image

Layout (little endian): magic `LWIF`, version, instruction count, blob
length; version 2 adds the target (bus << 16 | dev << 8 | fn, configuration
identity dword, window bytes, BAR offset or 0 for 0x10); version 3 further adds the policy
(flags with bit 0 = DMA, policy window, read bitmap low/high, write bitmap
low/high, command clear mask, command set mask, address-sink count, then
that many sink offsets; with flags bit 1, a descriptor count and per
descriptor kind (1 = TRB ring), start, count, stride); then 16-byte
instructions, then the blob. -/

def putU32 (b : ByteArray) (v : UInt32) : ByteArray :=
  b.push v.toUInt8 |>.push (v >>> 8).toUInt8 |>.push (v >>> 16).toUInt8 |>.push (v >>> 24).toUInt8

def Program.image (p : Program) : ByteArray := Id.run do
  let mut b := ByteArray.empty
  b := putU32 b 0x4649574c -- "LWIF"
  b := putU32 b (if p.policy.isSome then 3 else if p.target.isSome then 2 else 1)
  b := putU32 b p.words.size.toUInt32
  b := putU32 b p.blob.size.toUInt32
  if p.target.isSome || p.policy.isSome then
    let t := p.effTarget
    b := putU32 b ((t.bus <<< 16) ||| (t.dev <<< 8) ||| t.fn)
    b := putU32 b t.id
    b := putU32 b t.windowBytes
    b := putU32 b (if t.bar == 0x10 then 0 else t.bar)
  if let some π := p.policy then
    b := putU32 b ((if π.dma then 1 else 0) ||| (if π.descriptors.isEmpty then 0 else 2))
    b := putU32 b π.window
    b := putU32 b π.cfgRead.toUInt32
    b := putU32 b (π.cfgRead >>> 32).toUInt32
    b := putU32 b π.cfgWrite.toUInt32
    b := putU32 b (π.cfgWrite >>> 32).toUInt32
    b := putU32 b π.cmdClear
    b := putU32 b π.cmdSet
    b := putU32 b π.addrSinks.length.toUInt32
    for o in π.addrSinks do b := putU32 b o
    if !π.descriptors.isEmpty then
      b := putU32 b π.descriptors.length.toUInt32
      for d in π.descriptors do
        b := putU32 (putU32 (putU32 (putU32 b (if d.trb then 1 else 0)) d.start) d.count) d.stride
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

/-- Typed rejection, or — when a retry label is supplied — report the code
(tag 0xEEF0) and continue at that label. -/
def failOr (onFail : Option Nat) (code : UInt32) : ProgM Unit :=
  match onFail with
  | none => fail code
  | some l => do printImm 0xEEF0 code; emit (.jump l)

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
