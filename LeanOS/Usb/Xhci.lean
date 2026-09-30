import LeanOS.Wifi.Bytecode

/-
xHCI host controller driver as a Lean device program (xHCI 1.0 / 1.1).

Written from the xHCI specification (Intel, rev 1.1) and the USB 2.0
specification for the Qotom's Intel Bay Trail controller (PCI 8086:0f35 at
00:14.0; CAPLENGTH 0x80, 7 root ports: 1–6 USB 2, 7 USB 3; 32-byte
contexts; 16 scratchpad buffers; runtime registers at 0x2000, doorbells at
0x3000; extended capabilities at 0x8000 with USB legacy support at 0x8040 —
read from the hardware on 2026-09-27).

All DMA structures live in executor scratch RAM, whose bus address the
executor reports (`physAddr`; the LeanOS lab kernel identity-maps it). The
driver polls the event ring; it uses no interrupts.
-/
namespace LeanOS.Usb.Xhci

open LeanOS.Wifi.Bytecode

/-- The controller-specific facts a program is generated for. Every
definition below that touches a register takes the layout as an instance
argument, so the same driver source is generated for the Qotom's Bay Trail
controller (`bayTrail`) and for QEMU's `qemu-xhci` (`qemu`). -/
class Layout where
  target : Target
  /-- CAPLENGTH: the operational registers' offset. -/
  capLength : UInt32
  /-- RTSOFF: the runtime registers' offset. -/
  runtime : UInt32
  /-- DBOFF: the doorbell array's offset. -/
  doorbells : UInt32
  /-- Bay Trail port routing through configuration space (XUSB2PR,
  USB3_PSSEN); other controllers route by themselves. -/
  routing : Bool
  /-- Scratch offsets of the DMA structures (the executor zeroes scratch at
  start). A layout that confines them to a few pages lets a platform expose
  only those pages to the controller (the q35 device-service VT-d window). -/
  dcbaa : UInt32
  spArray : UInt32
  cmdRing : UInt32
  evRing : UInt32
  erst : UInt32
  inputCtx : UInt32
  outCtxBase : UInt32
  ep0RingBase : UInt32
  intRing : UInt32
  dataBuf : UInt32
  reportBuf : UInt32
  prevReport : UInt32
  /-- Driver state words (never handed to the controller). -/
  vars : UInt32
  /-- Scratchpad buffers handed to the controller (HCSPARAMS2), 4 KiB each
  from `spPages`. -/
  scratchpads : Nat
  spPages : UInt32

/-- The Qotom's Intel Bay Trail controller (8086:0f35 at 00:14.0). -/
@[instance_reducible] def bayTrail : Layout where
  target := { bus := 0, dev := 20, fn := 0, id := 0x0f358086, windowBytes := 0x10000 }
  capLength := 0x80
  runtime := 0x2000
  doorbells := 0x3000
  routing := true
  dcbaa := 0x20000
  spArray := 0x20200
  cmdRing := 0x20400
  evRing := 0x20800
  erst := 0x20C00
  inputCtx := 0x21000
  outCtxBase := 0x22000
  ep0RingBase := 0x24000
  intRing := 0x25000
  dataBuf := 0x25800
  reportBuf := 0x25C00
  prevReport := 0x25C40
  vars := 0x26000
  scratchpads := 16
  spPages := 0x10000

/-- QEMU's `qemu-xhci` (1b36:000d; the q35 device lab places it at 00:02.0, requester 16):
CAPLENGTH 0x40, runtime registers at 0x1000, doorbells at 0x2000, 16 KiB. -/
@[instance_reducible] def qemu : Layout where
  target := { bus := 0, dev := 2, fn := 0, id := 0x000d1b36, windowBytes := 0x4000 }
  capLength := 0x40
  runtime := 0x1000
  doorbells := 0x2000
  routing := false
  -- Everything the controller reads or writes lies in scratch 0x0000–0x3E47
  -- (four pages); qemu-xhci asks for no scratchpad buffers.
  dcbaa := 0x0000
  spArray := 0x0100
  cmdRing := 0x0400
  evRing := 0x0800
  erst := 0x0C00
  inputCtx := 0x1000
  outCtxBase := 0x1800
  ep0RingBase := 0x2800
  intRing := 0x3800
  dataBuf := 0x3C00
  reportBuf := 0x3E00
  prevReport := 0x3E40
  vars := 0x4000
  scratchpads := 0
  spPages := 0

variable [Layout]

def target : Target := Layout.target

/-! ## Register layout -/

def capLength : UInt32 := Layout.capLength
def op (o : UInt32) : UInt32 := capLength + o
def usbCmd : UInt32 := op 0x00
def usbSts : UInt32 := op 0x04
def crcrLo : UInt32 := op 0x18
def crcrHi : UInt32 := op 0x1C
def dcbaapLo : UInt32 := op 0x30
def dcbaapHi : UInt32 := op 0x34
def config : UInt32 := op 0x38
def portsc (port : UInt32) : UInt32 := op (0x400 + 0x10 * (port - 1))
def runtime : UInt32 := Layout.runtime
def mfindex : UInt32 := runtime
def ir0 (o : UInt32) : UInt32 := runtime + 0x20 + o
def iman : UInt32 := ir0 0x00
def erstsz : UInt32 := ir0 0x08
def erstbaLo : UInt32 := ir0 0x10
def erstbaHi : UInt32 := ir0 0x14
def erdpLo : UInt32 := ir0 0x18
def erdpHi : UInt32 := ir0 0x1C
def doorbell (slot : UInt32) : UInt32 := Layout.doorbells + 4 * slot

def cmdRun : UInt32 := 0x1
def cmdReset : UInt32 := 0x2
def stsHalted : UInt32 := 0x1
def stsNotReady : UInt32 := 0x800

/-- PORTSC bits. -/
def pscCcs : UInt32 := 0x1
def pscPed : UInt32 := 0x2
def pscPr : UInt32 := 0x10
def pscPrc : UInt32 := 0x200000
def pscCsc : UInt32 := 0x20000
/-- Bits preserved when writing PORTSC ("port state to neutral"): the
read/write and read-only fields; RW1C change bits and PED (RW1C) are written
as 0. -/
def pscNeutral : UInt32 := 0x0E00C3E0 ||| 0x00000009 ||| 0x00003C00 ||| 0x40000000

/-! ## Scratch layout (bytes; the executor zeroes scratch at start) -/

def spPages : UInt32 := Layout.spPages        -- scratchpad buffers, 4 KiB each
def dcbaa : UInt32 := Layout.dcbaa            -- (MaxSlots + 1) × 8
def spArray : UInt32 := Layout.spArray        -- scratchpad array, 8 per buffer
def cmdRing : UInt32 := Layout.cmdRing        -- 64 TRBs
def evRing : UInt32 := Layout.evRing          -- 64 TRBs
def erst : UInt32 := Layout.erst              -- one segment entry
def inputCtx : UInt32 := Layout.inputCtx      -- 33 × 32
def outCtxBase : UInt32 := Layout.outCtxBase  -- slot n: + 0x400 × (n - 1), 4 slots
def ep0RingBase : UInt32 := Layout.ep0RingBase -- slot n: + 0x400 × (n - 1)
def intRing : UInt32 := Layout.intRing        -- keyboard interrupt IN ring
def dataBuf : UInt32 := Layout.dataBuf        -- control transfer data (512)
def reportBuf : UInt32 := Layout.reportBuf    -- interrupt report (64)
def prevReport : UInt32 := Layout.prevReport
def vars : UInt32 := Layout.vars              -- driver state words
def ringTrbs : UInt32 := 64
def maxSlots : UInt32 := 4

-- Driver state words (offsets into scratch).
namespace Var
def cmdEnq : UInt32 := vars + 0x00
def cmdCycle : UInt32 := vars + 0x04
def evDeq : UInt32 := vars + 0x08
def evCycle : UInt32 := vars + 0x0C
def ev0 : UInt32 := vars + 0x10       -- last consumed event, 4 dwords
def ev1 : UInt32 := vars + 0x14
def ev2 : UInt32 := vars + 0x18
def ev3 : UInt32 := vars + 0x1C
def tmo : UInt32 := vars + 0x20
def legacyOff : UInt32 := vars + 0x38
/-- Transfer ring state per ring id: enqueue index, cycle. -/
def ringEnq (ring : Nat) : UInt32 := vars + 0x40 + 8 * ring.toUInt32
def ringCycle (ring : Nat) : UInt32 := vars + 0x44 + 8 * ring.toUInt32
end Var

-- Print tags (0x20xx).
namespace Tag
def begin : UInt32 := 0x2000
def handoff : UInt32 := 0x2001
def running : UInt32 := 0x2002
def portsc : UInt32 := 0x2003
def event : UInt32 := 0x2004
def slot : UInt32 := 0x2005
def addressed : UInt32 := 0x2006
def devDesc : UInt32 := 0x2007
def xferCc : UInt32 := 0x2008
def cmdCc : UInt32 := 0x2009
end Tag

namespace Fail
def noHandoff : UInt32 := 0x7F01
def notHalted : UInt32 := 0x7F02
def resetStuck : UInt32 := 0x7F03
def notRunning : UInt32 := 0x7F04
def eventTimeout : UInt32 := 0x7F05
def command : UInt32 := 0x7F06
def transfer : UInt32 := 0x7F07
def portReset : UInt32 := 0x7F08
def noDma : UInt32 := 0x7F09
end Fail

/-! ## Small helpers (scratch registers r0–r9; callers keep state in scratch) -/

def ld (w : Nat) (dst : Reg) (at_ : UInt32) : ProgM Unit := do
  li 9 0
  emit (.memLoad w dst 9 at_)

def st (w : Nat) (at_ : UInt32) (src : Operand) : ProgM Unit := do
  li 9 0
  emit (.memStore w 9 at_ src)

/-- 64-bit register write of a scratch bus address (high half 0: scratch is
below 4 GiB in every executor that provides DMA). -/
def writePhys64 (lo hi : UInt32) (scratchOff : UInt32) (orBits : UInt32 := 0) : ProgM Unit := do
  emit (.physAddr 0 scratchOff)
  ori 0 orBits
  emit (.write32 lo (.reg 0))
  w32 hi 0

/-- Store the bus address of scratch `off` as a 64-bit little-endian value
at scratch `at_`. -/
def storePhys64 (at_ off : UInt32) (orBits : UInt32 := 0) : ProgM Unit := do
  emit (.physAddr 0 off)
  ori 0 orBits
  st 4 at_ (.reg 0)
  st 4 (at_ + 4) (.imm 0)

/-! ## Rings -/

/-- A TRB ring at scratch `base` whose state lives at `enqV`/`cycleV`. -/
structure Ring where
  base : UInt32
  enqV : UInt32
  cycleV : UInt32

def commandRing : Ring := { base := cmdRing, enqV := Var.cmdEnq, cycleV := Var.cmdCycle }
def transferRing (id : Nat) (base : UInt32) : Ring :=
  { base, enqV := Var.ringEnq id, cycleV := Var.ringCycle id }

/-- Initialise a ring: enqueue 0, cycle 1, last TRB a Link TRB (toggle cycle)
back to the start. -/
def ringInit (r : Ring) : ProgM Unit := do
  st 4 r.enqV (.imm 0)
  st 4 r.cycleV (.imm 1)
  let link := r.base + 16 * (ringTrbs - 1)
  storePhys64 link r.base
  st 4 (link + 8) (.imm 0)
  -- type 6 (Link) | TC; cycle bit written when the producer wraps
  st 4 (link + 12) (.imm (((6 : UInt32) <<< 10) ||| 0x2))

/-- Enqueue one TRB: parameter (p0, p1), status, control (without the cycle
bit, which the ring supplies). Register operands are first copied to r10–r13
so callers may pass any of r0–r9. Uses r1–r5, r9–r13. -/
def enqueue (r : Ring) (p0 p1 status control : Operand) : ProgM Unit := do
  let save (o : Operand) (k : Reg) : ProgM Operand := match o with
    | .reg x => do mov k x; pure (.reg k)
    | .imm v => pure (.imm v)
  let p0 ← save p0 10
  let p1 ← save p1 11
  let status ← save status 12
  let control ← save control 13
  ld 4 1 r.enqV
  ld 4 2 r.cycleV
  mov 3 1
  shli 3 4                                 -- byte offset of the TRB
  emit (.memStore 4 3 r.base p0)
  emit (.memStore 4 3 (r.base + 4) p1)
  emit (.memStore 4 3 (r.base + 8) status)
  match control with
  | .imm c => li 4 c
  | .reg c => mov 4 c
  emit (.alu .or 4 (.reg 2))
  emit (.memStore 4 3 (r.base + 12) (.reg 4))
  addi 1 1
  let noWrap ← newLabel
  emit (.branch .ne 1 (.imm (ringTrbs - 1)) noWrap)
  -- hand the Link TRB to the consumer with the current cycle, then toggle
  li 5 0
  emit (.memLoad 4 4 5 (r.base + 16 * (ringTrbs - 1) + 12))
  andi 4 0xFFFFFFFE
  emit (.alu .or 4 (.reg 2))
  emit (.memStore 4 5 (r.base + 16 * (ringTrbs - 1) + 12) (.reg 4))
  li 1 0
  emit (.alu .xor 2 (.imm 1))
  st 4 r.cycleV (.reg 2)
  place noWrap
  st 4 r.enqV (.reg 1)

/-! ## Event ring -/

/-- Wait for the next event, at most `tries` × 100 µs. On success the event
is copied to `Var.ev0..ev3`, the dequeue pointer advanced and r0 = TRB type;
on timeout r0 = 0. Other events (e.g. port status changes) are returned too;
callers loop. Uses r0–r8. -/
def nextEvent (tries : UInt32) : ProgM Unit := do
  st 4 Var.tmo (.imm tries)
  let top ← newLabel
  let got ← newLabel
  let out ← newLabel
  place top
  ld 4 1 Var.evDeq
  ld 4 2 Var.evCycle
  mov 3 1
  shli 3 4
  emit (.memLoad 4 4 3 (evRing + 12))
  mov 5 4
  andi 5 1
  emit (.branch .eq 5 (.reg 2) got)
  ld 4 6 Var.tmo
  li 0 0
  emit (.branch .eq 6 (.imm 0) out)
  emit (.alu .sub 6 (.imm 1))
  st 4 Var.tmo (.reg 6)
  delay 100
  emit (.jump top)
  place got
  emit (.memLoad 4 5 3 evRing); st 4 Var.ev0 (.reg 5)
  emit (.memLoad 4 5 3 (evRing + 4)); st 4 Var.ev1 (.reg 5)
  emit (.memLoad 4 5 3 (evRing + 8)); st 4 Var.ev2 (.reg 5)
  st 4 Var.ev3 (.reg 4)
  addi 1 1
  let noWrap ← newLabel
  emit (.branch .ne 1 (.imm ringTrbs) noWrap)
  li 1 0
  emit (.alu .xor 2 (.imm 1))
  st 4 Var.evCycle (.reg 2)
  place noWrap
  st 4 Var.evDeq (.reg 1)
  -- ERDP := &evRing[deq] | EHB
  mov 3 1
  shli 3 4
  emit (.physAddr 6 evRing)
  emit (.alu .add 6 (.reg 3))
  ori 6 0x8
  emit (.write32 erdpLo (.reg 6))
  w32 erdpHi 0
  mov 0 4
  shri 0 10
  andi 0 0x3F
  place out

/-- Wait for an event of TRB `type`, discarding others (printed), at most
`tries` × 100 µs in total per event. Fails with `code` on timeout. -/
def waitEvent (type : UInt32) (tries code : UInt32) : ProgM Unit := do
  let top ← newLabel
  let done ← newLabel
  place top
  nextEvent tries
  let timedOut ← newLabel
  emit (.branch .eq 0 (.imm 0) timedOut)
  emit (.branch .eq 0 (.imm type) done)
  print Tag.event 0
  emit (.jump top)
  place timedOut
  printImm Tag.event (0x10000 ||| type)
  fail code
  place done

/-! ## Commands -/

/-- Issue a command TRB and wait for its completion event; fails unless the
completion code is Success (1). On return r7 = slot id from the event. -/
def command (p0 : Operand) (control : Operand) : ProgM Unit := do
  enqueue commandRing p0 (.imm 0) (.imm 0) control
  w32 (doorbell 0) 0
  waitEvent 33 20000 Fail.command
  ld 4 1 Var.ev2
  shri 1 24
  print Tag.cmdCc 1
  let ok ← newLabel
  emit (.branch .eq 1 (.imm 1) ok)
  fail Fail.command
  place ok
  ld 4 7 Var.ev3
  shri 7 24

/-! ## Controller bring-up -/

/-- Take ownership from the BIOS (USB legacy support capability), stop and
reset the controller, program DCBAA, scratchpads, command and event rings,
and start it. -/
def bringUp : ProgM Unit := do
  setTarget target
  emit (.physAddr 0 0)
  let dmaOk ← newLabel
  emit (.branch .ne 0 (.imm 0) dmaOk)
  fail Fail.noDma
  place dmaOk
  let noLegacy ← newLabel
  emit (.cfgRead32 0 0)
  print Tag.begin 0
  -- Memory Space only; zeros to the RW1C status half. Bus Master waits
  -- until the controller is reset: firmware may leave it running with ring
  -- pointers into its own memory, which an IOMMU (the q35 device service's
  -- VT-d window) would fault.
  emit (.cfgUpdate32 0x04 0xFFFF0000 0x0002)
  -- Bay Trail port routing: route every routable USB 2 port to xHCI
  -- (XUSB2PR := XUSB2PRM) and enable SuperSpeed (USB3_PSSEN := USB3PRM).
  if Layout.routing then
    emit (.cfgRead32 0 0xD4)
    emit (.cfgWrite32 0xD0 (.reg 0))
    emit (.cfgRead32 0 0xDC)
    emit (.cfgWrite32 0xD8 (.reg 0))
  -- BIOS handoff. Walk the extended capability list (HCCPARAMS1.xECP in
  -- dwords — 0x2000 → 0x8000 on Bay Trail; next pointer in bits 8–15, in
  -- dwords) to the USB legacy support capability (ID 1; 0x8460 on Bay
  -- Trail; absent on qemu-xhci), set HC OS Owned (bit 24) and wait for HC
  -- BIOS Owned (bit 16) to clear.
  r32 5 0x10
  shri 5 16
  shli 5 2
  emit (.branch .eq 5 (.imm 0) noLegacy)
  li 6 32                                      -- bounded walk
  let walk ← newLabel
  let found ← newLabel
  place walk
  emit (.read32At 0 5 0)
  mov 1 0
  andi 1 0xFF
  emit (.branch .eq 1 (.imm 1) found)
  shri 0 8
  andi 0 0xFF
  emit (.branch .eq 0 (.imm 0) noLegacy)
  shli 0 2
  emit (.alu .add 5 (.reg 0))
  emit (.branch .geu 5 (.imm (target.windowBytes - 4)) noLegacy)
  emit (.alu .sub 6 (.imm 1))
  emit (.branch .ne 6 (.imm 0) walk)
  emit (.jump noLegacy)
  place found
  print Tag.handoff 5
  st 4 Var.legacyOff (.reg 5)
  emit (.read32At 0 5 0)
  print Tag.handoff 0
  ori 0 0x01000000
  emit (.write32At 5 0 (.reg 0))
  st 4 Var.tmo (.imm 1000)
  let wait ← newLabel
  let released ← newLabel
  place wait
  ld 4 5 Var.legacyOff
  emit (.read32At 0 5 0)
  mov 1 0
  andi 1 0x00010000
  emit (.branch .eq 1 (.imm 0) released)
  delay 1000
  ld 4 1 Var.tmo
  emit (.alu .sub 1 (.imm 1))
  st 4 Var.tmo (.reg 1)
  emit (.branch .ne 1 (.imm 0) wait)
  print Tag.handoff 0
  fail Fail.noHandoff
  place released
  print Tag.handoff 0
  -- disable SMIs and clear their status (USBLEGCTLSTS; RW1C bits 29–31)
  emit (.write32At 5 4 (.imm 0xE0000000))
  emit (.read32At 0 5 4)
  print Tag.handoff 0
  place noLegacy
  -- stop, then reset
  maskSet32 usbCmd (~~~cmdRun) 0
  poll32 usbSts stsHalted stsHalted 200 100 Fail.notHalted
  w32 usbCmd cmdReset
  delay 1000
  poll32 usbCmd cmdReset 0 1000 100 Fail.resetStuck
  poll32 usbSts stsNotReady 0 1000 100 Fail.resetStuck
  -- the reset controller holds no stale DMA pointers: Bus Master on
  emit (.cfgUpdate32 0x04 0xFFFF0000 0x0006)
  w32 config maxSlots
  -- scratchpad buffers and DCBAA
  for i in [0:(Layout.scratchpads : Nat)] do
    storePhys64 (spArray + 8 * i.toUInt32) (spPages + 0x1000 * i.toUInt32)
  storePhys64 dcbaa spArray
  writePhys64 dcbaapLo dcbaapHi dcbaa
  -- command ring
  ringInit commandRing
  writePhys64 crcrLo crcrHi cmdRing 1
  -- event ring: one 64-TRB segment
  st 4 Var.evDeq (.imm 0)
  st 4 Var.evCycle (.imm 1)
  storePhys64 erst evRing
  st 4 (erst + 8) (.imm ringTrbs)
  w32 erstsz 1
  writePhys64 erdpLo erdpHi evRing
  writePhys64 erstbaLo erstbaHi erst
  -- run (interrupts stay disabled; the driver polls)
  w32 usbCmd cmdRun
  poll32 usbSts stsHalted 0 1000 100 Fail.notRunning
  r32 0 usbSts
  print Tag.running 0

/-! ## Ports -/

/-- Reset root port `port` (USB 2 protocol) if a device is connected: on
return r0 = PORTSC (0 if nothing connected). -/
def resetRootPort (port : UInt32) : ProgM Unit := do
  r32 0 (portsc port)
  print Tag.portsc 0
  let absent ← newLabel
  let out ← newLabel
  mov 1 0
  andi 1 pscCcs
  emit (.branch .eq 1 (.imm 0) absent)
  andi 0 pscNeutral
  ori 0 pscPr
  emit (.write32 (portsc port) (.reg 0))
  poll32 (portsc port) pscPrc pscPrc 1000 100 Fail.portReset
  -- clear PRC and CSC (RW1C)
  r32 0 (portsc port)
  andi 0 pscNeutral
  ori 0 (pscPrc ||| pscCsc)
  emit (.write32 (portsc port) (.reg 0))
  delay 20000
  r32 0 (portsc port)
  print Tag.portsc 0
  emit (.jump out)
  place absent
  li 0 0
  place out

/-! ## Device contexts -/

def outCtx (slotIdx : Nat) : UInt32 := outCtxBase + 0x400 * slotIdx.toUInt32
def ep0Ring (slotIdx : Nat) : Ring := transferRing slotIdx (ep0RingBase + 0x400 * slotIdx.toUInt32)

/-- Input context field address: context `ctx` (0 = input control, 1 = slot,
2 = EP0, …, DCI + 1), dword `dw`. -/
def ictx (ctx dw : UInt32) : UInt32 := inputCtx + 32 * ctx + 4 * dw

/-- Zero the input context (33 × 32 bytes). -/
def clearInput : ProgM Unit := do
  for k in [0:(33 * 32 / 4)] do
    st 4 (inputCtx + 4 * k.toUInt32) (.imm 0)

/-- Enable Slot, then Address Device with the slot context supplied in
registers: r(routeReg) = route string, r(speedReg) = PORTSC-style speed (1 FS,
2 LS, 3 HS), r(rootPortReg) = root hub port, r(ttReg) = TT hub slot |
TT port << 8 (0 if none). `slotIdx` names the driver's context/ring slot
(0–3). The xHCI slot id is stored at `slotVar` and left in r7. -/
def enableAndAddress (slotIdx : Nat) (slotVar : UInt32)
    (routeReg speedReg rootPortReg ttReg : Reg) : ProgM Unit := do
  -- keep the arguments in scratch across the command
  st 4 (Var.tmo + 4) (.reg routeReg)
  st 4 (Var.tmo + 8) (.reg speedReg)
  st 4 (Var.tmo + 12) (.reg rootPortReg)
  st 4 (Var.tmo + 16) (.reg ttReg)
  command (.imm 0) (.imm ((9 : UInt32) <<< 10))          -- Enable Slot
  st 4 slotVar (.reg 7)
  print Tag.slot 7
  -- DCBAA[slot] := output context
  mov 3 7
  shli 3 3
  emit (.physAddr 0 (outCtx slotIdx))
  emit (.memStore 4 3 dcbaa (.reg 0))
  emit (.memStore 4 3 (dcbaa + 4) (.imm 0))
  let ring := ep0Ring slotIdx
  ringInit ring
  clearInput
  st 4 (ictx 0 1) (.imm 0x3)                  -- add A0 (slot) | A1 (EP0)
  -- slot dw0: route | speed << 20 | context entries 1 << 27
  ld 4 1 (Var.tmo + 4)
  ld 4 2 (Var.tmo + 8)
  shli 2 20
  emit (.alu .or 1 (.reg 2))
  ori 1 ((1 : UInt32) <<< 27)
  st 4 (ictx 1 0) (.reg 1)
  -- slot dw1: root hub port << 16
  ld 4 1 (Var.tmo + 12)
  shli 1 16
  st 4 (ictx 1 1) (.reg 1)
  -- slot dw2: TT hub slot | TT port << 8
  ld 4 1 (Var.tmo + 16)
  st 4 (ictx 1 2) (.reg 1)
  -- EP0: CErr 3, type 4 (control), max packet by speed (LS/FS 8, HS 64)
  ld 4 2 (Var.tmo + 8)
  li 1 (((3 : UInt32) <<< 1) ||| ((4 : UInt32) <<< 3) ||| ((8 : UInt32) <<< 16))
  let notHs ← newLabel
  emit (.branch .ne 2 (.imm 3) notHs)
  li 1 (((3 : UInt32) <<< 1) ||| ((4 : UInt32) <<< 3) ||| ((64 : UInt32) <<< 16))
  place notHs
  st 4 (ictx 2 1) (.reg 1)
  emit (.physAddr 0 ring.base)
  ori 0 1                                      -- DCS
  st 4 (ictx 2 2) (.reg 0)
  st 4 (ictx 2 3) (.imm 0)
  st 4 (ictx 2 4) (.imm 8)                     -- average TRB length
  -- Address Device (BSR 0)
  ld 4 7 slotVar
  shli 7 24
  ori 7 ((11 : UInt32) <<< 10)
  emit (.physAddr 6 inputCtx)
  command (.reg 6) (.reg 7)
  ld 4 7 slotVar
  print Tag.addressed 7

/-! ## Control transfers on EP0 -/

/-- One control transfer on the slot in `slotVar`, driver context `slotIdx`.
`setup0` = bmRequestType | bRequest << 8 | wValue << 16 (register or
immediate), `setup1` = wIndex | wLength << 16; `dirIn` for device-to-host
data. Data goes to/from `dataBuf`. On return r1 = completion code (fails
unless Success or Short Packet). -/
def control (slotIdx : Nat) (slotVar : UInt32) (setup0 setup1 : Operand)
    (length : UInt32) (dirIn : Bool) : ProgM Unit := do
  let ring := ep0Ring slotIdx
  let trt : UInt32 := if length == 0 then 0 else if dirIn then 3 else 2
  enqueue ring setup0 setup1 (.imm 8) (.imm (((2 : UInt32) <<< 10) ||| (0x40 : UInt32) ||| (trt <<< (16 : UInt32))))
  if length != 0 then
    emit (.physAddr 6 dataBuf)
    enqueue ring (.reg 6) (.imm 0) (.imm length)
      (.imm (((3 : UInt32) <<< 10) ||| (if dirIn then 0x10000 else 0)))
  -- status stage: opposite direction of data (IN when no data)
  let statusIn := length == 0 || !dirIn
  enqueue ring (.imm 0) (.imm 0) (.imm 0)
    (.imm (((4 : UInt32) <<< 10) ||| 0x20 ||| (if statusIn then 0x10000 else 0)))
  ld 4 1 slotVar
  shli 1 2
  emit (.write32At 1 (doorbell 0) (.imm 1))
  waitEvent 32 20000 Fail.transfer
  ld 4 1 Var.ev2
  shri 1 24
  let ok ← newLabel
  emit (.branch .eq 1 (.imm 1) ok)
  emit (.branch .eq 1 (.imm 13) ok)
  print Tag.xferCc 1
  fail Fail.transfer
  place ok

/-- GET_DESCRIPTOR(DEVICE, 18) into `dataBuf`; prints idVendor | idProduct
<< 16. -/
def getDeviceDescriptor (slotIdx : Nat) (slotVar : UInt32) : ProgM Unit := do
  control slotIdx slotVar (.imm ((0x80 : UInt32) ||| ((6 : UInt32) <<< 8) ||| ((0x0100 : UInt32) <<< 16))) (.imm ((18 : UInt32) <<< 16)) 18 true
  ld 4 1 (dataBuf + 8)
  print Tag.devDesc 1

end LeanOS.Usb.Xhci
