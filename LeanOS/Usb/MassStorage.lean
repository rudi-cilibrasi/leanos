import LeanOS.Usb.Hid

/-
USB mass storage for LeanOS (issue #619): a read-only bulk-only-transport
(BOT) SCSI reader on the xHCI driver. It finds an interface of class 8 (mass
storage), subclass 6 (SCSI transparent command set) and protocol 0x50
(bulk-only transport), directly on a root port or behind one USB 2.0 hub,
configures its bulk IN and bulk OUT endpoints, and issues INQUIRY, TEST UNIT
READY, READ CAPACITY(10) and READ(10), reporting each step as a serial
record (`docs/usb-mass-storage.md` defines them). It never writes the
medium.

Controller bring-up, hub handling and enumeration are the HID programs'
(`LeanOS/Usb/Hid.lean`); only the interface match, the bulk endpoints and
the transport are this module's.

USB Mass Storage Class Bulk-Only Transport 1.0 (§5 CBW and CSW, §6.7 the
host's handling of the thirteen cases), SPC-4 (INQUIRY, TEST UNIT READY,
REQUEST SENSE) and SBC-3 (READ CAPACITY(10), READ(10)).

Confinement: the program touches the registers, address sinks and
descriptor map the xHCI policies already admit. Its two bulk rings share
the interrupt-ring region of the descriptor map (`intRing`, `ringTrbs`
TRBs): bulk OUT the first half, bulk IN the second, each closed by its own
Link TRB. The CBW, CSW and data buffers are plain scratch (`Layout.bulkBuf`),
which the controller reads or writes but never follows as pointers.
-/
namespace LeanOS.Usb.MassStorage

open LeanOS.Wifi.Bytecode LeanOS.Usb.Xhci LeanOS.Usb.Hid

variable [Layout]

/-! ## Interface and scratch -/

/-- bInterfaceClass mass storage, bInterfaceSubClass SCSI transparent
command set, bInterfaceProtocol bulk-only transport. -/
def ifaceClass : UInt32 := 8
def ifaceSubclass : UInt32 := 6
def ifaceProtocol : UInt32 := 0x50

/-- Command block wrapper (31 bytes), command status wrapper (13 bytes) and
the data stage buffer. -/
def cbwBuf : UInt32 := Layout.bulkBuf
def cswBuf : UInt32 := Layout.bulkBuf + 0x40
def xferBuf : UInt32 := Layout.bulkBuf + 0x100
def xferBytes : UInt32 := 0x4000

/-- Byte `k` of the CBW's command block (CBWCB starts at byte 15). -/
def cdbAt (k : UInt32) : UInt32 := cbwBuf + 15 + k

def cbwSignature : UInt32 := 0x43425355
def cswSignature : UInt32 := 0x53425355

/-- Blocks per READ(10) at most, and the largest block length the data
buffer then holds. -/
def maxCount : UInt32 := 4
def maxBlockBytes : UInt32 := xferBytes / maxCount

/-- The bulk rings: halves of the interrupt-ring region, ring ids 6 and 7. -/
def halfTrbs : UInt32 := ringTrbs / 2
def outRing : Ring := transferRing 6 intRing halfTrbs
def inRing : Ring := transferRing 7 (intRing + 16 * halfTrbs) halfTrbs

/-- TEST UNIT READY attempts before the program gives up. -/
def unitReadyAttempts : UInt32 := 10

/-! ## State (scratch words after the HID enumeration's) -/

namespace M
def inAddr : UInt32 := vars + 0x200
def inMps : UInt32 := vars + 0x204
def outAddr : UInt32 := vars + 0x208
def outMps : UInt32 := vars + 0x20C
def inDci : UInt32 := vars + 0x210
def outDci : UInt32 := vars + 0x214
/-- dCBWTag of the last command (a fresh one per command). -/
def tag : UInt32 := vars + 0x218
/-- The step being run (`Step`), for the CSW and error records. -/
def step : UInt32 := vars + 0x21C
def dataLen : UInt32 := vars + 0x220
/-- Bytes the data stage did not transfer (the transfer event's residual). -/
def residual : UInt32 := vars + 0x224
/-- bCSWStatus and dCSWDataResidue of the last command. -/
def status : UInt32 := vars + 0x228
def residue : UInt32 := vars + 0x22C
def reason : UInt32 := vars + 0x230
def detail : UInt32 := vars + 0x234
def blocks : UInt32 := vars + 0x238
def blockBytes : UInt32 := vars + 0x23C
def lba : UInt32 := vars + 0x240
def tries : UInt32 := vars + 0x244
def blocksRead : UInt32 := vars + 0x248
def skips : UInt32 := vars + 0x24C
def k : UInt32 := vars + 0x250
def blockAt : UInt32 := vars + 0x254
/-- 1 once the current command's CSW has been retried after a stall. -/
def cswRetried : UInt32 := vars + 0x258
end M

/-! ## Records -/

-- Print tags (0x23xx); the lab kernel's print hook renders them
-- (`hardware/lab/qotom-wifi.c.inc`). A record may span several prints: the
-- last one ends the line.
namespace Tag
/-- idVendor | idProduct << 16 of the accepted device. -/
def ready : UInt32 := 0x2300
/-- bulk IN address | max packet << 16 (line continues), then bulk OUT
(line ends). -/
def configuredIn : UInt32 := 0x2301
def configuredOut : UInt32 := 0x2302
/-- Peripheral device type | RMB << 8 (line continues). -/
def inquiry : UInt32 := 0x2310
/-- INQUIRY field `k`: 0 opens vendor, 1 closes it and opens product, 2
opens revision, 3 ends the line. -/
def inquiryField : UInt32 := 0x2311
/-- Four bytes of the current INQUIRY field, first byte lowest. -/
def inquiryText : UInt32 := 0x2312
/-- TEST UNIT READY passed after this many attempts. -/
def unitReady : UInt32 := 0x2320
/-- Sense key | ASC << 8 | ASCQ << 16 | the step it explains << 24. -/
def sense : UInt32 := 0x2321
/-- A CSW with failed status: step | status << 8 (line continues), then
dCSWDataResidue (line ends). -/
def csw : UInt32 := 0x2322
def cswResidue : UInt32 := 0x2323
/-- A stalled bulk endpoint recovered (`clearHalt`): step | stage << 8 |
endpoint address << 16. -/
def stallCleared : UInt32 := 0x2324
/-- Blocks (last LBA + 1; line continues), then the block length. -/
def capacity : UInt32 := 0x2330
def blockBytes : UInt32 := 0x2331
/-- A block read: its LBA (line continues), its first 16 bytes as four
dwords (first byte lowest), then FNV-1a of the whole block (line ends). -/
def block : UInt32 := 0x2340
def head : UInt32 := 0x2341
def fnv : UInt32 := 0x2342
/-- All steps passed: the blocks read. -/
def done : UInt32 := 0x2350
/-- Stop: step | stage << 8 | reason << 16 (line continues), then a
detail word (line ends). -/
def error : UInt32 := 0x23E0
def errorDetail : UInt32 := 0x23E1
end Tag

-- Steps, as the records name them.
namespace Step
def attach : UInt32 := 0
def configure : UInt32 := 1
def inquiry : UInt32 := 2
def unitReady : UInt32 := 3
def capacity : UInt32 := 4
def read : UInt32 := 5
def readPastEnd : UInt32 := 6
def sense : UInt32 := 7
end Step

-- Where in a command a stop happened.
namespace Stage
def none : UInt32 := 0
def cbw : UInt32 := 1
def data : UInt32 := 2
def csw : UInt32 := 3
end Stage

-- Why the program stopped.
namespace Reason
/-- No device with a BOT SCSI interface (and both bulk endpoints). -/
def noDevice : UInt32 := 1
/-- No transfer event within 2 s. -/
def timeout : UInt32 := 2
/-- The endpoint stalled (completion code 6). -/
def stall : UInt32 := 3
/-- Another completion code (detail). -/
def transfer : UInt32 := 4
/-- The CSW was shorter than 13 bytes (detail: bytes missing). -/
def cswLength : UInt32 := 5
def cswSignature : UInt32 := 6
def cswTag : UInt32 := 7
/-- bCSWStatus 2: phase error. -/
def phaseError : UInt32 := 8
/-- bCSWStatus above 2: not a valid CSW. -/
def cswStatus : UInt32 := 9
/-- bCSWStatus 1 where the step needs the command to pass. -/
def failed : UInt32 := 10
/-- TEST UNIT READY still failing after the bounded attempts. -/
def notReady : UInt32 := 11
/-- READ CAPACITY(10) gave a capacity the program cannot read (last LBA
0xFFFFFFFF, block length 0 or above `maxBlockBytes`; detail). -/
def capacity : UInt32 := 12
/-- A data stage moved fewer bytes than asked (detail: bytes missing). -/
def shortRead : UInt32 := 13
/-- The READ(10) past the last LBA passed. -/
def passedPastEnd : UInt32 := 14
end Reason

namespace Fail
/-- The program stopped after an `MSC error=` record. -/
def stopped : UInt32 := 0x7F23
end Fail

/-- Completion codes: Success, Stall Error, Short Packet; `ccNone` marks no
event. -/
def ccSuccess : UInt32 := 1
def ccStall : UInt32 := 6
def ccShort : UInt32 := 13
def ccNone : UInt32 := 0x100

/-! ## Helpers -/

/-- Record why the program stops and jump to the error record at `err`. -/
def stop (err : Nat) (stage reason : UInt32) (detail : Operand) : ProgM Unit := do
  st 4 M.detail detail
  st 4 M.reason (.imm ((stage <<< 8) ||| (reason <<< 16)))
  emit (.jump err)

/-- `dst` := the big-endian dword at scratch `at_`. Uses `tmp` and r9. -/
def ldBe32 (dst tmp : Reg) (at_ : UInt32) : ProgM Unit := do
  ld 1 dst at_
  for k in [1:4] do
    shli dst 8
    ld 1 tmp (at_ + k.toUInt32)
    emit (.alu .or dst (.reg tmp))

/-- Stop the controller (Run/Stop cleared, wait for HCHalted): no transfer
or DMA after the program ends. -/
def quiesce : ProgM Unit := do
  maskSet32 usbCmd (~~~cmdRun) 0
  poll32 usbSts stsHalted stsHalted 200 100 Fail.notHalted

/-! ## Discovery -/

/-- Read the configuration descriptor of the device in context 1 and record
the bulk IN and bulk OUT endpoints (address and max packet size) of the first
interface of class 8, subclass 6, protocol 0x50 that has both; a new matching
interface starts afresh. `M.inAddr`/`M.outAddr` stay 0 when there is none. -/
def findBulkInterface : ProgM Unit := do
  st 4 M.inAddr (.imm 0)
  st 4 M.outAddr (.imm 0)
  findInterface ifaceClass ifaceSubclass ifaceProtocol
    (do st 4 M.inAddr (.imm 0); st 4 M.outAddr (.imm 0))
    fun advance done => do
      emit (.memLoad 1 7 5 (dataBuf + 3))             -- bmAttributes
      andi 7 3
      emit (.branch .ne 7 (.imm 2) advance)           -- bulk only
      emit (.memLoad 1 4 5 (dataBuf + 2))             -- bEndpointAddress
      emit (.memLoad 2 7 5 (dataBuf + 4))             -- wMaxPacketSize
      andi 7 0x7FF
      mov 3 4
      andi 3 0x80
      let isOut ← newLabel
      let recorded ← newLabel
      emit (.branch .eq 3 (.imm 0) isOut)
      st 4 M.inAddr (.reg 4)
      st 4 M.inMps (.reg 7)
      emit (.jump recorded)
      place isOut
      st 4 M.outAddr (.reg 4)
      st 4 M.outMps (.reg 7)
      place recorded
      print Hid.Tag.endpoint 4
      ld 4 1 M.inAddr
      ld 4 3 M.outAddr
      emit (.branch .eq 1 (.imm 0) advance)
      emit (.branch .eq 3 (.imm 0) advance)
      emit (.jump done)

/-- The enumeration's `accept`: r1 ≠ 0 iff the device has a BOT SCSI
interface with both bulk endpoints. -/
def bulkInterface : ProgM Unit := do
  findBulkInterface
  ld 4 1 M.inAddr
  ld 4 3 M.outAddr
  let both ← newLabel
  emit (.branch .ne 3 (.imm 0) both)
  li 1 0
  place both

/-! ## Endpoints -/

/-- Endpoint context of the endpoint whose DCI is in `dciVar` (input context
index DCI + 1): CErr 3, `epType` (2 bulk OUT, 6 bulk IN), the max packet size
in `mpsVar`, its ring with DCS 1, average TRB length 1024. -/
def endpointContext (dciVar mpsVar epType : UInt32) (ring : Ring) : ProgM Unit := do
  ld 4 1 dciVar
  addi 1 1
  shli 1 5                                      -- × 32
  ld 4 2 mpsVar
  shli 2 16
  ori 2 (((3 : UInt32) <<< 1) ||| (epType <<< 3))
  emit (.memStore 4 1 (inputCtx + 4) (.reg 2))
  emit (.physAddr 2 ring.base)
  ori 2 1                                       -- DCS
  emit (.memStore 4 1 (inputCtx + 8) (.reg 2))
  emit (.memStore 4 1 (inputCtx + 12) (.imm 0))
  emit (.memStore 4 1 (inputCtx + 16) (.imm 1024))

/-- SET_CONFIGURATION, then Configure Endpoint for bulk IN (DCI 2n + 1) and
bulk OUT (DCI 2n), each on its half of the interrupt-ring region. -/
def configure : ProgM Unit := do
  ld 4 1 V.cfgValue
  shli 1 16
  ori 1 ((9 : UInt32) <<< 8)
  control 1 V.hidSlot (.reg 1) (.imm 0) 0 false
  ld 4 1 M.inAddr
  andi 1 0xF
  shli 1 1
  addi 1 1
  st 4 M.inDci (.reg 1)
  ld 4 1 M.outAddr
  andi 1 0xF
  shli 1 1
  st 4 M.outDci (.reg 1)
  clearInput
  -- add A0 (slot) | A(in) | A(out)
  li 2 1
  ld 4 1 M.inDci
  emit (.alu .shl 2 (.reg 1))
  li 3 1
  ld 4 1 M.outDci
  emit (.alu .shl 3 (.reg 1))
  emit (.alu .or 2 (.reg 3))
  ori 2 1
  st 4 (ictx 0 1) (.reg 2)
  -- slot: route | speed << 20 | context entries (the larger DCI) << 27
  ld 4 1 M.inDci
  ld 4 3 M.outDci
  let haveMax ← newLabel
  emit (.branch .geu 1 (.reg 3) haveMax)
  mov 1 3
  place haveMax
  shli 1 27
  ld 4 2 V.hidRoute
  emit (.alu .or 1 (.reg 2))
  ld 4 2 V.hidSpeed
  shli 2 20
  emit (.alu .or 1 (.reg 2))
  st 4 (ictx 1 0) (.reg 1)
  ld 4 2 V.rootPort
  shli 2 16
  st 4 (ictx 1 1) (.reg 2)
  ld 4 2 V.hidTt
  st 4 (ictx 1 2) (.reg 2)
  endpointContext M.inDci M.inMps 6 inRing
  endpointContext M.outDci M.outMps 2 outRing
  ringInit outRing
  ringInit inRing
  ld 4 7 V.hidSlot
  shli 7 24
  ori 7 ((12 : UInt32) <<< 10)
  emit (.physAddr 6 inputCtx)
  command (.reg 6) (.reg 7)
  ld 4 1 M.inAddr
  ld 4 2 M.inMps
  shli 2 16
  emit (.alu .or 1 (.reg 2))
  print Tag.configuredIn 1
  ld 4 1 M.outAddr
  ld 4 2 M.outMps
  shli 2 16
  emit (.alu .or 1 (.reg 2))
  print Tag.configuredOut 1

/-! ## Bulk transfers -/

/-- Queue one Normal TRB (IOC, ISP) of `len` bytes at scratch `buf` on
`ring` and ring the doorbell of the endpoint in `dciVar`. `len` may not be
r6. Uses r1–r6, r9–r13. -/
def bulkQueue (ring : Ring) (dciVar buf : UInt32) (len : Operand) : ProgM Unit := do
  emit (.physAddr 6 buf)
  enqueue ring (.reg 6) (.imm 0) len (.imm (((1 : UInt32) <<< 10) ||| 0x20 ||| 0x4))
  ld 4 1 V.hidSlot
  shli 1 2
  ld 4 2 dciVar
  emit (.write32At 1 (doorbell 0) (.reg 2))

/-- Wait for the transfer event of the endpoint in `dciVar` on the device's
slot, at most 2 s for each event: r1 := its completion code (`ccNone` if no
event came), r2 := its residual (bytes not transferred). Other events are
printed (`Xhci.Tag.event`) and skipped, at most 32. Uses r0–r9. -/
def bulkWait (dciVar : UInt32) : ProgM Unit := do
  st 4 M.skips (.imm 32)
  let top ← newLabel
  let skip ← newLabel
  let none_ ← newLabel
  let out ← newLabel
  place top
  nextEvent 20000
  emit (.branch .eq 0 (.imm 0) none_)
  emit (.branch .ne 0 (.imm 32) skip)
  ld 4 1 Var.ev3
  shri 1 24
  ld 4 2 V.hidSlot
  emit (.branch .ne 1 (.reg 2) skip)
  ld 4 1 Var.ev3
  shri 1 16
  andi 1 0x1F
  ld 4 2 dciVar
  emit (.branch .ne 1 (.reg 2) skip)
  ld 4 1 Var.ev2
  mov 2 1
  shri 1 24
  andi 2 0xFFFFFF
  emit (.jump out)
  place skip
  print Xhci.Tag.event 0
  ld 4 1 M.skips
  emit (.alu .sub 1 (.imm 1))
  st 4 M.skips (.reg 1)
  emit (.branch .ne 1 (.imm 0) top)
  place none_
  li 1 ccNone
  li 2 0
  place out

/-- Stop through `err` unless the completion code in r1 is Success (or, with
`allowShort`, Short Packet): a stall, no event or another code. -/
def transferOk (err : Nat) (stage : UInt32) (allowShort : Bool) : ProgM Unit := do
  let ok ← newLabel
  let notStall ← newLabel
  let notTimeout ← newLabel
  emit (.branch .eq 1 (.imm ccSuccess) ok)
  if allowShort then emit (.branch .eq 1 (.imm ccShort) ok)
  emit (.branch .ne 1 (.imm ccStall) notStall)
  stop err stage Reason.stall (.reg 1)
  place notStall
  emit (.branch .ne 1 (.imm ccNone) notTimeout)
  stop err stage Reason.timeout (.reg 1)
  place notTimeout
  stop err stage Reason.transfer (.reg 1)
  place ok

/-- Recover the halted bulk endpoint in `dciVar` (address in `addrVar`), whose
TD on `ring` ended with a stall: Reset Endpoint (xHCI 1.1 §4.6.8; Halted →
Stopped), Set TR Dequeue Pointer to the ring's enqueue TRB with its cycle state
(§4.6.10), which skips the stalled TD, then CLEAR_FEATURE(ENDPOINT_HALT) on the
device (USB 2.0 §9.4.1), which resets its data toggle as Reset Endpoint reset
the controller's (BOT 1.0 §6.6.2). The new dequeue pointer is a bus address
inside the ring, so the command TRB keeps the descriptor map in scratch. Prints
`Tag.stallCleared`. Uses r0–r13. -/
def clearHalt (ring : Ring) (dciVar addrVar : UInt32) (stage : UInt32) : ProgM Unit := do
  -- Reset Endpoint (type 14): slot << 24 | endpoint id << 16
  ld 4 7 V.hidSlot
  shli 7 24
  ld 4 1 dciVar
  shli 1 16
  emit (.alu .or 7 (.reg 1))
  ori 7 ((14 : UInt32) <<< 10)
  command (.imm 0) (.reg 7)
  -- Set TR Dequeue Pointer (type 16): &ring[enqueue] | DCS, SCT 0
  ld 4 1 ring.enqV
  shli 1 4
  emit (.physAddr 6 ring.base)
  emit (.alu .add 6 (.reg 1))
  ld 4 2 ring.cycleV
  emit (.alu .or 6 (.reg 2))
  ld 4 7 V.hidSlot
  shli 7 24
  ld 4 1 dciVar
  shli 1 16
  emit (.alu .or 7 (.reg 1))
  ori 7 ((16 : UInt32) <<< 10)
  command (.reg 6) (.reg 7)
  -- CLEAR_FEATURE(ENDPOINT_HALT): endpoint recipient, wIndex = the address
  ld 4 1 addrVar
  control 1 V.hidSlot (.imm ((0x02 : UInt32) ||| ((1 : UInt32) <<< 8))) (.reg 1) 0 false
  ld 4 1 addrVar
  shli 1 16
  ld 4 2 M.step
  emit (.alu .or 1 (.reg 2))
  ori 1 (stage <<< 8)
  print Tag.stallCleared 1

/-! ## Bulk-only transport -/

/-- One BOT command (BOT 1.0 §5): the CBW on bulk OUT (dCBWTag the next tag,
dCBWDataTransferLength `dataLen` bytes, direction IN when `dataIn`, LUN 0,
bCBWCBLength `cdbLen`; the CBW is zeroed, then `cdb` stores the command
block from `cdbAt 0`), then with `dataIn` the data stage into `xferBuf` on
bulk IN (`dataLen` > 0, at most `xferBytes`), then the 13-byte CSW on bulk
IN, whose signature, tag and status are checked. A data stage the device
stalls (BOT 1.0 §6.7.2: it may stall bulk IN when it has less data than asked,
or none) is recovered (`clearHalt`) and the CSW read; a stalled CSW is recovered
and read once more. A transfer that does not complete, a second stalled CSW, a
short CSW, a wrong signature or tag and a status above 1 stop the program
through `err`. A CSW with failed status (1) is reported
(`Tag.csw`). On return r1 = bCSWStatus (0 passed, 1 failed), also in
`M.status`; `M.residual` holds the bytes the data stage did not transfer,
`M.residue` the CSW's dCSWDataResidue. `dataLen` may not be r9. -/
def botCommand (err : Nat) (step : UInt32) (dataLen : Operand) (dataIn : Bool)
    (cdbLen : UInt32) (cdb : ProgM Unit) : ProgM Unit := do
  st 4 M.dataLen dataLen
  st 4 M.step (.imm step)
  st 4 M.residual (.imm 0)
  for k in [0:8] do
    st 4 (cbwBuf + 4 * k.toUInt32) (.imm 0)
  st 4 cbwBuf (.imm cbwSignature)
  ld 4 1 M.tag
  addi 1 1
  st 4 M.tag (.reg 1)
  st 4 (cbwBuf + 4) (.reg 1)
  ld 4 1 M.dataLen
  st 4 (cbwBuf + 8) (.reg 1)
  -- bmCBWFlags, bCBWLUN 0, bCBWCBLength (CBWCB[0] follows)
  st 4 (cbwBuf + 12) (.imm ((if dataIn then (0x80 : UInt32) else 0) ||| (cdbLen <<< 16)))
  cdb
  -- command transport
  bulkQueue outRing M.outDci cbwBuf (.imm 31)
  bulkWait M.outDci
  transferOk err Stage.cbw false
  -- data transport
  if dataIn then
    ld 4 7 M.dataLen
    bulkQueue inRing M.inDci xferBuf (.reg 7)
    bulkWait M.inDci
    st 4 M.residual (.reg 2)
    let notStalled ← newLabel
    let dataDone ← newLabel
    emit (.branch .ne 1 (.imm ccStall) notStalled)
    clearHalt inRing M.inDci M.inAddr Stage.data
    emit (.jump dataDone)
    place notStalled
    transferOk err Stage.data true
    place dataDone
  -- status transport, once more after a stalled CSW
  st 4 M.cswRetried (.imm 0)
  let cswTop ← newLabel
  place cswTop
  for k in [0:4] do
    st 4 (cswBuf + 4 * k.toUInt32) (.imm 0)
  bulkQueue inRing M.inDci cswBuf (.imm 13)
  bulkWait M.inDci
  let cswNotStalled ← newLabel
  emit (.branch .ne 1 (.imm ccStall) cswNotStalled)
  ld 4 3 M.cswRetried
  emit (.branch .ne 3 (.imm 0) cswNotStalled)
  st 4 M.cswRetried (.imm 1)
  clearHalt inRing M.inDci M.inAddr Stage.csw
  emit (.jump cswTop)
  place cswNotStalled
  transferOk err Stage.csw true
  let whole ← newLabel
  emit (.branch .eq 2 (.imm 0) whole)
  stop err Stage.csw Reason.cswLength (.reg 2)
  place whole
  ld 4 1 cswBuf
  let sigOk ← newLabel
  emit (.branch .eq 1 (.imm cswSignature) sigOk)
  stop err Stage.csw Reason.cswSignature (.reg 1)
  place sigOk
  ld 4 1 (cswBuf + 4)
  ld 4 2 M.tag
  let tagOk ← newLabel
  emit (.branch .eq 1 (.reg 2) tagOk)
  stop err Stage.csw Reason.cswTag (.reg 1)
  place tagOk
  ld 4 2 (cswBuf + 8)
  st 4 M.residue (.reg 2)
  ld 1 1 (cswBuf + 12)
  st 4 M.status (.reg 1)
  let notPhase ← newLabel
  let valid ← newLabel
  let passed ← newLabel
  emit (.branch .ne 1 (.imm 2) notPhase)
  stop err Stage.csw Reason.phaseError (.reg 1)
  place notPhase
  emit (.branch .ltu 1 (.imm 2) valid)
  stop err Stage.csw Reason.cswStatus (.reg 1)
  place valid
  emit (.branch .eq 1 (.imm 0) passed)
  ld 4 1 M.step
  ori 1 ((1 : UInt32) <<< 8)
  print Tag.csw 1
  ld 4 1 M.residue
  print Tag.cswResidue 1
  place passed
  ld 4 1 M.status

/-- Stop through `err` unless the last CSW passed (r1 = 0). -/
def passed (err : Nat) : ProgM Unit := do
  let ok ← newLabel
  emit (.branch .eq 1 (.imm 0) ok)
  stop err Stage.csw Reason.failed (.reg 1)
  place ok

/-! ## SCSI commands -/

/-- INQUIRY (SPC-4 §6.6), 36 bytes of standard data: peripheral device type,
RMB, T10 vendor (bytes 8–15), product (16–31) and revision (32–35). A short
reply leaves the rest zero. -/
def inquiry (err : Nat) : ProgM Unit := do
  for k in [0:9] do
    st 4 (xferBuf + 4 * k.toUInt32) (.imm 0)
  botCommand err Step.inquiry (.imm 36) true 6 do
    st 1 (cdbAt 0) (.imm 0x12)
    st 1 (cdbAt 4) (.imm 36)                       -- allocation length
  passed err
  ld 1 1 xferBuf
  andi 1 0x1F
  ld 1 2 (xferBuf + 1)
  shri 2 7
  shli 2 8
  emit (.alu .or 1 (.reg 2))
  print Tag.inquiry 1
  printImm Tag.inquiryField 0
  for k in [0:2] do
    ld 4 1 (xferBuf + 8 + 4 * k.toUInt32)
    print Tag.inquiryText 1
  printImm Tag.inquiryField 1
  for k in [0:4] do
    ld 4 1 (xferBuf + 16 + 4 * k.toUInt32)
    print Tag.inquiryText 1
  printImm Tag.inquiryField 2
  ld 4 1 (xferBuf + 32)
  print Tag.inquiryText 1
  printImm Tag.inquiryField 3

/-- REQUEST SENSE (SPC-4 §6.29), 18 bytes, reported as the sense that
explains `after`: key, ASC and ASCQ from fixed-format data (response code
0x70/0x71) or from descriptor-format data (0x72/0x73). -/
def requestSense (err : Nat) (after : UInt32) : ProgM Unit := do
  for k in [0:5] do
    st 4 (xferBuf + 4 * k.toUInt32) (.imm 0)
  botCommand err Step.sense (.imm 18) true 6 do
    st 1 (cdbAt 0) (.imm 0x03)
    st 1 (cdbAt 4) (.imm 18)
  passed err
  ld 1 1 xferBuf
  andi 1 0x7E
  let descriptor ← newLabel
  let got ← newLabel
  emit (.branch .eq 1 (.imm 0x72) descriptor)
  ld 1 1 (xferBuf + 2)
  andi 1 0xF
  ld 1 2 (xferBuf + 12)
  shli 2 8
  emit (.alu .or 1 (.reg 2))
  ld 1 2 (xferBuf + 13)
  shli 2 16
  emit (.alu .or 1 (.reg 2))
  emit (.jump got)
  place descriptor
  ld 1 1 (xferBuf + 1)
  andi 1 0xF
  ld 1 2 (xferBuf + 2)
  shli 2 8
  emit (.alu .or 1 (.reg 2))
  ld 1 2 (xferBuf + 3)
  shli 2 16
  emit (.alu .or 1 (.reg 2))
  place got
  ori 1 (after <<< 24)
  print Tag.sense 1

/-- TEST UNIT READY (SPC-4 §6.37) until it passes, at most `attempts` times
100 ms apart; each failure is followed by REQUEST SENSE (a fresh device
reports a unit attention first). -/
def unitReady (err : Nat) (attempts : UInt32) : ProgM Unit := do
  st 4 M.tries (.imm 0)
  let top ← newLabel
  let ready ← newLabel
  let more ← newLabel
  place top
  ld 4 1 M.tries
  addi 1 1
  st 4 M.tries (.reg 1)
  botCommand err Step.unitReady (.imm 0) false 6 (pure ())   -- opcode 0x00
  emit (.branch .eq 1 (.imm 0) ready)
  requestSense err Step.unitReady
  ld 4 1 M.tries
  emit (.branch .ltu 1 (.imm attempts) more)
  st 4 M.step (.imm Step.unitReady)              -- REQUEST SENSE was the last step
  stop err Stage.csw Reason.notReady (.reg 1)
  place more
  delay 100000
  emit (.jump top)
  place ready
  ld 4 1 M.tries
  print Tag.unitReady 1

/-- READ CAPACITY(10) (SBC-3 §5.15): `M.blocks` := last LBA + 1,
`M.blockBytes` := the block length (both big-endian in the reply). -/
def readCapacity (err : Nat) : ProgM Unit := do
  botCommand err Step.capacity (.imm 8) true 10 (st 1 (cdbAt 0) (.imm 0x25))
  passed err
  ld 4 1 M.residual
  let whole ← newLabel
  emit (.branch .eq 1 (.imm 0) whole)
  stop err Stage.data Reason.shortRead (.reg 1)
  place whole
  ldBe32 1 2 xferBuf
  let lbaOk ← newLabel
  emit (.branch .ne 1 (.imm 0xFFFFFFFF) lbaOk)
  stop err Stage.data Reason.capacity (.reg 1)          -- needs READ CAPACITY(16)
  place lbaOk
  addi 1 1
  st 4 M.blocks (.reg 1)
  ldBe32 1 2 (xferBuf + 4)
  st 4 M.blockBytes (.reg 1)
  let lenBad ← newLabel
  let lenOk ← newLabel
  emit (.branch .eq 1 (.imm 0) lenBad)
  emit (.branch .ltu 1 (.imm (maxBlockBytes + 1)) lenOk)
  place lenBad
  stop err Stage.data Reason.capacity (.reg 1)
  place lenOk
  ld 4 1 M.blocks
  print Tag.capacity 1
  ld 4 1 M.blockBytes
  print Tag.blockBytes 1

/-- READ(10) (SBC-3 §5.11) of `count` blocks (1 ≤ count ≤ `maxCount`) from
the LBA in `M.lba` into `xferBuf`; returns the CSW status in r1. -/
def read10 (err : Nat) (step count : UInt32) : ProgM Unit := do
  ld 4 7 M.blockBytes
  if count > 1 then emit (.alu .mul 7 (.imm count))
  botCommand err step (.reg 7) true 10 do
    st 1 (cdbAt 0) (.imm 0x28)
    ld 4 1 M.lba
    for k in [0:4] do                                   -- LBA, big-endian
      mov 2 1
      shri 2 (24 - 8 * k.toUInt32)
      st 1 (cdbAt (2 + k.toUInt32)) (.reg 2)
    st 1 (cdbAt 7) (.imm (count >>> 8))                 -- transfer length
    st 1 (cdbAt 8) (.imm (count &&& 0xFF))

/-- Report the `count` blocks in `xferBuf` read from `M.lba` on: per block
its LBA, its first 16 bytes and the 32-bit FNV-1a hash of its
`M.blockBytes` bytes (offset basis 0x811C9DC5, prime 0x01000193: for each
byte, xor then multiply). Counts them in `M.blocksRead`. -/
def reportBlocks (count : UInt32) : ProgM Unit := do
  st 4 M.k (.imm 0)
  st 4 M.blockAt (.imm 0)
  let next ← newLabel
  let hash ← newLabel
  place next
  ld 4 1 M.lba
  ld 4 2 M.k
  emit (.alu .add 1 (.reg 2))
  print Tag.block 1
  ld 4 3 M.blockAt
  for d in [0:4] do
    emit (.memLoad 4 1 3 (xferBuf + 4 * d.toUInt32))
    print Tag.head 1
  ld 4 4 M.blockBytes
  emit (.alu .add 4 (.reg 3))                           -- end of the block
  li 1 0x811C9DC5
  place hash
  emit (.memLoad 1 2 3 xferBuf)
  emit (.alu .xor 1 (.reg 2))
  emit (.alu .mul 1 (.imm 0x01000193))
  addi 3 1
  emit (.branch .ltu 3 (.reg 4) hash)
  print Tag.fnv 1
  st 4 M.blockAt (.reg 3)
  ld 4 1 M.blocksRead
  addi 1 1
  st 4 M.blocksRead (.reg 1)
  ld 4 1 M.k
  addi 1 1
  st 4 M.k (.reg 1)
  emit (.branch .ltu 1 (.imm count) next)

/-- READ(10) of `count` blocks from the LBA in `M.lba`, which must pass and
transfer every byte, then their records. -/
def readBlocks (err : Nat) (count : UInt32) : ProgM Unit := do
  read10 err Step.read count
  passed err
  ld 4 1 M.residual
  let moved ← newLabel
  let whole ← newLabel
  emit (.branch .eq 1 (.imm 0) moved)
  stop err Stage.data Reason.shortRead (.reg 1)
  place moved
  ld 4 1 M.residue
  emit (.branch .eq 1 (.imm 0) whole)
  stop err Stage.csw Reason.shortRead (.reg 1)
  place whole
  reportBlocks count

/-- READ(10) of the block after the last one: the device must fail it (the
`Tag.csw` record), and REQUEST SENSE then says why (an illegal request, LBA
out of range, on a conforming device). -/
def readPastEnd (err : Nat) : ProgM Unit := do
  ld 4 1 M.blocks
  st 4 M.lba (.reg 1)
  read10 err Step.readPastEnd 1
  let failedOk ← newLabel
  emit (.branch .ne 1 (.imm 0) failedOk)
  stop err Stage.csw Reason.passedPastEnd (.reg 1)
  place failedOk
  requestSense err Step.readPastEnd

/-! ## Program -/

/-- The complete mass-storage program: controller bring-up, enumeration
through at most one hub or directly on a root port, the bulk endpoints,
INQUIRY, TEST UNIT READY, READ CAPACITY(10), READ(10) of LBAs 0–3 (one
command), of the middle LBA (blocks / 2) and of the last two LBAs (one
command), then READ(10) of the LBA after the last, which must fail. The
controller is stopped at the end; a failed step stops it too, after its
`MSC error=` record, and the program then fails with `Fail.stopped`. -/
def program : ProgM Unit := do
  let err ← newLabel
  st 4 M.step (.imm Step.attach)
  attachWith bulkInterface (stop err Stage.none Reason.noDevice (.imm 0))
  ld 4 1 V.ids
  print Tag.ready 1
  st 4 M.step (.imm Step.configure)
  configure
  st 4 M.tag (.imm 0)
  st 4 M.blocksRead (.imm 0)
  inquiry err
  unitReady err unitReadyAttempts
  readCapacity err
  st 4 M.lba (.imm 0)
  readBlocks err maxCount
  ld 4 1 M.blocks
  shri 1 1
  st 4 M.lba (.reg 1)
  readBlocks err 1
  ld 4 1 M.blocks
  emit (.alu .sub 1 (.imm 2))
  st 4 M.lba (.reg 1)
  readBlocks err 2
  readPastEnd err
  ld 4 1 M.blocksRead
  print Tag.done 1
  quiesce
  halt
  place err
  ld 4 1 M.step
  ld 4 2 M.reason
  emit (.alu .or 1 (.reg 2))
  print Tag.error 1
  ld 4 1 M.detail
  print Tag.errorDetail 1
  quiesce
  fail Fail.stopped

end LeanOS.Usb.MassStorage
