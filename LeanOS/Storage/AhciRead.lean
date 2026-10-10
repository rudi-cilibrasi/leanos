import LeanOS.Wifi.Bytecode

/-
One-sector, read-only AHCI device program for the q35 device service
(issue #496).

Written from the Serial ATA AHCI 1.3.1 specification and ATA8-ACS for QEMU's
built-in ICH9 AHCI controller on q35 (PCI 8086:2922 at 00:1f.2, requester
0xFA; ABAR at configuration offset 0x24). Port 0 holds the boot CD-ROM; the
device service attaches a fixed disk image to port 1.

The program is a copy of the #449 keyboard pattern for a second device: the
canonical kernel binds it for the one subject holding the device capability
and resumes it in budgeted slices; each `yield` hands one value to that
subject, which sends it over the verified blocking IPC to a ring-3 client.

It never writes the disk. It checks the controller identity, that ports 0
and 1 are implemented and that port 1 has a device with the PHY up, stops
the command and FIS-receive engines of both ports (firmware may have left
them running on its own memory), and only then enables Bus Master. It
points port 1's command list and received-FIS area at scratch, issues one
READ DMA EXT of one sector at the fixed LBA `readLba` through command slot 0
with a single 512-byte PRD, and polls for completion (a task-file error, an
error status or a timeout fails the program). It then stops port 1's
engines again and clears Bus Master, so the controller can no longer touch
memory, reports the LBA it read, and yields the sector's 128 little-endian
dwords in order before halting.

Every structure the controller reads or writes lies in the first scratch
page (`0x000`–`0x9FF`), which is all the q35 device service grants it through
VT-d. PxCLB and PxFB of ports 0 and 1 are address sinks of its policy; the
command headers' CTBA fields and the PRD data-base fields form its descriptor
map (`descriptorMap`), so `run_admissible_descriptors` covers them.
-/
namespace LeanOS.Storage.AhciRead

open LeanOS.Wifi.Bytecode

/-- QEMU's ICH9 AHCI on q35 (00:1f.2). The window is the generic host
control registers and ports 0 and 1 (`0x000`–`0x1FF`) of the 4 KiB ABAR;
ports 2–5 are outside it. -/
def target : Target :=
  { bus := 0, dev := 31, fn := 2, id := 0x29228086, windowBytes := 0x200, bar := 0x24 }

/-- The one sector the program reads. -/
def readLba : UInt32 := 7

/-! ## Registers (ABAR offsets) -/

def cap : UInt32 := 0x00
def ghc : UInt32 := 0x04
def pi : UInt32 := 0x0C

/-- Port `n`'s register `o` (AHCI 3.3). -/
def port (n o : UInt32) : UInt32 := 0x100 + 0x80 * n + o
def pxClb (n : UInt32) : UInt32 := port n 0x00
def pxClbu (n : UInt32) : UInt32 := port n 0x04
def pxFb (n : UInt32) : UInt32 := port n 0x08
def pxFbu (n : UInt32) : UInt32 := port n 0x0C
def pxIs (n : UInt32) : UInt32 := port n 0x10
def pxCmd (n : UInt32) : UInt32 := port n 0x18
def pxTfd (n : UInt32) : UInt32 := port n 0x20
def pxSsts (n : UInt32) : UInt32 := port n 0x28
def pxSerr (n : UInt32) : UInt32 := port n 0x30
def pxCi (n : UInt32) : UInt32 := port n 0x38

/-- The data port. -/
def dataPort : UInt32 := 1

/-- PxCMD bits. -/
def cmdSt : UInt32 := 0x1
def cmdFre : UInt32 := 0x10
def cmdFr : UInt32 := 0x4000
def cmdCr : UInt32 := 0x8000
/-- PxIS.TFES: task-file error. -/
def isTfes : UInt32 := 0x40000000
/-- PxTFD.STS BSY | DRQ, and BSY | DRQ | ERR. -/
def tfdBusy : UInt32 := 0x88
def tfdBad : UInt32 := 0x89

/-! ## Scratch layout (the executor zeroes scratch at start)

Everything the controller reads or writes lies in the first scratch page. -/

def cmdList : UInt32 := 0x000      -- 32 headers × 32 bytes, 1 KiB aligned
def rfis : UInt32 := 0x400         -- received FIS area, 256 bytes
def cmdTable : UInt32 := 0x500     -- CFIS at +0, PRDT at +0x80; 128-byte aligned
def prdt : UInt32 := cmdTable + 0x80
/-- PRDT entries that fit between the command table's PRDT and the sector. -/
def prdSlots : UInt32 := 40
def sector : UInt32 := 0x800       -- 512-byte data buffer
def sectorBytes : UInt32 := 512

/-- The pointer fields the controller follows inside scratch: the
command-table base (CTBA, CTBAU) of every one of the 32 command headers, and
the data base (DBA, DBAU) of every PRD that fits in the command table's PRDT
before the data buffer. That this lists every scratch pointer the
controller dereferences for the commands this program issues (one header,
PRDTL 1) is an assumption about the AHCI specification (§4.2.2, §4.2.3). -/
def descriptorMap : List Descriptor :=
  [{ trb := false, start := cmdList + 8, count := 32, stride := 32 },
   { trb := false, start := prdt, count := prdSlots, stride := 16 }]

namespace Tag
/-- The sector at the reported LBA has been read and the controller is
quiescent (engines stopped, Bus Master cleared). -/
def read : UInt32 := 0x3301
end Tag

namespace Fail
def wrongDevice : UInt32 := 0x7D11
def noDma : UInt32 := 0x7D12
def noPort : UInt32 := 0x7D13
def crStuck : UInt32 := 0x7D14
def frStuck : UInt32 := 0x7D15
def busy : UInt32 := 0x7D16
def taskFile : UInt32 := 0x7D17
def timeout : UInt32 := 0x7D18
def noDevice : UInt32 := 0x7D19
def status : UInt32 := 0x7D1A
end Fail

/-- `scratch[at] := src` (width `w`), through r9. -/
def st (w : Nat) (at_ : UInt32) (src : Operand) : ProgM Unit := do
  li 9 0
  emit (.memStore w 9 at_ src)

/-- Stop port `n`'s command engine, then its FIS-receive engine (AHCI 10.1.2). -/
def stopPort (n : UInt32) : ProgM Unit := do
  maskSet32 (pxCmd n) (~~~cmdSt) 0
  poll32 (pxCmd n) cmdCr 0 500 1000 Fail.crStuck
  maskSet32 (pxCmd n) (~~~cmdFre) 0
  poll32 (pxCmd n) cmdFr 0 500 1000 Fail.frStuck

/-- Wait until command slot 0 of port `n` completes; a task-file error or a
timeout fails the program. Uses r13 and r14. -/
def waitSlot0 (n : UInt32) : ProgM Unit := do
  let top ← newLabel
  let done ← newLabel
  let tfe ← newLabel
  li 14 1000
  place top
  r32 13 (pxIs n)
  andi 13 isTfes
  emit (.branch .ne 13 (.imm 0) tfe)
  r32 13 (pxCi n)
  andi 13 1
  emit (.branch .eq 13 (.imm 0) done)
  delay 1000
  emit (.alu .sub 14 (.imm 1))
  emit (.branch .ne 14 (.imm 0) top)
  fail Fail.timeout
  place tfe
  fail Fail.taskFile
  place done

def program : ProgM Unit := do
  setTarget target
  emit (.cfgRead32 0 0)
  expectEq 0 target.id Fail.wrongDevice
  emit (.physAddr 0 0)
  let dmaOk ← newLabel
  emit (.branch .ne 0 (.imm 0) dmaOk)
  fail Fail.noDma
  place dmaOk
  r32 0 pi
  andi 0 0x3
  expectEq 0 0x3 Fail.noPort
  -- GHC.AE (bit 31); HR reads 0 and IE is preserved.
  maskSet32 ghc 0xFFFFFFFF 0x80000000
  -- Firmware may have left either port running on its own memory.
  stopPort 0
  stopPort dataPort
  r32 0 (pxSsts dataPort)
  andi 0 0xF
  expectEq 0 0x3 Fail.noDevice             -- DET = device present, PHY up
  -- Only now may the controller master the bus; zeros to the RW1C status half.
  emit (.cfgUpdate32 0x04 0xFFFF0000 0x0006)
  -- Point the port at scratch (address sinks: low dword in scratch, high 0).
  emit (.physAddr 0 cmdList)
  emit (.write32 (pxClb dataPort) (.reg 0))
  w32 (pxClbu dataPort) 0
  emit (.physAddr 0 rfis)
  emit (.write32 (pxFb dataPort) (.reg 0))
  w32 (pxFbu dataPort) 0
  w32 (pxSerr dataPort) 0xFFFFFFFF
  w32 (pxIs dataPort) 0xFFFFFFFF
  maskSet32 (pxCmd dataPort) 0xFFFFFFFF cmdFre
  poll32 (pxTfd dataPort) tfdBusy 0 1000 1000 Fail.busy
  maskSet32 (pxCmd dataPort) 0xFFFFFFFF cmdSt
  -- Command header 0: CFL 5 dwords, read (W = 0), PRDTL 1; CTBA = command table.
  st 4 cmdList (.imm (((1 : UInt32) <<< 16) ||| 5))
  st 4 (cmdList + 4) (.imm 0)
  emit (.physAddr 0 cmdTable)
  st 4 (cmdList + 8) (.reg 0)
  st 4 (cmdList + 12) (.imm 0)
  -- Register H2D FIS: type 0x27, C = 1, READ DMA EXT (0x25), LBA mode,
  -- 48-bit LBA `readLba`, count 1.
  st 4 cmdTable (.imm 0x00258027)
  st 4 (cmdTable + 4) (.imm ((readLba &&& 0xFFFFFF) ||| 0x40000000))
  st 4 (cmdTable + 8) (.imm (readLba >>> 24))
  st 4 (cmdTable + 12) (.imm 1)
  -- PRD 0: one sector into the data buffer (DBC is byte count - 1).
  emit (.physAddr 0 sector)
  st 4 prdt (.reg 0)
  st 4 (prdt + 4) (.imm 0)
  st 4 (prdt + 8) (.imm 0)
  st 4 (prdt + 12) (.imm (sectorBytes - 1))
  w32 (pxCi dataPort) 1
  waitSlot0 dataPort
  r32 0 (pxTfd dataPort)
  andi 0 tfdBad
  expectEq 0 0 Fail.status
  -- Quiesce: stop the engines and leave the controller unable to master the bus.
  stopPort dataPort
  w32 (pxIs dataPort) 0xFFFFFFFF
  emit (.cfgUpdate32 0x04 0xFFFF0004 0x0002)
  printImm Tag.read readLba
  -- Hand the sector to the invoking subject, one dword per yield.
  li 1 0
  let next ← newLabel
  place next
  emit (.memLoad 4 2 1 sector)
  emit (.yield (.reg 2))
  addi 1 4
  emit (.branch .ltu 1 (.imm sectorBytes) next)
  halt

end LeanOS.Storage.AhciRead
