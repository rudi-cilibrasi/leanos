import LeanOS.Wifi.Bytecode

/-
AHCI IDENTIFY DEVICE as a Lean device program (issue #452).

Written from the Serial ATA AHCI 1.3.1 specification and ATA8-ACS for the
Qotom's Intel Bay Trail SATA controller (PCI 8086:0f23 at 00:13.0; ABAR at
configuration offset 0x24, 2 KiB; CAP c720ff01: 64-bit, 32 command slots;
PI 2: only port 1 is implemented, and it holds the FreeBSD SSD — see
`docs/qotom-ahci-observation.md`).

The program is read-only towards the disk: it stops port 1's command and
FIS-receive engines if firmware left them running, points the port's command
list and received-FIS area at executor scratch, issues one IDENTIFY DEVICE
through command slot 0 with a single 512-byte PRD, and prints the identify
words that name the drive (serial, firmware, model, capacity). It then stops
the engines again and clears Bus Master. PxCLB and PxFB are address sinks of
its policy; the command-table and PRD pointers live in scratch (ADR 0021).
-/
namespace LeanOS.Storage.Ahci

open LeanOS.Wifi.Bytecode

def target : Target :=
  { bus := 0, dev := 19, fn := 0, id := 0x0f238086, windowBytes := 0x800, bar := 0x24 }

/-! ## Registers (ABAR offsets) -/

def cap : UInt32 := 0x00
def ghc : UInt32 := 0x04
def pi : UInt32 := 0x0C
def vs : UInt32 := 0x10
def port1 (o : UInt32) : UInt32 := 0x180 + o
def pClb : UInt32 := port1 0x00
def pClbu : UInt32 := port1 0x04
def pFb : UInt32 := port1 0x08
def pFbu : UInt32 := port1 0x0C
def pIs : UInt32 := port1 0x10
def pCmd : UInt32 := port1 0x18
def pTfd : UInt32 := port1 0x20
def pSig : UInt32 := port1 0x24
def pSsts : UInt32 := port1 0x28
def pSerr : UInt32 := port1 0x30
def pCi : UInt32 := port1 0x38

/-- PxCMD bits. -/
def cmdSt : UInt32 := 0x1
def cmdFre : UInt32 := 0x10
def cmdFr : UInt32 := 0x4000
def cmdCr : UInt32 := 0x8000
/-- PxIS.TFES: task-file error. -/
def isTfes : UInt32 := 0x40000000
/-- PxTFD.STS BSY | DRQ. -/
def tfdBusy : UInt32 := 0x88

/-! ## Scratch layout (the executor zeroes scratch at start) -/

def cmdList : UInt32 := 0x0000     -- 32 headers × 32 bytes, 1 KiB aligned
def rfis : UInt32 := 0x0400        -- received FIS area, 256 bytes
def cmdTable : UInt32 := 0x0800    -- CFIS at +0, PRDT at +0x80; 128-byte aligned
def idBuf : UInt32 := 0x1000       -- 512-byte IDENTIFY data

namespace Tag
def pciId : UInt32 := 0x3100
def cap : UInt32 := 0x3101
def ghc : UInt32 := 0x3102
def pi : UInt32 := 0x3103
def vs : UInt32 := 0x3104
def cmdBefore : UInt32 := 0x3105
def ssts : UInt32 := 0x3106
def sig : UInt32 := 0x3107
def tfd : UInt32 := 0x3108
def is : UInt32 := 0x3109
/-- IDENTIFY dwords: serial (words 10–19), firmware (23–26), model (27–46),
LBA48 sector count (100–103); tag low byte = first word index. -/
def identify : UInt32 := 0x3200
def done : UInt32 := 0x31FF
end Tag

namespace Fail
def wrongDevice : UInt32 := 0x7D01
def noDma : UInt32 := 0x7D02
def noPort : UInt32 := 0x7D03
def crStuck : UInt32 := 0x7D04
def frStuck : UInt32 := 0x7D05
def busy : UInt32 := 0x7D06
def taskFile : UInt32 := 0x7D07
def timeout : UInt32 := 0x7D08
def noDevice : UInt32 := 0x7D09
end Fail

/-- `scratch[at] := src` (width `w`), through r9. -/
def st (w : Nat) (at_ : UInt32) (src : Operand) : ProgM Unit := do
  li 9 0
  emit (.memStore w 9 at_ src)

/-- Stop the command engine, then the FIS-receive engine (AHCI 10.1.2). -/
def stopPort : ProgM Unit := do
  maskSet32 pCmd (~~~cmdSt) 0
  poll32 pCmd cmdCr 0 500 1000 Fail.crStuck
  maskSet32 pCmd (~~~cmdFre) 0
  poll32 pCmd cmdFr 0 500 1000 Fail.frStuck

def program : ProgM Unit := do
  setTarget target
  emit (.cfgRead32 0 0)
  print Tag.pciId 0
  expectEq 0 0x0f238086 Fail.wrongDevice
  emit (.physAddr 0 0)
  let dmaOk ← newLabel
  emit (.branch .ne 0 (.imm 0) dmaOk)
  fail Fail.noDma
  place dmaOk
  -- Memory Space + Bus Master; zeros to the RW1C status half.
  emit (.cfgUpdate32 0x04 0xFFFF0000 0x0006)
  r32 0 cap; print Tag.cap 0
  r32 0 ghc; print Tag.ghc 0
  r32 0 vs; print Tag.vs 0
  r32 0 pi; print Tag.pi 0
  andi 0 0x2
  expectEq 0 0x2 Fail.noPort
  -- GHC.AE (bit 31); HR reads 0 and IE is preserved.
  maskSet32 ghc 0xFFFFFFFF 0x80000000
  r32 0 pSsts; print Tag.ssts 0
  andi 0 0xF
  expectEq 0 0x3 Fail.noDevice             -- DET = device present, PHY up
  r32 0 pCmd; print Tag.cmdBefore 0
  stopPort
  -- Point the port at scratch (address sinks: low dword in scratch, high 0).
  emit (.physAddr 0 cmdList)
  emit (.write32 pClb (.reg 0))
  w32 pClbu 0
  emit (.physAddr 0 rfis)
  emit (.write32 pFb (.reg 0))
  w32 pFbu 0
  w32 pSerr 0xFFFFFFFF
  w32 pIs 0xFFFFFFFF
  maskSet32 pCmd 0xFFFFFFFF cmdFre
  poll32 pTfd tfdBusy 0 1000 1000 Fail.busy
  maskSet32 pCmd 0xFFFFFFFF cmdSt
  -- Command header 0: CFL 5 dwords, read, PRDTL 1; CTBA = command table.
  st 4 cmdList (.imm (((1 : UInt32) <<< 16) ||| 5))
  st 4 (cmdList + 4) (.imm 0)
  emit (.physAddr 0 cmdTable)
  st 4 (cmdList + 8) (.reg 0)
  st 4 (cmdList + 12) (.imm 0)
  -- Register H2D FIS: type 0x27, C = 1, command IDENTIFY DEVICE (0xEC).
  st 1 cmdTable (.imm 0x27)
  st 1 (cmdTable + 1) (.imm 0x80)
  st 1 (cmdTable + 2) (.imm 0xEC)
  -- PRD 0: 512 bytes into the identify buffer (DBC is byte count - 1).
  emit (.physAddr 0 idBuf)
  st 4 (cmdTable + 0x80) (.reg 0)
  st 4 (cmdTable + 0x84) (.imm 0)
  st 4 (cmdTable + 0x88) (.imm 0)
  st 4 (cmdTable + 0x8C) (.imm 511)
  w32 pCi 1
  -- Wait for slot 0 to complete; a task-file error fails the program.
  let top ← newLabel
  let done ← newLabel
  let tfe ← newLabel
  li 14 1000
  place top
  r32 13 pIs
  andi 13 isTfes
  emit (.branch .ne 13 (.imm 0) tfe)
  r32 13 pCi
  andi 13 1
  emit (.branch .eq 13 (.imm 0) done)
  delay 1000
  emit (.alu .sub 14 (.imm 1))
  emit (.branch .ne 14 (.imm 0) top)
  r32 0 pTfd; print Tag.tfd 0
  fail Fail.timeout
  place tfe
  r32 0 pTfd; print Tag.tfd 0
  r32 0 pIs; print Tag.is 0
  fail Fail.taskFile
  place done
  r32 0 pTfd; print Tag.tfd 0
  r32 0 pSig; print Tag.sig 0
  -- Identify words as dwords: serial 10–19, firmware 23–26, model 27–46
  -- (27 starts an odd word: print from 26 so dwords stay aligned), capacity
  -- 100–103.
  for (first, count) in [(10, 5), (22, 13), (100, 2)] do
    for k in [0:count] do
      let word := first + 2 * k
      li 1 0
      emit (.memLoad 4 2 1 (idBuf + 2 * word.toUInt32))
      print (Tag.identify + word.toUInt32) 2
  stopPort
  w32 pIs 0xFFFFFFFF
  -- Leave the controller unable to master the bus.
  emit (.cfgUpdate32 0x04 0xFFFF0004 0x0002)
  printImm Tag.done 0
  halt

end LeanOS.Storage.Ahci
