import LeanOS.Wifi.NPhy

/-
BCM43224 D11 MAC-side initialisation and receive, as Lean device programs.

Sequences follow brcmsmac (ISC; Copyright (c) 2010 Broadcom Corporation)
`main.c`: the tail of `brcms_b_coreinit`, `brcms_b_bsinit` with
`brcms_c_ucode_bsinit`, and `brcms_c_enable_mac`. DMA engines are not
started; frames are drained through the receive FIFO's programmed-I/O
registers (`struct pio4regs` in the `fifo64` block of `d11.h`).
-/
namespace LeanOS.Wifi.Mac

open LeanOS.Wifi.Bytecode LeanOS.Wifi.Bcm43224 LeanOS.Wifi.NPhy

/-! ## Registers and shared-memory offsets (d11.h) -/

def d11MacHwCap : UInt32 := 0x15C
def d11IntRcvLazy0 : UInt32 := 0x100
def d11TsfCfpRep : UInt32 := 0x188
def d11TsfCfpStart : UInt32 := 0x18C
def d11IfsCtl : UInt32 := 0x688
def d11IfsAifsn : UInt32 := 0x69C
def d11FastPwrupDly : UInt32 := 0x6A8
/-- fifo64[0]: dmaxmt +0x00, piotx +0x18, dmarcv +0x20, piorx +0x38. -/
def rxPioCtl : UInt32 := 0x200 + 0x38
def rxPioData : UInt32 := 0x200 + 0x3C
def rxDmaCtl : UInt32 := 0x200 + 0x20

def mShmHostFlags : Array UInt32 := #[0x02f * 2, 0x030 * 2, 0x031 * 2, 0x03c * 2, 0x06a * 2]
def mMacHwVer : UInt32 := 0x00b * 2
def mMacHwCapL : UInt32 := 0x060 * 2
def mMacHwCapH : UInt32 := 0x061 * 2
def mPhyVer : UInt32 := 0x028 * 2
def mPhyType : UInt32 := 0x029 * 2
def mSynthPuDly : UInt32 := 0x04a * 2

def mctlDiscardPmq : UInt32 := 0x40000000
def mctlPromisc : UInt32 := 0x01000000
def mctlKeepControl : UInt32 := 0x00400000
def mctlBcnsPromisc : UInt32 := 0x00100000
def mctlAp : UInt32 := 0x00040000
def miGp1 : UInt32 := 0x00004000
def sicfMpClkE : UInt32 := 0x0010

namespace Tag
def macHwCap : UInt32 := 0x0700
def macEnabled : UInt32 := 0x0701
def rxCtl : UInt32 := 0x0710
def rxWord : UInt32 := 0x0711
def rxFrame : UInt32 := 0x0712
def rxNone : UInt32 := 0x0713
def rxTimeout : UInt32 := 0x0714
def rxSummary : UInt32 := 0x0715
end Tag

/-- brcms_b_mctrl: `maccontrol := (maccontrol & ~mask) | val`. -/
def mctrl (mask val : UInt32) : ProgM Unit :=
  maskSet32 d11MacCtl (~~~mask) (val &&& mask)

/-- `shm16[off] := r` for a run-time value. -/
def shmWrite16R (off : UInt32) (r : Reg) : ProgM Unit := do
  w32 d11ObjAddr (objShm ||| (off >>> 2))
  r32 12 d11ObjAddr
  emit (.write16 (if off &&& 2 == 0 then d11ObjData else d11ObjData + 2) (.reg r))

/-- Tail of brcms_b_coreinit after the init values (no DMA engines). -/
def coreInitTail : ProgM Unit := do
  -- one receive interrupt per frame
  w32 d11IntRcvLazy0 ((1 : UInt32) <<< 24)
  -- BSS station mode
  mctrl (mctlInfra ||| mctlDiscardPmq ||| mctlAp) (mctlInfra ||| mctlDiscardPmq)
  -- beacon interval placeholder until associated
  let bcnintUs : UInt32 := (0x8000 : UInt32) <<< 10
  w32 d11TsfCfpRep (bcnintUs <<< 6)
  w32 d11TsfCfpStart bcnintUs
  w32 d11MacIntStatus miGp1
  -- allow the MAC to control the PHY clock
  maskSet32 wrapIoCtl 0xFFFFFFFF sicfMpClkE
  -- PMU fast power-up delay (si_pmu_fast_pwrup_delay: 3700 for 43224)
  w16 d11FastPwrupDly 3700
  shmWrite16 mMacHwVer 23
  r32 0 d11MacHwCap
  print Tag.macHwCap 0
  mov 1 0
  andi 1 0xFFFF
  shmWrite16R mMacHwCapL 1
  shri 0 16
  shmWrite16R mMacHwCapH 0
  maskSet16 d11IfsCtl 0x0FFF 0
  w16 d11IfsAifsn 1

/-- brcms_c_ucode_bsinit (host flags then band-specific init values), the
PHY initialisation supplied by the caller, then the rest of brcms_b_bsinit
that matters for reception (PHY type/version and synth power-up delay). -/
def bandInit (fw : Firmware) (phyInit : ProgM Unit) : ProgM Unit := do
  -- brcms_c_mhfdef: all host flags zero for this board (no BFL_NOPLLDOWN,
  -- N-PHY rev >= 2); later workarounds set MHF4 bits in shared memory.
  for off in mShmHostFlags do shmWrite16 off 0
  writeInits fw.bsinitvals
  phyInit
  shmWrite16 mPhyType 4
  shmWrite16 mPhyVer 6
  shmWrite16 mSynthPuDly 2048

/-- brcms_c_enable_mac with promiscuous reception of all frames including
beacons from any BSS (scan mode). -/
def enableMacPromisc : ProgM Unit := do
  mctrl (mctlPromisc ||| mctlBcnsPromisc) (mctlPromisc ||| mctlBcnsPromisc)
  mctrl mctlEnMac mctlEnMac
  w32 d11MacIntStatus miMacSuspended
  r32 0 d11MacCtl
  print Tag.macEnabled 0

/-- Drain up to `frames` received frames from the RX FIFO by programmed I/O,
printing each frame's first `words` 32-bit words (receive header included).
Polls for up to `tries` × 1 ms per frame.

PIO register semantics (hardware facts for 4-byte PIO FIFOs): control bit 0
signals a frame ready and is written back to claim it; bit 1 signals data
ready; data is read as 32-bit words starting with the 12-halfword receive
header whose first halfword is the frame length. -/
def rxDump (frames words tries : UInt32) : ProgM Unit := do
  li 5 0                                  -- frames seen
  let next ← newLabel
  let done ← newLabel
  place next
  emit (.branch .geu 5 (.imm frames) done)
  -- wait for a frame
  let got ← newLabel
  li 6 tries
  let wait ← newLabel
  place wait
  r32 0 rxPioCtl
  mov 1 0
  andi 1 1
  emit (.branch .ne 1 (.imm 0) got)
  delay 1000
  emit (.alu .sub 6 (.imm 1))
  emit (.branch .ne 6 (.imm 0) wait)
  print Tag.rxTimeout 0
  emit (.jump done)
  place got
  print Tag.rxCtl 0
  w32 rxPioCtl 1
  -- wait for data ready (bounded)
  li 6 100
  let dr ← newLabel
  let drOk ← newLabel
  place dr
  r32 0 rxPioCtl
  mov 1 0
  andi 1 2
  emit (.branch .ne 1 (.imm 0) drOk)
  delay 10
  emit (.alu .sub 6 (.imm 1))
  emit (.branch .ne 6 (.imm 0) dr)
  print Tag.rxTimeout 1
  emit (.jump done)
  place drOk
  -- first word carries the frame length in its low half
  r32 2 rxPioData
  print Tag.rxWord 2
  mov 3 2
  andi 3 0xFFFF
  print Tag.rxFrame 3
  -- total words = ceil((24 header bytes + len) / 4); one already read
  addi 3 (24 + 3)
  shri 3 2
  li 4 1
  let rd ← newLabel
  let rdDone ← newLabel
  place rd
  emit (.branch .geu 4 (.reg 3) rdDone)
  r32 2 rxPioData
  let skip ← newLabel
  emit (.branch .geu 4 (.imm words) skip)
  print Tag.rxWord 2
  place skip
  addi 4 1
  emit (.branch .ltu 4 (.imm 1200) rd)
  place rdDone
  w32 rxPioCtl 2
  addi 5 1
  emit (.jump next)
  place done
  print Tag.rxSummary 5

end LeanOS.Wifi.Mac
