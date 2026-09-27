import LeanOS.Wifi.Bytecode

/-
Broadcom BCM43224 (PCI 14e4:4353, BCMA bus, D11 core rev 23, N-PHY rev 6,
radio 2056) driver programs, authored against the instruction set in
`LeanOS.Wifi.Bytecode`.

Register facts come from the Linux `bcma`, `b43` and `brcmsmac` drivers and
from read-only observation of the Qotom's card under FreeBSD (2026-09-26):
ChipCommon chip id word `0x1381a8d8`, capabilities `0x58500000`, EROM at
`0x18107000`, D11 core at `0x18001000` with wrapper `0x18101000`.
-/
namespace LeanOS.Wifi.Bcm43224

open LeanOS.Wifi.Bytecode

/-! ## Host-bridge window (PCIe gen1 BCMA host) -/

/-- PCI config: backplane address shown in BAR0[0x0000, 0x1000). -/
def cfgBar0Win : UInt32 := 0x80
/-- PCI config: backplane address shown in BAR0[0x1000, 0x2000) (wrapper). -/
def cfgBar0Win2 : UInt32 := 0xAC
/-- BAR0 offset of the fixed PCIe core and ChipCommon windows. -/
def pcieWin : UInt32 := 0x2000
def ccWin : UInt32 := 0x3000
def wrapWin : UInt32 := 0x1000

def d11Core : UInt32 := 0x18001000
def d11Wrap : UInt32 := 0x18101000
def eromBase : UInt32 := 0x18107000

/-! ## ChipCommon -/

def ccChipId : UInt32 := ccWin + 0x000
def ccCaps : UInt32 := ccWin + 0x004
def ccOtpStatus : UInt32 := ccWin + 0x010
def ccChipCtl : UInt32 := ccWin + 0x028
def ccChipStat : UInt32 := ccWin + 0x02C
def ccEromPtr : UInt32 := ccWin + 0x0FC
def ccClkCtlSt : UInt32 := ccWin + 0x1E0
def ccPmuCtl : UInt32 := ccWin + 0x600
def ccPmuCaps : UInt32 := ccWin + 0x604
def ccPmuStat : UInt32 := ccWin + 0x608
def ccPmuResState : UInt32 := ccWin + 0x60C
def ccPmuMinRes : UInt32 := ccWin + 0x618
def ccPmuMaxRes : UInt32 := ccWin + 0x61C
def ccSprom : UInt32 := ccWin + 0x800

/-! ## BCMA agent (wrapper) registers, via the second window -/

def wrapIoCtl : UInt32 := wrapWin + 0x408
def wrapIoSt : UInt32 := wrapWin + 0x500
def wrapResetCtl : UInt32 := wrapWin + 0x800
def wrapResetSt : UInt32 := wrapWin + 0x804

-- Print tags (shown as `WIFI <tag> <value>`).
namespace Tag
def pciId : UInt32 := 0x0100
def pciCmd : UInt32 := 0x0104
def chipId : UInt32 := 0x0110
def chipCaps : UInt32 := 0x0111
def erom : UInt32 := 0x0112
def otpStatus : UInt32 := 0x0113
def pmuCaps : UInt32 := 0x0114
def pmuStat : UInt32 := 0x0115
def pmuRes : UInt32 := 0x0116
def clkCtlSt : UInt32 := 0x0117
def eromEntry : UInt32 := 0x0120
def d11IoCtl : UInt32 := 0x0130
def d11ResetCtl : UInt32 := 0x0131
def d11IoSt : UInt32 := 0x0132
def spromRev : UInt32 := 0x0140
def mac01 : UInt32 := 0x0141
def mac23 : UInt32 := 0x0142
def mac45 : UInt32 := 0x0143
def boardRev : UInt32 := 0x0144
def boardFlags : UInt32 := 0x0145
def done : UInt32 := 0x01FF
end Tag

-- Fail codes (typed rejection reasons).
namespace Fail
def wrongDevice : UInt32 := 0x10
def wrongChip : UInt32 := 0x11
def eromRunaway : UInt32 := 0x12
def noSprom : UInt32 := 0x13
end Fail

/-- Select the D11 core and its wrapper in the two BAR0 windows. -/
def selectD11 : ProgM Unit := do
  emit (.cfgWrite32 cfgBar0Win (.imm d11Core))
  emit (.cfgWrite32 cfgBar0Win2 (.imm d11Wrap))

/-- Identity checks shared by every program: the exact PCI function and the
43224 chip id. Also ensures memory decoding is enabled. -/
def identify : ProgM Unit := do
  emit (.cfgRead32 0 0)
  print Tag.pciId 0
  expectEq 0 0x435314e4 Fail.wrongDevice
  emit (.cfgRead32 0 0x04)
  print Tag.pciCmd 0
  r32 0 ccChipId
  print Tag.chipId 0
  andi 0 0xFFFF
  expectEq 0 0xA8D8 Fail.wrongChip

/-- Walk the enumeration ROM through window 1, printing every entry up to the
end tag (bounded to 128 entries). Restores the D11 window afterwards. -/
def walkErom : ProgM Unit := do
  emit (.cfgWrite32 cfgBar0Win (.imm eromBase))
  li 1 0            -- byte offset inside the EROM page
  let top ← newLabel
  let done ← newLabel
  place top
  emit (.read32At 0 1 0)
  print Tag.eromEntry 0
  mov 2 0
  andi 2 0xF
  emit (.branch .eq 2 (.imm 0xF) done)    -- valid end tag
  addi 1 4
  emit (.branch .ltu 1 (.imm 512) top)
  fail Fail.eromRunaway
  place done
  selectD11

/-- Read-only probe: identity, ChipCommon/PMU state, EROM, D11 agent state and
the SPROM identity words (MAC address, board revision, SPROM revision). -/
def probe : ProgM Unit := do
  identify
  r32 0 ccCaps; print Tag.chipCaps 0
  r32 0 ccEromPtr; print Tag.erom 0
  r32 0 ccOtpStatus; print Tag.otpStatus 0
  r32 0 ccPmuCaps; print Tag.pmuCaps 0
  r32 0 ccPmuStat; print Tag.pmuStat 0
  r32 0 ccPmuResState; print Tag.pmuRes 0
  r32 0 ccClkCtlSt; print Tag.clkCtlSt 0
  walkErom
  r32 0 wrapIoCtl; print Tag.d11IoCtl 0
  r32 0 wrapResetCtl; print Tag.d11ResetCtl 0
  r32 0 wrapIoSt; print Tag.d11IoSt 0
  -- SPROM revision 8 layout (440 bytes): revision in the low byte of the
  -- last word, IL0 MAC at byte 0x8C, board revision 0x82, board flags 0x84.
  r16 0 (ccSprom + 438); print Tag.spromRev 0
  r16 0 (ccSprom + 0x8C); print Tag.mac01 0
  r16 0 (ccSprom + 0x8E); print Tag.mac23 0
  r16 0 (ccSprom + 0x90); print Tag.mac45 0
  r16 0 (ccSprom + 0x82); print Tag.boardRev 0
  r32 0 (ccSprom + 0x84); print Tag.boardFlags 0
  printImm Tag.done 0
  halt

end LeanOS.Wifi.Bcm43224

namespace LeanOS.Wifi.Bcm43224

open LeanOS.Wifi.Bytecode

/-! ## D11 core registers (window 1) -/

def d11MacCtl : UInt32 := 0x120
def d11MacIntStatus : UInt32 := 0x128
def d11MacIntMask : UInt32 := 0x12C
def d11ObjAddr : UInt32 := 0x160
def d11ObjData : UInt32 := 0x164
def d11ClkCtlSt : UInt32 := 0x1E0
def d11PhyVersion : UInt32 := 0x3E0
def d11RadioCtl : UInt32 := 0x3F6
def d11RadioDataHigh : UInt32 := 0x3F8
def d11RadioDataLow : UInt32 := 0x3FA
def d11PhyCtl : UInt32 := 0x3FC
def d11PhyData : UInt32 := 0x3FE

def mctlGMode : UInt32 := 0x80000000
def mctlWake : UInt32 := 0x04000000
def mctlInfra : UInt32 := 0x00020000
def mctlIhrEn : UInt32 := 0x00000400
def mctlPsmJmp0 : UInt32 := 0x00000004
def mctlPsmRun : UInt32 := 0x00000002
def mctlEnMac : UInt32 := 0x00000001
def miMacSuspended : UInt32 := 0x00000001

def objUcm : UInt32 := 0x00000000
def objShm : UInt32 := 0x00010000
def objAutoInc : UInt32 := 0x03000000

/-! ## BCMA agent flags for the 802.11 core -/

def ioctlClk : UInt32 := 0x1
def ioctlFgc : UInt32 := 0x2
def ioctlPhyClkEn : UInt32 := 0x4
def ioctlPhyReset : UInt32 := 0x8
def ioctlPhyBw20 : UInt32 := 0x40
def ioctlGMode : UInt32 := 0x2000

namespace Tag
def phyVersion : UInt32 := 0x0200
def radioId : UInt32 := 0x0201
def resetDone : UInt32 := 0x0202
def ucodeLoaded : UInt32 := 0x0210
def macIntStatus : UInt32 := 0x0211
def ucodeRev : UInt32 := 0x0212
def ucodePatch : UInt32 := 0x0213
def ucodeDate : UInt32 := 0x0214
def ucodeTime : UInt32 := 0x0215
def fifoSize0 : UInt32 := 0x0216
def initvals : UInt32 := 0x0217
def macCtl : UInt32 := 0x0218
def machwVer : UInt32 := 0x0219
end Tag

namespace Fail
def htTimeout : UInt32 := 0x20
def pllTimeout : UInt32 := 0x21
def resetStBusy : UInt32 := 0x22
def notNPhy : UInt32 := 0x23
def ucodeNoSuspend : UInt32 := 0x24
def badInitvals : UInt32 := 0x25
end Fail

/-- bcma_core_enable(d11, PHY_CLKEN | GMODE) followed by the b43 fast clock
request, PHY reset pulse and 802.11/PHY PLL request (2.4 GHz, 20 MHz). -/
def d11CoreReset : ProgM Unit := do
  let flags := ioctlPhyClkEn ||| ioctlGMode
  -- bcma_core_disable (skipped when the core is already held in reset).
  r32 0 wrapResetCtl
  andi 0 1
  ifEq 0 0 do
    poll32 wrapResetSt 0xFFFFFFFF 0 300 1 Fail.resetStBusy
    w32 wrapResetCtl 1
    r32 0 wrapResetCtl
    delay 1
    w32 wrapIoCtl flags
    r32 0 wrapIoCtl
    delay 10
  w32 wrapIoCtl (ioctlClk ||| ioctlFgc ||| flags)
  r32 0 wrapIoCtl
  w32 wrapResetCtl 0
  r32 0 wrapResetCtl
  delay 1
  w32 wrapIoCtl (ioctlClk ||| flags)
  r32 0 wrapIoCtl
  delay 1
  -- bcma_core_set_clockmode(FAST): force HT and wait for HAVEHT.
  maskSet32 d11ClkCtlSt 0xFFFFFFFF 0x2
  delay 100
  poll32 d11ClkCtlSt 0x00020000 0x00020000 1500 10 Fail.htTimeout
  -- b43_bcma_phy_reset: pulse PHY reset at 20 MHz, then release with FGC.
  maskSet32 wrapIoCtl 0xFFFFFFFF (ioctlPhyReset ||| ioctlPhyBw20)
  delay 2
  maskSet32 wrapIoCtl (~~~(ioctlPhyReset ||| ioctlPhyClkEn)) ioctlFgc
  delay 1
  maskSet32 wrapIoCtl (~~~ioctlFgc) ioctlPhyClkEn
  delay 1
  -- bcma_core_pll_ctl(80211_PLL_REQ | PHY_PLL_REQ).
  maskSet32 d11ClkCtlSt 0xFFFFFFFF 0x300
  poll32 d11ClkCtlSt 0x03000000 0x03000000 10000 10 Fail.pllTimeout
  printImm Tag.resetDone 0

/-- `dst := shm16[off]` (byte offset, 2-aligned). -/
def shmRead16 (dst : Reg) (off : UInt32) : ProgM Unit := do
  w32 d11ObjAddr (objShm ||| (off >>> 2))
  r32 dst d11ObjAddr
  if off &&& 2 == 0 then r16 dst d11ObjData else r16 dst (d11ObjData + 2)

def shmWrite16 (off v : UInt32) : ProgM Unit := do
  w32 d11ObjAddr (objShm ||| (off >>> 2))
  r32 12 d11ObjAddr
  if off &&& 2 == 0 then w16 d11ObjData v else w16 (d11ObjData + 2) v

/-- PHY identity: N-PHY (type 4). Radio id via the core-rev < 24 interface. -/
def identifyPhy : ProgM Unit := do
  r16 0 d11PhyVersion
  print Tag.phyVersion 0
  mov 1 0
  shri 1 8
  andi 1 0xF
  expectEq 1 4 Fail.notNPhy
  -- read_radio_id (D11 rev < 24): the id register is latched per access.
  w16 d11RadioCtl 0x01
  r16 0 d11RadioDataLow
  w16 d11RadioCtl 0x01
  r16 1 d11RadioDataHigh
  shli 1 16
  emit (.alu .or 0 (.reg 1))
  print Tag.radioId 0

/-- The brcmsmac firmware container, split by the host generator. -/
structure Firmware where
  ucode : ByteArray        -- d11ucode16_mimo, little-endian 32-bit words
  initvals : ByteArray     -- d11n0initvals16: {le16 addr, le16 size, le32 value}*
  bsinitvals : ByteArray   -- d11n0bsinitvals16

def le16 (b : ByteArray) (i : Nat) : UInt32 :=
  (b.get! i).toUInt32 ||| ((b.get! (i + 1)).toUInt32 <<< 8)
def le32 (b : ByteArray) (i : Nat) : UInt32 :=
  le16 b i ||| (le16 b (i + 2) <<< 16)

/-- Expand a d11init table into register writes (brcms_c_write_inits). The
table must end with address 0xffff and contain only 2- and 4-byte writes. -/
def writeInits (t : ByteArray) : ProgM Unit := do
  let n := t.size / 8
  let mut ended := false
  for k in [0:n] do
    if !ended then
      let addr := le16 t (8 * k)
      let size := le16 t (8 * k + 2)
      let value := le32 t (8 * k + 4)
      if addr == 0xFFFF then ended := true
      else if size == 2 then w16 addr (value &&& 0xFFFF)
      else if size == 4 then w32 addr value
      else fail Fail.badInitvals
  if !ended then fail Fail.badInitvals

/-- Upload the MIMO microcode, let the PSM run to its self-suspended state,
then apply the N-PHY init values (brcms_b_coreinit, first half). The D11
core must already be out of reset. -/
def ucodeStart (fw : Firmware) : ProgM Unit := do
  let ucodeOff ← addBlob "d11ucode16_mimo" fw.ucode
  -- Reset the PSM with the host interface enabled.
  w32 d11MacCtl (mctlIhrEn ||| mctlPsmJmp0 ||| mctlWake)
  -- Upload microcode words through the auto-incrementing object window.
  w32 d11ObjAddr (objAutoInc ||| objUcm)
  r32 0 d11ObjAddr
  emit (.blobStream32 d11ObjData ucodeOff (fw.ucode.size / 4).toUInt32)
  printImm Tag.ucodeLoaded (fw.ucode.size / 4).toUInt32
  -- Run the PSM (infrastructure STA mode) and wait for self-suspend.
  w32 d11MacIntStatus 0xFFFFFFFF
  w32 d11MacCtl (mctlIhrEn ||| mctlInfra ||| mctlPsmRun ||| mctlWake)
  poll32 d11MacIntStatus miMacSuspended miMacSuspended 100000 10 Fail.ucodeNoSuspend
  r32 0 d11MacIntStatus
  print Tag.macIntStatus 0
  writeInits fw.initvals
  printImm Tag.initvals (fw.initvals.size / 8).toUInt32
  shmRead16 0 0x0000; print Tag.ucodeRev 0
  shmRead16 0 0x0002; print Tag.ucodePatch 0

/-- Identification, core reset, microcode boot, then a report. -/
def ucodeBoot (fw : Firmware) : ProgM Unit := do
  identify
  selectD11
  d11CoreReset
  identifyPhy
  ucodeStart fw
  shmRead16 0 0x0004; print Tag.ucodeDate 0
  shmRead16 0 0x0006; print Tag.ucodeTime 0
  shmRead16 0 (0x4c * 2); print Tag.fifoSize0 0
  r32 0 d11MacCtl; print Tag.macCtl 0
  printImm Tag.done 0
  halt

end LeanOS.Wifi.Bcm43224

namespace LeanOS.Wifi.Bcm43224
open LeanOS.Wifi.Bytecode

/-- Read-only dump of all 220 SPROM words (tag 0x03nn = word nn) and the
radio identity. Requires the D11 core to be out of reset. -/
def spromDump : ProgM Unit := do
  identify
  selectD11
  r32 0 wrapResetCtl
  expectEq 0 0 0x30
  identifyPhy
  for k in [0:220] do
    r16 0 (ccSprom + (2 * k).toUInt32)
    print (0x0300 + k.toUInt32) 0
  printImm Tag.done 0
  halt

end LeanOS.Wifi.Bcm43224
