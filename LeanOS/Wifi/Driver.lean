import LeanOS.Wifi.NPhyTables
import LeanOS.Wifi.Radio2056
import LeanOS.Wifi.NPhyWorkarounds
import LeanOS.Wifi.Mac

/-
Top-level BCM43224 driver programs, composed from the ported brcmsmac pieces.
-/
namespace LeanOS.Wifi.Driver

open LeanOS.Wifi.Bytecode LeanOS.Wifi.Bcm43224 LeanOS.Wifi.NPhy
open LeanOS.Wifi.NPhyTablesData LeanOS.Wifi.NPhyTables

/-- Identify the card, select the 802.11 core and bring it out of reset with
the PHY clocked (2.4 GHz, 20 MHz). -/
def bringUp : ProgM Unit := do
  identify
  selectD11
  d11CoreReset
  identifyPhy

/-- Table readback check: after `tblInit`, read selected elements of static
tables back through the PHY table window and require the ported values. -/
def tableCheck (cfg : PhyCfg) : ProgM Unit := do
  bringUp
  tblInit cfg
  let mut code : UInt32 := 0x7100
  for t in mimophytblInfoRev3 do
    let vals := hexU32s t.data
    for k in [0, 1, vals.size / 2, vals.size - 1] do
      let v := vals.getD k 0
      tableRead 0 t.id (t.offset + k.toUInt32) t.width
      if t.width == 8 then andi 0 0xFF
      else if t.width == 16 then andi 0 0xFFFF
      expectEq 0 v code
    code := code + 1
  printImm 0x0400 mimophytblInfoRev3.size.toUInt32
  printImm Tag.done 0
  halt

end LeanOS.Wifi.Driver

namespace LeanOS.Wifi.Driver
open LeanOS.Wifi.Bytecode LeanOS.Wifi.Bcm43224 LeanOS.Wifi.NPhy

/-- Experiment: PHY table access semantics on this chip. -/
def tableExperiment : ProgM Unit := do
  bringUp
  -- 32-bit table 10 (frame_struct), entries 0..1.
  phyWrite tblAddr (10 * 1024 : UInt32)
  phyWrite tblDataHi 0x1234
  phyWrite tblDataLo 0x5678
  phyWrite tblDataHi 0x9abc
  phyWrite tblDataLo 0xdef0
  -- A: plain lo, hi, lo, hi
  phyWrite tblAddr (10 * 1024 : UInt32)
  phyRead 0 tblDataLo; print 0x0501 0
  phyRead 0 tblDataHi; print 0x0502 0
  phyRead 0 tblDataLo; print 0x0503 0
  phyRead 0 tblDataHi; print 0x0504 0
  -- B: hi first
  phyWrite tblAddr (10 * 1024 : UInt32)
  phyRead 0 tblDataHi; print 0x0511 0
  phyRead 0 tblDataLo; print 0x0512 0
  phyRead 0 tblDataHi; print 0x0513 0
  phyRead 0 tblDataLo; print 0x0514 0
  -- 16-bit table 11 (pilot) entries 0..1
  phyWrite tblAddr (11 * 1024 : UInt32)
  phyWrite tblDataLo 0x1111
  phyWrite tblDataLo 0x2222
  phyWrite tblAddr (11 * 1024 : UInt32)
  phyRead 0 tblDataLo; print 0x0521 0
  phyRead 0 tblDataLo; print 0x0522 0
  phyRead 0 tblDataLo; print 0x0523 0
  -- PHY register sanity: write/read a scratch-like register (0x70 bphy?).
  phyRead 0 0x01; print 0x0530 0
  phyRead 0 0x72; print 0x0531 0
  printImm Tag.done 0
  halt

end LeanOS.Wifi.Driver

namespace LeanOS.Wifi.Driver
open LeanOS.Wifi.Bytecode LeanOS.Wifi.Bcm43224 LeanOS.Wifi.NPhy

/-- 16-bit address/data write (brcmsmac CONFIG_BCM47XX style). -/
def phyWrite16 (addr val : UInt32) : ProgM Unit := do
  w16 d11PhyCtl addr
  r16 11 d11PhyCtl
  w16 d11PhyData val

def tableExperiment2 : ProgM Unit := do
  bringUp
  phyWrite16 tblAddr (10 * 1024 : UInt32)
  phyWrite16 tblDataHi 0x1234
  phyWrite16 tblDataLo 0x5678
  phyWrite16 tblDataHi 0x9abc
  phyWrite16 tblDataLo 0xdef0
  for k in [0:2] do
    phyWrite16 tblAddr (10 * 1024 : UInt32)
    phyRead 0 tblDataLo
    phyWrite16 tblAddr (10 * 1024 + k.toUInt32 : UInt32)
    phyRead 0 tblDataLo; print (0x0600 + k.toUInt32 * 2) 0
    phyRead 0 tblDataHi; print (0x0601 + k.toUInt32 * 2) 0
  -- 16-bit table 11 with quirk reads
  phyWrite16 tblAddr (11 * 1024 : UInt32)
  phyWrite16 tblDataLo 0x1111
  phyWrite16 tblDataLo 0x2222
  phyWrite16 tblDataLo 0x3333
  for k in [0:3] do
    phyRead 0 tblDataLo
    phyWrite16 tblAddr (11 * 1024 + k.toUInt32 : UInt32)
    phyRead 0 tblDataLo; print (0x0610 + k.toUInt32) 0
  -- plain 16-bit reads without quirk
  phyWrite16 tblAddr (11 * 1024 : UInt32)
  phyRead 0 tblDataLo; print 0x0620 0
  phyRead 0 tblDataLo; print 0x0621 0
  phyRead 0 tblDataLo; print 0x0622 0
  printImm Tag.done 0
  halt

end LeanOS.Wifi.Driver

namespace LeanOS.Wifi.Driver
open LeanOS.Wifi.Bytecode LeanOS.Wifi.Bcm43224 LeanOS.Wifi.NPhy

/-- wlc_phy_anacore(ON) for N-PHY rev >= 3 (phy_cmn.c). -/
def anacoreOnRev3 : ProgM Unit := do
  phyWrite 0xa6 0x0d
  phyWrite 0x8f 0x0
  phyWrite 0xa7 0x0d
  phyWrite 0xa5 0x0

/-- Radio power-up and channel set only (no N-PHY init body). -/
def radioTest (cfg : PhyCfg) : ProgM Unit := do
  bringUp
  anacoreOnRev3
  LeanOS.Wifi.Radio2056.radioOn cfg
  radioRead 0 0x01; print 0x0800 0
  phyRead 0 0x01; print 0x0801 0
  printImm Tag.done 0
  halt

end LeanOS.Wifi.Driver

namespace LeanOS.Wifi.Driver
open LeanOS.Wifi.Bytecode LeanOS.Wifi.Bcm43224 LeanOS.Wifi.NPhy LeanOS.Wifi.Mac

/-- Power up, initialise MAC and PHY with the supplied PHY init, enable the
MAC promiscuously and drain received frames by PIO. -/
def listen (fw : Firmware) (phyInit : ProgM Unit) (frames words tries : UInt32) :
    ProgM Unit := do
  bringUp
  ucodeStart fw
  coreInitTail
  bandInit fw phyInit
  enableMacPromisc
  rxDump frames words tries
  printImm Tag.done 0
  halt

/-- Interim PHY init: anacore, radio on + channel, tables and workarounds. -/
def phyInitPartial (cfg : PhyCfg) : ProgM Unit := do
  anacoreOnRev3
  LeanOS.Wifi.Radio2056.radioOn cfg
  NPhyTables.tblInit cfg
  LeanOS.Wifi.NPhyWorkarounds.workarounds cfg

end LeanOS.Wifi.Driver

namespace LeanOS.Wifi.Driver
open LeanOS.Wifi.Bytecode LeanOS.Wifi.Bcm43224 LeanOS.Wifi.NPhy LeanOS.Wifi.Mac

/-- Dump the microcode MAC statistics block (SHM bytes 0xE0..0x19F) twice,
`us` apart, as tags 0x09nn (nn = byte offset / 2 - 0x70) and 0x0Ann. -/
def macstatDump (us : UInt32) : ProgM Unit := do
  for k in [0:0x60] do
    shmRead16 0 (0xE0 + 2 * k.toUInt32); print (0x0900 + k.toUInt32) 0
  delay us
  for k in [0:0x60] do
    shmRead16 0 (0xE0 + 2 * k.toUInt32); print (0x0A00 + k.toUInt32) 0
  r32 0 d11MacIntStatus; print 0x0B00 0
  r32 0 rxPioCtl; print 0x0B01 0
  r32 0 (rxDmaCtl + 0x10); print 0x0B02 0

def listenStats (fw : Firmware) (phyInit : ProgM Unit) : ProgM Unit := do
  bringUp
  ucodeStart fw
  coreInitTail
  bandInit fw phyInit
  enableMacPromisc
  macstatDump 2000000
  printImm Tag.done 0
  halt

end LeanOS.Wifi.Driver
