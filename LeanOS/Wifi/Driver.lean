import LeanOS.Wifi.NPhyTables

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
