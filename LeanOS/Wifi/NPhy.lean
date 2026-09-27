import LeanOS.Wifi.Bcm43224

/-
N-PHY access layer and board configuration for the BCM43224 programs.

Accessor semantics follow brcmsmac (ISC; Copyright (c) 2010 Broadcom
Corporation) `phy_cmn.c`: PHY registers through `phyregaddr/phyregdata`
(0x3FC/0x3FE), radio registers through `phy4waddr/phy4wdatalo`
(0x3F6/0x3FA) with the 2055-style read offset for N-PHY revisions below 7,
and PHY tables through the N-PHY table address/data registers
(0x72/0x73/0x74).

Porting convention: brcmsmac branches on PHY revision, band, board flags and
SROM contents are decided while *generating* the program from `PhyCfg`, so
the emitted program contains only the path for this board. Branches on
values read from hardware at run time become bytecode branches.
-/
namespace LeanOS.Wifi.NPhy

open LeanOS.Wifi.Bytecode LeanOS.Wifi.Bcm43224

/-- Generation-time description of the board. Values for the Qotom card were
read from hardware on 2026-09-26 (see `qotom` below). -/
structure PhyCfg where
  phyRev : Nat
  radioRev : Nat
  chipRev : Nat
  chipPkg : Nat
  boardFlags : UInt32
  boardFlags2 : UInt32
  /-- 2.4 GHz channel number (1–13); 20 MHz only. -/
  channel : Nat
  /-- The 220 SROM words (revision 8 layout). -/
  sprom : Array UInt32

/-- 16-bit SROM word at *byte* offset `off`. -/
def PhyCfg.srom16 (c : PhyCfg) (off : Nat) : UInt32 := c.sprom.getD (off / 2) (0 : UInt32)

/-- SROM rev 8 FEM word for 2 GHz (byte 0xAE): tssipos, extpagain, pdetrange,
triso, antswctrllut. -/
def PhyCfg.fem2g (c : PhyCfg) : UInt32 := c.srom16 0xAE
def PhyCfg.extPaGain2g (c : PhyCfg) : UInt32 := (c.fem2g >>> 1) &&& 3
def PhyCfg.pdetRange2g (c : PhyCfg) : UInt32 := (c.fem2g >>> 3) &&& 0x1F
def PhyCfg.triso2g (c : PhyCfg) : UInt32 := (c.fem2g >>> 8) &&& 7
def PhyCfg.antSwLut2g (c : PhyCfg) : UInt32 := (c.fem2g >>> 11) &&& 0x1F
/-- brcmsmac: `ipa2g_on = (srom_fem2g.extpagain == 2)`. -/
def PhyCfg.ipa2g (c : PhyCfg) : Bool := c.extPaGain2g == 2
/-- Channel centre frequency in MHz (2.4 GHz band). -/
def PhyCfg.freqMHz (c : PhyCfg) : Nat := if c.channel == 14 then 2484 else 2407 + 5 * c.channel

/-- The SROM words dumped from the Qotom card (tag 0x03nn run, 2026-09-26). -/
def qotomSprom : Array UInt32 := #[
  0x2801, 0x0000, 0x04d8, 0x14e4, 0x0078, 0xedbe, 0x0000, 0x2bc4,
  0x2a64, 0x2964, 0x2c64, 0x3ce7, 0x46ff, 0x47ff, 0x0c00, 0x0820,
  0x0030, 0x1002, 0x9f28, 0x5d44, 0x8080, 0x1d8f, 0x0032, 0x0100,
  0xdf00, 0x71f5, 0x8400, 0x0083, 0x8500, 0x2010, 0x0001, 0xffff,
  0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff,
  0xffff, 0xffff, 0x1008, 0x0305, 0xffff, 0xffff, 0xffff, 0xffff,
  0x4353, 0x8000, 0x0002, 0x0000, 0x1f30, 0x1800, 0x0000, 0x0000,
  0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff,
  0x5372, 0x1167, 0x0200, 0x0000, 0x1000, 0x0000, 0x100d, 0x7fc9,
  0x75f1, 0x0000, 0x0000, 0xffff, 0xffff, 0xffff, 0x0303, 0x0202,
  0xffff, 0x0033, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0x0325,
  0x0325, 0x7800, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff,
  0x204c, 0xfea9, 0x16b5, 0xfa7d, 0x3e40, 0x3a3c, 0xfebb, 0x1348,
  0xfb23, 0xfe87, 0x1637, 0xfa8e, 0xfec4, 0x1383, 0xfb14, 0x0000,
  0x204c, 0xfeba, 0x16ba, 0xfaa8, 0x3e40, 0x3a3c, 0xfed6, 0x13aa,
  0xfb2e, 0xfe9a, 0x1591, 0xfabc, 0xfec4, 0x1461, 0xfaf8, 0x0000,
  0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff,
  0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff,
  0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff,
  0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff,
  0x0000, 0x4444, 0x4444, 0x0000, 0x2000, 0x0000, 0x0000, 0x0000,
  0x0000, 0x4444, 0x4444, 0x4444, 0x4444, 0x4444, 0x4444, 0x4444,
  0x4444, 0x0000, 0x2000, 0x0000, 0x2000, 0x0000, 0x0000, 0x0000,
  0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000,
  0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000,
  0x0000, 0x0000, 0x0000, 0x0022, 0x0000, 0xffff, 0xffff, 0xffff,
  0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff,
  0xffff, 0xffff, 0xffff, 0x8b08]

/-- Qotom card: chip 43224 rev 1 package 8, N-PHY rev 6, radio 2056 rev 11,
board flags 0x0200 / 0x1000 (SROM bytes 0x84/0x88). -/
def qotom (channel : Nat) : PhyCfg :=
  { phyRev := 6, radioRev := 11, chipRev := 1, chipPkg := 8,
    boardFlags := 0x0200, boardFlags2 := 0x1000, channel, sprom := qotomSprom }

/-! ## Scratch register convention

r0–r9 are free for ported code; r10–r11 are used by the accessors below;
r12 by `maskSet*`; r13–r14 by `poll*`; r15 is reserved. -/

/-- Flush posted writes (brcmsmac reads `phyversion` after PCI writes). -/
def flush : ProgM Unit := r16 11 d11PhyVersion

/-- write_phy_reg: one 32-bit write of `addr | val << 16`, then a flush. -/
def phyWrite (addr val : UInt32) : ProgM Unit := do
  w32 d11PhyCtl ((addr &&& (0xFFFF : UInt32)) ||| ((val &&& (0xFFFF : UInt32)) <<< (16 : UInt32)))
  flush

/-- write_phy_reg with the value taken from register `r` (low 16 bits). -/
def phyWriteR (addr : UInt32) (r : Reg) : ProgM Unit := do
  mov 10 r
  andi 10 0xFFFF
  shli 10 16
  ori 10 (addr &&& 0xFFFF)
  emit (.write32 d11PhyCtl (.reg 10))
  flush

/-- read_phy_reg into `dst`. -/
def phyRead (dst : Reg) (addr : UInt32) : ProgM Unit := do
  w16 d11PhyCtl addr
  r16 11 d11PhyCtl
  r16 dst d11PhyData

/-- mod_phy_reg: `reg := (reg & ~mask) | (val & mask)`. -/
def phyMod (addr mask val : UInt32) : ProgM Unit := do
  w16 d11PhyCtl addr
  r16 11 d11PhyCtl
  maskSet16 d11PhyData ((~~~mask) &&& 0xFFFF) (val &&& mask)

/-- mod_phy_reg with a run-time value in register `r` (already shifted). -/
def phyModR (addr mask : UInt32) (r : Reg) : ProgM Unit := do
  w16 d11PhyCtl addr
  r16 11 d11PhyCtl
  r16 10 d11PhyData
  andi 10 ((~~~mask) &&& 0xFFFF)
  mov 12 r
  andi 12 mask
  emit (.alu .or 10 (.reg 12))
  emit (.write16 d11PhyData (.reg 10))

def phyAnd (addr mask : UInt32) : ProgM Unit := do
  w16 d11PhyCtl addr
  r16 11 d11PhyCtl
  maskSet16 d11PhyData (mask &&& 0xFFFF) 0

def phyOr (addr bits : UInt32) : ProgM Unit := do
  w16 d11PhyCtl addr
  r16 11 d11PhyCtl
  maskSet16 d11PhyData 0xFFFF (bits &&& 0xFFFF)

/-- N-PHY (rev < 7) radio read offset (RADIO_2055_READ_OFF). -/
def radioReadOff : UInt32 := 0x100

def radioWrite (addr val : UInt32) : ProgM Unit := do
  w16 d11RadioCtl addr
  r16 11 d11RadioCtl
  w16 d11RadioDataLow (val &&& 0xFFFF)
  r32 11 d11MacCtl

def radioWriteR (addr : UInt32) (r : Reg) : ProgM Unit := do
  w16 d11RadioCtl addr
  r16 11 d11RadioCtl
  emit (.write16 d11RadioDataLow (.reg r))
  r32 11 d11MacCtl

def radioRead (dst : Reg) (addr : UInt32) : ProgM Unit := do
  w16 d11RadioCtl (addr ||| radioReadOff)
  r16 11 d11RadioCtl
  r16 dst d11RadioDataLow

/-- mod_radio_reg: `reg := (reg & ~mask) | (val & mask)`. -/
def radioMod (addr mask val : UInt32) : ProgM Unit := do
  radioRead 10 addr
  andi 10 ((~~~mask) &&& 0xFFFF)
  ori 10 (val &&& mask)
  radioWriteR addr 10

def radioOr (addr bits : UInt32) : ProgM Unit := radioMod addr bits bits
def radioAnd (addr mask : UInt32) : ProgM Unit := radioMod addr ((~~~mask) &&& 0xFFFF) 0

/-! ## PHY tables -/

def tblAddr : UInt32 := 0x72
def tblDataHi : UInt32 := 0x73
def tblDataLo : UInt32 := 0x74
/-- NPHY_TBL_ID_ANTSWCTRLLUT; subject to the 43224 rev 1 table quirk. -/
def tblIdAntSwCtrlLut : UInt32 := 9

/-- wlc_phy_write_table for the N-PHY with element width 8, 16 or 32,
including the BCM43224 chip-rev-1 ANTSWCTRLLUT per-element re-addressing. -/
def tableWrite (cfg : PhyCfg) (id offset width : UInt32) (values : Array UInt32) :
    ProgM Unit := do
  phyWrite tblAddr ((id <<< 10) ||| offset)
  let quirk := cfg.chipRev == 1 && id == tblIdAntSwCtrlLut
  for h : k in [0:values.size] do
    let v := values[k]
    if quirk then
      phyRead 10 tblDataLo
      phyWrite tblAddr ((id <<< 10) ||| (offset + k.toUInt32))
    if width == 32 then
      phyWrite tblDataHi (v >>> 16)
      phyWrite tblDataLo (v &&& 0xFFFF)
    else if width == 16 then
      phyWrite tblDataLo (v &&& 0xFFFF)
    else
      phyWrite tblDataLo (v &&& 0xFF)

/-- Single-element table write with a run-time value in register `r`. -/
def tableWriteR (id offset width : UInt32) (r : Reg) : ProgM Unit := do
  phyWrite tblAddr ((id <<< 10) ||| offset)
  if width == 32 then
    mov 9 r
    shri 9 16
    phyWriteR tblDataHi 9
  phyWriteR tblDataLo r

/-- wlc_phy_read_table, one element into `dst` (32-bit reads combine hi/lo). -/
def tableRead (dst : Reg) (id offset width : UInt32) : ProgM Unit := do
  phyWrite tblAddr ((id <<< 10) ||| offset)
  if width == 32 then
    phyRead 9 tblDataLo
    phyRead dst tblDataHi
    shli dst 16
    emit (.alu .or dst (.reg 9))
  else
    phyRead dst tblDataLo

end LeanOS.Wifi.NPhy
