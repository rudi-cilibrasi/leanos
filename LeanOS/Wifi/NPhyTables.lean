import LeanOS.Wifi.NPhy
import LeanOS.Wifi.NPhyTablesData

/-
N-PHY table initialisation (`wlc_phy_tbl_init_nphy`) for the BCM43224.

Ported from Linux brcmsmac (ISC license), Copyright (c) 2010 Broadcom
Corporation; see drivers/net/wireless/broadcom/brcm80211/brcmsmac at Linux
commit fd179f8a05be3ccae366b9b96e176b51fbe54aab.

Only the N-PHY revision 3..6 path is kept: the static download writes
`mimophytbl_info_rev3` and the volatile part writes the antenna switch
control table chosen by the 2 GHz SROM `antswctrllut` field. The table data
lives in `NPhyTablesData` (extracted mechanically from `phy/phytbl_n.c`).
-/
namespace LeanOS.Wifi.NPhyTables

open LeanOS.Wifi.Bytecode LeanOS.Wifi.NPhy LeanOS.Wifi.NPhyTablesData

/-- Decoded elements of `t` if the literal is well formed, has the C array
length and every element fits the table width; `none` otherwise. -/
def checkedTable (t : TblSpec) : Option (Array UInt32) :=
  let vals := hexU32s t.data
  let limit : Nat := 2 ^ t.width.toNat
  if hexU32sValid t.data && vals.size == t.len &&
      (t.width == 8 || t.width == 16 || t.width == 32) &&
      vals.all (fun v => v.toNat < limit) then
    some vals
  else
    none

/-- wlc_phy_write_table_nphy (phy_int.h macro over `wlc_phy_write_table`,
phy_cmn.c:824-859) for one `phytbl_info` entry. A table that fails the
generation-time checks is replaced by `fail code`, so it can never run. -/
def writeTableNphy (cfg : PhyCfg) (code : UInt32) (t : TblSpec) : ProgM Unit :=
  match checkedTable t with
  | some vals => tableWrite cfg t.id t.offset t.width vals
  | none => fail code

/-- wlc_phy_static_table_download_nphy, phy_n.c:14177-14199. Only the
revision 3..6 branch (`mimophytbl_info_rev3`) is ported; other revisions
emit `fail 0x7E3F`. Bad tables fail with `0x7E40 + index`. -/
def wlcPhyStaticTableDownloadNphy (cfg : PhyCfg) : ProgM Unit := do
  if cfg.phyRev >= 3 && cfg.phyRev < 7 then
    for h : k in [0:mimophytblInfoRev3.size] do
      writeTableNphy cfg (0x7E40 + k.toUInt32) mimophytblInfoRev3[k]
  else
    fail 0x7E3F

/-- `pi->phy_init_por`: true from `wlc_phy_attach` (phy_cmn.c:429) until the
first `wlc_phy_init` completes (phy_cmn.c:741), and again after
`wlc_phy_por_inform`. The programs here model the first init after attach. -/
def phyInitPor : Bool := true

/-- wlc_phy_tbl_init_nphy, phy_n.c:14201-14325, for N-PHY revisions 3..6
on the 2 GHz band. `por` is `pi->phy_init_por` (the static tables are only
downloaded after power-on reset). The volatile antenna switch control table
(`ANT_SWCTRL_TBL_REV3_IDX` = 0, the only `mimophytbl_info_rev3_volatile`
entry) is selected by SROM `fem2g.antswctrllut`; values above 3 write
nothing, as in brcmsmac. Bad volatile tables fail with `0x7E60 + lut`. -/
def wlcPhyTblInitNphy (cfg : PhyCfg) (por : Bool := phyInitPor) : ProgM Unit := do
  if por then
    wlcPhyStaticTableDownloadNphy cfg
  if cfg.phyRev >= 7 || cfg.phyRev < 3 then
    -- Revision 7+ (2057 antswctrl LUTs) and revision 0..2 paths not ported.
    fail 0x7E3E
  else
    -- 2 GHz only: antswctrllut comes from srom_fem2g.
    match cfg.antSwLut2g.toNat with
    | 0 => writeTableNphy cfg 0x7E60 mimophytblInfoRev3Volatile
    | 1 => writeTableNphy cfg 0x7E61 mimophytblInfoRev3Volatile1
    | 2 => writeTableNphy cfg 0x7E62 mimophytblInfoRev3Volatile2
    | 3 => writeTableNphy cfg 0x7E63 mimophytblInfoRev3Volatile3
    | _ => pure ()

/-- Table initialisation for the board, as run by the first PHY init. -/
def tblInit (cfg : PhyCfg) : ProgM Unit := wlcPhyTblInitNphy cfg

end LeanOS.Wifi.NPhyTables
