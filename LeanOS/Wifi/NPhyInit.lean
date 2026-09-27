import LeanOS.Wifi.NPhy

/-
N-PHY initialisation (`wlc_phy_init_nphy`) for the BCM43224 programs.

Ported from Linux brcmsmac (ISC license), Copyright (c) 2010 Broadcom
Corporation; see drivers/net/wireless/broadcom/brcm80211/brcmsmac at Linux
commit fd179f8a05be3ccae366b9b96e176b51fbe54aab.

Scope: the path taken by N-PHY rev 6 / radio 2056 rev 11 / 2.4 GHz / 20 MHz /
internal PA (IPA) on the Qotom board, on the *first* `wlc_phy_init` after
attach. Every revision, band, board-flag and attach-state branch is decided
while generating; only hardware-read values are handled in bytecode.

Pieces supplied by the caller (ported elsewhere):
* `tblInit`     = `wlc_phy_tbl_init_nphy`
* `workarounds` = `wlc_phy_workarounds_nphy`
* `rssiCal`     = `wlc_phy_rssi_cal_nphy` (first init: `nphy_rssical_chanspec_2G == 0`)
* `txRxCal`     = the `do_nphy_cal` block (precal tx gain, tx IQ/LO cal,
  rx IQ cal, savecal). See `initNphy` for what brcmsmac really does there.
Hooks may clobber r0–r9; `initNphy` keeps nothing live across a hook.

## Attach-time state assumed (first init after `wlc_phy_attach`)
All from brcmsmac `phy_cmn.c` (`wlc_phy_attach`, `wlc_set_phy_uninitted`),
`phy_n.c` (`wlc_phy_attach_nphy`, `wlc_phy_txpwrctrl_config_nphy`,
`wlc_phy_txpwr_srom_read_nphy`) and `main.c` call order:
* `n_preamble_override = AUTO` (rev 6 is not 3/4) → not greenfield.
* `nphy_txrx_chain = AUTO` → both chains; `nphy_perical` becomes MPHASE.
* `nphy_txpwrctrl = PHY_TPC_HW_ON` (rev ≥ 3).
* `nphy_papd_epsilon_offset[0..1] = 0xf588`, `nphy_txpwr_idx[0..1] = 128`.
* `sh->phyrxchain = 3`, `sh->_rifs_phy = false` (kzalloc; nothing sets it).
* `phyhang_avoid = false` (only rev 3..5), `pi->bw = 20 MHz`.
* `nphy_gband_spurwar_en = true` (rev 3..6); `nphy_gband_spurwar2_en` iff
  boardflags2 & BFL2_2G_SPUR_WAR (0x2000); `nphy_aband_spurwar_en` iff
  boardflags2 & BFL2_SPUR_WAR (0x200). `nphy_anarxlpf_adjusted`,
  `nphy_noisevars_adjusted`, `nphy_crsminpwr_adjusted` are false.
* `measure_hold` has no scan/mute bit; no scan in progress; `do_initcal`.
* `mphase_cal_phase_id = IDLE` (no mphase cal pending),
  `nphy_rssical_chanspec_2G == 0` and `nphy_iqcal_chanspec_2G == 0`.
* `nphy_bb_mult_save = 0` on entry to the idle-TSSI measurement.
* `tx_power_max = 0` and `tx_power_offset[] = 0` ⇒ `adj_pwr_tbl_nphy[] = 0`:
  brcmsmac's first `wlc_phy_init` (from `brcms_b_init`) runs before
  `brcms_c_bandinit_ordered` → `wlc_phy_txpower_limit_set` →
  `wlc_phy_txpower_recalc_target`, which later rewrites the target (0x1ea)
  and the per-rate offset table. That recalculation is not part of this port.
* SROM rev 8 per-core power info (byte offsets 0xC0 / 0xE0): +2/+4/+6 are
  `pa_2g[0..2]` = pwrdet a1 / b0 / b1 (signed 16-bit). `maxp2ga`/`itt2ga`
  (+0) only feed the target recalculation above and are not used here.
-/
namespace LeanOS.Wifi.NPhyInit

open LeanOS.Wifi.Bytecode LeanOS.Wifi.Bcm43224 LeanOS.Wifi.NPhy

/-! ## Diagnostics -/

namespace Fail
/-- A generation-time table failed its length/format check. -/
def badTable : UInt32 := 0x7E40
/-- The configuration asks for a path this port does not carry. -/
def unsupported : UInt32 := 0x7E41
end Fail

namespace Tag
/-- `wlc_phy_force_rfseq_nphy` WARN: sequencer status bit still set. -/
def rfseqStuck : UInt32 := 0x0440
/-- Tx power control was on at `txpwrctrl_enable(OFF)`; its current indices
are not carried to the final `txpwrctrl_enable(ON)` (see `txpwrctrlOff`). -/
def tpcWasOn : UInt32 := 0x0441
end Tag

/-! ## Attach-time constants and board-derived decisions -/

/-- `PHY_IPA(pi)` on a 2.4 GHz channel. -/
def ipa (cfg : PhyCfg) : Bool := cfg.ipa2g

/-- `pi->nphy_papd_epsilon_offset[core]` from `wlc_set_phy_uninitted`. -/
def papdEpsilonOffset : UInt32 := 0xf588

/-- `pi->nphy_txpwrindex[core].index_internal` chosen by
`wlc_phy_txpwr_fixpower_nphy` (40 for rev 3..6; 30 for rev ≥ 7). Calibration
ports that save `nphy_cal_orig_pwr_idx` should use this value. -/
def fixTxPwrIndex (cfg : PhyCfg) : Nat :=
  if cfg.phyRev >= 7 then 30 else if cfg.phyRev >= 3 then 40 else 91

/-- `pi->nphy_gband_spurwar_en` (wlc_phy_attach_nphy). -/
def gbandSpurwarEn (cfg : PhyCfg) : Bool := cfg.phyRev >= 3 && cfg.phyRev < 7
/-- `pi->nphy_gband_spurwar2_en`: rev 6 with BFL2_2G_SPUR_WAR (0x2000). -/
def gbandSpurwar2En (cfg : PhyCfg) : Bool :=
  cfg.phyRev == 6 && (cfg.boardFlags2 &&& 0x2000) != 0

/-- `pi->sh->phyrxchain` after attach. -/
def phyRxChain : Nat := 3
/-- `pi->sh->_rifs_phy` (never set before the first init). -/
def rifsPhy : Bool := false
/-- `pi->tx_power_max` on the first init (see module header). -/
def txPowerMaxFirstInit : Int := 0
/-- `pi->adj_pwr_tbl_nphy` (ADJ_PWR_TBL_LEN = 84) on the first init. -/
def adjPwrTblFirstInit : Array UInt32 := Array.replicate 84 0

/-! ## Tables (exact brcmsmac values) -/

/-- `nphy_tpc_txgain_ipa_rev6` (phy_n.c:13461), 128 words. -/
def tpcTxgainIpaRev6 : String := "
0x0ff7002d 0x0ff7002b 0x0ff7002a 0x0ff70029 0x0ff70028 0x0ff70027 0x0ff70026 0x0ff70025
0x0ef7002d 0x0ef7002b 0x0ef7002a 0x0ef70029 0x0ef70028 0x0ef70027 0x0ef70026 0x0ef70025
0x0df7002d 0x0df7002b 0x0df7002a 0x0df70029 0x0df70028 0x0df70027 0x0df70026 0x0df70025
0x0cf7002d 0x0cf7002b 0x0cf7002a 0x0cf70029 0x0cf70028 0x0cf70027 0x0cf70026 0x0cf70025
0x0bf7002d 0x0bf7002b 0x0bf7002a 0x0bf70029 0x0bf70028 0x0bf70027 0x0bf70026 0x0bf70025
0x0af7002d 0x0af7002b 0x0af7002a 0x0af70029 0x0af70028 0x0af70027 0x0af70026 0x0af70025
0x09f7002d 0x09f7002b 0x09f7002a 0x09f70029 0x09f70028 0x09f70027 0x09f70026 0x09f70025
0x08f7002d 0x08f7002b 0x08f7002a 0x08f70029 0x08f70028 0x08f70027 0x08f70026 0x08f70025
0x07f7002d 0x07f7002b 0x07f7002a 0x07f70029 0x07f70028 0x07f70027 0x07f70026 0x07f70025
0x06f7002d 0x06f7002b 0x06f7002a 0x06f70029 0x06f70028 0x06f70027 0x06f70026 0x06f70025
0x05f7002d 0x05f7002b 0x05f7002a 0x05f70029 0x05f70028 0x05f70027 0x05f70026 0x05f70025
0x04f7002d 0x04f7002b 0x04f7002a 0x04f70029 0x04f70028 0x04f70027 0x04f70026 0x04f70025
0x03f7002d 0x03f7002b 0x03f7002a 0x03f70029 0x03f70028 0x03f70027 0x03f70026 0x03f70025
0x02f7002d 0x02f7002b 0x02f7002a 0x02f70029 0x02f70028 0x02f70027 0x02f70026 0x02f70025
0x01f7002d 0x01f7002b 0x01f7002a 0x01f70029 0x01f70028 0x01f70027 0x01f70026 0x01f70025
0x00f7002d 0x00f7002b 0x00f7002a 0x00f70029 0x00f70028 0x00f70027 0x00f70026 0x00f70025"

/-- `nphy_papd_pga_gain_delta_ipa_2g` (phy_n.c:13741), 16 signed bytes,
stored here sign-extended to the 32-bit words brcmsmac writes. -/
def papdPgaGainDeltaIpa2g : String := "
0xffffff8e 0xffffff94 0xffffff9e 0xffffffa5 0xffffffac 0xffffffb2 0xffffffba 0xffffffc2
0xffffffca 0xffffffd2 0xffffffd9 0xffffffe1 0xffffffe9 0xfffffff1 0xfffffff8 0x00000000"

/-- `NPHY_IPA_REV4_txdigi_filtcoeffs` (phy_n.c:262) rows 0, 1, 2 and 6 (the
rows reachable at 20 MHz in 2.4 GHz), 15 coefficients each as 16-bit words. -/
def ipaTxDigiFiltRow0 : String :=
  "0xfe87 0x0089 0xfe69 0x00d0 0xfa09 0x03bc 0x005d 0x00ba 0x005d 0x00e6 0xffd4 0x00e6 0x00c9 0xff41 0x00c9"
def ipaTxDigiFiltRow1 : String :=
  "0xffb3 0x0014 0xff9e 0x0031 0xffa3 0x003c 0x0038 0x006f 0x0038 0x001a 0xfffb 0x001a 0x0022 0xffe0 0x0022"
def ipaTxDigiFiltRow2 : String :=
  "0xfe98 0x00a4 0xfe88 0x00a4 0xfa03 0x0240 0x0134 0xfec6 0x0134 0x0079 0xffb7 0x0079 0x005b 0x007c 0x005b"
def ipaTxDigiFiltRow6 : String :=
  "0x0ed9 0x00c8 0x0e95 0x008e 0x0a91 0x033a 0x0097 0x012d 0x0097 0x0097 0x012d 0x0097 0x025a 0x0d10 0x025a"

/-- Decode a table and emit a `fail` unless it has exactly `n` valid words. -/
def checkedTable (s : String) (n : Nat) : ProgM (Array UInt32) := do
  let t := hexU32s s
  if t.size != n || !hexU32sValid s then fail Fail.badTable
  return t

/-- `wlc_phy_get_ipa_gaintbl_nphy` (phy_n.c:17771-17817), 2.4 GHz rev 3..6
branch. Only rev 6 (not BCM47162) is carried; any other revision yields an
empty table and an emitted `fail Fail.unsupported`. -/
def ipaGainTblSrc (cfg : PhyCfg) : Option String :=
  if cfg.phyRev == 6 then some tpcTxgainIpaRev6 else none

def ipaGainTbl (cfg : PhyCfg) : ProgM (Array UInt32) :=
  match ipaGainTblSrc cfg with
  | some s => checkedTable s 128
  | none => do fail Fail.unsupported; return Array.replicate 128 0

/-- `pi->nphy_gmval` recorded by `wlc_phy_init_nphy` from the gain table. -/
def nphyGmval : UInt32 := ((hexU32s tpcTxgainIpaRev6).getD 0 0 >>> 16) &&& 0x7000

/-! ## Small bytecode helpers -/

/-- `SPINWAIT(read_phy_reg(addr) & mask, us)` (brcmu_utils.h): poll at most
`(us + 9) / 10` times with 10 µs delays while the masked value is non-zero.
No failure on timeout (the caller checks). Uses `rt` and `rc`. -/
def spinWhilePhySet (addr mask us : UInt32) (rt rc : Reg) : ProgM Unit := do
  let top ← newLabel
  let done ← newLabel
  li rc ((us + 9) / 10)
  place top
  phyRead rt addr
  andi rt mask
  emit (.branch .eq rt (.imm 0) done)
  emit (.branch .eq rc (.imm 0) done)
  delay 10
  emit (.alu .sub rc (.imm 1))
  emit (.jump top)
  place done

/-- Write `count` copies of the 32-bit value `hi:lo` (registers holding the
16-bit halves) to a PHY table starting at `offset`, using the table
auto-increment (wlc_phy_write_table_nphy with a constant buffer). Uses `rc`. -/
def tableFill32R (id offset count : UInt32) (hi lo rc : Reg) : ProgM Unit := do
  phyWrite tblAddr ((id <<< 10) ||| offset)
  let top ← newLabel
  li rc count
  place top
  phyWriteR tblDataHi hi
  phyWriteR tblDataLo lo
  emit (.alu .sub rc (.imm 1))
  emit (.branch .ne rc (.imm 0) top)

/-- `wlc_phy_read_table` (phy_cmn.c:859-894) for the N-PHY: read
`dsts.size` consecutive elements starting at `offset` into the registers
`dsts`. On the BCM43224 rev 1 brcmsmac applies its read quirk to *every*
table (unlike the ANTSWCTRLLUT-only write quirk): before each element it does
a dummy read of the data register and re-writes the address. (`NPhy.tableRead`
omits this quirk, so this module uses its own reader.) For 32-bit elements
the low half is read first into `tmp`, then the high half. -/
def tableReadSeq (cfg : PhyCfg) (id offset width : UInt32) (dsts : Array Reg)
    (tmp : Reg := 9) : ProgM Unit := do
  phyWrite tblAddr ((id <<< 10) ||| offset)
  let quirk := cfg.chipRev == 1   -- chip is always the BCM43224 here
  for h : k in [0:dsts.size] do
    let dst := dsts[k]
    if quirk then
      phyRead dst tblDataLo
      phyWrite tblAddr ((id <<< 10) ||| (offset + k.toUInt32))
    if width == 32 then
      phyRead tmp tblDataLo
      phyRead dst tblDataHi
      shli dst 16
      emit (.alu .or dst (.reg tmp))
    else if width == 16 then
      phyRead dst tblDataLo
    else
      phyRead dst tblDataLo
      andi dst 0xff

/-- One-element `wlc_phy_table_read_nphy` with the 43224 read quirk. -/
def tableRead1 (cfg : PhyCfg) (dst : Reg) (id offset width : UInt32) (tmp : Reg := 9) :
    ProgM Unit :=
  tableReadSeq cfg id offset width #[dst] tmp

/-- Sign-extend the 6-bit field in `r` to 8 bits (`(s8)(x << 2) >> 2` then
`& 0xff`). Uses `tmp`. -/
def sext6to8 (r tmp : Reg) : ProgM Unit := do
  andi r 0x3f
  mov tmp r
  andi tmp 0x20
  let skip ← newLabel
  emit (.branch .eq tmp (.imm 0) skip)
  ori r 0xc0
  place skip

/-! ## MAC-side shims (brcmsmac main.c) -/

/-- `wlapi_bmac_phyclk_fgc` → `brcms_b_phyclk_fgc` (main.c:1716-1727):
N-PHY only; `brcms_b_core_ioctl(SICF_FGC, on ? SICF_FGC : 0)`, a
read-modify-write of the BCMA IOCTL register (SICF_FGC = BCMA_IOCTL_FGC = 0x2). -/
def phyclkFgc (on : Bool) : ProgM Unit :=
  maskSet32 wrapIoCtl (~~~ioctlFgc) (if on then ioctlFgc else 0)

/-- `SICF_MPCLKE` (d11.h:1740). -/
def sicfMpclke : UInt32 := 0x0010

/-- `wlapi_bmac_macphyclk_set` → `brcms_b_macphyclk_set` (main.c:1729-1735). -/
def macphyclkSet (on : Bool) : ProgM Unit :=
  maskSet32 wrapIoCtl (~~~sicfMpclke) (if on then sicfMpclke else 0)

/-! ## phy_cmn.c -/

/-- `wlc_phy_anacore(pih, ON)` for the N-PHY (phy_cmn.c:604-640). -/
def anacoreOn (cfg : PhyCfg) : ProgM Unit := do
  if cfg.phyRev >= 3 then
    phyWrite 0xa6 0x0d
    phyWrite 0x8f 0x0
    phyWrite 0xa7 0x0d
    phyWrite 0xa5 0x0
  else
    phyWrite 0xa5 0x0

/-! ## phy_n.c helpers on the init path -/

/-- `wlc_phy_update_mimoconfig_nphy` (phy_n.c:14687-14703) with the attach
default `n_preamble_override = AUTO` (not greenfield). -/
def wlcPhyUpdateMimoconfigNphy (_cfg : PhyCfg) (greenfield : Bool := false) : ProgM Unit := do
  phyRead 0 0xed
  ori 0 0x0100            -- RX_GF_MM_AUTO
  andi 0 (~~~0x0004)      -- ~RX_GF_OR_MM
  if greenfield then ori 0 0x0004
  phyWriteR 0xed 0

/-- `wlc_phy_stf_chain_upd_nphy` (phy_n.c:19593-19623) with
`nphy_txrx_chain = AUTO`: both chains active, no core override
(`nphy_perical` becomes PHY_PERICAL_MPHASE). -/
def wlcPhyStfChainUpdNphy (_cfg : PhyCfg) : ProgM Unit := do
  phyMod 0xa2 0xff (0x11 ||| 0x22)
  phyAnd 0xa1 (~~~0x0001 &&& 0xffff)

/-- `wlc_phy_ipa_set_tx_digi_filts_nphy` (phy_n.c:14705-14731), 20 MHz. -/
def wlcPhyIpaSetTxDigiFiltsNphy (cfg : PhyCfg) : ProgM Unit := do
  let rows : Array (UInt32 × String) := #[(0x186, ipaTxDigiFiltRow0), (0x195, ipaTxDigiFiltRow1),
    (0x2c5, ipaTxDigiFiltRow2)]
  for (base, row) in rows do
    let c ← checkedTable row 15
    for h : j in [0:c.size] do
      phyWrite (base + j.toUInt32) c[j]
  -- bw 40 and 5 GHz branches are not reachable on this board.
  if cfg.channel == 14 then
    let c ← checkedTable ipaTxDigiFiltRow6 15
    for h : j in [0:c.size] do
      phyWrite (0x2c5 + j.toUInt32) c[j]

/-- `wlc_phy_pa_override_nphy(pi, OFF)` (phy_n.c:19566-19591): saves 0x91 and
0x92 in **r7 / r8** (brcmsmac `rfctrlIntc{1,2}_save`) for the matching
`paOverrideOn`, then forces the 2.4 GHz rev 3..6 override value. -/
def paOverrideOff (cfg : PhyCfg) : ProgM Unit := do
  phyRead 7 0x91
  phyRead 8 0x92
  let v : UInt32 := if cfg.phyRev >= 7 then 0x1480
    else if cfg.phyRev >= 3 then 0x480 else 0x120
  phyWrite 0x91 v
  phyWrite 0x92 v

/-- `wlc_phy_pa_override_nphy(pi, ON)`: restores from r7 / r8. -/
def paOverrideOn : ProgM Unit := do
  phyWriteR 0x91 7
  phyWriteR 0x92 8

/-- RF sequencer commands (phyreg_n.h). -/
inductive Rfseq where
  | rx2tx | tx2rx | reset2rx | updateGainH | updateGainL | updateGainU

/-- Trigger bit in 0xa3 and status bit in 0xa4 (identical encodings). -/
def Rfseq.bit : Rfseq → UInt32
  | .rx2tx => 0x01 | .tx2rx => 0x02 | .updateGainH => 0x04
  | .updateGainL => 0x08 | .updateGainU => 0x10 | .reset2rx => 0x20

/-- `wlc_phy_force_rfseq_nphy` (phy_n.c:21316-21357). Uses r0–r2 only
(r7/r8 are preserved for the PA override). The WARN becomes a print. -/
def wlcPhyForceRfseqNphy (_cfg : PhyCfg) (cmd : Rfseq) : ProgM Unit := do
  phyRead 0 0xa1
  phyOr 0xa1 (0x0001 ||| 0x0002)   -- CoreActv_override | Trigger_override
  phyOr 0xa3 cmd.bit
  spinWhilePhySet 0xa4 cmd.bit 200000 1 2
  phyWriteR 0xa1 0
  phyRead 1 0xa4
  andi 1 cmd.bit
  let ok ← newLabel
  emit (.branch .eq 1 (.imm 0) ok)
  printImm Tag.rfseqStuck cmd.bit
  place ok

/-- `wlc_phy_classifier_nphy(pi, 0, 0)` (phy_n.c:21292-21314); core rev 23
is not 16, so no MAC suspend. With mask 0 the value is re-written unchanged. -/
def wlcPhyClassifierNphy (_cfg : PhyCfg) (mask val : UInt32) : ProgM Unit := do
  phyRead 0 0xb0
  andi 0 0x7
  andi 0 (~~~mask)
  ori 0 (val &&& mask)
  phyModR 0xb0 0x7 0

/-- `wlc_phy_clip_det_nphy(pi, 0, vals)` (phy_n.c:17047-17057): reads the clip
thresholds into r0/r1 (`wlc_phy_init_nphy` does not use them afterwards). -/
def wlcPhyClipDetNphyRead (_cfg : PhyCfg) : ProgM Unit := do
  phyRead 0 0x2c
  phyRead 1 0x42

/-- `wlc_phy_bphy_init_nphy` (phy_n.c:14132-14146): NPHY_TO_BPHY_OFF = 0xc00,
BPHY_RSSI_LUT 0x88..0xa7, BPHY_STEP 0x38. -/
def wlcPhyBphyInitNphy (_cfg : PhyCfg) : ProgM Unit := do
  let mut v : UInt32 := 0x1e1f
  for a in [0xc88:0xca8] do
    phyWrite a.toUInt32 v
    v := if a == 0xc97 then 0x3e3f else v - 0x0202
  phyWrite (0xc00 + 0x38) 0x668

/-- `wlc_phy_txpwrctrl_enable_nphy(pi, PHY_TPC_HW_OFF)` (phy_n.c:28150-28283).

Deviation: when hardware power control is already on, brcmsmac stores the
current indices (`wlc_phy_txpwr_idx_cur_get_nphy`) in `pi->nphy_txpwr_idx`
and re-applies them in the final `txpwrctrl_enable(ON)`. The bytecode has no
storage that survives the calibration hooks, so we print `Tag.tpcWasOn` with
0x1e7 and keep the attach value 128 (no re-apply). After the PHY reset that
precedes the first init the bits are expected to be clear. -/
def txpwrctrlOff (cfg : PhyCfg) : ProgM Unit := do
  if cfg.phyRev >= 3 then
    phyRead 0 0x1e7
    andi 0 0xe000
    let off ← newLabel
    emit (.branch .eq 0 (.imm 0) off)
    phyRead 0 0x1e7
    print Tag.tpcWasOn 0
    place off
  let zeros := Array.replicate 84 (0 : UInt32)
  tableWrite cfg 26 64 16 zeros
  tableWrite cfg 27 64 16 zeros
  if cfg.phyRev >= 3 then
    phyAnd 0x1e7 (0xffff &&& ~~~(0x8000 ||| 0x4000 ||| 0x2000))
    phyOr 0x8f 0x100
    phyOr 0xa5 0x100
  else
    phyAnd 0x1e7 (~~~(0x4000 ||| 0x2000) &&& 0xffff)
    phyOr 0xa5 0x4000

/-- `wlc_phy_txpwrctrl_enable_nphy(pi, PHY_TPC_HW_ON)` (phy_n.c:28150-28283),
2.4 GHz, rev 3..6, IPA, `nphy_txpwr_idx = 128` (see `txpwrctrlOff`). -/
def txpwrctrlOn (cfg : PhyCfg) (adjPwrTbl : Array UInt32) : ProgM Unit := do
  tableWrite cfg 26 64 8 adjPwrTbl
  tableWrite cfg 27 64 8 adjPwrTbl
  let mask : UInt32 := 0x4000 ||| 0x2000 ||| (if cfg.phyRev >= 3 then 0x8000 else 0)
  phyMod 0x1e7 mask mask
  -- nphy_txpwr_idx[] == 128: wlc_phy_txpwr_idx_cur_set_nphy is skipped.
  if cfg.phyRev >= 3 then
    phyAnd 0x8f (~~~0x100 &&& 0xffff)
    phyAnd 0xa5 (~~~0x100 &&& 0xffff)
  else
    phyAnd 0xa5 (~~~0x4000 &&& 0xffff)
  if ipa cfg then
    phyMod 0x297 0x4 0
    phyMod 0x29b 0x4 0

/-- `wlc_phy_txpwrctrl_enable_nphy` (phy_n.c:28150-28283). -/
def wlcPhyTxpwrctrlEnableNphy (cfg : PhyCfg) (on : Bool) : ProgM Unit :=
  if on then txpwrctrlOn cfg adjPwrTblFirstInit else txpwrctrlOff cfg

/-- `wlc_phy_txpwr_fixpower_nphy` (phy_n.c:27696-27836), rev 3..6 IPA 2 GHz:
`txpi = 40` for both cores. -/
def wlcPhyTxpwrFixpowerNphy (cfg : PhyCfg) : ProgM Unit := do
  let txpi := fixTxPwrIndex cfg
  let tbl ← ipaGainTbl cfg
  for core in [0:2] do
    let txgain := tbl.getD txpi 0
    let radGain := (txgain >>> 16) &&& 0xffff      -- (1 << 17) - 1, as u16
    let dacGain := (txgain >>> 8) &&& 0x3f
    let bbmult := txgain &&& 0xff
    phyMod (if core == 0 then 0x8f else 0xa5) 0x100 0x100
    phyWrite (if core == 0 then 0xaa else 0xab) dacGain
    tableWrite cfg 7 (0x110 + core.toUInt32) 16 #[radGain]
    -- m1m2 in the IQLOCAL table, entry 87.
    tableRead1 cfg 0 15 87 16
    andi 0 (if core == 0 then 0x00ff else 0xff00)
    ori 0 (if core == 0 then bbmult <<< 8 else bbmult)
    tableWriteR 15 87 16 0
    if ipa cfg then
      tableRead1 cfg 1 (if core == 0 then 26 else 27) (576 + txpi.toUInt32) 32
      shli 1 4
      phyModR (if core == 0 then 0x297 else 0x29b) ((0x1ff : UInt32) <<< 4) 1
      phyMod (if core == 0 then 0x297 else 0x29b) 0x4 0x4
  phyAnd 0xbf (~~~0x1f &&& 0xffff)

/-- `wlc_phy_ipa_internal_tssi_setup_nphy` (phy_n.c:17059-17159), radio 2056. -/
def wlcPhyIpaInternalTssiSetupNphy (cfg : PhyCfg) : ProgM Unit := do
  radioWrite 0x1f 0x128      -- SYN RESERVED_ADDR31 (2 GHz)
  radioWrite 0x1e 0x0        -- SYN RESERVED_ADDR30
  radioWrite 0x20 0x29       -- SYN GPIO_MASTER1
  for tx in [0x2000, 0x3000] do
    let t : UInt32 := tx.toUInt32
    radioWrite (t ||| 0x29) 0x0   -- IQCAL_VCM_HG
    radioWrite (t ||| 0x2a) 0x0   -- IQCAL_IDAC
    radioWrite (t ||| 0x2b) 0x3   -- TSSI_VCM
    radioWrite (t ||| 0x2c) 0x0   -- TX_AMP_DET
    radioWrite (t ||| 0x30) 0x8   -- TSSI_MISC1
    radioWrite (t ||| 0x31) 0x0   -- TSSI_MISC2
    radioWrite (t ||| 0x32) 0x0   -- TSSI_MISC3
    radioWrite (t ||| 0x28) 0x5   -- TX_SSI_MASTER
    if cfg.radioRev != 5 then radioWrite (t ||| 0x2e) 0x0  -- TSSIA
    radioWrite (t ||| 0x2f) (if cfg.phyRev >= 5 then 0x31 else 0x11)  -- TSSIG
    radioWrite (t ||| 0x2d) 0xe   -- TX_SSI_MUX

/-- `wlc_phy_rfctrl_override_nphy` (phy_n.c:17162-17300), rev 3..6 branch,
for the `field = 1 << 13` (rssi/tssi aux override) case used here. -/
def rfctrlOverrideTssi (value : UInt32) (coreMask : Nat) (off : Bool) : ProgM Unit := do
  for core in [0:2] do
    let enAddr : UInt32 := if core == 0 then 0xe7 else 0xec
    let valAddr : UInt32 := if core == 0 then 0x7c else 0x7f
    if off then
      phyAnd enAddr (~~~0x2000 &&& 0xffff)
      phyAnd valAddr 0x0
    else if coreMask == 0 || (coreMask >>> core) % 2 == 1 then
      phyOr enAddr 0x2000
      phyMod valAddr 0xffff value

/-- `wlc_phy_stopplayback_nphy` (phy_n.c:23177-23216) for rev < 7. With
`restoreBbMult`, the saved bb multiplier is written back to IQLOCAL[87];
see `wlcPhyTxpwrctrlIdleTssiNphy` for why it is re-read here. Uses r0–r1. -/
def wlcPhyStopplaybackNphy (cfg : PhyCfg) (restoreBbMult : Bool) : ProgM Unit := do
  phyRead 0 0xc7
  mov 1 0
  andi 1 0x1
  let notSample ← newLabel
  let done ← newLabel
  emit (.branch .eq 1 (.imm 0) notSample)
  phyOr 0xc3 0x0002                 -- NPHY_sampleCmd_STOP
  emit (.jump done)
  place notSample
  andi 0 0x2
  emit (.branch .eq 0 (.imm 0) done)
  phyAnd 0xc2 0x7fff                -- ~NPHY_iqloCalCmdGctl_IQLO_CAL_EN
  place done
  phyAnd 0xc3 (~~~0x4 &&& 0xffff)
  if restoreBbMult then
    tableRead1 cfg 0 15 87 16
    tableWriteR 15 87 16 0

/-- `wlc_phy_tx_tone_nphy(pi, 4000, 0, 0, 0, false)` (phy_n.c:23159-23175) with
`wlc_phy_gen_load_samples_nphy` (23030-23076), `wlc_phy_loadsampletable_nphy`
(23004-23028) and `wlc_phy_runsamples_nphy` (23078-23157), 20 MHz, rev < 7.
`max_val = 0` makes every CORDIC sample 0, so the 160-entry sample table is
all zeros (no CORDIC needed). The bb multiplier save (`nphy_bb_mult_save`) is
a table read whose value is restored by `wlc_phy_stopplayback_nphy`. -/
def txToneIdle (cfg : PhyCfg) : ProgM Unit := do
  let numSamps : UInt32 := (20 : UInt32) <<< 3
  li 0 0
  tableFill32R 17 0 numSamps 0 0 1           -- NPHY_TBL_ID_SAMPLEPLAY
  -- runsamples(num_samps, 0xffff, 0, iqmode 0, dac_test_mode 0, false)
  tableRead1 cfg 0 15 87 16                   -- bb_mult save (value unused)
  phyWrite 0xc6 (numSamps - 1)
  phyWrite 0xc4 0xffff
  phyWrite 0xc5 0
  phyRead 2 0xa1
  phyOr 0xa1 0x0001
  phyWrite 0xc3 0x1
  spinWhilePhySet 0xa4 0x1 1000 0 1
  phyWriteR 0xa1 2

/-- `wlc_phy_rssisel_nphy` (phy_n.c:21631-21850), rev ≥ 3, for
`RADIO_MIMO_CORESEL_OFF` or ALLRX with `NPHY_RSSI_SEL_TSSI_2G`, including
`brcms_phy_wr_tx_mux` (21592-21629, IPA 2 GHz rev < 7: TX_SSI_MUX = 0xe). -/
def rssiselTssi2g (on : Bool) : ProgM Unit := do
  if !on then
    phyMod 0x8f 0x200 0
    phyMod 0xa5 0x200 0
    phyMod 0xa6 0x300 0
    phyMod 0xa7 0x300 0
    phyMod 0xe5 0x20 0
    phyMod 0xe6 0x20 0
    phyMod 0xf9 0x3c 0
    phyMod 0xfb 0x3c 0
  else
    for core in [0:2] do
      let afeOvr : UInt32 := if core == 0 then 0x8f else 0xa5
      let afeCore : UInt32 := if core == 0 then 0xa6 else 0xa7
      phyMod afeOvr 0x200 0x200
      phyMod afeCore 0x300 0x300
      phyMod afeCore 0xc00 0xc00
      radioWrite (0x2d ||| (if core == 0 then 0x2000 else 0x3000)) 0xe
      phyMod afeOvr 0x200 0x200

/-- `wlc_phy_poll_rssi_nphy(pi, NPHY_RSSI_SEL_TSSI_2G, buf, 1)`
(phy_n.c:21852-21934), rev ≥ 3. Only the two bytes `wlc_phy_init_nphy`
consumes are formed: r8 = `(int_val >> 24) & 0xff` (core 0 TSSI) and
r9 = `(int_val >> 8) & 0xff` (core 1 TSSI). Uses r0–r9. -/
def pollTssi2g : ProgM Unit := do
  let saves : Array UInt32 := #[0xa6, 0xa7, 0xf9, 0xfb, 0x8f, 0xa5, 0xe5, 0xe6]
  for h : k in [0:saves.size] do
    phyRead k saves[k]
  rssiselTssi2g true
  phyRead 8 0xca                     -- gpiosel_orig (only rewritten for rev < 2)
  phyRead 8 0x219
  phyRead 9 0x21a
  for h : k in [0:saves.size] do
    phyWriteR saves[k] k
  sext6to8 8 0
  sext6to8 9 0

/-- `wlc_phy_txpwrctrl_idle_tssi_nphy` (phy_n.c:17405-17466), rev 3..6, IPA,
2.4 GHz. Leaves the core 0 / core 1 idle TSSI (u8) in **r8 / r9** for
`wlcPhyTxpwrctrlPwrSetupNphy`.

bb multiplier: `wlc_phy_runsamples_nphy` saves IQLOCAL[87] into
`nphy_bb_mult_save` and the second `wlc_phy_stopplayback_nphy` writes it back.
Nothing between those two points writes IQLOCAL (modify_bbmult is false), so
the port re-reads the entry at restore time instead of holding it in a
register through the ten-register TSSI poll; the write sequence is the same. -/
def wlcPhyTxpwrctrlIdleTssiNphy (cfg : PhyCfg) : ProgM Unit := do
  if ipa cfg then wlcPhyIpaInternalTssiSetupNphy cfg
  rfctrlOverrideTssi 0 3 false
  wlcPhyStopplaybackNphy cfg false   -- nphy_bb_mult_save == 0 on entry
  txToneIdle cfg
  delay 20
  pollTssi2g
  -- r8/r9 hold the result; the steps below use r0–r1 and accessor registers.
  wlcPhyStopplaybackNphy cfg true
  rssiselTssi2g false
  rfctrlOverrideTssi 0 3 true

/-- Round-to-nearest signed division (`DIV_ROUND_CLOSEST`, C truncation). -/
def divRoundClosest (x d : Int) : Int :=
  if (x > 0) == (d > 0) then (x + d.tdiv 2).tdiv d else (x - d.tdiv 2).tdiv d

/-- Signed 16-bit SROM word at byte offset `off`. -/
def srom16s (cfg : PhyCfg) (off : Nat) : Int :=
  let v := (cfg.srom16 off).toNat
  if v >= 0x8000 then (v : Int) - 0x10000 else v

/-- `pwrdet_2g_{a1,b0,b1}` for `core` (SROM rev 8 `pa_2g[0..2]`). -/
def pwrdet2g (cfg : PhyCfg) (core : Nat) : Int × Int × Int :=
  let base := if core == 0 then 0xC0 else 0xE0
  (srom16s cfg (base + 2), srom16s cfg (base + 4), srom16s cfg (base + 6))

/-- The 64-entry TSSI→power estimate table of `wlc_phy_txpwrctrl_pwr_setup_nphy`
for `core` (rev ≥ 3: no idle-TSSI clamp), as 32-bit two's complement words. -/
def pwrEstTable (cfg : PhyCfg) (core : Nat) : Array UInt32 := Id.run do
  let (a1, b0, b1) := pwrdet2g cfg core
  let mut out := #[]
  for idx in [0:64] do
    let i : Int := idx
    let num := 8 * (16 * b0 + b1 * i)
    let den := 32768 + a1 * i
    let est := max (divRoundClosest (4 * num) den) (-8)
    out := out.push (est % 4294967296).toNat.toUInt32
  return out

/-- `wlc_phy_txpwrctrl_pwr_setup_nphy` (phy_n.c:17561-17769), core rev 23,
SROM rev 8, 2.4 GHz, rev 3..6, IPA. Expects the idle TSSI in r8 / r9. -/
def wlcPhyTxpwrctrlPwrSetupNphy (cfg : PhyCfg) : ProgM Unit := do
  phyOr 0x122 0x1
  phyAnd 0x1e7 0x7fff
  if cfg.fem2g &&& 1 != 0 then phyOr 0x1e9 0x4000     -- srom_fem2g.tssipos
  if ipa cfg then
    radioWrite (0x2d ||| 0x2000) 0xe                   -- TX0 TX_SSI_MUX
    radioWrite (0x2d ||| 0x3000) 0xe                   -- TX1 TX_SSI_MUX
  else
    radioWrite (0x2d ||| 0x2000) 0x11
    radioWrite (0x2d ||| 0x3000) 0x11
  phyMod 0x1e7 0x7f 0x40                               -- pwrIndex_init
  phyMod 0x222 0xff 0x40
  phyWrite 0x1e8 (((0x3 : UInt32) <<< 8) ||| 240)
  -- 0x1e9 = (1 << 15) | idle_tssi[0] | idle_tssi[1] << 8
  andi 8 0xff
  andi 9 0xff
  shli 9 8
  emit (.alu .or 8 (.reg 9))
  ori 8 0x8000
  phyWriteR 0x1e9 8
  let tgt : UInt32 := (txPowerMaxFirstInit % 256).toNat.toUInt32
  phyWrite 0x1ea (tgt ||| (tgt <<< 8))
  tableWrite cfg 26 0 32 (pwrEstTable cfg 0)
  tableWrite cfg 27 0 32 (pwrEstTable cfg 1)
  -- wlc_phy_txpwr_limit_to_tbl_nphy: all offsets are 0 on the first init.
  tableWrite cfg 26 64 8 adjPwrTblFirstInit
  tableWrite cfg 27 64 8 adjPwrTblFirstInit

/-- TX power control gain tables of `wlc_phy_init_nphy` (phy_n.c:19401-19480),
rev 3..6, IPA 2.4 GHz: the gain table at 192 and the per-index rf power
offsets (`nphy_papd_pga_gain_delta_ipa_2g[pga_gn]`) at 576 + idx. -/
def txpwrctrlGainTables (cfg : PhyCfg) : ProgM Unit := do
  let tbl ← ipaGainTbl cfg
  tableWrite cfg 26 192 32 tbl
  tableWrite cfg 27 192 32 tbl
  let delta ← checkedTable papdPgaGainDeltaIpa2g 16
  for h : idx in [0:tbl.size] do
    let pga := ((tbl[idx] >>> 24) &&& 0xf).toNat
    let off := delta.getD pga 0
    tableWrite cfg 26 (576 + idx.toUInt32) 32 #[off]
    tableWrite cfg 27 (576 + idx.toUInt32) 32 #[off]

/-- `wlc_phy_txpwrctrl_coeff_setup_nphy` (phy_n.c:18788-18857), rev ≥ 3:
IQ comp words at 320 and LO comp words at 448 of both tx power control
tables, from IQLOCAL[80..86]. -/
def wlcPhyTxpwrctrlCoeffSetupNphy (cfg : PhyCfg) : ProgM Unit := do
  -- iqloCalbuf[0..6] = IQLOCAL[80..86].
  -- r0..r3 = [0..3], r4 = [4] then overwritten by [5], r5 = [6].
  tableReadSeq cfg 15 80 16 #[0, 1, 2, 3, 4, 4, 5]
  -- iqcomp core 0 = ([0] & 0x3ff) << 10 | ([1] & 0x3ff): hi → r6, lo → r0
  andi 0 0x3ff
  andi 1 0x3ff
  mov 6 0
  shri 6 6
  shli 0 10
  emit (.alu .or 0 (.reg 1))
  andi 0 0xffff
  -- iqcomp core 1 from [2], [3]: hi → r7, lo → r2
  andi 2 0x3ff
  andi 3 0x3ff
  mov 7 2
  shri 7 6
  shli 2 10
  emit (.alu .or 2 (.reg 3))
  andi 2 0xffff
  tableFill32R 26 320 128 6 0 8
  tableFill32R 27 320 128 7 2 8
  -- locomp (rev ≥ 3: unscaled): ((i & 0xff) << 8) | (q & 0xff) == [5] / [6]
  li 1 0
  tableFill32R 26 448 128 1 4 8
  tableFill32R 27 448 128 1 5 8

/-- `wlc_phy_nphy_tkip_rifs_war` (phy_n.c:14334-14352) with
`wlc_phy_write_txmacreg_nphy`. -/
def wlcPhyNphyTkipRifsWar (_cfg : PhyCfg) (rifs : Bool) : ProgM Unit := do
  let (holdoff, dly) : UInt32 × UInt32 := if rifs then (0x10, 0x258) else (0x15, 0x320)
  phyWrite 0x77 holdoff
  phyWrite 0xb4 dly

/-- `wlc_phy_txlpfbw_nphy` (phy_n.c:18859-18893), rev 3..6, 20 MHz. -/
def wlcPhyTxlpfbwNphy (cfg : PhyCfg) : ProgM Unit := do
  if cfg.phyRev >= 3 && cfg.phyRev < 7 then
    let bw : UInt32 := if ipa cfg then 4 else 1
    phyWrite 0xe8 (bw ||| (bw <<< 3) ||| (bw <<< 6) ||| (bw <<< 9))
    if ipa cfg then
      let bw2 : UInt32 := 1
      phyWrite 0xe9 (bw2 ||| (bw2 <<< 3) ||| (bw2 <<< 6) ||| (bw2 <<< 9))

/-- `wlc_phy_spurwar_nphy` (phy_n.c:19024-19192), 2.4 GHz 20 MHz, first init.
With `gband_spurwar_en`: `adjust_rx_analpfbw` (18895-18921),
`adjust_min_noisevar(0, NULL)` (18923-18966) and `adjust_crsminpwr`
(18968-19022) only undo earlier adjustments, and nothing was adjusted
(40 MHz channel 11 only), so they write nothing. `gband_spurwar2_en` needs
BFL2_2G_SPUR_WAR and acts only at 40 MHz; otherwise it is the same no-op
reset. A-band workaround is 5 GHz only. Hence no register accesses. -/
def wlcPhySpurwarNphy (_cfg : PhyCfg) : ProgM Unit := pure ()

/-! ## wlc_phy_init_nphy -/

/-- `wlc_phy_init_nphy` (phy_n.c:19194-19546) for this board, first init.

The four calibration/table hooks are called exactly where brcmsmac calls
the corresponding code. About `txRxCal`: brcmsmac takes the `do_nphy_cal`
branch on the first init, but with `nphy_perical == PHY_PERICAL_MPHASE` (set
by `wlc_phy_stf_chain_upd_nphy`) it only *schedules* the multi-phase cal
(`wlc_phy_cal_perical(PHYINIT)` → phycal timer). The inline sequence
(`rssi_cal`, precal tx gain with `nphy_cal_orig_pwr_idx = fixTxPwrIndex`,
txiqlo, rxiq, savecal) is what the non-MPHASE branch does; `txRxCal` stands in
for either. Note the inline branch runs `wlc_phy_rssi_cal_nphy` a second time;
include it in `txRxCal` if that behaviour is wanted.
`wlc_phy_restorecal_nphy` / `wlc_phy_restore_rssical_nphy` are not reached on
the first init. `pi->use_int_tx_iqlo_cal_nphy` is true (IPA) and
`internal_tx_iqlo_cal_tapoff_intpa_nphy` false, for the calibration ports. -/
def initNphy (cfg : PhyCfg) (tblInit workarounds rssiCal txRxCal : ProgM Unit) :
    ProgM Unit := do
  -- chippkg 4717/4718, chip 5357 and 40 MHz spurwar2 branches: not this board.
  tblInit
  if cfg.phyRev >= 3 then
    phyWrite 0xe7 0
    phyWrite 0xec 0
    if cfg.phyRev >= 7 then
      phyWrite 0x342 0
      phyWrite 0x343 0
      phyWrite 0x346 0
      phyWrite 0x347 0
    phyWrite 0xe5 0
    phyWrite 0xe6 0
  else
    phyWrite 0xec 0
  phyWrite 0x91 0
  phyWrite 0x92 0
  if cfg.phyRev < 6 then
    phyWrite 0x93 0
    phyWrite 0x94 0
  phyAnd 0xa1 (~~~3 &&& 0xffff)
  if cfg.phyRev >= 3 then
    phyWrite 0x8f 0
    phyWrite 0xa5 0
  else
    phyWrite 0xa5 0
  if cfg.phyRev == 2 then phyMod 0xdc 0x00ff 0x3b
  else if cfg.phyRev < 2 then phyMod 0xdc 0x00ff 0x40
  phyWrite 0x203 32
  phyWrite 0x201 32
  phyWrite 0x20d (if cfg.boardFlags2 &&& 0x100 != 0 then 160 else 184)  -- BFL2_SKWRKFEM_BRD
  phyWrite 0x13a 200
  phyWrite 0x70 80
  phyWrite 0x1ff 48
  if cfg.phyRev < 8 then wlcPhyUpdateMimoconfigNphy cfg
  wlcPhyStfChainUpdNphy cfg
  if cfg.phyRev < 2 then
    phyWrite 0x180 0xaa8
    phyWrite 0x181 0x9a4
  if ipa cfg then
    for core in [0:2] do
      phyMod (if core == 0 then 0x297 else 0x29b) 0x1 0x1
      phyMod (if core == 0 then 0x298 else 0x29c) ((0x1ff : UInt32) <<< 7)
        ((papdEpsilonOffset <<< 7) &&& 0xffff)
    wlcPhyIpaSetTxDigiFiltsNphy cfg
  else
    -- wlc_phy_extpa_set_tx_digi_filts_nphy is not ported (non-IPA boards).
    fail Fail.unsupported
  workarounds
  phyclkFgc true
  phyRead 0 0x01
  mov 1 0
  ori 1 0x4000                    -- BBCFG_RESETCCA
  phyWriteR 0x01 1
  andi 0 (~~~0x4000 &&& 0xffff)
  phyWriteR 0x01 0
  phyclkFgc false
  macphyclkSet true
  paOverrideOff cfg
  wlcPhyForceRfseqNphy cfg .rx2tx
  wlcPhyForceRfseqNphy cfg .reset2rx
  paOverrideOn
  wlcPhyClassifierNphy cfg 0 0
  wlcPhyClipDetNphyRead cfg
  wlcPhyBphyInitNphy cfg          -- CHSPEC_IS2G
  -- tx_pwr_ctrl_state = nphy_txpwrctrl = PHY_TPC_HW_ON (attach, rev ≥ 3)
  wlcPhyTxpwrctrlEnableNphy cfg false
  wlcPhyTxpwrFixpowerNphy cfg
  wlcPhyTxpwrctrlIdleTssiNphy cfg
  wlcPhyTxpwrctrlPwrSetupNphy cfg
  if cfg.phyRev >= 3 then txpwrctrlGainTables cfg
  -- phyrxchain == 3: wlc_phy_rxcore_setstate_nphy not called.
  -- No mphase cal pending: wlc_phy_cal_perical_mphase_restart not called.
  rssiCal                          -- nphy_rssical_chanspec_2G == 0
  txRxCal                          -- do_nphy_cal (see doc comment)
  wlcPhyTxpwrctrlCoeffSetupNphy cfg
  wlcPhyTxpwrctrlEnableNphy cfg true
  wlcPhyNphyTkipRifsWar cfg rifsPhy
  if cfg.phyRev >= 3 && cfg.phyRev <= 6 then phyWrite 0x70 50
  wlcPhyTxlpfbwNphy cfg
  wlcPhySpurwarNphy cfg

end LeanOS.Wifi.NPhyInit
