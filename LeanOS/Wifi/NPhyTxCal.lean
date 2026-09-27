import LeanOS.Wifi.NPhyInit

/-
N-PHY transmit calibration for the BCM43224 programs: the TX half of the
`do_nphy_cal` block of `wlc_phy_init_nphy` (non-MPHASE branch):
`wlc_phy_precal_txgain_nphy`, `wlc_phy_get_tx_gain_nphy`,
`wlc_phy_cal_txiqlo_nphy(target_gain, fullcal = true, mphase = false)` and
`wlc_phy_savecal_nphy`.

Ported from Linux brcmsmac (ISC license), Copyright (c) 2010 Broadcom
Corporation; see drivers/net/wireless/broadcom/brcm80211/brcmsmac at Linux
commit fd179f8a05be3ccae366b9b96e176b51fbe54aab. The tone samples use
`cordic_calc_iq` from lib/math/cordic.c (Copyright (c) 2011 Broadcom
Corporation, ISC-style permission notice) at the same commit.

Scope: N-PHY rev 6, radio 2056 rev 11, 2.4 GHz, 20 MHz, IPA, two cores, on
the first `wlc_phy_init` after attach. Every revision/band/IPA branch is
decided while generating; any other configuration emits
`fail Fail.unsupported`.

## Attach-time / caller state assumed on entry
* `pi->phyhang_avoid = false` (rev 6), so no carrier-search bracketing except
  the unconditional one in `wlc_phy_cal_txiqlo_nphy`; `nphy_deaf_count = 0`.
* `pi->nphy_txpwrctrl = PHY_TPC_HW_OFF` (`wlc_phy_init_nphy` turned hardware
  power control off before the calibration block and nothing turns it on
  again before `wlc_phy_txpwrctrl_enable_nphy(tx_pwr_ctrl_state)` after it).
* `pi->nphy_txpwrindex[core].index = AUTO (-1)` (wlc_phy_attach_nphy) and
  `.AfectrlOverride = 0` (never assigned for rev >= 3).
* `pi->nphy_cal_orig_pwr_idx[core] = nphy_txpwrindex[core].index_internal = 40`
  (`wlc_phy_txpwr_fixpower_nphy`, rev 3..6: `NPhyInit.fixTxPwrIndex`).
* `pi->nphy_bb_mult_save = 0` (restored and cleared by the idle-TSSI
  playback of `wlc_phy_init_nphy`; the RSSI cal does not play samples).
* `pi->use_int_tx_iqlo_cal_nphy = true` (IPA),
  `internal_tx_iqlo_cal_tapoff_intpa_nphy = false`,
  `mphase_cal_phase_id = MPHASE_CAL_STATE_IDLE`,
  `nphy_txiqlocal_coeffsvalid = false` (irrelevant: fullcal).
* SROM `fem2g.extpagain = 2` (IPA) — the extpagain == 3 floor of 50 in
  `wlc_phy_cal_txgainctrl_nphy` is not taken.

## Run-time state in scratch RAM (region 0x5400–0x57FF, see `Scratch`)
brcmsmac `pi->` fields written here and read later by this module live at
fixed scratch addresses; `nphy_txcal_bbmult`, `tx_rx_cal_*_saveregs`,
`classifier_state`, `clip_state`, `nphy_bb_mult_save`, `nphy_txiqlocal_bestc`
and the `calibration_cache` fields written by `wlc_phy_savecal_nphy`. The
target TX gain (`struct nphy_txgains`) is written to 0x5C00–0x5C13.

## Registers
r0–r9 are clobbered; nothing is kept in registers across the top-level defs.
`precalAndTxiqlo` leaves r0 = 0 on success and r0 = -EIO (0xFFFFFFFB) when the
IQ/LO calibration engine did not finish a command (brcmsmac's `WARN` +
`return -EIO`, which also skips the cleanup exactly like brcmsmac).
Subroutines nest at most two calls deep below the top-level def.
-/
namespace LeanOS.Wifi.NPhyTxCal

open LeanOS.Wifi.Bytecode LeanOS.Wifi.Bcm43224 LeanOS.Wifi.NPhy
open LeanOS.Wifi.NPhyInit (tableRead1 tableReadSeq spinWhilePhySet phyclkFgc
  wlcPhyForceRfseqNphy wlcPhyStopplaybackNphy rssiselTssi2g txpwrctrlOff
  wlcPhyClassifierNphy fixTxPwrIndex Rfseq)

/-! ## Diagnostics -/

namespace Fail
/-- The configuration asks for a path this port does not carry. -/
def unsupported : UInt32 := 0x7EB0
/-- A generation-time table (tone samples) failed its length check. -/
def badTable : UInt32 := 0x7EB1
end Fail

namespace Tag
/-- `wlc_phy_rfctrlintc_override_nphy` WARN "HW error: override failed"
(value: the 0x78 bit that stayed set). -/
def overrideFailed : UInt32 := 0x0460
/-- `wlc_phy_cal_txiqlo_nphy` WARN "HW error: txiq calib" (value: the cal
command that did not complete). -/
def txiqCalTimeout : UInt32 := 0x0461
end Tag

/-- `-EIO` as the 32-bit value left in r0 on a calibration-engine timeout. -/
def errEio : UInt32 := 0xFFFFFFFB

/-! ## Constants (phyreg_n.h, phy_radio.h, phy_n.c, brcmu_wifi.h) -/

def tblIdRfseq : UInt32 := 7
def tblIdAfeCtrl : UInt32 := 8
def tblIdIqlocal : UInt32 := 15
def tblIdSamplePlay : UInt32 := 17
def tblIdCore1TxPwrCtl : UInt32 := 26
def tblIdCore2TxPwrCtl : UInt32 := 27

/-- RADIO_2056_TX0 / TX1 block selectors. -/
def radioTx (core : Nat) : UInt32 := if core == 0 then 0x2000 else 0x3000
def r2056TxLoftFineI : UInt32 := 0x21
def r2056TxLoftFineQ : UInt32 := 0x22
def r2056TxLoftCoarseI : UInt32 := 0x23
def r2056TxLoftCoarseQ : UInt32 := 0x24
def r2056TxSsiMaster : UInt32 := 0x28
def r2056TxIqcalVcmHg : UInt32 := 0x29
def r2056TxIqcalIdac : UInt32 := 0x2a
def r2056TxTssiVcm : UInt32 := 0x2b
def r2056TxAmpDet : UInt32 := 0x2c
def r2056TxSsiMux : UInt32 := 0x2d
def r2056TxTssia : UInt32 := 0x2e
def r2056TxTssig : UInt32 := 0x2f
def r2056TxTssiMisc1 : UInt32 := 0x30
def r2056TxTssiMisc2 : UInt32 := 0x31
def r2056TxTssiMisc3 : UInt32 := 0x32

/-- The eleven TX radio registers saved by `wlc_phy_txcal_radio_setup_nphy`,
in `tx_rx_cal_radio_saveregs[core * 11 + k]` order. -/
def txcalRadioRegs : Array UInt32 := #[r2056TxSsiMaster, r2056TxIqcalVcmHg,
  r2056TxIqcalIdac, r2056TxTssiVcm, r2056TxAmpDet, r2056TxSsiMux, r2056TxTssia,
  r2056TxTssig, r2056TxTssiMisc1, r2056TxTssiMisc2, r2056TxTssiMisc3]

/-- NPHY_N_GCTL (phy_n.c:129). -/
def nphyNGctl : UInt32 := 0x66
/-- NPHY_CAL_TSSISAMPS (phy_n.c:155). -/
def calTssiSamps : UInt32 := 64
/-- BBCFG_RESETCCA (d11.h). -/
def bbcfgResetCca : UInt32 := 0x4000
/-- `ncorr[]` of `wlc_phy_iqcal_gainparams_nphy` for rev >= 3. -/
def iqcalNcorr : UInt32 := 0x79

/-- `tbl_tx_iqlo_cal_cmds_fullcal_nphyrev3` (phy_n.c, `wlc_phy_cal_txiqlo_nphy`). -/
def calCmdsFullcalRev3 : Array UInt32 :=
  #[0x8434, 0x8334, 0x8084, 0x8267, 0x8056, 0x8234,
    0x9434, 0x9334, 0x9084, 0x9267, 0x9056, 0x9234]
/-- `ARRAY_SIZE(tbl_tx_iqlo_cal_startcoefs_nphyrev3)` = ARRAY_SIZE(nphy_txiqlocal_bestc). -/
def startCoefsLen : Nat := 11

/-- `ladder_lo` / `ladder_iq` of `wlc_phy_update_txcal_ladder_nphy`
as (percent, g_env). -/
def ladderLo : Array (UInt32 × UInt32) := #[(3, 0), (4, 0), (6, 0), (9, 0), (13, 0),
  (18, 0), (25, 0), (25, 1), (25, 2), (25, 3), (25, 4), (25, 5), (25, 6), (25, 7),
  (35, 7), (50, 7), (71, 7), (100, 7)]
def ladderIq : Array (UInt32 × UInt32) := #[(3, 0), (4, 0), (6, 0), (9, 0), (13, 0),
  (18, 0), (25, 0), (35, 0), (50, 0), (71, 0), (100, 0), (100, 1), (100, 2), (100, 3),
  (100, 4), (100, 5), (100, 6), (100, 7)]

/-- `dBm_targetpower` passed by `wlc_phy_precal_txgain_nphy` (rev 6, IPA, 2 GHz). -/
def precalTargetDbm : Int := 12
/-- `stepsize` of `wlc_phy_cal_txgainctrl_nphy` for rev < 7. -/
def gainctrlStep : UInt32 := 1
/-- Tone of the gain control and IQ/LO calibration (20 MHz): 2500 kHz, amplitude 250. -/
def toneKHz : Nat := 2500
def toneAmpl : Nat := 250

/-- brcmsmac chanspec of a 2.4 GHz 20 MHz channel:
WL_CHANSPEC_BAND_2G | WL_CHANSPEC_BW_20 | WL_CHANSPEC_CTL_SB_NONE | channel. -/
def chanspec (cfg : PhyCfg) : UInt32 := 0x2000 ||| 0x0800 ||| 0x0300 ||| cfg.channel.toUInt32

/-! ## Scratch layout (0x5400–0x57FF, plus the shared target gain at 0x5C00) -/

namespace Scratch
/-- `phy_saveregs[0..3]` of `wlc_phy_cal_txgainctrl_nphy` (0x91 0x92 0xe7 0xec). -/
def gainctrlSave : UInt32 := 0x5400
/-- `orig_BBConfig` of `wlc_phy_cal_txgainctrl_nphy`. -/
def origBbConfig : UInt32 := 0x5408
/-- `m0m1` of `wlc_phy_cal_txgainctrl_nphy`. -/
def m0m1 : UInt32 := 0x540A
/-- Running `txpwrindex` of `wlc_phy_cal_txgainctrl_nphy` (clamped 0..127). -/
def txpwrIndex : UInt32 := 0x540C
/-- `pi->nphy_txcal_pwr_idx[0..1]`. -/
def txcalPwrIdx : UInt32 := 0x5410
/-- `pi->nphy_txcal_bbmult`. -/
def txcalBbmult : UInt32 := 0x5414
/-- `pi->nphy_bb_mult_save & BB_MULT_MASK` (validity is tracked while generating). -/
def bbMultSave : UInt32 := 0x5416
/-- `pi->classifier_state`, `pi->clip_state[0..1]`. -/
def classifierState : UInt32 := 0x5418
def clipState : UInt32 := 0x541A
/-- `gain_save[0..1]` of `wlc_phy_cal_txiqlo_nphy`. -/
def gainSave : UInt32 := 0x5420
/-- `diq_start` of `wlc_phy_cal_txiqlo_nphy` (kept for fidelity; unused). -/
def diqStart : UInt32 := 0x5424
/-- `pi->nphy_txiqlocal_coeffsvalid` (u16 flag) and `nphy_txiqlocal_chanspec`. -/
def txiqlocalValid : UInt32 := 0x5426
def txiqlocalChanspec : UInt32 := 0x5428
/-- Saved PHY registers of `wlc_phy_poll_rssi_nphy` (8 × u16). -/
def pollSave : UInt32 := 0x5430
/-- `pi->tx_rx_cal_radio_saveregs[0..21]` (22 × u16). -/
def radioSave : UInt32 := 0x5440
/-- `pi->tx_rx_cal_phy_saveregs[0..10]` (11 × u16). -/
def phySave : UInt32 := 0x5470
/-- `tbl_buf[0..10]` of `wlc_phy_cal_txiqlo_nphy`. -/
def tblBuf : UInt32 := 0x5490
/-- `pi->nphy_txiqlocal_bestc[0..10]`. -/
def bestc : UInt32 := 0x54B0
/-- `pi->nphy_txpwrindex[core]` save fields written on the first
`wlc_phy_txpwr_index_nphy` for the core: AfeCtrlDacGain, rad_gain, bbmult,
iqcomp_a, iqcomp_b, locomp (6 × u16 per core, core 1 at +12). -/
def txpwrIndexSave : UInt32 := 0x54D0
/-- `pi->calibration_cache` fields written by `wlc_phy_savecal_nphy`:
`rxcal_coeffs_2G` (a0 b0 a1 b1), `txcal_radio_regs_2G[0..7]`,
`txcal_coeffs_2G[0..7]`, and `nphy_iqcal_chanspec_2G`. -/
def rxcalCoeffs2G : UInt32 := 0x5500
def txcalRadioRegs2G : UInt32 := 0x5508
def txcalCoeffs2G : UInt32 := 0x5518
def iqcalChanspec2G : UInt32 := 0x5528
/-- Shared `struct nphy_txgains` (txlpf[2] txgm[2] pga[2] pad[2] ipa[2], u16 LE). -/
def targetGain : UInt32 := 0x5C00
def tgTxlpf : UInt32 := targetGain
def tgTxgm : UInt32 := targetGain + 4
def tgPga : UInt32 := targetGain + 8
def tgPad : UInt32 := targetGain + 12
def tgIpa : UInt32 := targetGain + 16
/-- The byte ranges this module may write. -/
def regions : List (Nat × Nat) := [(0x5400, 0x5800), (0x5C00, 0x5C14)]
end Scratch

/-! ## Small bytecode helpers -/

/-- Store the low 16 bits of `src` at scratch `off` (uses r12 as a zero base). -/
def stS (off : UInt32) (src : Reg) : ProgM Unit := do
  li 12 0
  emit (.memStore 2 12 off (.reg src))

/-- Store an immediate u16 at scratch `off`. -/
def stSi (off v : UInt32) : ProgM Unit := do
  li 12 0
  emit (.memStore 2 12 off (.imm v))

/-- Load the u16 at scratch `off` into `dst` (uses r12 as a zero base). -/
def ldS (dst : Reg) (off : UInt32) : ProgM Unit := do
  li 12 0
  emit (.memLoad 2 dst 12 off)

/-- Clamp the signed value in `r` to `lo..hi`. -/
def clampS (r : Reg) (lo hi : UInt32) : ProgM Unit := do
  let geLo ← newLabel
  let leHi ← newLabel
  emit (.branch .ges r (.imm lo) geLo)
  li r lo
  place geLo
  emit (.branch .lts r (.imm (hi + 1)) leHi)
  li r hi
  place leHi

/-- Sign-extend the 6-bit field in the low bits of `r` to 32 bits
(`((s8)((x & 0x3f) << 2)) >> 2`). -/
def sext6 (r : Reg) : ProgM Unit := do
  andi r 0x3f
  shli r 26
  emit (.alu .sar r (.imm 26))

/-- `wlc_phy_table_read_nphy` of one 32-bit element whose full table address
(`id << 10 | offset`) is in register `a` (43224 rev-1 read quirk included).
`dst := hi << 16 | lo`; uses `tmp`. -/
def tableRead32AtR (dst a tmp : Reg) : ProgM Unit := do
  phyWriteR tblAddr a
  phyRead tmp tblDataLo          -- 43224 rev 1: dummy read, then re-address
  phyWriteR tblAddr a
  phyRead tmp tblDataLo
  phyRead dst tblDataHi
  shli dst 16
  emit (.alu .or dst (.reg tmp))

/-- `wlc_phy_table_read_nphy(pi, id, n, offset, 16, buf)` into scratch
`buf[0..n-1]` (43224 rev-1 read quirk included). Uses r0 and r9. -/
def tableReadToScratch (cfg : PhyCfg) (id offset : UInt32) (n : Nat) (buf : UInt32) :
    ProgM Unit := do
  phyWrite tblAddr ((id <<< 10) ||| offset)
  for k in [0:n] do
    if cfg.chipRev == 1 then
      phyRead 9 tblDataLo
      phyWrite tblAddr ((id <<< 10) ||| (offset + k.toUInt32))
    phyRead 0 tblDataLo
    stS (buf + 2 * k.toUInt32) 0

/-- `wlc_phy_table_write_nphy(pi, id, n, offset, 16, buf)` from scratch
`buf[0..n-1]`. Uses r0. -/
def tableWriteFromScratch (id offset : UInt32) (n : Nat) (buf : UInt32) : ProgM Unit := do
  phyWrite tblAddr ((id <<< 10) ||| offset)
  for k in [0:n] do
    ldS 0 (buf + 2 * k.toUInt32)
    phyWriteR tblDataLo 0

/-- `wlc_phy_table_write_nphy(pi, id, regs.size, offset, 16, ...)` from registers. -/
def tableWriteRegs (id offset : UInt32) (regs : Array Reg) : ProgM Unit := do
  phyWrite tblAddr ((id <<< 10) ||| offset)
  for r in regs do phyWriteR tblDataLo r

/-- Emit `jump over; place l; body; ret; over:` and return `l`. -/
def subroutine (body : ProgM Unit) : ProgM Nat := do
  let over ← newLabel
  let l ← newLabel
  emit (.jump over)
  place l
  body
  emit .ret
  place over
  return l

/-! ## CORDIC tone samples (generation time)

`wlc_phy_gen_load_samples_nphy` computes its samples from generation-time
values only (`f_kHz`, `max_val`, bandwidth), so the sample table is computed
here with an exact integer model of `cordic_calc_iq` and carried in the blob. -/

/-- `arctan_table` of lib/math/cordic.c. -/
def cordicArctan : Array Int := #[2949120, 1740967, 919879, 466945, 234379, 117304,
  58666, 29335, 14668, 7334, 3667, 1833, 917, 458, 229, 115, 57, 29]

/-- CORDIC_FIXED / CORDIC_FLOAT (include/linux/cordic.h). -/
def cordicFixed (x : Int) : Int := x * 65536
def cordicFloat (x : Int) : Int :=
  if x >= 0 then Int.fdiv (Int.fdiv x 32768 + 1) 2
  else -(Int.fdiv (Int.fdiv (-x) 32768 + 1) 2)

/-- `cordic_calc_iq(theta)` (lib/math/cordic.c), theta in degrees; returns
(i, q) scaled by 2^16. C `%` truncates (`Int.tmod`), `>>` of a negative s32
is arithmetic (`Int.fdiv` by a power of two). -/
def cordicCalcIq (theta0 : Int) : Int × Int := Id.run do
  let mut ci : Int := 39797      -- CORDIC_ANGLE_GEN
  let mut cq : Int := 0
  let mut angle : Int := 0
  let mut theta := cordicFixed theta0
  let signtheta : Int := if theta < 0 then -1 else 1
  theta := Int.tmod (theta + cordicFixed 180 * signtheta) (cordicFixed 360) -
    cordicFixed 180 * signtheta
  let mut signx : Int := 1
  if cordicFloat theta > 90 then
    theta := theta - cordicFixed 180
    signx := -1
  else if cordicFloat theta < -90 then
    theta := theta + cordicFixed 180
    signx := -1
  for iter in [0:18] do
    let p : Int := 2 ^ iter
    let at_ := cordicArctan.getD iter 0
    let valtmp := if theta > angle then ci - Int.fdiv cq p else ci + Int.fdiv cq p
    if theta > angle then
      cq := cq + Int.fdiv ci p
      angle := angle + at_
    else
      cq := cq - Int.fdiv ci p
      angle := angle - at_
    ci := valtmp
  return (ci * signx, cq * signx)

/-- The SAMPLEPLAY words of `wlc_phy_gen_load_samples_nphy(f_kHz, max_val, 0)`
at 20 MHz: `num_samps = 160`, `rot = ((f_kHz * 36) / 20) / 100` degrees,
word = `(i & 0x3ff) << 10 | (q & 0x3ff)` (`wlc_phy_loadsampletable_nphy`). -/
def toneSamples (fKHz maxVal : Nat) : Array UInt32 := Id.run do
  let phyBw := 20
  let numSamps := phyBw * 8
  let rot : Int := ((fKHz * 36) / phyBw / 100 : Nat)
  let mut theta : Int := 0
  let mut out := #[]
  for _ in [0:numSamps] do
    let (i, q) := cordicCalcIq theta
    theta := theta + rot
    let qv := cordicFloat (q * maxVal)
    let iv := cordicFloat (i * maxVal)
    let w := ((iv % 1024).toNat <<< 10) ||| (qv % 1024).toNat
    out := out.push w.toUInt32
  return out

/-- Little-endian bytes of 32-bit words (for the blob). -/
def wordsLE (ws : Array UInt32) : ByteArray := Id.run do
  let mut b := ByteArray.empty
  for w in ws do
    b := b.push w.toUInt8 |>.push (w >>> 8).toUInt8 |>.push (w >>> 16).toUInt8
      |>.push (w >>> 24).toUInt8
  return b

/-! ## Shared pieces -/

/-- `wlc_phy_resetcca_nphy` (phy_n.c:19550-19563). Uses r0–r2. -/
def wlcPhyResetccaNphy (cfg : PhyCfg) : ProgM Unit := do
  phyclkFgc true
  phyRead 0 0x01
  mov 1 0
  ori 1 bbcfgResetCca
  phyWriteR 0x01 1
  delay 1
  andi 0 (~~~bbcfgResetCca &&& 0xffff)
  phyWriteR 0x01 0
  phyclkFgc false
  wlcPhyForceRfseqNphy cfg .reset2rx

/-- `wlc_phy_stay_in_carriersearch_nphy(pi, true)` (phy_n.c:28545-28569) with
`nphy_deaf_count == 0` on entry: saves `classifier_state` and `clip_state`
to scratch. Uses r0–r2. -/
def carriersearchOn (cfg : PhyCfg) : ProgM Unit := do
  wlcPhyClassifierNphy cfg 0 0          -- returns new_ctl in r0
  stS Scratch.classifierState 0
  wlcPhyClassifierNphy cfg 0x7 4
  phyRead 0 0x2c                        -- wlc_phy_clip_det_nphy(pi, 0, clip_state)
  stS Scratch.clipState 0
  phyRead 0 0x42
  stS (Scratch.clipState + 2) 0
  phyWrite 0x2c 0xffff                  -- wlc_phy_clip_det_nphy(pi, 1, clip_off)
  phyWrite 0x42 0xffff
  wlcPhyResetccaNphy cfg

/-- `wlc_phy_stay_in_carriersearch_nphy(pi, false)` bringing `nphy_deaf_count`
back to 0: `wlc_phy_classifier_nphy(pi, 7, classifier_state)` and
`wlc_phy_clip_det_nphy(pi, 1, clip_state)`. Uses r0–r1. -/
def carriersearchOff : ProgM Unit := do
  phyRead 0 0xb0                        -- curr_ctl (fully replaced by mask 7)
  ldS 1 Scratch.classifierState
  andi 1 0x7
  phyModR 0xb0 0x7 1
  ldS 0 Scratch.clipState
  phyWriteR 0x2c 0
  ldS 0 (Scratch.clipState + 2)
  phyWriteR 0x42 0

/-- `wlc_phy_rfctrlintc_override_nphy` (phy_n.c:18034-18266) fields used here. -/
inductive IntcField where
  | trsw | pa

/-- `wlc_phy_rfctrlintc_override_nphy(pi, field, value, core_code)` for
rev 3..6, 2.4 GHz. `cores` lists the cores selected by `core_code`
(CORE1 → [0], CORE2 → [1], CORE1|CORE2 → [0, 1]). The TRSW WARN
"override failed" returns from the function, as in brcmsmac. Uses r0–r1. -/
def rfctrlintcOverride (field : IntcField) (value : UInt32) (cores : List Nat) :
    ProgM Unit := do
  let out ← newLabel
  for core in cores do
    let rIntc : UInt32 := if core == 0 then 0x91 else 0x92
    phyMod rIntc 0x400 0x400
    match field with
    | .pa => phyMod rIntc 0x10 (value <<< 4)
    | .trsw =>
      let rOvr : UInt32 := if core == 0 then 0xe7 else 0xec
      let bit : UInt32 := if core == 0 then 0x1 else 0x2
      phyMod rIntc 0x3c0 (value <<< 6)
      phyMod rOvr 0x1 0x1
      phyMod 0x78 bit bit
      spinWhilePhySet 0x78 bit 10000 0 1
      phyRead 0 0x78
      andi 0 bit
      let ok ← newLabel
      emit (.branch .eq 0 (.imm 0) ok)
      printImm Tag.overrideFailed bit
      emit (.jump out)
      place ok
      phyMod rOvr 0x1 0x0
  place out

/-- `wlc_phy_runsamples_nphy(pi, 160, 0xffff, 0, iqmode, 0, false)`
(phy_n.c:23078-23157), rev < 7, 20 MHz, `phyhang_avoid` false. With
`nphy_bb_mult_save` invalid on entry (always the case here), IQLOCAL[87] is
read; when `keepBbMult` the value is stored at `Scratch.bbMultSave` for the
matching `wlc_phy_stopplayback_nphy`, otherwise the caller clears
`nphy_bb_mult_save` before stopping (as `wlc_phy_cal_txgainctrl_nphy` does).
Uses r0–r2. -/
def runsamples (cfg : PhyCfg) (iqmode keepBbMult : Bool) : ProgM Unit := do
  let numSamps : UInt32 := 20 * 8
  tableRead1 cfg 0 tblIdIqlocal 87 16
  if keepBbMult then stS Scratch.bbMultSave 0
  phyWrite 0xc6 (numSamps - 1)
  phyWrite 0xc4 0xffff                     -- loops == 0xffff
  phyWrite 0xc5 0
  phyRead 2 0xa1
  phyOr 0xa1 0x0001                        -- NPHY_RfseqMode_CoreActv_override
  if iqmode then
    phyAnd 0xc2 0x7fff
    phyOr 0xc2 0x8000
  else
    phyWrite 0xc3 0x1
  spinWhilePhySet 0xa4 0x1 1000 0 1
  phyWriteR 0xa1 2

/-! ## Subroutines -/

structure Subs where
  /-- `wlc_phy_txpwrctrl_enable_nphy(pi, PHY_TPC_HW_OFF)`. -/
  tpcOff : Nat
  /-- `wlc_phy_txpwr_index_nphy(pi, 1 << core, r1, true)` main part, per core. -/
  txpwrIndex : Array Nat
  /-- `wlc_phy_gen_load_samples_nphy(pi, 2500, 250, 0)` table load. -/
  loadSamples : Nat
  /-- `wlc_phy_est_tonepwr_nphy(pi, qdBm, 64)`: r2 = qdBm[0], r3 = qdBm[1]. -/
  estTonePwr : Nat
  /-- `wlc_phy_update_txcal_ladder_nphy` with bbmult in r1. -/
  ladder : Nat
  /-- Copy IQLOCAL[96..106] → IQLOCAL[64..74] via `tbl_buf`. -/
  copyCoefs : Nat

/-- Main (index ≥ 0) part of `wlc_phy_txpwr_index_nphy(pi, 1 << core, r1,
restore_cals = true)` (phy_n.c:28295-28513), rev 3..6, IPA, with
`tx_pwr_ctrl_state = nphy_txpwrctrl = PHY_TPC_HW_OFF`. Input r1 = index
(0..127, preserved). Uses r0–r9; calls `tpcOff`. -/
def txpwrIndexBody (cfg : PhyCfg) (tpcOff : Nat) (core : Nat) : ProgM Unit := do
  let tbl : UInt32 := if core == 0 then tblIdCore1TxPwrCtl else tblIdCore2TxPwrCtl
  let c := core.toUInt32
  emit (.call tpcOff)
  -- txgain = CORExTXPWRCTL[192 + index]
  mov 2 1
  addi 2 ((tbl <<< 10) ||| 192)
  tableRead32AtR 3 2 9
  mov 4 3
  shri 4 16                                -- rad_gain (u16 of bits 16..32)
  mov 5 3
  shri 5 8
  andi 5 0x3f                              -- dac_gain
  mov 6 3
  andi 6 0xff                              -- bbmult
  phyMod (if core == 0 then 0x8f else 0xa5) 0x100 0x100
  phyWriteR (if core == 0 then 0xaa else 0xab) 5
  tableWriteR tblIdRfseq (0x110 + c) 16 4
  tableRead1 cfg 7 tblIdIqlocal 87 16      -- m1m2
  andi 7 (if core == 0 then 0x00ff else 0xff00)
  if core == 0 then shli 6 8
  emit (.alu .or 7 (.reg 6))
  tableWriteR tblIdIqlocal 87 16 7
  -- iqcomp = CORExTXPWRCTL[320 + index]
  mov 2 1
  addi 2 ((tbl <<< 10) ||| 320)
  tableRead32AtR 3 2 9
  mov 4 3
  shri 4 10
  andi 4 0x3ff                             -- iqcomp_a
  andi 3 0x3ff                             -- iqcomp_b
  tableWriteRegs tblIdIqlocal (80 + 2 * c) #[4, 3]
  -- locomp = CORExTXPWRCTL[448 + index]
  mov 2 1
  addi 2 ((tbl <<< 10) ||| 448)
  tableRead32AtR 3 2 9
  tableWriteR tblIdIqlocal (85 + c) 16 3
  -- PHY_IPA: rf power offset at 576 + index
  mov 2 1
  addi 2 ((tbl <<< 10) ||| 576)
  tableRead32AtR 3 2 9
  shli 3 4
  phyModR (if core == 0 then 0x297 else 0x29b) ((0x1ff : UInt32) <<< 4) 3
  phyMod (if core == 0 then 0x297 else 0x29b) 0x4 0x4
  emit (.call tpcOff)                      -- txpwrctrl_enable(tx_pwr_ctrl_state = OFF)

/-- The save branch of `wlc_phy_txpwr_index_nphy` taken on the first call
for a core (`nphy_txpwrindex[core].index < 0`), rev >= 3. The saved fields
go to `Scratch.txpwrIndexSave` (only the restore branch, `txpwrindex < 0`,
would read them; it is not reached here). Uses r0, r1, r9. -/
def txpwrIndexFirstSave (cfg : PhyCfg) (core : Nat) : ProgM Unit := do
  let c := core.toUInt32
  let base := Scratch.txpwrIndexSave + 12 * c
  -- AfectrlOverride is never assigned for rev >= 3: both writes use 0.
  phyMod 0x8f 0x100 0
  phyMod 0xa5 0x100 0
  phyRead 0 (if core == 0 then 0xaa else 0xab)
  stS base 0
  tableRead1 cfg 0 tblIdRfseq (0x110 + c) 16
  stS (base + 2) 0
  tableRead1 cfg 0 tblIdIqlocal 87 16
  if core == 0 then shri 0 8
  andi 0 0xff
  stS (base + 4) 0
  tableReadSeq cfg tblIdIqlocal (80 + 2 * c) 16 #[0, 1]
  stS (base + 6) 0
  stS (base + 8) 1
  tableRead1 cfg 0 tblIdIqlocal (85 + c) 16
  stS (base + 10) 0

/-- `wlc_phy_est_tonepwr_nphy(pi, qdBm_pwrbuf, NPHY_CAL_TSSISAMPS)`
(phy_n.c:24120-24163) with `wlc_phy_poll_rssi_nphy(pi, NPHY_RSSI_SEL_TSSI_2G,
buf, 64)` (21852-21945, rev >= 3). Only `rssi_buf[0]` and `rssi_buf[2]` are
consumed, so only those sums are formed. Output r2 = qdBm[0], r3 = qdBm[1]
(s32). Uses r0–r9. -/
def estTonePwrBody (_cfg : PhyCfg) : ProgM Unit := do
  -- idle_tssi from 0x1e9 (6-bit signed fields)
  phyRead 0 0x1e9
  mov 1 0
  sext6 1                                  -- idle_tssi[0]
  shri 0 8
  mov 2 0
  sext6 2                                  -- idle_tssi[1]
  -- wlc_phy_poll_rssi_nphy
  let saves : Array UInt32 := #[0xa6, 0xa7, 0xf9, 0xfb, 0x8f, 0xa5, 0xe5, 0xe6]
  for h : k in [0:saves.size] do
    phyRead 0 saves[k]
    stS (Scratch.pollSave + 2 * k.toUInt32) 0
  rssiselTssi2g true
  phyRead 0 0xca                           -- gpiosel_orig (rewritten only for rev < 2)
  li 3 0                                   -- rssi_buf[0]
  li 4 0                                   -- rssi_buf[2]
  li 5 calTssiSamps
  let top ← newLabel
  place top
  phyRead 6 0x219
  phyRead 7 0x21a
  sext6 6
  emit (.alu .add 3 (.reg 6))
  sext6 7
  emit (.alu .add 4 (.reg 7))
  emit (.alu .sub 5 (.imm 1))
  emit (.branch .ne 5 (.imm 0) top)
  for h : k in [0:saves.size] do
    ldS 0 (Scratch.pollSave + 2 * k.toUInt32)
    phyWriteR saves[k] 0
  -- tssival = rssi_buf / num_samps; pwrindex = idle - tssival + 64, clamped
  emit (.alu .sdiv 3 (.imm calTssiSamps))
  emit (.alu .sdiv 4 (.imm calTssiSamps))
  emit (.alu .sub 1 (.reg 3))
  addi 1 64
  clampS 1 0 63
  emit (.alu .sub 2 (.reg 4))
  addi 2 64
  clampS 2 0 63
  mov 6 1
  addi 6 (tblIdCore1TxPwrCtl <<< 10)
  tableRead32AtR 7 6 9
  mov 6 2
  addi 6 (tblIdCore2TxPwrCtl <<< 10)
  tableRead32AtR 8 6 9
  mov 2 7
  mov 3 8

/-- `wlc_phy_update_txcal_ladder_nphy` (phy_n.c:24165-24203) with the core's
bbmult (`nphy_txcal_bbmult` byte) in r1. Uses r2, r9–r10. -/
def ladderBody : ProgM Unit := do
  for h : k in [0:ladderLo.size] do
    let (pl, gl) := ladderLo[k]
    let (pq, gq) := ladderIq.getD k (0, 0)
    for (pct, genv, idx) in [(pl, gl, k.toUInt32), (pq, gq, k.toUInt32 + 32)] do
      li 2 pct
      emit (.alu .mul 2 (.reg 1))
      emit (.alu .udiv 2 (.imm 100))
      andi 2 0xff
      shli 2 8
      ori 2 genv
      tableWriteR tblIdIqlocal idx 16 2

/-- Install the subroutines (emits `jump over` blocks). -/
def installSubs (cfg : PhyCfg) : ProgM Subs := do
  let tpcOff ← subroutine (txpwrctrlOff cfg)
  let idx0 ← subroutine (txpwrIndexBody cfg tpcOff 0)
  let idx1 ← subroutine (txpwrIndexBody cfg tpcOff 1)
  let samples := toneSamples toneKHz toneAmpl
  if samples.size != 160 then fail Fail.badTable
  let blobOff ← addBlob "nphy-txcal-tone-2500k" (wordsLE samples)
  let loadSamples ← subroutine do
    -- wlc_phy_loadsampletable_nphy: SAMPLEPLAY[0..159], 32-bit (hi, lo)
    phyWrite tblAddr (tblIdSamplePlay <<< 10)
    li 1 0
    let top ← newLabel
    place top
    emit (.blobLoad32 2 1 blobOff)
    mov 3 2
    shri 3 16
    phyWriteR tblDataHi 3
    phyWriteR tblDataLo 2
    addi 1 1
    emit (.branch .ltu 1 (.imm samples.size.toUInt32) top)
  let est ← subroutine (estTonePwrBody cfg)
  let ladder ← subroutine ladderBody
  let copyCoefs ← subroutine do
    tableReadToScratch cfg tblIdIqlocal 96 startCoefsLen Scratch.tblBuf
    tableWriteFromScratch tblIdIqlocal 64 startCoefsLen Scratch.tblBuf
  return { tpcOff, txpwrIndex := #[idx0, idx1], loadSamples, estTonePwr := est, ladder,
           copyCoefs }

/-- `wlc_phy_tx_tone_nphy(pi, 2500, 250, iqmode, 0, false)` (phy_n.c:23159-23175);
`num_samps` is 160, so it always returns 0. Uses r0–r3. -/
def txTone (cfg : PhyCfg) (S : Subs) (iqmode keepBbMult : Bool) : ProgM Unit := do
  emit (.call S.loadSamples)
  runsamples cfg iqmode keepBbMult

/-- `wlc_phy_txpwr_index_nphy(pi, 1 << core, r1, true)`; `first` selects the
save branch of the core's first call. -/
def txpwrIndex (cfg : PhyCfg) (S : Subs) (core : Nat) (first : Bool) : ProgM Unit := do
  if first then
    mov 8 1
    txpwrIndexFirstSave cfg core
    mov 1 8
  emit (.call (S.txpwrIndex.getD core 0))

/-! ## Ported functions -/

/-- `wlc_phy_cal_txgainctrl_nphy(pi, 12, false)` (phy_n.c:18268-18427), rev 6,
20 MHz, 2.4 GHz, IPA (extpagain 2), `phyhang_avoid` false,
`nphy_cal_orig_pwr_idx[] = fixTxPwrIndex = 40`. -/
def wlcPhyCalTxgainctrlNphy (cfg : PhyCfg) (S : Subs) (dBmTarget : Int) : ProgM Unit := do
  let orig := (fixTxPwrIndex cfg).toUInt32
  li 1 orig
  txpwrIndex cfg S 0 true
  li 1 orig
  txpwrIndex cfg S 1 true
  let saveRegs : Array UInt32 := #[0x91, 0x92, 0xe7, 0xec]
  for h : k in [0:saveRegs.size] do
    phyRead 0 saveRegs[k]
    stS (Scratch.gainctrlSave + 2 * k.toUInt32) 0
  rfctrlintcOverride .pa 1 [0, 1]
  rfctrlintcOverride .trsw 0x2 [0]
  rfctrlintcOverride .trsw 0x8 [1]
  phyRead 0 0x01
  stS Scratch.origBbConfig 0
  phyMod 0x01 0x8000 0
  tableRead1 cfg 0 tblIdIqlocal 87 16
  stS Scratch.m0m1 0
  let targetQdBm : UInt32 := ((dBmTarget * 4) % 4294967296).toNat.toUInt32
  for core in [0:2] do
    li 0 orig
    stS Scratch.txpwrIndex 0
    for _ in [0:2] do
      txTone cfg S false false
      ldS 0 Scratch.m0m1
      andi 0 (if core == 0 then 0xff00 else 0x00ff)
      tableWriteR tblIdIqlocal 87 16 0
      tableWriteR tblIdIqlocal 95 16 0
      delay 50
      emit (.call S.estTonePwr)
      -- nphy_bb_mult_save = 0; wlc_phy_stopplayback_nphy (no bb_mult restore)
      wlcPhyStopplaybackNphy cfg false
      -- txpwrindex -= stepsize * (4 * target - qdBm[core]), stepsize 1 (rev < 7);
      -- clamp 0..127 (no extpagain == 3 floor)
      ldS 1 Scratch.txpwrIndex
      emit (.alu .add 1 (.reg (if core == 0 then 2 else 3)))
      emit (.alu .sub 1 (.imm targetQdBm))
      clampS 1 0 127
      stS Scratch.txpwrIndex 1
      txpwrIndex cfg S core false
    ldS 0 Scratch.txpwrIndex
    stS (Scratch.txcalPwrIdx + 2 * core.toUInt32) 0
  ldS 1 Scratch.txcalPwrIdx
  txpwrIndex cfg S 0 false
  ldS 1 (Scratch.txcalPwrIdx + 2)
  txpwrIndex cfg S 1 false
  tableRead1 cfg 0 tblIdIqlocal 87 16
  stS Scratch.txcalBbmult 0
  ldS 0 Scratch.origBbConfig
  phyWriteR 0x01 0
  for h : k in [0:saveRegs.size] do
    ldS 0 (Scratch.gainctrlSave + 2 * k.toUInt32)
    phyWriteR saveRegs[k] 0

/-- `wlc_phy_precal_txgain_nphy` (phy_n.c:17949-18032): internal TX IQ/LO cal
(IPA), rev 6, IPA, 2.4 GHz → `wlc_phy_cal_txgainctrl_nphy(pi, 12, false)`;
`save_bbmult` stays false. -/
def wlcPhyPrecalTxgainNphy (cfg : PhyCfg) (S : Subs) : ProgM Unit :=
  wlcPhyCalTxgainctrlNphy cfg S precalTargetDbm

/-- `wlc_phy_get_tx_gain_nphy` (phy_n.c:23259-23375) with
`nphy_txpwrctrl == PHY_TPC_HW_OFF`, rev 3..6: decode RFSEQ[0x110..0x111]
and write `struct nphy_txgains` to `Scratch.targetGain`. brcmsmac leaves
`txlpf[]` uninitialised on this path (rev < 7); 0 is written. Uses r0–r2, r9. -/
def wlcPhyGetTxGainNphy (cfg : PhyCfg) : ProgM Unit := do
  tableReadSeq cfg tblIdRfseq 0x110 16 #[1, 2]
  for core in [0:2] do
    let r : Reg := if core == 0 then 1 else 2
    let o : UInt32 := 2 * core.toUInt32
    stSi (Scratch.tgTxlpf + o) 0
    mov 0 r
    shri 0 12
    andi 0 0x7
    stS (Scratch.tgTxgm + o) 0
    mov 0 r
    shri 0 8
    andi 0 0xf
    stS (Scratch.tgPga + o) 0
    mov 0 r
    shri 0 4
    andi 0 0xf
    stS (Scratch.tgPad + o) 0
    mov 0 r
    andi 0 0xf
    stS (Scratch.tgIpa + o) 0

/-- `cal_gain` of `wlc_phy_iqcal_gainparams_nphy` (phy_n.c:23377-23433),
rev 3..6: `txgm << 12 | pga << 8 | pad << 4 | ipa` from the target gain in
scratch, into `dst`. Uses r0. -/
def iqcalCalGain (core : Nat) (dst : Reg) : ProgM Unit := do
  let o : UInt32 := 2 * core.toUInt32
  ldS dst (Scratch.tgTxgm + o)
  shli dst 12
  ldS 0 (Scratch.tgPga + o)
  shli 0 8
  emit (.alu .or dst (.reg 0))
  ldS 0 (Scratch.tgPad + o)
  shli 0 4
  emit (.alu .or dst (.reg 0))
  ldS 0 (Scratch.tgIpa + o)
  emit (.alu .or dst (.reg 0))

/-- `wlc_phy_txcal_radio_setup_nphy` (phy_n.c:23435-23744), rev 3..6,
2.4 GHz, IPA, rev >= 5. Uses r0. -/
def wlcPhyTxcalRadioSetupNphy (_cfg : PhyCfg) : ProgM Unit := do
  for core in [0:2] do
    let j := radioTx core
    for h : k in [0:txcalRadioRegs.size] do
      radioRead 0 (txcalRadioRegs[k] ||| j)
      stS (Scratch.radioSave + 2 * (11 * core + k).toUInt32) 0
    radioWrite (r2056TxSsiMaster ||| j) 0x06
    radioWrite (r2056TxIqcalVcmHg ||| j) 0x40
    radioWrite (r2056TxIqcalIdac ||| j) 0x55
    radioWrite (r2056TxTssiVcm ||| j) 0x00
    radioWrite (r2056TxAmpDet ||| j) 0x00
    radioWrite (r2056TxTssia ||| j) 0x00
    radioWrite (r2056TxSsiMux ||| j) 0x06
    radioWrite (r2056TxTssig ||| j) 0x1           -- rev >= 5
    radioWrite (r2056TxTssiMisc1 ||| j) 0x00
    radioWrite (r2056TxTssiMisc2 ||| j) 0x00
    radioWrite (r2056TxTssiMisc3 ||| j) 0x00

/-- `wlc_phy_txcal_radio_cleanup_nphy` (phy_n.c:23746-23878), rev 3..6. Uses r0. -/
def wlcPhyTxcalRadioCleanupNphy (_cfg : PhyCfg) : ProgM Unit := do
  for core in [0:2] do
    let j := radioTx core
    for h : k in [0:txcalRadioRegs.size] do
      ldS 0 (Scratch.radioSave + 2 * (11 * core + k).toUInt32)
      radioWriteR (txcalRadioRegs[k] ||| j) 0

/-- `wlc_phy_txcal_physetup_nphy` (phy_n.c:23880-24035), rev 3..6 with
`use_int_tx_iqlo_cal_nphy` and no tap-off (nothing extra for rev 6). Uses r0–r2, r9. -/
def wlcPhyTxcalPhysetupNphy (cfg : PhyCfg) : ProgM Unit := do
  let sv (k : Nat) := Scratch.phySave + 2 * k.toUInt32
  phyRead 0 0xa6
  stS (sv 0) 0
  phyRead 0 0xa7
  stS (sv 1) 0
  phyMod 0xa6 0xf00 0xa00
  phyMod 0xa7 0xf00 0xa00
  phyRead 0 0x8f
  stS (sv 2) 0
  ori 0 0x600
  phyWriteR 0x8f 0
  phyRead 0 0xa5
  stS (sv 3) 0
  ori 0 0x600
  phyWriteR 0xa5 0
  phyRead 0 0x01
  stS (sv 4) 0
  phyMod 0x01 0x8000 0
  tableRead1 cfg 0 tblIdAfeCtrl 3 16
  stS (sv 5) 0
  tableWrite cfg tblIdAfeCtrl 3 16 #[0]
  tableRead1 cfg 0 tblIdAfeCtrl 19 16
  stS (sv 6) 0
  tableWrite cfg tblIdAfeCtrl 19 16 #[0]
  phyRead 0 0x91
  stS (sv 7) 0
  phyRead 0 0x92
  stS (sv 8) 0
  rfctrlintcOverride .pa 0 [0, 1]           -- use_int_tx_iqlo_cal_nphy
  rfctrlintcOverride .trsw 0x2 [0]
  rfctrlintcOverride .trsw 0x8 [1]
  phyRead 0 0x297
  stS (sv 9) 0
  phyRead 0 0x29b
  stS (sv 10) 0
  phyMod 0x297 0x1 0
  phyMod 0x29b 0x1 0

/-- `wlc_phy_txcal_phycleanup_nphy` (phy_n.c:24037-24118), rev 3..6. Uses r0–r2. -/
def wlcPhyTxcalPhycleanupNphy (cfg : PhyCfg) : ProgM Unit := do
  let sv (k : Nat) := Scratch.phySave + 2 * k.toUInt32
  for (k, a) in [(0, (0xa6 : UInt32)), (1, 0xa7), (2, 0x8f), (3, 0xa5), (4, 0x01)] do
    ldS 0 (sv k)
    phyWriteR a 0
  ldS 0 (sv 5)
  tableWriteR tblIdAfeCtrl 3 16 0
  ldS 0 (sv 6)
  tableWriteR tblIdAfeCtrl 19 16 0
  for (k, a) in [(7, (0x91 : UInt32)), (8, 0x92), (9, 0x297), (10, 0x29b)] do
    ldS 0 (sv k)
    phyWriteR a 0
  wlcPhyResetccaNphy cfg

/-- `wlc_phy_cal_txiqlo_nphy(pi, target_gain, fullcal = true, mphase = false)`
(phy_n.c:25624-25982), rev 6, 20 MHz, 2.4 GHz, IPA, mphase idle. The target
gain is taken from `Scratch.targetGain`. Leaves r0 = 0, or r0 = -EIO when a
calibration command does not complete (then returns at once, skipping the
cleanup, as brcmsmac does). -/
def wlcPhyCalTxiqloNphy (cfg : PhyCfg) (S : Subs) : ProgM Unit := do
  let done ← newLabel
  let eio ← newLabel
  carriersearchOn cfg
  -- rev >= 4: phyhang_avoid is saved and cleared (it is already false).
  tableReadSeq cfg tblIdRfseq 0x110 16 #[1, 2]           -- gain_save
  stS Scratch.gainSave 1
  stS (Scratch.gainSave + 2) 2
  iqcalCalGain 0 1
  iqcalCalGain 1 2
  tableWriteRegs tblIdRfseq 0x110 #[1, 2]
  wlcPhyTxcalRadioSetupNphy cfg
  wlcPhyTxcalPhysetupNphy cfg
  -- rev >= 6: the loft/iqimb ladders are rebuilt per core below.
  phyWrite 0xc2 0x8aa9
  txTone cfg S true true                                 -- bcmerror = 0
  tableWrite cfg tblIdIqlocal 64 16 (Array.replicate startCoefsLen 0)
  let mut ladderDone := #[false, false]
  for cmd in calCmdsFullcalRev3 do
    let core := ((cmd &&& 0x3000) >>> 12).toNat
    let calType := (cmd &&& 0x0f00) >>> 8
    if !(ladderDone.getD core true) then
      ldS 1 Scratch.txcalBbmult
      if core == 0 then shri 1 8
      andi 1 0xff
      emit (.call S.ladder)
      ladderDone := ladderDone.set! core true
    phyWrite 0xc1 ((iqcalNcorr <<< 8) ||| nphyNGctl)
    if calType == 1 || calType == 3 || calType == 4 then
      tableRead1 cfg 0 tblIdIqlocal (69 + core.toUInt32) 16
      stS Scratch.diqStart 0
      tableWrite cfg tblIdIqlocal (69 + core.toUInt32) 16 #[0]
    phyWrite 0xc0 cmd
    spinWhilePhySet 0xc0 0xc000 20000 0 1
    phyRead 0 0xc0
    andi 0 0xc000
    li 8 cmd
    emit (.branch .ne 0 (.imm 0) eio)
    emit (.call S.copyCoefs)
  -- !mphase: best coefficients
  tableReadSeq cfg tblIdIqlocal 96 16 #[1, 2, 3, 4]
  tableWriteRegs tblIdIqlocal 80 #[1, 2, 3, 4]
  tableWriteRegs tblIdIqlocal 88 #[1, 2, 3, 4]
  tableReadSeq cfg tblIdIqlocal 101 16 #[1, 2]
  tableWriteRegs tblIdIqlocal 85 #[1, 2]
  tableWriteRegs tblIdIqlocal 93 #[1, 2]
  tableReadToScratch cfg tblIdIqlocal 96 startCoefsLen Scratch.bestc
  stSi Scratch.txiqlocalValid 1
  stSi Scratch.txiqlocalChanspec (chanspec cfg)
  -- wlc_phy_stopplayback_nphy with the bb_mult saved by runsamples
  wlcPhyStopplaybackNphy cfg false
  ldS 0 Scratch.bbMultSave
  tableWriteR tblIdIqlocal 87 16 0
  phyWrite 0xc2 0x0000
  wlcPhyTxcalPhycleanupNphy cfg
  ldS 1 Scratch.gainSave
  ldS 2 (Scratch.gainSave + 2)
  tableWriteRegs tblIdRfseq 0x110 #[1, 2]
  wlcPhyTxcalRadioCleanupNphy cfg
  carriersearchOff
  li 0 0
  emit (.jump done)
  place eio
  print Tag.txiqCalTimeout 8
  li 0 errEio
  place done

/-- True for the configuration this module ports. -/
def supported (cfg : PhyCfg) : Bool :=
  cfg.phyRev == 6 && cfg.radioRev == 11 && cfg.ipa2g && cfg.channel >= 1 && cfg.channel <= 13

/-- The TX part of `do_nphy_cal` (phy_n.c:19490-19520, non-MPHASE branch after
the RSSI cal): `wlc_phy_precal_txgain_nphy`, `target_gain =
wlc_phy_get_tx_gain_nphy` (written to scratch 0x5C00), then
`wlc_phy_cal_txiqlo_nphy(target_gain, true, false)`. r0 = 0 on success,
-EIO (0xFFFFFFFB) on a calibration-engine timeout. -/
def precalAndTxiqlo (cfg : PhyCfg) : ProgM Unit := do
  if !supported cfg then
    fail Fail.unsupported
    return
  let S ← installSubs cfg
  wlcPhyPrecalTxgainNphy cfg S
  wlcPhyGetTxGainNphy cfg
  wlcPhyCalTxiqloNphy cfg S

/-- `wlc_phy_savecal_nphy` (phy_n.c:18429-18575), 2.4 GHz, rev 3..6,
`phyhang_avoid` false: RX IQ coefficients, the 2056 LOFT radio registers and
IQLOCAL[80..87] into `Scratch` (`pi->calibration_cache`), and
`nphy_iqcal_chanspec_2G`. Uses r0, r9. -/
def saveCal (cfg : PhyCfg) : ProgM Unit := do
  if !supported cfg then
    fail Fail.unsupported
    return
  -- wlc_phy_rx_iq_coeffs_nphy(pi, 0, &rxcal_coeffs_2G)
  for (k, a) in [(0, (0x9a : UInt32)), (1, 0x9b), (2, 0x9c), (3, 0x9d)] do
    phyRead 0 a
    stS (Scratch.rxcalCoeffs2G + 2 * k.toUInt32) 0
  let regs : Array UInt32 := #[
    r2056TxLoftFineI ||| radioTx 0, r2056TxLoftFineQ ||| radioTx 0,
    r2056TxLoftFineI ||| radioTx 1, r2056TxLoftFineQ ||| radioTx 1,
    r2056TxLoftCoarseI ||| radioTx 0, r2056TxLoftCoarseQ ||| radioTx 0,
    r2056TxLoftCoarseI ||| radioTx 1, r2056TxLoftCoarseQ ||| radioTx 1]
  for h : k in [0:regs.size] do
    radioRead 0 regs[k]
    stS (Scratch.txcalRadioRegs2G + 2 * k.toUInt32) 0
  stSi Scratch.iqcalChanspec2G (chanspec cfg)
  tableReadToScratch cfg tblIdIqlocal 80 8 Scratch.txcalCoeffs2G

end LeanOS.Wifi.NPhyTxCal
