import LeanOS.Wifi.NPhy

/-
N-PHY workarounds (`wlc_phy_workarounds_nphy`) for the BCM43224 programs:
N-PHY rev 6, radio 2056 rev 11, 2.4 GHz, 20 MHz, IPA, two chains.

Ported from Linux brcmsmac (ISC license), Copyright (c) 2010 Broadcom
Corporation; see drivers/net/wireless/broadcom/brcm80211/brcmsmac at Linux
commit fd179f8a05be3ccae366b9b96e176b51fbe54aab.

Only the path for this board family is emitted: revision, band, bandwidth,
IPA, board-flag and SROM decisions are made while generating from `PhyCfg`.
Configurations outside what was ported (PHY rev < 3, rev ≥ 7, rev 3–5 gain
control) generate a program that stops with `Fail.unsupported`.

Registers: r0–r3 are used as scratch here; the accessors use r9–r12.
-/
namespace LeanOS.Wifi.NPhyWorkarounds

open LeanOS.Wifi.Bytecode LeanOS.Wifi.Bcm43224 LeanOS.Wifi.NPhy

namespace Fail
/-- The generated configuration is outside the ported brcmsmac path. -/
def unsupported : UInt32 := 0x7E50
/-- Phy register 0x09 reports the 5 GHz band while the program is 2.4 GHz only. -/
def not2g : UInt32 := 0x7E51
end Fail

/-! ## Constants (brcmsmac phyreg_n.h, phy_radio.h, d11.h, types.h, pub.h) -/

def tblIdGain1 : UInt32 := 0
def tblIdGain2 : UInt32 := 1
def tblIdGainBits1 : UInt32 := 2
def tblIdGainBits2 : UInt32 := 3
def tblIdRfseq : UInt32 := 7
def tblIdAfeCtrl : UInt32 := 8
def tblIdNoiseVar : UInt32 := 16
def tblIdCmpMetricDataWeight : UInt32 := 30

def classifierCtrlCckEn : UInt32 := 0x1
def iqFlipAdc1 : UInt32 := 0x0001
def iqFlipAdc2 : UInt32 := 0x0010
def bandControlCurrentBand : UInt32 := 0x0001

/-- NPHY_RFSEQ_* sequence ids. -/
def rfseqRx2Tx : UInt32 := 0x0
def rfseqTx2Rx : UInt32 := 0x1

/-! NPHY_REV3_RFSEQ_CMD_* events. -/
namespace RfseqCmd
def nop : UInt32 := 0x0
def rxgFbw : UInt32 := 0x1
def trSwitch : UInt32 := 0x2
def intPaPu : UInt32 := 0x3
def extPa : UInt32 := 0x4
def rxpdTxpd : UInt32 := 0x5
def txGain : UInt32 := 0x6
def clrHiqDis : UInt32 := 0x8
def clrRxrxBias : UInt32 := 0xf
def endSeq : UInt32 := 0x1f
end RfseqCmd

/-- RADIO_2056_RX0 / RADIO_2056_RX1 register block selectors. -/
def radio2056Rx0 : UInt32 := 0x6000 -- (0x6 << 12)
def radio2056Rx1 : UInt32 := 0x7000 -- (0x7 << 12)

def r2056RxRssiGain : UInt32 := 0x23
def r2056RxRssiPole : UInt32 := 0x29
def r2056RxBiaspoleLnaa1Idac : UInt32 := 0x30
def r2056RxLnaa2Idac : UInt32 := 0x31
def r2056RxBiaspoleLnag1Idac : UInt32 := 0x37
def r2056RxLnag2Idac : UInt32 := 0x38
def r2056RxMixaLobBias : UInt32 := 0x3d
def r2056RxMixaCmfbIdac : UInt32 := 0x3f
def r2056RxMixaBiasAux : UInt32 := 0x40
def r2056RxMixaBiasMain : UInt32 := 0x41
def r2056RxMixaMastBias : UInt32 := 0x43
def r2056RxMixgCmfbIdac : UInt32 := 0x49

def bflExtLna : UInt32 := 0x00001000
def bfl2GpllWar : UInt32 := 0x00000400
def bfl2SingleAntCck : UInt32 := 0x00001000
def bfl2GpllWar2 : UInt32 := 0x00010000

/-- M_HOST_FLAGS4 shared-memory byte offset (d11.h: 0x03c * 2). -/
def mHostFlags4 : UInt32 := 0x03c * 2
def mhf4BphyTxCore0 : UInt32 := 0x0080

/-! ## Attach-time state derived from the configuration -/

/-- `hw_phytxchain`: brcmsmac stf.c takes `sprom->txchain` (bcma SROM rev 8
field `txchain`, SSB_SPROM8_TXRXC byte 0xA2, bits 3:0) and replaces 0 or 0xf
by TXCHAIN_DEF_NPHY (3). -/
def hwTxChain (cfg : PhyCfg) : UInt32 :=
  let c := cfg.srom16 0xA2 &&& 0xf
  if c == 0 || c == 0xf then 3 else c

/-- `hw_phyrxchain`: `sprom->rxchain` (SSB_SPROM8_TXRXC byte 0xA2, bits 7:4),
0 or 0xf replaced by RXCHAIN_DEF_NPHY (3). -/
def hwRxChain (cfg : PhyCfg) : UInt32 :=
  let c := (cfg.srom16 0xA2 >>> 4) &&& 0xf
  if c == 0 || c == 0xf then 3 else c

/-- `PHY_IPA(pi)` for a 2.4 GHz channel: `ipa2g_on`. -/
def phyIpa (cfg : PhyCfg) : Bool := cfg.ipa2g

/-- `pi->phyhang_avoid`: wlc_phy_attach_nphy sets it for PHY revs 3–5 only. -/
def phyhangAvoid (cfg : PhyCfg) : Bool := cfg.phyRev >= 3 && cfg.phyRev < 6

/-- `pi->edcrs_threshold_lock` is never set by brcmsmac (zeroed at attach). -/
def edcrsThresholdLock : Bool := false

/-- Two's-complement byte of a signed 8-bit gain value (brcmsmac `s8` tables
written with width 8). -/
def s8 (v : Int) : UInt32 := (v % 256).toNat.toUInt32

/-! ## MAC-side shims -/

/-- wlapi_bmac_mhf → brcms_b_mhf(wlc_hw, idx, mask, val, BRCM_BAND_ALL)
(main.c:1284-1330) for host-flag word 4. brcmsmac updates its software
shadow `band->mhfs[idx]` and, the clock being on and the band current,
writes the shadow through to M_HOST_FLAGS4 with brcms_b_write_shm
(main.c:2882-2912: objaddr select, objaddr read-back, 16-bit objdata
write). The shadow equals the shared-memory word after brcms_c_mhfdef, so
the program reads the word from shared memory instead of a shadow, and
writes it back only when the value changes, as brcms_b_mhf does. -/
def bmacMhf4 (mask val : UInt32) : ProgM Unit := do
  let off := mHostFlags4
  let dataOff := if off &&& 2 == 0 then d11ObjData else d11ObjData + 2
  -- brcms_b_read_objmem
  w32 d11ObjAddr (objShm ||| (off >>> 2))
  r32 1 d11ObjAddr
  r16 0 dataOff
  mov 1 0
  andi 1 ((~~~mask) &&& 0xFFFF)
  ori 1 (val &&& mask)
  let same ← newLabel
  emit (.branch .eq 1 (.reg 0) same)
  -- brcms_b_write_objmem
  w32 d11ObjAddr (objShm ||| (off >>> 2))
  r32 2 d11ObjAddr
  emit (.write16 dataOff (.reg 1))
  place same

/-! ## Helpers -/

/-- wlc_phy_table_read_nphy for one element (phy_n.c:14163-14175 →
wlc_phy_read_table, phy_cmn.c:862-892), including the BCM43224 chip-rev-1
quirk that brcmsmac applies to reads of *every* table: a dummy read of the
data-low register followed by re-writing the table address. -/
def tableRead1 (cfg : PhyCfg) (dst : Reg) (id offset width : UInt32) : ProgM Unit := do
  phyWrite tblAddr ((id <<< 10) ||| offset)
  if cfg.chipRev == 1 then
    phyRead 9 tblDataLo
    phyWrite tblAddr ((id <<< 10) ||| offset)
  if width == 32 then
    phyRead 9 tblDataLo
    phyRead dst tblDataHi
    shli dst 16
    emit (.alu .or dst (.reg 9))
  else
    phyRead dst tblDataLo

/-- wlc_phy_classifier_nphy (phy_n.c:21292-21314). D11 core rev 23, so the
rev-16 MAC suspend around the update is not emitted. Returns nothing (the
caller in the workarounds ignores the new control value). -/
def wlcPhyClassifierNphy (mask val : UInt32) : ProgM Unit := do
  phyRead 0 0xb0
  andi 0 0x7
  andi 0 ((~~~mask) &&& 0xFFFF)
  ori 0 (val &&& mask)
  phyModR 0xb0 0x7 0

/-- wlc_phy_set_rfseq_nphy (phy_n.c:14750-14780): event and delay lists for
RF sequence `cmd`, padded to 16 entries with END events and delay 1.
`phyhang_avoid` is false for PHY rev ≥ 6, so the carrier-search hold is not
emitted (other revisions are rejected before reaching here). -/
def wlcPhySetRfseqNphy (cfg : PhyCfg) (cmd : UInt32) (events dlys : Array UInt32) :
    ProgM Unit := do
  if phyhangAvoid cfg || events.size != dlys.size || events.size > 16 then
    fail Fail.unsupported
  else
    let endEvent := if cfg.phyRev >= 3 then RfseqCmd.endSeq else 0x0
    let endDly : UInt32 := 1
    let t1 := cmd <<< 4
    let t2 := t1 + 0x80
    tableWrite cfg tblIdRfseq t1 8 events
    tableWrite cfg tblIdRfseq t2 8 dlys
    for ctr in [events.size:16] do
      tableWrite cfg tblIdRfseq (t1 + ctr.toUInt32) 8 #[endEvent]
      tableWrite cfg tblIdRfseq (t2 + ctr.toUInt32) 8 #[endDly]

/-- wlc_phy_war_force_trsw_to_R_cliplo_nphy (phy_n.c:15138-15154), 2.4 GHz. -/
def wlcPhyWarForceTrswToRCliploNphy (core : Nat) : ProgM Unit := do
  if core == 0 then
    phyWrite 0x38 0x4
    phyWrite 0x37 0x0060
  else if core == 1 then
    phyWrite 0x2ae 0x4
    phyWrite 0x2ad 0x0060

/-- wlc_phy_war_txchain_upd_nphy (phy_n.c:15156-15167). -/
def wlcPhyWarTxchainUpdNphy (txchain : UInt32) : ProgM Unit := do
  if txchain &&& 0x1 == 0 then wlcPhyWarForceTrswToRCliploNphy 0
  if txchain &&& 0x2 == 0 then wlcPhyWarForceTrswToRCliploNphy 1

/-- Write `val` to a 2056 RX register on both cores. -/
def radioWriteRxBoth (reg val : UInt32) : ProgM Unit := do
  radioWrite (reg ||| radio2056Rx0) val
  radioWrite (reg ||| radio2056Rx1) val

/-! ## Gain control -/

/-- 2.4 GHz gain-control settings selected by
wlc_phy_workarounds_nphy_gainctrl for PHY rev 6. -/
structure GainCtrlG where
  lna1GainDb : Array UInt32
  lna2GainDb : Array UInt32
  rfseqInitGain : Array UInt32
  initGaincode : UInt32
  clip1hiGaincode : UInt32
  clip1loGaincode : UInt32
  nbclipTh : UInt32
  w1clipTh : UInt32
  crsminTh : UInt32
  crsminlTh : UInt32
  crsminuTh : UInt32
  rssiGain : UInt32

/-- Rev 6 2.4 GHz selections (phy_n.c:15670-15755). Radio 2056 rev 11 is the
BCM43224 B0 (`*_rev6_224B0`) set; otherwise the external-LNA board flag and
the SROM `triso` pick the rev 6 values. -/
def gainCtrlGRev6 (cfg : PhyCfg) : GainCtrlG :=
  if cfg.radioRev == 11 then
    { lna1GainDb := #[10, 14, 19, 27].map s8
      lna2GainDb := #[-5, 6, 10, 15].map s8
      rfseqInitGain := #[0x413f, 0x413f]
      initGaincode := 0x427e
      clip1hiGaincode := 0x007e
      clip1loGaincode := 0x1074
      nbclipTh := 0x1d0
      w1clipTh := 5
      crsminTh := 0x18
      crsminlTh := 0x18
      crsminuTh := 0x18
      rssiGain := 0x50 }
  else
    let elna := cfg.boardFlags &&& bflExtLna != 0
    let clip1loRev6 : Array UInt32 :=
      #[0x106a, 0x106c, 0x1074, 0x107c, 0x007e, 0x107e, 0x207e, 0x307e]
    -- SROM rev 8 fem2g.triso (SSB_SPROM8_FEM2G byte 0xAE, bits 10:8).
    let triso := cfg.triso2g.toNat
    { lna1GainDb := #[8, 13, 18, 25].map s8
      lna2GainDb := #[-5, 6, 10, 14].map s8
      rfseqInitGain := if elna then #[0x113f, 0x113f] else #[0x513f, 0x513f]
      initGaincode := if elna then 0x127e else 0x527e
      clip1hiGaincode := 0x007e
      clip1loGaincode := clip1loRev6.getD triso 0x107c
      nbclipTh := 0x1d0
      w1clipTh := 5
      crsminTh := 0x18
      crsminlTh := 0x18
      crsminuTh := 0x18
      rssiGain := 0x50 }

/-- wlc_phy_workarounds_nphy_gainctrl (phy_n.c:15425-16045), PHY rev 3–6
branch, 2.4 GHz, PHY rev 6 selections. The band is taken from phy register
0x09 at run time in brcmsmac; the program is generated for 2.4 GHz only and
stops with `Fail.not2g` if the hardware reports the 5 GHz band. -/
def wlcPhyWorkaroundsNphyGainctrl (cfg : PhyCfg) : ProgM Unit := do
  if cfg.phyRev != 6 then
    -- rev 3–5 selections and the rev ≥ 7 (2057) / rev < 3 paths are not ported.
    fail Fail.unsupported
  else
    let g := gainCtrlGRev6 cfg
    phyMod 0xa0 0x0040 0x0040 -- (0x1 << 6), (1 << 6)
    phyMod 0x1c 0x2000 0x2000 -- (0x1 << 13), (1 << 13)
    phyMod 0x32 0x2000 0x2000
    -- currband = read_phy_reg(0x09) & NPHY_BandControl_currentBand
    phyRead 0 0x09
    andi 0 bandControlCurrentBand
    let ok ← newLabel
    emit (.branch .eq 0 (.imm 0) ok)
    print 0xEEEE 0
    fail Fail.not2g
    place ok
    -- tia_gain_db = tiaG_gain_db, tia_gainbits = tiaG_gainbits,
    -- clip1md_gaincode = clip1mdG_gaincode
    let tiaGainDb : Array UInt32 := Array.replicate 10 0x0A
    let tiaGainBits : Array UInt32 := Array.replicate 10 0x03
    let clip1mdGaincode : UInt32 := 0x0066
    let lpfGainDb : Array UInt32 := #[0x00, 0x06, 0x0c, 0x12, 0x12, 0x12]
    let lpfGainBits : Array UInt32 := #[0x00, 0x01, 0x02, 0x03, 0x03, 0x03]

    radioWriteRxBoth r2056RxBiaspoleLnag1Idac 0x17
    radioWriteRxBoth r2056RxLnag2Idac 0xf0
    radioWriteRxBoth r2056RxRssiPole 0x0
    radioWriteRxBoth r2056RxRssiGain g.rssiGain
    radioWriteRxBoth r2056RxBiaspoleLnaa1Idac 0x17
    radioWriteRxBoth r2056RxLnaa2Idac 0xFF

    tableWrite cfg tblIdGain1 8 8 g.lna1GainDb
    tableWrite cfg tblIdGain2 8 8 g.lna1GainDb
    tableWrite cfg tblIdGain1 0x10 8 g.lna2GainDb
    tableWrite cfg tblIdGain2 0x10 8 g.lna2GainDb
    tableWrite cfg tblIdGain1 0x20 8 tiaGainDb
    tableWrite cfg tblIdGain2 0x20 8 tiaGainDb
    tableWrite cfg tblIdGainBits1 0x20 8 tiaGainBits
    tableWrite cfg tblIdGainBits2 0x20 8 tiaGainBits
    tableWrite cfg tblIdGain1 0x40 8 lpfGainDb
    tableWrite cfg tblIdGain2 0x40 8 lpfGainDb
    tableWrite cfg tblIdGainBits1 0x40 8 lpfGainBits
    tableWrite cfg tblIdGainBits2 0x40 8 lpfGainBits

    phyWrite 0x20 g.initGaincode
    phyWrite 0x2a7 g.initGaincode
    -- phy_corenum == 2 entries of rfseq_init_gain.
    tableWrite cfg tblIdRfseq 0x106 16 g.rfseqInitGain

    phyWrite 0x22 g.clip1hiGaincode
    phyWrite 0x2a9 g.clip1hiGaincode
    phyWrite 0x24 clip1mdGaincode
    phyWrite 0x2ab clip1mdGaincode
    phyWrite 0x37 g.clip1loGaincode
    phyWrite 0x2ad g.clip1loGaincode

    phyMod 0x27d 0xff g.crsminTh
    phyMod 0x280 0xff g.crsminlTh
    phyMod 0x283 0xff g.crsminuTh

    phyWrite 0x2b g.nbclipTh
    phyWrite 0x41 g.nbclipTh

    phyMod 0x27 0x3f g.w1clipTh
    phyMod 0x3d 0x3f g.w1clipTh

    phyWrite 0x150 0x809c

/-! ## Rev 3+ workarounds -/

/-- AFE control aux-ADC Vmid/gain writes for the SROM power-detector range
(phy_n.c:16706-16809), 2.4 GHz (`chan_freq_range == WL_CHAN_FREQ_RANGE_2G`). -/
def afeCtrlAuxAdc (cfg : PhyCfg) : ProgM Unit := do
  -- SROM rev 8 fem2g.pdetrange (SSB_SPROM8_FEM2G byte 0xAE, bits 7:3).
  let pdetrange := cfg.pdetRange2g
  let write4 (vmid0 gain0 vmid1 gain1 : Array UInt32) : ProgM Unit := do
    tableWrite cfg tblIdAfeCtrl 0x08 16 vmid0
    tableWrite cfg tblIdAfeCtrl 0x18 16 vmid1
    tableWrite cfg tblIdAfeCtrl 0x0c 16 gain0
    tableWrite cfg tblIdAfeCtrl 0x1c 16 gain1
  if pdetrange == 0 then
    -- aux_adc_vmid_rev4 / aux_adc_gain_rev4 (identical to rev3), 2G unchanged.
    let vmid := #[0xa2, 0xb4, 0xb4, 0x89]
    let gain := #[0x02, 0x02, 0x02, 0x00]
    write4 vmid gain vmid gain
  else if pdetrange == 1 then
    let vmid := #[0xb4, 0xb4, 0xb4, 0x24]
    let gain := #[0x02, 0x02, 0x02, 0x02]
    write4 vmid gain vmid gain
  else if pdetrange == 2 then
    let (v3, g3) : UInt32 × UInt32 :=
      if cfg.phyRev >= 6 then (0x94, 0x03)
      else if cfg.phyRev == 5 then (0x84, 0x02)
      else (0x74, 0x04)
    let vmid := #[0xa2, 0xb4, 0xb4, v3]
    let gain := #[0x02, 0x02, 0x02, g3]
    write4 vmid gain vmid gain
  else if pdetrange == 3 then
    if cfg.phyRev >= 4 then
      let vmid := #[0xa2, 0xb4, 0xb4, 0x270]
      let gain := #[0x02, 0x02, 0x02, 0x00]
      write4 vmid gain vmid gain
  else if pdetrange == 4 || pdetrange == 5 then
    let (vm0, vm1, av) : UInt32 × UInt32 × UInt32 :=
      if pdetrange == 4 then (0x89, 0x8b, 2) else (0x74, 0x70, 0)
    -- brcmsmac order: 0x08, 0x0c with Vmid[0]/Av[0], then 0x18, 0x1c.
    tableWrite cfg tblIdAfeCtrl 0x08 16 #[0xa2, 0xb4, 0xb4, vm0]
    tableWrite cfg tblIdAfeCtrl 0x0c 16 #[0x02, 0x02, 0x02, av]
    tableWrite cfg tblIdAfeCtrl 0x18 16 #[0xa2, 0xb4, 0xb4, vm1]
    tableWrite cfg tblIdAfeCtrl 0x1c 16 #[0x02, 0x02, 0x02, av]

/-- wlc_phy_workarounds_nphy_rev3 (phy_n.c:16549-16889) for PHY revs 3–6 on
a 2.4 GHz, 20 MHz channel. -/
def wlcPhyWorkaroundsNphyRev3 (cfg : PhyCfg) : ProgM Unit := do
  let tx2rxEvents : Array UInt32 := #[RfseqCmd.extPa, RfseqCmd.intPaPu, RfseqCmd.txGain,
    RfseqCmd.rxpdTxpd, RfseqCmd.trSwitch, RfseqCmd.rxgFbw, RfseqCmd.clrHiqDis, RfseqCmd.endSeq]
  let tx2rxDlys : Array UInt32 := #[8, 4, 2, 2, 4, 4, 6, 1]
  let rx2txEventsIpa : Array UInt32 := #[RfseqCmd.nop, RfseqCmd.rxgFbw, RfseqCmd.trSwitch,
    RfseqCmd.clrHiqDis, RfseqCmd.rxpdTxpd, RfseqCmd.txGain, RfseqCmd.clrRxrxBias,
    RfseqCmd.intPaPu, RfseqCmd.endSeq]
  let rx2txDlysIpa : Array UInt32 := #[8, 6, 6, 4, 4, 16, 43, 1, 1]

  phyWrite 0x23f 0x1f8
  phyWrite 0x240 0x1f8

  -- leg_data_weights &= 0xffffff (run-time read-modify-write)
  tableRead1 cfg 0 tblIdCmpMetricDataWeight 0 32
  andi 0 0xffffff
  tableWriteR tblIdCmpMetricDataWeight 0 32 0

  -- alpha0..2, beta0..2
  phyWrite 0x145 293
  phyWrite 0x146 435
  phyWrite 0x147 261
  phyWrite 0x148 366
  phyWrite 0x149 205
  phyWrite 0x14a 32

  phyWrite 0x38 0xC
  phyWrite 0x2ae 0xC

  wlcPhySetRfseqNphy cfg rfseqTx2Rx tx2rxEvents tx2rxDlys

  if phyIpa cfg then
    wlcPhySetRfseqNphy cfg rfseqRx2Tx rx2txEventsIpa rx2txDlysIpa

  if hwRxChain cfg != 0x3 && hwRxChain cfg != hwTxChain cfg then
    let mut ev : Array UInt32 := #[RfseqCmd.nop, RfseqCmd.rxgFbw, RfseqCmd.trSwitch,
      RfseqCmd.clrHiqDis, RfseqCmd.rxpdTxpd, RfseqCmd.txGain, RfseqCmd.intPaPu,
      RfseqCmd.extPa, RfseqCmd.endSeq]
    let mut dl : Array UInt32 := #[8, 6, 6, 4, 4, 18, 42, 1, 1]
    if phyIpa cfg then
      dl := (dl.set! 5 59).set! 6 1
      ev := ev.set! 7 RfseqCmd.endSeq
    wlcPhySetRfseqNphy cfg rfseqRx2Tx ev dl

  -- CHSPEC_IS2G
  phyWrite 0x6a 0x2

  phyMod 0x294 0x0f00 0x0700 -- (0xf << 8), (7 << 8)

  -- 20 MHz: min_nvar_val = 0x18d at noise-variance entries 3 and 127.
  tableWrite cfg tblIdNoiseVar 3 32 #[0x18d]
  tableWrite cfg tblIdNoiseVar 127 32 #[0x18d]

  wlcPhyWorkaroundsNphyGainctrl cfg

  -- dac_control
  tableWrite cfg tblIdAfeCtrl 0x00 16 #[0x0002]
  tableWrite cfg tblIdAfeCtrl 0x10 16 #[0x0002]

  afeCtrlAuxAdc cfg

  radioWriteRxBoth r2056RxMixaMastBias 0x0
  radioWriteRxBoth r2056RxMixaBiasMain 0x6
  radioWriteRxBoth r2056RxMixaBiasAux 0x7
  radioWriteRxBoth r2056RxMixaLobBias 0x88
  radioWriteRxBoth r2056RxMixaCmfbIdac 0x0
  radioWriteRxBoth r2056RxMixgCmfbIdac 0x0

  -- SROM rev 8 fem2g.triso (SSB_SPROM8_FEM2G byte 0xAE, bits 10:8).
  if cfg.triso2g == 7 then
    wlcPhyWarForceTrswToRCliploNphy 0
    wlcPhyWarForceTrswToRCliploNphy 1

  wlcPhyWarTxchainUpdNphy (hwTxChain cfg)

  -- 2.4 GHz: only the GPLL workarounds apply (APLL_WAR is 5 GHz only).
  let w : UInt32 :=
    if cfg.boardFlags2 &&& (bfl2GpllWar ||| bfl2GpllWar2) != 0 then 0x00088888
    else 0x88888888
  tableWrite cfg tblIdCmpMetricDataWeight 1 32 #[w]
  tableWrite cfg tblIdCmpMetricDataWeight 2 32 #[w]
  tableWrite cfg tblIdCmpMetricDataWeight 3 32 #[w]

  -- PHY rev 4 has 5 GHz-only TX GMBB IDAC writes; nothing on 2.4 GHz.

  if !edcrsThresholdLock then
    phyWrite 0x224 0x3eb
    phyWrite 0x225 0x3eb
    phyWrite 0x226 0x341
    phyWrite 0x227 0x341
    phyWrite 0x228 0x42b
    phyWrite 0x229 0x42b
    phyWrite 0x22a 0x381
    phyWrite 0x22b 0x381
    phyWrite 0x22c 0x42b
    phyWrite 0x22d 0x42b
    phyWrite 0x22e 0x381
    phyWrite 0x22f 0x381

  if cfg.phyRev >= 6 then
    if cfg.boardFlags2 &&& bfl2SingleAntCck != 0 then
      bmacMhf4 mhf4BphyTxCore0 mhf4BphyTxCore0

/-- wlc_phy_workarounds_nphy (phy_n.c:17014-17035) for this board: 2.4 GHz,
PHY rev 6 (`phyhang_avoid` false, so no carrier-search hold). -/
def workarounds (cfg : PhyCfg) : ProgM Unit := do
  if cfg.phyRev < 3 || cfg.phyRev >= 7 || phyhangAvoid cfg then
    -- rev7 (2057) and rev1/2 workarounds, and the phyhang_avoid
    -- carrier-search hold used by revs 3–5, are not ported.
    fail Fail.unsupported
  else
    -- CHSPEC_IS2G: enable the CCK classifier.
    wlcPhyClassifierNphy classifierCtrlCckEn 1
    phyOr 0xb1 (iqFlipAdc1 ||| iqFlipAdc2)
    wlcPhyWorkaroundsNphyRev3 cfg

end LeanOS.Wifi.NPhyWorkarounds
