import LeanOS.Wifi.NPhyInit

/-
N-PHY RSSI calibration (`wlc_phy_rssi_cal_nphy`) for the BCM43224 programs.

Ported from Linux brcmsmac (ISC license), Copyright (c) 2010 Broadcom
Corporation; see drivers/net/wireless/broadcom/brcm80211/brcmsmac at Linux
commit fd179f8a05be3ccae366b9b96e176b51fbe54aab.

Scope: N-PHY rev 6 (rev 3..6 path of `wlc_phy_rssi_cal_nphy_rev3`), radio
2056, 2.4 GHz, 20 MHz, two cores. Revision, band and core-count branches are
decided while generating; everything computed from hardware reads (the RSSI
polls, the VCM search, the fine digital offsets, the rx core state) runs in
bytecode with signed 32-bit arithmetic, as brcmsmac's `s32` code does.

`rssiCal cfg` is meant for the `rssiCal` hook of `NPhyInit.initNphy`. It
clobbers r0–r9 (plus the accessor registers) and keeps nothing live on exit.
It uses one level of `call` (the RSSI poll subroutines).

## Scratch RAM (0x5000–0x53FF only)
See `Scratch`. The results brcmsmac keeps in `pi->rssical_cache` (the two
radio RSSI_MISC values and the twelve NB/W1/W2 offset registers) and
`pi->nphy_rssical_chanspec_2G` are written to `Scratch.cache*` in brcmsmac's
order for a later `wlc_phy_restore_rssical_nphy` port.
-/
namespace LeanOS.Wifi.NPhyRssiCal

open LeanOS.Wifi.Bytecode LeanOS.Wifi.Bcm43224 LeanOS.Wifi.NPhy LeanOS.Wifi.NPhyInit

namespace Fail
/-- The configuration asks for a path this port does not carry (PHY rev < 3
or ≥ 7, or an rfctrl override field outside the rev 3..6 table). -/
def unsupported : UInt32 := 0x7E60
end Fail

namespace Tag
/-- `wlc_phy_rfctrlintc_override_nphy` WARN "HW error: override failed"
(RfctrlCmd bit still set after the SPINWAIT); value = the bit. brcmsmac then
returns from the override routine; so does this port. -/
def overrideFailed : UInt32 := 0x0460
end Tag

/-! ## Constants (brcmsmac phy_n.c, phyreg_n.h, phy_radio.h, brcmu_wifi.h) -/

/-- `NPHY_RSSICAL_MAXREAD` (phy_n.c:99). -/
def rssicalMaxRead : Int := 31
/-- `NPHY_RSSICAL_NPOLL` (phy_n.c:101). -/
def rssicalNPoll : Nat := 8
/-- `NPHY_RSSICAL_MAXD` (phy_n.c:102). -/
def rssicalMaxD : UInt32 := 0x100000
/-- `NPHY_RSSICAL_NB_TARGET` (phy_n.c:107). -/
def rssicalNbTarget : Int := 0
/-- `NPHY_RSSICAL_W1_TARGET_REV3` = `NPHY_RSSICAL_W2_TARGET_REV3` (phy_n.c:109-110). -/
def rssicalWbTargetRev3 : Int := 29
/-- `vcm_level_max` in `wlc_phy_rssi_cal_nphy_rev3`. -/
def vcmLevelMax : Nat := 8

/-- `RADIO_2056_RX_RSSI_MISC` (0x2b) with `RADIO_2056_RX0` / `RADIO_2056_RX1`. -/
def radio2056RxRssiMisc (core : Nat) : UInt32 := 0x2b ||| (if core == 0 then 0x6000 else 0x7000)
/-- `RADIO_2056_VCM_MASK` and `RADIO_2056_RSSI_VCM_SHIFT`. -/
def radio2056VcmMask : UInt32 := 0x1c
def radio2056RssiVcmShift : UInt32 := 2

/-- `ch20mhz_chspec(channel)` (brcmu_wifi.h): channel | BW_20 (0x0800) |
CTL_SB_NONE (0x0300) | BAND_2G (0x2000). -/
def chanspec20 (cfg : PhyCfg) : UInt32 := cfg.channel.toUInt32 ||| 0x0800 ||| 0x0300 ||| 0x2000

/-- Wrap a (small) signed Lean integer to a 32-bit two's-complement word. -/
def i32 (x : Int) : UInt32 := (x % 4294967296).toNat.toUInt32

/-- RSSI selector (`NPHY_RSSI_SEL_*`), for the three types the calibration uses. -/
inductive RssiSel where
  | w1 | w2 | nb
  deriving BEq

/-- `NPHY_RAIL_I` / `NPHY_RAIL_Q`. -/
inductive Rail where
  | i | q
  deriving BEq

/-! ## Scratch layout -/

namespace Scratch
def base : UInt32 := 0x5000
/-- `classif_state` (u32 slot). -/
def classifState : UInt32 := 0x5000
/-- `clip_state[0..1]`. -/
def clipState0 : UInt32 := 0x5004
def clipState1 : UInt32 := 0x5008
/-- The fifteen `NPHY_*_save` registers, 4 bytes each, in `saveRegs` order. -/
def saves : UInt32 := 0x5010
/-- `rxcore_state`. -/
def rxcoreState : UInt32 := 0x5050
/-- `vcm_final`. -/
def vcmFinal : UInt32 := 0x5054
/-- Registers saved by `wlc_phy_poll_rssi_nphy` (8 × 4 bytes). -/
def pollSaves : UInt32 := 0x5060
/-- `poll_result_core[4]` (s32). -/
def pollResultCore : UInt32 := 0x5080
/-- `poll_results_min[4]` (s32). -/
def pollResultsMin : UInt32 := 0x5090
/-- `fine_digital_offset[4]` (s32). -/
def fineOffset : UInt32 := 0x50A0
/-- `poll_results[8][4]` (s32), row `vcm` at `+ 16 * vcm`. -/
def pollResults : UInt32 := 0x5100
/-- `pi->rssical_cache.rssical_radio_regs_2G[0..1]` (u16 each). -/
def cacheRadio : UInt32 := 0x5200
/-- `pi->rssical_cache.rssical_phyregs_2G[0..11]` (u16 each). -/
def cachePhy : UInt32 := 0x5204
/-- `pi->nphy_rssical_chanspec_2G` (u16). -/
def cacheChanspec : UInt32 := 0x521C
/-- Last byte of this module's region (inclusive). -/
def limit : UInt32 := 0x53FF
end Scratch

/-! ## Small helpers -/

/-- `dst := mem32[addr]` (uses only `dst`). -/
private def ldS (dst : Reg) (addr : UInt32) : ProgM Unit := do
  li dst 0
  emit (.memLoad 4 dst dst addr)

/-- `mem[addr] := src` with width `w` (uses r9 as the base; `src ≠ 9`). -/
private def stS (addr : UInt32) (src : Reg) (w : Nat := 4) : ProgM Unit := do
  li 9 0
  emit (.memStore w 9 addr (.reg src))

private def stSi (addr v : UInt32) (w : Nat := 4) : ProgM Unit := do
  li 9 0
  emit (.memStore w 9 addr (.imm v))

/-- `dst := -dst` (uses `tmp`). -/
private def neg (dst tmp : Reg) : ProgM Unit := do
  li tmp 0
  emit (.alu .sub tmp (.reg dst))
  mov dst tmp

/-- mod_radio_reg with a run-time value in `r` (already shifted); clobbers `r`. -/
def radioModR (addr mask : UInt32) (r : Reg) : ProgM Unit := do
  radioRead 10 addr
  andi 10 ((~~~mask) &&& 0xFFFF)
  andi r mask
  emit (.alu .or 10 (.reg r))
  radioWriteR addr 10

/-! ## phy_n.c helpers -/

/-- `wlc_phy_rxcore_getstate_nphy` (phy_n.c:19705-19714): `r := (0xa2 >> 4) & 0xf`. -/
def wlcPhyRxcoreGetstateNphy (r : Reg) : ProgM Unit := do
  phyRead r 0xa2
  shri r 4
  andi r 0xf

/-- `wlc_phy_classifier_nphy(pi, mask, val)` (phy_n.c:21292-21314) with the
value in register `r` (core rev 23: no MAC suspend). Uses r0. -/
def wlcPhyClassifierNphyR (mask : UInt32) (r : Reg) : ProgM Unit := do
  phyRead 0 0xb0
  andi 0 0x7
  andi 0 (~~~mask)
  andi r mask
  emit (.alu .or 0 (.reg r))
  phyModR 0xb0 0x7 0

/-- Per-core registers of `wlc_phy_rfctrl_override_nphy` (phy_n.c:17161-17403),
rev 3..6: `(en_addr, val_addr, val_mask, val_shift)` for `field`. -/
def rfctrlField (field : UInt32) (core : Nat) : Option (UInt32 × UInt32 × UInt32 × UInt32) :=
  let c0 := core == 0
  let en : UInt32 := if c0 then 0xe7 else 0xec
  let v7a : UInt32 := if c0 then 0x7a else 0x7d
  match field with
  | 0x0002 => some (en, v7a, 0x1, 0)
  | 0x0004 => some (en, v7a, 0x2, 1)
  | 0x0008 => some (en, v7a, 0x4, 2)
  | 0x0010 => some (en, v7a, 0x10, 4)
  | 0x0020 => some (en, v7a, 0x20, 5)
  | 0x0040 => some (en, v7a, 0x40, 6)
  | 0x0080 => some (en, v7a, 0x80, 7)
  | 0x0100 => some (en, v7a, 0x700, 8)
  | 0x0800 => some (en, v7a, 0xe000, 13)
  | 0x0200 => some (en, if c0 then 0xf8 else 0xfa, 0x7, 0)
  | 0x0400 => some (en, if c0 then 0xf8 else 0xfa, 0x70, 4)
  | 0x1000 => some (en, if c0 then 0x7b else 0x7e, 0xffff, 0)
  | 0x2000 => some (en, if c0 then 0x7c else 0x7f, 0xffff, 0)
  | 0x4000 => some (en, if c0 then 0xf9 else 0xfb, 0xc0, 6)
  | 0x0001 => some (if c0 then 0xe5 else 0xe6, if c0 then 0xf9 else 0xfb, 0x8000, 15)
  | _ => none

/-- `wlc_phy_rfctrl_override_nphy` (phy_n.c:17161-17403), rev 3..6 branch. -/
def wlcPhyRfctrlOverrideNphy (cfg : PhyCfg) (field value : UInt32) (coreMask : Nat) (off : Bool) :
    ProgM Unit := do
  if cfg.phyRev < 3 || cfg.phyRev >= 7 then
    fail Fail.unsupported
    return
  for core in [0:2] do
    match rfctrlField field core with
    | none => fail Fail.unsupported
    | some (enAddr, valAddr, valMask, valShift) =>
      if off then
        phyAnd enAddr ((~~~field) &&& 0xffff)
        phyAnd valAddr ((~~~valMask) &&& 0xffff)
      else if coreMask == 0 || (coreMask >>> core) % 2 == 1 then
        phyOr enAddr field
        phyMod valAddr valMask (value <<< valShift)

/-- `NPHY_RfctrlIntc_override_*` fields used by the RSSI calibration. -/
inductive RfctrlIntc where
  | off | trsw

/-- `wlc_phy_rfctrlintc_override_nphy` (phy_n.c:18034-18266), rev 3..6, for
`RADIO_MIMO_CORESEL_ALLRXTX` and the OFF / TRSW fields. The WARN after the
TRSW SPINWAIT prints `Tag.overrideFailed` and leaves the routine, as
brcmsmac's `return` does. Uses r0–r2. -/
def wlcPhyRfctrlintcOverrideNphy (cfg : PhyCfg) (field : RfctrlIntc) (value : UInt32) :
    ProgM Unit := do
  let done ← newLabel
  for core in [0:2] do
    let intc : UInt32 := if core == 0 then 0x91 else 0x92
    phyMod intc 0x400 0x400
    match field with
    | .off =>
      phyWrite intc 0
      wlcPhyForceRfseqNphy cfg .reset2rx
    | .trsw =>
      phyMod intc 0x3c0 (value <<< 6)
      let ovr : UInt32 := if core == 0 then 0xe7 else 0xec
      phyMod ovr 0x1 0x1
      let bit : UInt32 := if core == 0 then 0x1 else 0x2
      phyMod 0x78 bit bit
      spinWhilePhySet 0x78 bit 10000 1 2
      phyRead 0 0x78
      andi 0 bit
      let ok ← newLabel
      emit (.branch .eq 0 (.imm 0) ok)
      printImm Tag.overrideFailed bit
      emit (.jump done)
      place ok
      phyMod ovr 0x1 0x0
  place done

/-- PHY register written by `wlc_phy_scale_offset_rssi_nphy` for a single
core (`RADIO_MIMO_CORESEL_CORE1/2`), rail and RSSI type (phy_n.c:21463-21590). -/
def rssiOffsetReg (core : Nat) (rail : Rail) (sel : RssiSel) : UInt32 :=
  let base : UInt32 := match sel with
    | .nb => 0x1a6 | .w1 => 0x1a4 | .w2 => 0x1a5
  base + (if core == 0 then 0 else 0xc) + (if rail == .i then 0 else 0x6)

/-- `wlc_phy_scale_offset_rssi_nphy` (phy_n.c:21463-21590) with generation-time
scale and offset. -/
def wlcPhyScaleOffsetRssiNphy (scale : UInt32) (offset : Int) (core : Nat) (rail : Rail)
    (sel : RssiSel) : ProgM Unit := do
  let o := max (min offset rssicalMaxRead) (-rssicalMaxRead - 1)
  phyWrite (rssiOffsetReg core rail sel) (((scale &&& 0x3f) <<< 8) ||| (i32 o &&& 0x3f))

/-- `wlc_phy_scale_offset_rssi_nphy(pi, 0, (s8) r, ...)` with the offset in
register `r` (a 32-bit value; the `(s8)` cast is applied here). Clobbers `r`. -/
def wlcPhyScaleOffsetRssiNphyR (r : Reg) (core : Nat) (rail : Rail) (sel : RssiSel) :
    ProgM Unit := do
  -- (s8) cast
  shli r 24
  emit (.alu .sar r (.imm 24))
  -- clamp to [-MAXREAD - 1, MAXREAD]
  let notHigh ← newLabel
  emit (.branch .lts r (.imm (i32 (rssicalMaxRead + 1))) notHigh)
  li r (i32 rssicalMaxRead)
  place notHigh
  let notLow ← newLabel
  emit (.branch .ges r (.imm (i32 (-rssicalMaxRead - 1))) notLow)
  li r (i32 (-rssicalMaxRead - 1))
  place notLow
  andi r 0x3f      -- scale 0
  phyWriteR (rssiOffsetReg core rail sel) r

/-- `wlc_phy_rssisel_nphy(pi, RADIO_MIMO_CORESEL_ALLRX, sel)` (phy_n.c:21631-21849),
rev ≥ 3, 2.4 GHz, for W1 / W2 / NB. -/
def wlcPhyRssiselNphy (sel : RssiSel) : ProgM Unit := do
  for core in [0:2] do
    let c0 := core == 0
    phyMod (if c0 then 0x8f else 0xa5) 0x200 0x200
    phyMod (if c0 then 0xa6 else 0xa7) 0x300 0
    let misc : UInt32 := if c0 then 0xf9 else 0xfb
    phyMod misc 0x3c 0
    -- W1 in 2.4 GHz: bit 3; W2: bit 4; NB: bit 5.
    let m : UInt32 := match sel with | .w1 => 0x8 | .w2 => 0x10 | .nb => 0x20
    phyMod misc m m
    phyMod (if c0 then 0xe5 else 0xe6) 0x20 0x20

/-- Registers saved and restored by `wlc_phy_poll_rssi_nphy` (rev ≥ 3). -/
def pollSaveRegs : Array UInt32 := #[0xa6, 0xa7, 0xf9, 0xfb, 0x8f, 0xa5, 0xe5, 0xe6]

/-- Body of the `wlc_phy_poll_rssi_nphy(pi, sel, buf, NPHY_RSSICAL_NPOLL)`
subroutine (phy_n.c:21851-21945), rev ≥ 3. On entry r8 = scratch address of
`rssi_buf[4]`; the four s32 sums are stored there. Uses r0–r7, r9; preserves r8.
The packed return value (`rssi_out_val`) is not used by the calibration and is
not formed. -/
def pollRssiBody (sel : RssiSel) : ProgM Unit := do
  for h : k in [0:pollSaveRegs.size] do
    phyRead 0 pollSaveRegs[k]
    stS (Scratch.pollSaves + 4 * k.toUInt32) 0
  wlcPhyRssiselNphy sel
  phyRead 0 0xca                       -- gpiosel_orig (rewritten only for rev < 2)
  for r in [1, 2, 3, 4] do li r 0
  for _ in [0:rssicalNPoll] do
    phyRead 5 0x219
    phyRead 6 0x21a
    -- tmp_buf[] = sign-extended 6-bit fields; rssi_buf[] += tmp_buf[].
    for (dst, src, hi) in [(1, 5, false), (2, 5, true), (3, 6, false), (4, 6, true)] do
      mov 0 src
      if hi then shri 0 8
      shli 0 26
      emit (.alu .sar 0 (.imm 26))
      emit (.alu .add dst (.reg 0))
  for (r, off) in [(1, 0), (2, 4), (3, 8), (4, 12)] do
    emit (.memStore 4 8 (off : Nat).toUInt32 (.reg r))
  for h : k in [0:pollSaveRegs.size] do
    ldS 0 (Scratch.pollSaves + 4 * k.toUInt32)
    phyWriteR pollSaveRegs[k] 0

/-- Round `(target * NPOLL - r3) / NPOLL` to nearest as brcmsmac does
(magnitude + NPOLL/2, truncating divide, sign restored) into r4. Uses r5. -/
def fineOffsetFrom (target : Int) : ProgM Unit := do
  li 4 (i32 (target * rssicalNPoll))
  emit (.alu .sub 4 (.reg 3))
  let pos ← newLabel
  let done ← newLabel
  emit (.branch .ges 4 (.imm 0) pos)
  neg 4 5
  addi 4 (rssicalNPoll / 2).toUInt32
  emit (.alu .sdiv 4 (.imm rssicalNPoll.toUInt32))
  neg 4 5
  emit (.jump done)
  place pos
  addi 4 (rssicalNPoll / 2).toUInt32
  emit (.alu .sdiv 4 (.imm rssicalNPoll.toUInt32))
  place done

/-- Registers saved by `wlc_phy_rssi_cal_nphy_rev3` (rev < 7), in order. -/
def saveRegs : Array UInt32 :=
  #[0x91, 0x92, 0x8f, 0xa5, 0xa6, 0xa7, 0xe7, 0xec, 0xe5, 0xe6, 0x78, 0xf9, 0xfb, 0x7a, 0x7d]

def saveSlot (reg : UInt32) : UInt32 :=
  Scratch.saves + 4 * (saveRegs.findIdx? (· == reg)).get!.toUInt32

/-- Offset registers cached in `pi->rssical_cache.rssical_phyregs_2G[0..11]`. -/
def cachePhyRegs : Array UInt32 :=
  #[0x1a6, 0x1ac, 0x1b2, 0x1b8, 0x1a4, 0x1aa, 0x1b0, 0x1b6, 0x1a5, 0x1ab, 0x1b1, 0x1b7]

/-- NB pass for one core: VCM sweep, VCM choice, NB fine offsets
(phy_n.c:22430-22557). `pollNb` is the NB poll subroutine label. -/
def nbCore (core : Nat) (pollNb : Nat) : ProgM Unit := do
  wlcPhyScaleOffsetRssiNphy 0 0 core .i .nb
  wlcPhyScaleOffsetRssiNphy 0 0 core .q .nb
  for vcm in [0:vcmLevelMax] do
    radioMod (radio2056RxRssiMisc core) radio2056VcmMask (vcm.toUInt32 <<< radio2056RssiVcmShift)
    li 8 (Scratch.pollResults + 16 * vcm.toUInt32)
    emit (.call pollNb)
  -- result_idx == 2 * core (the I rail; the search also uses rail Q).
  let ri := 2 * core
  li 0 rssicalMaxD                                          -- min_d
  li 1 0                                                    -- min_vcm
  li 2 (i32 (rssicalMaxRead * rssicalNPoll + 1))            -- min_poll
  for vcm in [0:vcmLevelMax] do
    let row := Scratch.pollResults + 16 * vcm.toUInt32
    ldS 3 (row + 4 * ri.toUInt32)
    ldS 4 (row + 4 * (ri + 1).toUInt32)
    mov 5 3
    emit (.alu .mul 5 (.reg 3))
    mov 6 4
    emit (.alu .mul 6 (.reg 4))
    emit (.alu .add 5 (.reg 6))                             -- curr_d
    let noD ← newLabel
    emit (.branch .ges 5 (.reg 0) noD)
    mov 0 5
    li 1 vcm.toUInt32
    place noD
    let noP ← newLabel
    emit (.branch .ges 3 (.reg 2) noP)
    mov 2 3
    place noP
  stS Scratch.vcmFinal 1
  stS (Scratch.pollResultsMin + 4 * ri.toUInt32) 2
  shli 1 radio2056RssiVcmShift
  radioModR (radio2056RxRssiMisc core) radio2056VcmMask 1
  for idx in [ri, ri + 1] do
    ldS 9 Scratch.vcmFinal
    shli 9 4
    emit (.memLoad 4 3 9 (Scratch.pollResults + 4 * idx.toUInt32))
    fineOffsetFrom rssicalNbTarget
    ldS 5 (Scratch.pollResultsMin + 4 * idx.toUInt32)
    let keep ← newLabel
    emit (.branch .ne 5 (.imm (i32 (rssicalMaxRead * rssicalNPoll))) keep)
    li 4 (i32 (rssicalNbTarget - rssicalMaxRead - 1))
    place keep
    stS (Scratch.fineOffset + 4 * idx.toUInt32) 4
    wlcPhyScaleOffsetRssiNphyR 4 core (if idx % 2 == 0 then .i else .q) .nb

/-- W1 / W2 pass for one core (phy_n.c:22561-22630). As in brcmsmac, both
rails are written with `fine_digital_offset[core * 2]` (the I-rail value). -/
def wbCore (core : Nat) (sel : RssiSel) (pollW : Nat) : ProgM Unit := do
  wlcPhyScaleOffsetRssiNphy 0 0 core .i sel
  wlcPhyScaleOffsetRssiNphy 0 0 core .q sel
  li 8 Scratch.pollResultCore
  emit (.call pollW)
  for idx in [2 * core, 2 * core + 1] do
    ldS 3 (Scratch.pollResultCore + 4 * idx.toUInt32)
    fineOffsetFrom rssicalWbTargetRev3
    stS (Scratch.fineOffset + 4 * idx.toUInt32) 4
    ldS 4 (Scratch.fineOffset + 4 * (2 * core).toUInt32)
    wlcPhyScaleOffsetRssiNphyR 4 core (if idx % 2 == 0 then .i else .q) sel

/-- Skip `body` at run time unless bit `core` of the saved `rxcore_state` is set. -/
def ifRxCore (core : Nat) (body : ProgM Unit) : ProgM Unit := do
  let skip ← newLabel
  ldS 0 Scratch.rxcoreState
  andi 0 ((1 : UInt32) <<< core.toUInt32)
  emit (.branch .eq 0 (.imm 0) skip)
  body
  place skip

/-- `wlc_phy_rssi_cal_nphy_rev3` (phy_n.c:22277-22764) for rev 3..6, 2.4 GHz,
two cores, radio 2056. -/
def wlcPhyRssiCalNphyRev3 (cfg : PhyCfg) : ProgM Unit := do
  if cfg.phyRev < 3 || cfg.phyRev >= 7 then
    fail Fail.unsupported
    return
  -- The three poll subroutines (one per RSSI type), jumped over.
  let pollNb ← newLabel
  let pollW1 ← newLabel
  let pollW2 ← newLabel
  let start ← newLabel
  emit (.jump start)
  place pollNb; pollRssiBody .nb; emit .ret
  place pollW1; pollRssiBody .w1; emit .ret
  place pollW2; pollRssiBody .w2; emit .ret
  place start
  -- poll_results_min[] = { 0 } (only even entries are written below).
  for k in [0:4] do stSi (Scratch.pollResultsMin + 4 * k.toUInt32) 0
  -- classif_state = classifier(0, 0); classifier(7, 4)
  wlcPhyClassifierNphy cfg 0 0
  stS Scratch.classifState 0
  wlcPhyClassifierNphy cfg 0x7 4
  -- clip_det(0, clip_state); clip_det(1, clip_off = {0xffff, 0xffff})
  wlcPhyClipDetNphyRead cfg
  stS Scratch.clipState0 0
  stS Scratch.clipState1 1
  phyWrite 0x2c 0xffff
  phyWrite 0x42 0xffff
  for h : k in [0:saveRegs.size] do
    phyRead 0 saveRegs[k]
    stS (Scratch.saves + 4 * k.toUInt32) 0
  wlcPhyRfctrlintcOverrideNphy cfg .off 0
  wlcPhyRfctrlintcOverrideNphy cfg .trsw 1
  wlcPhyRfctrlOverrideNphy cfg 0x1 0 0 false
  wlcPhyRfctrlOverrideNphy cfg 0x2 1 0 false
  wlcPhyRfctrlOverrideNphy cfg 0x80 1 0 false
  wlcPhyRfctrlOverrideNphy cfg 0x40 1 0 false
  -- CHSPEC_IS2G
  wlcPhyRfctrlOverrideNphy cfg 0x10 0 0 false
  wlcPhyRfctrlOverrideNphy cfg 0x20 1 0 false
  wlcPhyRxcoreGetstateNphy 0
  stS Scratch.rxcoreState 0
  -- phy_corenum = 2
  for core in [0:2] do
    ifRxCore core (nbCore core pollNb)
  for core in [0:2] do
    ifRxCore core do
      wbCore core .w1 pollW1
      wbCore core .w2 pollW2
  ldS 0 (saveSlot 0x91); phyWriteR 0x91 0
  ldS 0 (saveSlot 0x92); phyWriteR 0x92 0
  wlcPhyForceRfseqNphy cfg .reset2rx
  phyMod 0xe7 0x1 0x1
  phyMod 0x78 0x1 0x1
  phyMod 0xe7 0x1 0x0
  phyMod 0xec 0x1 0x1
  phyMod 0x78 0x2 0x2
  phyMod 0xec 0x1 0x0
  for reg in [0x8f, 0xa5, 0xa6, 0xa7, 0xe7, 0xec, 0xe5, 0xe6, 0x78, 0xf9, 0xfb, 0x7a, 0x7d] do
    ldS 0 (saveSlot reg)
    phyWriteR reg 0
  -- CHSPEC_IS2G: fill rssical_cache (2G) and nphy_rssical_chanspec_2G.
  for core in [0:2] do
    radioRead 0 (radio2056RxRssiMisc core)
    stS (Scratch.cacheRadio + 2 * core.toUInt32) 0 2
  for h : k in [0:cachePhyRegs.size] do
    phyRead 0 cachePhyRegs[k]
    stS (Scratch.cachePhy + 2 * k.toUInt32) 0 2
  stSi Scratch.cacheChanspec (chanspec20 cfg) 2
  -- classifier(7, classif_state); clip_det(1, clip_state)
  ldS 1 Scratch.classifState
  wlcPhyClassifierNphyR 0x7 1
  ldS 0 Scratch.clipState0; phyWriteR 0x2c 0
  ldS 0 Scratch.clipState1; phyWriteR 0x42 0

/-- `wlc_phy_rssi_cal_nphy` (phy_n.c:22958-22967): rev ≥ 3 → rev3 routine.
For the `rssiCal` hook of `NPhyInit.initNphy`. -/
def rssiCal (cfg : PhyCfg) : ProgM Unit :=
  if cfg.phyRev >= 3 then wlcPhyRssiCalNphyRev3 cfg
  else fail Fail.unsupported      -- wlc_phy_rssi_cal_nphy_rev2 is not ported

end LeanOS.Wifi.NPhyRssiCal
