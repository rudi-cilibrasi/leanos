import LeanOS.Wifi.NPhyInit

/-
N-PHY receive IQ calibration (`wlc_phy_cal_rxiq_nphy(target_gain, 2, false)`)
for the BCM43224 programs.

Ported from Linux brcmsmac (ISC license), Copyright (c) 2010 Broadcom
Corporation; see drivers/net/wireless/broadcom/brcm80211/brcmsmac at Linux
commit fd179f8a05be3ccae366b9b96e176b51fbe54aab. The CORDIC tone generator
follows Linux `lib/math/cordic.c` (ISC header, Copyright (c) 2011 Broadcom
Corporation) and `include/linux/cordic.h`.

Scope: N-PHY rev 6 / radio 2056 rev 11 / 2.4 GHz / 20 MHz / IPA, i.e. the
`wlc_phy_cal_rxiq_nphy_rev3` path (phy_n.c:27304-27463) with `cal_type = 2`
(IQ compensation for both cores, then the RC-filter sweep on core 1). Every
revision / band / bandwidth / radio-revision branch is decided while
generating; values read from hardware are handled in bytecode.

## Run-time state (scratch RAM, region 0x5800-0x5BFF only)
brcmsmac keeps several `pi->` fields across the helpers used here; they live
in scratch (see `Scr`). The target TX gain (`struct nphy_txgains`) is read
from the shared slot 0x5C00 (`txlpf[2] txgm[2] pga[2] pad[2] ipa[2]`, u16 LE).

## State assumed on entry (set by the init path / TX calibration)
* `pi->nphy_deaf_count == 0` (every carrier-search enter has been left).
* `pi->phyhang_avoid == false` (rev 6), `pi->nphy_txpwrctrl == PHY_TPC_HW_OFF`
  (`wlc_phy_init_nphy` turned hardware power control off before the cals).
* `pi->nphy_bb_mult_save == 0` (every sample playback has been stopped).
* `pi->rx2tx_biasentry == -1` (attach value; `phyrxchain == 3` so
  `wlc_phy_rxcore_setstate_nphy` has not run).
* `pi->nphy_txpwrindex[core].index >= 0`: `wlc_phy_cal_txgainctrl_nphy`
  (from `wlc_phy_precal_txgain_nphy`) finished with
  `wlc_phy_txpwr_index_nphy(core, nphy_txcal_pwr_idx[core], true)`. The
  values that call saved when it first left `AUTO` (`AfeCtrlDacGain`,
  `rad_gain`, `bbmult`) are the ones `wlc_phy_txpwr_fixpower_nphy` wrote for
  index `fixTxPwrIndex` (40), and `AfectrlOverride` is 0 (never assigned for
  rev >= 3). They are only used if the RX gain search reaches table entry 0
  (`txpwrindex = (s8)128 = -128`, the "restore" branch).
-/
namespace LeanOS.Wifi.NPhyRxCal

open LeanOS.Wifi.Bytecode LeanOS.Wifi.Bcm43224 LeanOS.Wifi.NPhy
open LeanOS.Wifi.NPhyInit (wlcPhyForceRfseqNphy wlcPhyClassifierNphy phyclkFgc txpwrctrlOff
  tableReadSeq ipaGainTbl fixTxPwrIndex nphyGmval Rfseq)

/-! ## Diagnostics -/

namespace Fail
/-- The configuration is not N-PHY rev 3..6 / radio 2056 rev >= 5 / IPA 2.4 GHz
20 MHz. -/
def unsupported : UInt32 := 0x7EA0
/-- The RX gain search did not settle within its bound (cannot happen: the
table index moves monotonically over six entries). -/
def gainLoop : UInt32 := 0x7EA1
/-- `wlc_phy_rxcore_setstate_nphy` found the MAC running; brcmsmac would
suspend it (`wlapi_suspend_mac_and_wait`), which this port does not carry. -/
def macRunning : UInt32 := 0x7EA2
/-- A generation-time table (gain table, tone samples) failed its check. -/
def badTable : UInt32 := 0x7EA3
end Fail

namespace Tag
/-- `wlc_phy_rx_iq_est_nphy` WARN "HW error: rxiq est" (value: 0x129). -/
def iqEstTimeout : UInt32 := 0x0480
/-- `wlc_phy_rfctrlintc_override_nphy` WARN "HW error: override failed". -/
def trswOverride : UInt32 := 0x0481
/-- `wlc_phy_calc_rx_iq_comp_nphy` estimate rejected (value: retry count). -/
def compRetry : UInt32 := 0x0482
/-- Final RX IQ compensation: `a0 << 16 | b0`, then `a1 << 16 | b1`. -/
def rxIqComp : UInt32 := 0x0483
/-- Best RC-cal value from `wlc_phy_rc_sweep_nphy` (u8, value - 0x80). -/
def rccal : UInt32 := 0x0484
end Tag

/-! ## Scratch layout (0x5800-0x5BFF) -/

namespace Scr
def gainSave : UInt32 := 0x5800        -- u16 [2]
def origBBConfig : UInt32 := 0x5804    -- u16
def rxcoreState : UInt32 := 0x5806     -- u16
def classifierState : UInt32 := 0x5808 -- u16
def clipState : UInt32 := 0x580A       -- u16 [2]
def radioSave : UInt32 := 0x5810       -- u16 [5]  tx_rx_cal_radio_saveregs
def phySave : UInt32 := 0x5820         -- u16 [11] tx_rx_cal_phy_saveregs
/-- `struct phy_iq_est est[2]`: per core `i_pwr, q_pwr, iq_prod` (u32). -/
def est : UInt32 := 0x5840
def oldComp : UInt32 := 0x5860         -- u16 a0 b0 a1 b1
def newComp : UInt32 := 0x5868        -- u16 a0 b0 a1 b1
def saveComp : UInt32 := 0x5870       -- u16 a0 b0 a1 b1 (gain control)
def bbMultSave : UInt32 := 0x5878     -- u32 pi->nphy_bb_mult_save
def biasEntry : UInt32 := 0x587C      -- u8  pi->rx2tx_biasentry (0xFF = -1)
/-- `pi->nphy_txpwrindex[core]`: +0 index (s32), +4 AfeCtrlDacGain,
+6 rad_gain, +8 bbmult (u16 each); 16 bytes per core. -/
def txpwrIdx : UInt32 := 0x5880
def txpwrArg : UInt32 := 0x58A0       -- s32 argument of txpwrIndex
-- gain control locals (s32/u32)
def gcCur : UInt32 := 0x58B0
def gcPrev : UInt32 := 0x58B4
def gcDirn : UInt32 := 0x58B8
def gcPrevPwr : UInt32 := 0x58BC
def gcOptimPwr : UInt32 := 0x58C0
def gcOptimIdx : UInt32 := 0x58C4
def gcDone : UInt32 := 0x58C8
def gcIter : UInt32 := 0x58CC
def gcCurrPwr : UInt32 := 0x58D0
-- rx iq comp locals
def compErr : UInt32 := 0x58E0
def compRetry : UInt32 := 0x58E4
-- rc sweep saves (u16)
def rcOrigTxlpf : UInt32 := 0x5900
def rcOrigRxhpc : UInt32 := 0x5902
def rcOrigDcBypass : UInt32 := 0x5904
def rcOrigFilt : UInt32 := 0x5906     -- u16 [10] 0x267..0x270
def rcOrigOvr : UInt32 := 0x591A      -- u16 [2] 0xe7 0xec
def rcOrigAux : UInt32 := 0x591E      -- u16 [2] 0xf8 0xfa
def rcOrigRssiOthers : UInt32 := 0x5922
-- rc sweep locals (u32)
def rcVal : UInt32 := 0x5930
def rcLastVal : UInt32 := 0x5934
def rcLastRatio : UInt32 := 0x5938
def rcRatio : UInt32 := 0x593C
def rcRef : UInt32 := 0x5940
def rcBest : UInt32 := 0x5944
def bestRccal : UInt32 := 0x5950      -- u32 best_rccal (u8 value)
/-- `pi->nphy_rccal_value` (only read by the 40 MHz channel-11 LPF
adjustment, which this board never takes; kept for completeness). -/
def rccalValue : UInt32 := 0x5954
-- iq comp arithmetic temporaries
def mIq : UInt32 := 0x5960
def mIi : UInt32 := 0x5964
def mQq : UInt32 := 0x5968
def mIqN : UInt32 := 0x596C
def mQqN : UInt32 := 0x5970
def mA : UInt32 := 0x5974
/-- End of this module's region (exclusive). -/
def limit : UInt32 := 0x5C00
end Scr

/-- Shared target TX gain, `struct nphy_txgains` (u16 fields, LE). -/
def txGainsSlot : UInt32 := 0x5C00

/-! ## Scratch and subroutine helpers -/

/-- `dst := mem[addr]` (width 1, 2 or 4). Uses r13 as the zero base. -/
def ld (w : Nat) (dst : Reg) (addr : UInt32) : ProgM Unit := do
  li 13 0
  emit (.memLoad w dst 13 addr)

/-- `mem[addr] := src`. Uses r13 as the zero base. -/
def st (w : Nat) (addr : UInt32) (src : Reg) : ProgM Unit := do
  li 13 0
  emit (.memStore w 13 addr (.reg src))

def stI (w : Nat) (addr v : UInt32) : ProgM Unit := do
  li 13 0
  emit (.memStore w 13 addr (.imm v))

def br (c : Cond) (r : Reg) (v : UInt32) (l : Nat) : ProgM Unit := emit (.branch c r (.imm v) l)
def brR (c : Cond) (r s : Reg) (l : Nat) : ProgM Unit := emit (.branch c r (.reg s) l)
def jmp (l : Nat) : ProgM Unit := emit (.jump l)
def call (l : Nat) : ProgM Unit := emit (.call l)
def alu (op : AluOp) (d s : Reg) : ProgM Unit := emit (.alu op d (.reg s))
def aluI (op : AluOp) (d : Reg) (v : UInt32) : ProgM Unit := emit (.alu op d (.imm v))

/-- Emit `body` as a subroutine in place (jumped over) and return its label. -/
def subroutine (body : ProgM Unit) : ProgM Nat := do
  let entry ← newLabel
  let skip ← newLabel
  jmp skip
  place entry
  body
  emit .ret
  place skip
  return entry

/-- Table element read at a run-time address: `addrReg` holds
`(id << 10) | offset`; same access sequence as `NPhy.tableRead` (43224 rev 1
read quirk). Uses r9-r11. `addrReg` must not be r9-r12 or `dst`. -/
def tableReadAt (dst addrReg : Reg) (width : UInt32) : ProgM Unit := do
  phyWriteR tblAddr addrReg
  phyRead 9 tblDataLo
  phyWriteR tblAddr addrReg
  if width == 32 then
    phyRead 9 tblDataLo
    phyRead dst tblDataHi
    shli dst 16
    alu .or dst 9
  else
    phyRead dst tblDataLo

/-! ## Arithmetic subroutines (unit-tested in `tests/WifiNPhyRxCal.lean`) -/

/-- `wlc_phy_nbits(s32 value)` (phy_cmn.c:2422-2432): r0 := number of bits
of `abs(r0)`. `abs(INT_MIN)` stays negative, so the result is 0 as in C.
Uses r1-r2. -/
def nbitsBody : ProgM Unit := do
  let pos ← newLabel
  let loop ← newLabel
  let done ← newLabel
  mov 1 0
  br .ges 1 0 pos
  li 2 0
  alu .sub 2 1
  mov 1 2
  place pos
  li 0 0
  place loop
  mov 2 1
  alu .sar 2 0
  br .lts 2 1 done             -- (abs_val >> nbits) <= 0
  addi 0 1
  br .ltu 0 32 loop
  place done

/-- `(s32) int_sqrt((unsigned long) b)` for an s32 `b` in r0 (lib/math
int_sqrt: floor square root). A negative `b` becomes 2^64 + b as a 64-bit
`unsigned long` whose root truncates to 0xFFFFFFFF, i.e. -1 as s32 (the
x86-64 behaviour). Result in r0; uses r1-r3. -/
def isqrtBody : ProgM Unit := do
  let neg ← newLabel
  let loop ← newLabel
  let skip ← newLabel
  let done ← newLabel
  br .lts 0 0 neg
  li 1 0                        -- y
  li 2 0x40000000               -- m
  place loop
  br .eq 2 0 done
  mov 3 1
  alu .add 3 2                  -- b = y + m
  shri 1 1
  brR .ltu 0 3 skip
  alu .sub 0 3
  alu .add 1 2
  place skip
  shri 2 2
  jmp loop
  place neg
  li 1 0xFFFFFFFF
  place done
  mov 0 1

/-- The arithmetic core of `wlc_phy_calc_rx_iq_comp_nphy`
(phy_n.c:26113-26161) for one core. Inputs r1 = `iq` (s32), r2 = `ii`,
r3 = `qq` (u32). Outputs r0 = 0 (ok) or 1 (`-EBADE`), r4 = `a`, r5 = `b`
(s32, before the `& 0x3ff`). Shift counts follow C; the one count that can
go negative (`30 - iq_nbits` with `iq_nbits == 31`) is masked to 5 bits, as
the x86 `shl` does. Uses r0-r8 and the `Scr.m*` temporaries. -/
def iqCompMathBody (nbits isqrt : Nat) : ProgM Unit := do
  let err ← newLabel
  let negA ← newLabel
  let divA ← newLabel
  let negB ← newLabel
  let divB ← newLabel
  st 4 Scr.mIq 1
  st 4 Scr.mIi 2
  st 4 Scr.mQq 3
  mov 0 2
  alu .add 0 3
  br .ltu 0 2 err                        -- (ii + qq) < NPHY_MIN_RXIQ_PWR
  ld 4 0 Scr.mIq
  call nbits
  st 4 Scr.mIqN 0
  ld 4 0 Scr.mQq
  call nbits
  st 4 Scr.mQqN 0
  -- a
  ld 4 1 Scr.mIqN
  li 4 30
  alu .sub 4 1
  andi 4 31                              -- 30 - iq_nbits
  ld 4 5 Scr.mIq
  alu .shl 5 4
  li 6 0
  alu .sub 6 5                           -- -(iq << (30 - iq_nbits))
  mov 7 1
  aluI .sub 7 20                         -- arsh = 10 - (30 - iq_nbits)
  ld 4 2 Scr.mIi
  br .lts 7 0 negA
  mov 3 7
  addi 3 1
  mov 8 2
  alu .shr 8 3
  alu .add 6 8                           -- + (ii >> (1 + arsh))
  mov 8 2
  alu .shr 8 7                           -- temp = ii >> arsh
  jmp divA
  place negA
  li 3 0
  alu .sub 3 7                           -- -arsh
  mov 4 3
  aluI .sub 4 1                          -- -1 - arsh
  mov 8 2
  alu .shl 8 4
  alu .add 6 8                           -- + (ii << (-1 - arsh))
  mov 8 2
  alu .shl 8 3                           -- temp = ii << -arsh
  place divA
  br .eq 8 0 err
  alu .sdiv 6 8                          -- a /= temp
  st 4 Scr.mA 6
  -- b
  ld 4 1 Scr.mQqN
  mov 7 1
  aluI .sub 7 11                         -- brsh = qq_nbits - 31 + 20
  li 4 31
  alu .sub 4 1
  ld 4 5 Scr.mQq
  alu .shl 5 4                           -- b = qq << (31 - qq_nbits)
  ld 4 2 Scr.mIi
  br .lts 7 0 negB
  mov 8 2
  alu .shr 8 7
  jmp divB
  place negB
  li 3 0
  alu .sub 3 7
  mov 8 2
  alu .shl 8 3
  place divB
  br .eq 8 0 err
  alu .sdiv 5 8                          -- b /= temp
  ld 4 6 Scr.mA
  mov 3 6
  alu .mul 3 6
  alu .sub 5 3                           -- b -= a * a
  mov 0 5
  call isqrt
  mov 5 0
  aluI .sub 5 1024                       -- b -= 1 << 10
  mov 4 6
  li 0 0
  emit .ret
  place err
  li 0 1

/-! ## Tone generation (generation-time CORDIC) -/

/-- `arctan_table` of lib/math/cordic.c (atan(2^-i) in degrees, Q16). -/
def arctanTable : Array Int := #[2949120, 1740967, 919879, 466945, 234379, 117304,
  58666, 29335, 14668, 7334, 3667, 1833, 917, 458, 229, 115, 57, 29]

def cordicFixed (x : Int) : Int := x * 65536
/-- `CORDIC_FLOAT` (include/linux/cordic.h). -/
def cordicFloat (x : Int) : Int :=
  if x ≥ 0 then ((x >>> 15) + 1) >>> 1 else -((((-x) >>> 15) + 1) >>> 1)

/-- `cordic_calc_iq(theta)` (lib/math/cordic.c): (i, q) ≈ 2^16·(cos, sin). -/
def cordicCalcIq (theta0 : Int) : Int × Int := Id.run do
  let mut ci : Int := 39797               -- CORDIC_ANGLE_GEN
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
  for h : iter in [0:arctanTable.size] do
    let valtmp : Int := if theta > angle then ci - (cq >>> iter) else ci + (cq >>> iter)
    if theta > angle then
      cq := cq + (ci >>> iter)
      angle := angle + arctanTable[iter]
    else
      cq := cq - (ci >>> iter)
      angle := angle - arctanTable[iter]
    ci := valtmp
  return (ci * signx, cq * signx)

/-- The sample-play words of `wlc_phy_gen_load_samples_nphy` +
`wlc_phy_loadsampletable_nphy` (phy_n.c:23004-23076) for a tone of `fKHz`,
amplitude `maxVal`, with `phyBw` (20, or 80/82 in DAC test mode) and
`tblLen` samples. -/
def toneSamples (fKHz maxVal phyBw tblLen : Nat) : Array UInt32 := Id.run do
  let rot : Int := ((fKHz * 36) / phyBw / 100 : Nat)
  let mut theta : Int := 0
  let mut out := #[]
  for _ in [0:tblLen] do
    let (ci, cq) := cordicCalcIq theta
    theta := theta + rot
    let q := cordicFloat (cq * maxVal)
    let i := cordicFloat (ci * maxVal)
    out := out.push ((((i % 1024).toNat <<< 10) ||| (q % 1024).toNat).toUInt32)
  return out

/-- `NPHY_RXCAL_TONEAMP`. -/
def rxcalToneAmp : Nat := 181

/-- Load `samples` into NPHY_TBL_ID_SAMPLEPLAY (17) from the blob, 32-bit
elements (hi then lo, as `wlc_phy_table_write_nphy`). Uses r3-r5. -/
def loadSamples (name : String) (samples : Array UInt32) : ProgM Unit := do
  let bytes := samples.foldl (fun b v => putU32 b v) ByteArray.empty
  let off ← addBlob name bytes
  phyWrite tblAddr ((17 : UInt32) <<< 10)
  let top ← newLabel
  li 3 0
  place top
  emit (.blobLoad32 4 3 off)
  mov 5 4
  shri 5 16
  phyWriteR tblDataHi 5
  phyWriteR tblDataLo 4
  addi 3 1
  br .ltu 3 samples.size.toUInt32 top

/-- `wlc_phy_runsamples_nphy(pi, numSamps, 0xffff, 0, 0, dacTestMode, false)`
(phy_n.c:23078-23157), rev < 7, 20 MHz, `phyhang_avoid` false. The
`nphy_bb_mult_save` bookkeeping lives in `Scr.bbMultSave`. Uses r0-r2. -/
def runSamples (numSamps : UInt32) (dacTestMode : Nat) : ProgM Unit := do
  let saved ← newLabel
  ld 4 0 Scr.bbMultSave
  shri 0 31
  br .ne 0 0 saved
  NPhy.tableRead 0 15 87 16                   -- NPHY_TBL_ID_IQLOCAL
  andi 0 0xffff
  ori 0 0x80000000                            -- BB_MULT_VALID_MASK
  st 4 Scr.bbMultSave 0
  place saved
  phyWrite 0xc6 (numSamps - 1)
  phyWrite 0xc4 0xffff                        -- loops == 0xffff
  phyWrite 0xc5 0
  phyRead 2 0xa1
  phyOr 0xa1 0x0001                           -- NPHY_RfseqMode_CoreActv_override
  phyWrite 0xc3 (if dacTestMode == 1 then 0x5 else 0x1)
  NPhyInit.spinWhilePhySet 0xa4 0x1 1000 0 1
  phyWriteR 0xa1 2

/-- `wlc_phy_tx_tone_nphy(pi, fKHz, NPHY_RXCAL_TONEAMP, 0, dacTestMode, false)`
(phy_n.c:23159-23175) for 20 MHz. In DAC test mode 1 the sample count and
rotation depend on BBConfig (0x01) bit 15 at run time (80 or 82), so both
tables are carried. Uses r0-r5. -/
def txToneBody (fKHz : Nat) (dacTestMode : Nat) : ProgM Unit := do
  if dacTestMode == 1 then
    let s80 := toneSamples fKHz rxcalToneAmp 80 160
    let s82 := toneSamples fKHz rxcalToneAmp 82 164
    let use82 ← newLabel
    let done ← newLabel
    phyRead 0 0x01
    shri 0 15
    andi 0 1
    br .ne 0 0 use82
    loadSamples s!"rxcal tone {fKHz} kHz /80" s80
    runSamples 160 1
    jmp done
    place use82
    loadSamples s!"rxcal tone {fKHz} kHz /82" s82
    runSamples 164 1
    place done
  else
    let s := toneSamples fKHz rxcalToneAmp 20 160
    loadSamples s!"rxcal tone {fKHz} kHz" s
    runSamples 160 dacTestMode

/-- `wlc_phy_stopplayback_nphy` (phy_n.c:23177-23216), rev < 7, with the
`nphy_bb_mult_save` restore from `Scr.bbMultSave`. Uses r0-r1. -/
def stopPlaybackBody : ProgM Unit := do
  let notSample ← newLabel
  let cmdDone ← newLabel
  let noRestore ← newLabel
  phyRead 0 0xc7
  mov 1 0
  andi 1 0x1
  br .eq 1 0 notSample
  phyOr 0xc3 0x0002                    -- NPHY_sampleCmd_STOP
  jmp cmdDone
  place notSample
  andi 0 0x2
  br .eq 0 0 cmdDone
  phyAnd 0xc2 0x7fff                   -- ~NPHY_iqloCalCmdGctl_IQLO_CAL_EN
  place cmdDone
  phyAnd 0xc3 (~~~0x4 &&& 0xffff)
  ld 4 0 Scr.bbMultSave
  mov 1 0
  shri 1 31
  br .eq 1 0 noRestore
  andi 0 0xffff
  tableWriteR 15 87 16 0
  stI 4 Scr.bbMultSave 0
  place noRestore

/-! ## PHY helpers on this path -/

/-- `wlc_phy_resetcca_nphy` (phy_n.c:19550-19563). Uses r0-r2. -/
def resetCca (cfg : PhyCfg) : ProgM Unit := do
  phyclkFgc true
  phyRead 0 0x01
  mov 1 0
  ori 1 0x4000                         -- BBCFG_RESETCCA
  phyWriteR 0x01 1
  delay 1
  andi 0 (~~~0x4000 &&& 0xffff)
  phyWriteR 0x01 0
  phyclkFgc false
  wlcPhyForceRfseqNphy cfg .reset2rx

/-- `wlc_phy_stay_in_carriersearch_nphy` (phy_n.c:28545-28570) with
`nphy_deaf_count` 0 → 1 (enable) and 1 → 0 (disable). -/
def stayInCarrierSearch (cfg : PhyCfg) (enable : Bool) (resetCcaL : Nat) : ProgM Unit := do
  if enable then
    wlcPhyClassifierNphy cfg 0 0       -- r0 := current classifier state
    st 2 Scr.classifierState 0
    wlcPhyClassifierNphy cfg 0x7 4
    phyRead 0 0x2c                     -- wlc_phy_clip_det_nphy(read)
    st 2 Scr.clipState 0
    phyRead 0 0x42
    st 2 (Scr.clipState + 2) 0
    phyWrite 0x2c 0xffff               -- clip_off
    phyWrite 0x42 0xffff
    call resetCcaL
  else
    phyRead 1 0xb0                     -- wlc_phy_classifier_nphy(0x7, state)
    ld 2 0 Scr.classifierState
    andi 0 0x7
    phyModR 0xb0 0x7 0
    ld 2 0 Scr.clipState
    phyWriteR 0x2c 0
    ld 2 0 (Scr.clipState + 2)
    phyWriteR 0x42 0

/-- A run-time or constant value for the override helpers. -/
inductive Val where
  | imm (v : UInt32)
  | reg (r : Reg)

/-- `wlc_phy_rfctrl_override_nphy` (phy_n.c:17162-17300), rev 3..6 branch.
A register value is shifted into place in r8. -/
def rfctrlOverride (field : UInt32) (value : Val) (coreMask : Nat) (off : Bool) :
    ProgM Unit := do
  for core in [0:2] do
    let c0 := core == 0
    let e : UInt32 := if c0 then 0xe7 else 0xec
    let rssi : UInt32 := if c0 then 0x7a else 0x7d
    let aux : UInt32 := if c0 then 0xf8 else 0xfa
    let spec : Option (UInt32 × UInt32 × UInt32 × UInt32) :=
      -- (en_addr, val_addr, val_mask, val_shift)
      if field == 0x2 then some (e, rssi, 0x1, 0)
      else if field == 0x4 then some (e, rssi, 0x2, 1)
      else if field == 0x8 then some (e, rssi, 0x4, 2)
      else if field == 0x10 then some (e, rssi, 0x10, 4)
      else if field == 0x20 then some (e, rssi, 0x20, 5)
      else if field == 0x40 then some (e, rssi, 0x40, 6)
      else if field == 0x80 then some (e, rssi, 0x80, 7)
      else if field == 0x100 then some (e, rssi, 0x700, 8)
      else if field == 0x800 then some (e, rssi, 0xe000, 13)
      else if field == 0x200 then some (e, aux, 0x7, 0)
      else if field == 0x400 then some (e, aux, 0x70, 4)
      else if field == 0x1000 then some (e, if c0 then 0x7b else 0x7e, 0xffff, 0)
      else if field == 0x2000 then some (e, if c0 then 0x7c else 0x7f, 0xffff, 0)
      else if field == 0x4000 then some (e, if c0 then 0xf9 else 0xfb, 0xc0, 6)
      else if field == 0x1 then some (if c0 then 0xe5 else 0xe6, if c0 then 0xf9 else 0xfb, 0x8000, 15)
      else none
    match spec with
    | none => fail Fail.unsupported
    | some (enAddr, valAddr, valMask, valShift) =>
      if off then
        phyAnd enAddr (~~~field &&& 0xffff)
        phyAnd valAddr (~~~valMask &&& 0xffff)
      else if coreMask == 0 || (coreMask >>> core) % 2 == 1 then
        phyOr enAddr field
        match value with
        | .imm v => phyMod valAddr valMask (v <<< valShift)
        | .reg r =>
          mov 8 r
          shli 8 valShift
          phyModR valAddr valMask 8

/-- `wlc_phy_rfctrlintc_override_nphy(pi, NPHY_RfctrlIntc_override_PA, value,
coreCode)` (phy_n.c:18035-18266), rev 3..6, 2.4 GHz. -/
def rfctrlIntcOverridePa (value : UInt32) (coreCode : Nat) : ProgM Unit := do
  for core in [0:2] do
    if coreCode == 1 && core == 1 then continue
    if coreCode == 2 && core == 0 then continue
    let a : UInt32 := if core == 0 then 0x91 else 0x92
    phyMod a 0x400 0x400
    phyMod a 0x10 (value <<< 4)

/-- `wlc_phy_rfctrlintc_override_nphy(pi, NPHY_RfctrlIntc_override_TRSW,
value, core + 1)` for one core, rev 3..6. On the WARN (0x78 bit still set
after 10 ms) brcmsmac returns immediately. Uses r0-r1. -/
def rfctrlIntcOverrideTrsw (value : UInt32) (core : Nat) : ProgM Unit := do
  let a : UInt32 := if core == 0 then 0x91 else 0x92
  let en : UInt32 := if core == 0 then 0xe7 else 0xec
  let bit : UInt32 := if core == 0 then 0x1 else 0x2
  let ok ← newLabel
  let done ← newLabel
  phyMod a 0x400 0x400
  phyMod a 0x3c0 (value <<< 6)
  phyMod en 0x1 0x1
  phyMod 0x78 bit bit
  NPhyInit.spinWhilePhySet 0x78 bit 10000 0 1
  phyRead 0 0x78
  andi 0 bit
  br .eq 0 0 ok
  printImm Tag.trswOverride core.toUInt32
  jmp done
  place ok
  phyMod en 0x1 0x0
  place done

/-- `wlc_phy_rx_iq_coeffs_nphy(pi, 0, comp)`: 0x9a..0x9d → scratch. -/
def rxIqCoeffsRead (dst : UInt32) : ProgM Unit := do
  for k in [0:4] do
    phyRead 0 (0x9a + k.toUInt32)
    st 2 (dst + 2 * k.toUInt32) 0

/-- `wlc_phy_rx_iq_coeffs_nphy(pi, 1, comp)`: scratch → 0x9a..0x9d. -/
def rxIqCoeffsWrite (src : UInt32) : ProgM Unit := do
  for k in [0:4] do
    ld 2 0 (src + 2 * k.toUInt32)
    phyWriteR (0x9a + k.toUInt32) 0

/-- `wlc_phy_rx_iq_est_nphy(pi, est, numSamps, 32, 0)` (phy_n.c:26037-26073)
into `Scr.est`. On the WARN timeout brcmsmac returns with `est` unwritten
(uninitialised stack in the callers); this port leaves it zeroed. Uses r0-r2. -/
def iqEstBody (numSamps : UInt32) : ProgM Unit := do
  let ok ← newLabel
  let done ← newLabel
  for k in [0:6] do
    stI 4 (Scr.est + 4 * k.toUInt32) 0
  phyWrite 0x12b numSamps
  phyMod 0x12a 0xff 32
  phyMod 0x129 0x2 0                   -- NPHY_IqestCmd_iqMode off
  phyMod 0x129 0x1 0x1                 -- NPHY_IqestCmd_iqstart
  NPhyInit.spinWhilePhySet 0x129 0x1 10000 0 1
  phyRead 0 0x129
  andi 0 0x1
  br .eq 0 0 ok
  phyRead 0 0x129
  print Tag.iqEstTimeout 0
  jmp done
  place ok
  for core in [0:2] do
    let c := core.toUInt32
    -- (hi, lo) pairs: i_pwr, q_pwr, iq_prod (phyreg_n.h NPHY_Iqest*)
    let regs : Array (UInt32 × UInt32) :=
      if core == 0 then #[(0x12f, 0x12e), (0x131, 0x130), (0x12d, 0x12c)]
      else #[(0x137, 0x136), (0x139, 0x138), (0x135, 0x134)]
    for h : k in [0:regs.size] do
      let (hi, lo) := regs[k]
      phyRead 0 hi
      shli 0 16
      phyRead 1 lo
      alu .or 0 1
      st 4 (Scr.est + 12 * c + 4 * k.toUInt32) 0
  place done

/-! ## TX power index (used by the RX gain search) -/

/-- `wlc_phy_txpwr_index_nphy(pi, 1 << core, txpwrindex, false)`
(phy_n.c:28295-28515) for rev 6, IPA, `phyhang_avoid` false,
`nphy_txpwrctrl == PHY_TPC_HW_OFF`. `txpwrindex` (s8, sign-extended) is read
from `Scr.txpwrArg`; per-core state is `Scr.txpwrIdx`. `index_internal`
bookkeeping is not carried (nothing on this path reads it). Uses r0-r9. -/
def txpwrIndexBody (cfg : PhyCfg) (core : Nat) (tpcOff : Nat) : ProgM Unit := do
  let base := Scr.txpwrIdx + 16 * core.toUInt32
  let c0 := core == 0
  let ttbl : UInt32 := if c0 then 26 else 27
  let afeOvr : UInt32 := if c0 then 0x8f else 0xa5
  let dacReg : UInt32 := if c0 then 0xaa else 0xab
  let rfpwrReg : UInt32 := if c0 then 0x297 else 0x29b
  let nonneg ← newLabel
  let noSave ← newLabel
  let setIndex ← newLabel
  let out ← newLabel
  ld 4 0 Scr.txpwrArg
  br .ges 0 0 nonneg
  -- txpwrindex < 0: restore the state saved when the index left "unset".
  ld 4 1 base
  br .lts 1 0 out                              -- index < 0: continue
  phyMod 0x8f 0x100 0                          -- AfectrlOverride (0)
  phyMod 0xa5 0x100 0
  ld 2 1 (base + 4)
  phyWriteR dacReg 1
  ld 2 1 (base + 6)
  tableWriteR 7 (0x110 + core.toUInt32) 16 1
  NPhy.tableRead 1 15 87 16
  andi 1 (if c0 then 0x00ff else 0xff00)
  ld 2 2 (base + 8)
  if c0 then shli 2 8
  alu .or 1 2
  tableWriteR 15 87 16 1
  call tpcOff                                  -- txpwrctrl_enable(nphy_txpwrctrl)
  jmp setIndex
  place nonneg
  ld 4 1 base
  br .ges 1 0 noSave
  phyMod 0x8f 0x100 0
  phyMod 0xa5 0x100 0
  phyRead 1 dacReg
  st 2 (base + 4) 1
  NPhy.tableRead 1 7 (0x110 + core.toUInt32) 16
  st 2 (base + 6) 1
  NPhy.tableRead 1 15 87 16
  if c0 then shri 1 8
  andi 1 0xff
  st 2 (base + 8) 1
  tableReadSeq cfg 15 (80 + 2 * core.toUInt32) 16 #[1, 2]  -- iqcomp_a/b
  NPhy.tableRead 1 15 (85 + core.toUInt32) 16                                    -- locomp
  place noSave
  call tpcOff                                  -- txpwrctrl_enable(OFF)
  ld 4 0 Scr.txpwrArg
  mov 8 0
  addi 8 ((ttbl <<< 10) + 192)
  tableReadAt 1 8 32                           -- txgain
  mov 2 1
  shri 2 16
  andi 2 0xffff                                -- rad_gain (u16)
  mov 3 1
  shri 3 8
  andi 3 0x3f                                  -- dac_gain
  andi 1 0xff                                  -- bbmult
  phyMod afeOvr 0x100 0x100
  phyWriteR dacReg 3
  tableWriteR 7 (0x110 + core.toUInt32) 16 2
  NPhy.tableRead 4 15 87 16
  andi 4 (if c0 then 0x00ff else 0xff00)
  if c0 then shli 1 8
  alu .or 4 1
  tableWriteR 15 87 16 4
  ld 4 0 Scr.txpwrArg
  mov 8 0
  addi 8 ((ttbl <<< 10) + 320)
  tableReadAt 5 8 32                           -- iqcomp (restore_cals false)
  ld 4 0 Scr.txpwrArg
  mov 8 0
  addi 8 ((ttbl <<< 10) + 448)
  tableReadAt 5 8 32                           -- locomp (restore_cals false)
  ld 4 0 Scr.txpwrArg                          -- PHY_IPA: rfpwr_offset
  mov 8 0
  addi 8 ((ttbl <<< 10) + 576)
  tableReadAt 5 8 32
  andi 5 0x1ff
  shli 5 4
  phyModR rfpwrReg 0x1ff0 5
  phyMod rfpwrReg 0x4 0x4
  call tpcOff                                  -- txpwrctrl_enable(tx_pwr_ctrl_state)
  place setIndex
  ld 4 0 Scr.txpwrArg
  st 4 base 0
  place out

/-! ## RX calibration gain control -/

/-- `nphy_ipa_rxcal_gaintbl_2GHz` (phy_n.c:223-230): hpvga, lpf_biq1,
lpf_biq0, lna2, lna1, txpwrindex (s8) per entry. -/
def ipaRxcalGaintbl2g : String :=
  "0 0 0 0 0 0x80  0 0 0 0 0 0x46  0 0 0 0 0 0x14
   0 0 0 3 0 0x14  0 0 3 3 0 0x14  0 2 3 3 0 0x14"

/-- `NPHY_IPA_RXCAL_MAXGAININDEX`. -/
def rxcalMaxGainIndex : UInt32 := 5

/-- Sign-extend an 8-bit value to 32 bits. -/
def sext8 (v : UInt32) : UInt32 := if v &&& 0x80 != 0 then v ||| 0xFFFFFF00 else v

structure Subs where
  resetCca : Nat
  reset2rx : Nat
  tpcOff : Nat
  nbits : Nat
  isqrt : Nat
  iqCompMath : Nat
  iqEst1024 : Nat
  iqEst16k : Nat
  stopPlayback : Nat
  /-- (f_kHz, dac_test_mode) → subroutine. -/
  tones : Array ((Nat × Nat) × Nat)
  txpwrIndex : Array Nat

def Subs.tone (s : Subs) (f mode : Nat) : ProgM Unit :=
  match s.tones.find? (·.1 == (f, mode)) with
  | some (_, l) => call l
  | none => fail Fail.unsupported

/-- `wlc_phy_rxcal_gainctrl_nphy_rev5(pi, rxCore, NULL, calType)`
(phy_n.c:26854-27055) via `wlc_phy_rxcal_gainctrl_nphy` (27057-27062),
rev 6 / 2.4 GHz (`mix_tia_gain = 3`, the 2 GHz IPA table). The search
state lives in `Scr.gc*`. `pi->nphy_rxcal_pwr_idx` is not carried (nothing
on this path reads it). -/
def gainctrlBody (subs : Subs) (rxCore calType : Nat) : ProgM Unit := do
  let tbl := hexU32s ipaRxcalGaintbl2g
  if tbl.size != 36 || !hexU32sValid ipaRxcalGaintbl2g then fail Fail.badTable
  let txCore := 1 - rxCore
  let mixTia : UInt32 := 3
  let ent (k : Nat) (f : Nat) : UInt32 := tbl.getD (6 * k + f) 0
  let fullVal (k : Nat) : UInt32 := (ent k 0 <<< 12) ||| (ent k 1 <<< 10) ||| (ent k 2 <<< 8) |||
    (mixTia <<< 4) ||| (ent k 3 <<< 2) ||| ent k 4
  let baseVal (k : Nat) : UInt32 := fullVal k &&& 0x0fff
  let words : Array UInt32 := (Array.range 6).map fullVal ++ (Array.range 6).map baseVal ++
    (Array.range 6).map (ent · 0) ++ (Array.range 6).map (fun k => sext8 (ent k 5))
  let off ← addBlob s!"rxcal gain table core {rxCore} type {calType}"
    (words.foldl (fun b v => putU32 b v) ByteArray.empty)
  let offFull := off
  let offBase := off + 24
  let offHpvga := off + 48
  let offTxpwr := off + 72
  let thresh : UInt32 := 10000
  let loop ← newLabel
  let loopEnd ← newLabel
  let notMinus1 ← newLabel
  let toneL ← newLabel
  let dirUp ← newLabel
  let dirDown ← newLabel
  let rangeCheck ← newLabel
  let outOfRange ← newLabel
  let next ← newLabel
  let done ← newLabel
  rxIqCoeffsRead Scr.saveComp
  for k in [0:4] do phyWrite (0x9a + k.toUInt32) 0
  stI 4 Scr.gcCur 3
  stI 4 Scr.gcPrev 0
  stI 4 Scr.gcOptimIdx 0
  stI 4 Scr.gcDirn 0                           -- NPHY_RXCAL_GAIN_INIT
  stI 4 Scr.gcPrevPwr 0
  stI 4 Scr.gcOptimPwr 0
  stI 4 Scr.gcDone 0
  stI 4 Scr.gcIter 0
  place loop
  ld 4 0 Scr.gcIter
  br .geu 0 8 loopEnd
  addi 0 1
  st 4 Scr.gcIter 0
  ld 4 0 Scr.gcCur
  emit (.blobLoad32 1 0 offFull)
  rfctrlOverride 0x1000 (.reg 1) 3 false
  ld 4 0 Scr.gcCur
  emit (.blobLoad32 1 0 offTxpwr)
  br .ne 1 0xFFFFFFFF notMinus1
  -- txpwrindex == -1 (not in the 2 GHz table; kept for fidelity)
  phyWrite tblAddr (((7 : UInt32) <<< 10) ||| 0x110)
  phyWrite tblDataLo (0x8ff0 ||| nphyGmval)
  phyWrite tblDataLo (0x8ff0 ||| nphyGmval)
  jmp toneL
  place notMinus1
  st 4 Scr.txpwrArg 1
  call (subs.txpwrIndex.getD txCore 0)
  place toneL
  subs.tone 2000 calType
  call subs.iqEst1024
  -- DIV_ROUND_CLOSEST(u32, 1024) for i_pwr and q_pwr
  ld 4 0 (Scr.est + 12 * rxCore.toUInt32)
  addi 0 512
  shri 0 10
  ld 4 1 (Scr.est + 12 * rxCore.toUInt32 + 4)
  addi 1 512
  shri 1 10
  alu .add 0 1
  st 4 Scr.gcCurrPwr 0
  ld 4 1 Scr.gcDirn
  br .eq 1 1 dirUp
  br .eq 1 2 dirDown
  -- INIT (r0 = curr_pwr)
  let initUp ← newLabel
  ld 4 2 Scr.gcCur
  st 4 Scr.gcPrev 2
  br .ltu 0 (thresh + 1) initUp                -- curr_pwr <= thresh_pwr
  stI 4 Scr.gcDirn 2                           -- GAIN_DOWN
  aluI .sub 2 1
  st 4 Scr.gcCur 2
  jmp rangeCheck
  place initUp
  stI 4 Scr.gcDirn 1                           -- GAIN_UP
  addi 2 1
  st 4 Scr.gcCur 2
  jmp rangeCheck
  place dirUp
  let upMore ← newLabel
  br .ltu 0 (thresh + 1) upMore
  stI 4 Scr.gcDone 1
  ld 4 1 Scr.gcPrevPwr
  st 4 Scr.gcOptimPwr 1
  ld 4 1 Scr.gcPrev
  st 4 Scr.gcOptimIdx 1
  jmp rangeCheck
  place upMore
  ld 4 2 Scr.gcCur
  st 4 Scr.gcPrev 2
  addi 2 1
  st 4 Scr.gcCur 2
  jmp rangeCheck
  place dirDown
  let downDone ← newLabel
  br .ltu 0 (thresh + 1) downDone
  ld 4 2 Scr.gcCur
  st 4 Scr.gcPrev 2
  aluI .sub 2 1
  st 4 Scr.gcCur 2
  jmp rangeCheck
  place downDone
  stI 4 Scr.gcDone 1
  st 4 Scr.gcOptimPwr 0
  ld 4 1 Scr.gcCur
  st 4 Scr.gcOptimIdx 1
  place rangeCheck
  ld 4 2 Scr.gcCur
  br .lts 2 0 outOfRange
  br .ges 2 (rxcalMaxGainIndex + 1) outOfRange
  st 4 Scr.gcPrevPwr 0
  jmp next
  place outOfRange
  stI 4 Scr.gcDone 1
  st 4 Scr.gcOptimPwr 0
  ld 4 1 Scr.gcPrev
  st 4 Scr.gcOptimIdx 1
  place next
  call subs.stopPlayback
  ld 4 0 Scr.gcDone
  br .eq 0 0 loop
  jmp done
  place loopEnd
  fail Fail.gainLoop
  place done
  -- Final gain: hpvga += desired_log2_pwr (13) - nbits(optim_pwr), clamped.
  ld 4 0 Scr.gcOptimPwr
  call subs.nbits
  li 1 13
  alu .sub 1 0                                 -- delta_pwr
  ld 4 0 Scr.gcOptimIdx
  emit (.blobLoad32 2 0 offHpvga)
  alu .add 2 1
  let le10 ← newLabel
  let ge0 ← newLabel
  br .lts 2 11 le10
  li 2 10
  place le10
  br .ges 2 0 ge0
  li 2 0
  place ge0
  shli 2 12
  emit (.blobLoad32 3 0 offBase)
  alu .or 3 2
  rfctrlOverride 0x1000 (.reg 3) 3 false
  rxIqCoeffsWrite Scr.saveComp

/-! ## Rx IQ compensation -/

/-- `wlc_phy_calc_rx_iq_comp_nphy(pi, 1 << core)` (phy_n.c:26075-26195),
rev >= 3 coefficient layout (a → a{core}, b → b{core}). The C error flag is
sticky across retries: after a rejected estimate brcmsmac re-estimates twice
more and then restores the old coefficients. -/
def calcRxIqComp (subs : Subs) (core : Nat) : ProgM Unit := do
  let c := core.toUInt32
  let tryL ← newLabel
  let coreDone ← newLabel
  let noErr ← newLabel
  let final ← newLabel
  rxIqCoeffsRead Scr.oldComp
  for k in [0:4] do phyWrite (0x9a + k.toUInt32) 0
  stI 4 Scr.compErr 0
  stI 4 Scr.compRetry 0
  place tryL
  call subs.iqEst16k
  for k in [0:4] do                           -- new_comp = old_comp
    ld 2 0 (Scr.oldComp + 2 * k.toUInt32)
    st 2 (Scr.newComp + 2 * k.toUInt32) 0
  ld 4 1 (Scr.est + 12 * c + 8)                -- iq_prod
  ld 4 2 (Scr.est + 12 * c)                    -- i_pwr
  ld 4 3 (Scr.est + 12 * c + 4)                -- q_pwr
  call subs.iqCompMath
  br .eq 0 0 noErr
  stI 4 Scr.compErr 1
  jmp coreDone
  place noErr
  andi 4 0x3ff
  andi 5 0x3ff
  st 2 (Scr.newComp + 4 * c) 4                 -- a{core}
  st 2 (Scr.newComp + 4 * c + 2) 5             -- b{core}
  place coreDone
  ld 4 0 Scr.compErr
  br .eq 0 0 final
  ld 4 1 Scr.compRetry
  print Tag.compRetry 1
  let exhausted ← newLabel
  br .geu 1 2 exhausted                         -- CAL_RETRY_CNT
  addi 1 1
  st 4 Scr.compRetry 1
  jmp tryL
  place exhausted
  for k in [0:4] do
    ld 2 0 (Scr.oldComp + 2 * k.toUInt32)
    st 2 (Scr.newComp + 2 * k.toUInt32) 0
  place final
  rxIqCoeffsWrite Scr.newComp
  ld 2 0 (Scr.newComp + 4 * c)
  shli 0 16
  ld 2 1 (Scr.newComp + 4 * c + 2)
  alu .or 0 1
  print Tag.rxIqComp 0

/-! ## Rx calibration setup and cleanup -/

/-- 2056 register block offsets. -/
def tx0 : UInt32 := 0x2000
def tx1 : UInt32 := 0x3000
def rx0 : UInt32 := 0x6000
def rx1 : UInt32 := 0x7000
def txBlk (core : Nat) : UInt32 := if core == 0 then tx0 else tx1
def rxBlk (core : Nat) : UInt32 := if core == 0 then rx0 else rx1

/-- `wlc_phy_rxcal_radio_setup_nphy` (phy_n.c:26197-26517), rev < 7,
radio 2056 rev >= 5, 2.4 GHz (`bias_g = 0`). -/
def rxcalRadioSetup (rxCore : Nat) : ProgM Unit := do
  let tx := txBlk (1 - rxCore)
  let rx := rxBlk rxCore
  let saves : Array UInt32 := #[0x27 ||| tx, 0x20 ||| rx, 0x7c ||| rx, 0x7e ||| tx, 0x33 ||| rx]
  for h : k in [0:saves.size] do
    radioRead 0 saves[k]
    st 2 (Scr.radioSave + 2 * k.toUInt32) 0
  radioWrite (0x33 ||| rx) 0x40                -- RX_LNAG_MASTER
  radioWrite (0x7e ||| tx) 0                   -- TX_TXSPARE2 = bias_g
  radioWrite (0x7c ||| rx) 0                   -- RX_RXSPARE2 = bias_g
  radioWrite (0x27 ||| tx) 0x6                 -- TX_RXIQCAL_TXMUX
  radioWrite (0x20 ||| rx) 0x6                 -- RX_RXIQCAL_RXMUX

/-- `wlc_phy_rxcal_radio_cleanup_nphy` (phy_n.c:26519-26699), same branch. -/
def rxcalRadioCleanup (rxCore : Nat) : ProgM Unit := do
  let tx := txBlk (1 - rxCore)
  let rx := rxBlk rxCore
  let saves : Array UInt32 := #[0x27 ||| tx, 0x20 ||| rx, 0x7c ||| rx, 0x7e ||| tx, 0x33 ||| rx]
  for h : k in [0:saves.size] do
    ld 2 0 (Scr.radioSave + 2 * k.toUInt32)
    radioWriteR saves[k] 0

/-- Registers saved by `wlc_phy_rxcal_physetup_nphy`, in
`tx_rx_cal_phy_saveregs` order (rev < 7: entries 0..10). -/
def phySaveRegs (rxCore : Nat) : Array UInt32 :=
  #[0xa2, if rxCore == 0 then 0xa6 else 0xa7, if rxCore == 0 then 0x8f else 0xa5,
    0x91, 0x92, 0x7a, 0x7d, 0xe7, 0xec, 0x297, 0x29b]

/-- `wlc_phy_rxcal_physetup_nphy` (phy_n.c:26701-26826), rev < 7. -/
def rxcalPhySetup (cfg : PhyCfg) (rxCore : Nat) : ProgM Unit := do
  let txCore := 1 - rxCore
  let regs := phySaveRegs rxCore
  for h : k in [0:regs.size] do
    phyRead 0 regs[k]
    st 2 (Scr.phySave + 2 * k.toUInt32) 0
  phyMod 0x297 0x1 0
  phyMod 0x29b 0x1 0
  let t : UInt32 := (1 : UInt32) <<< txCore.toUInt32
  let r : UInt32 := (1 : UInt32) <<< rxCore.toUInt32
  phyMod 0xa2 0xf000 (t <<< 12)
  phyMod 0xa2 0x000f t
  phyMod 0xa2 0x00f0 (r <<< 4)
  phyMod 0xa2 0x0f00 (r <<< 8)
  let afeCore : UInt32 := if rxCore == 0 then 0xa6 else 0xa7
  let afeOvr : UInt32 := if rxCore == 0 then 0x8f else 0xa5
  phyMod afeCore 0x4 0
  phyMod afeOvr 0x4 0x4
  phyMod afeCore 0x3 0
  phyMod afeOvr 0x3 0x3
  rfctrlIntcOverridePa 0 3                     -- CORESEL_CORE1 | CORESEL_CORE2
  rfctrlOverride 0x8 (.imm 0) 3 false
  wlcPhyForceRfseqNphy cfg .rx2tx
  let (rxAnt, txAnt) : UInt32 × UInt32 := if rxCore == 0 then (0x1, 0x8) else (0x4, 0x2)
  rfctrlIntcOverrideTrsw rxAnt rxCore
  rfctrlIntcOverrideTrsw txAnt txCore

/-- `wlc_phy_rxcal_phycleanup_nphy` (phy_n.c:26828-26852), rev < 7. -/
def rxcalPhyCleanup (rxCore : Nat) : ProgM Unit := do
  let regs := phySaveRegs rxCore
  for h : k in [0:regs.size] do
    ld 2 0 (Scr.phySave + 2 * k.toUInt32)
    phyWriteR regs[k] 0

/-! ## Rx core state -/

/-- `wlc_phy_rxcore_setstate_nphy(pih, mask)` (phy_n.c:19625-19703), rev 6,
`pi->sh->clk` true, `phyhang_avoid` false. brcmsmac suspends a running MAC
first; this port fails with `Fail.macRunning` instead. `pi->sh->phyrxchain`
is not carried. -/
def rxcoreSetstate (cfg : PhyCfg) (mask : UInt32) : ProgM Unit := do
  let ok ← newLabel
  let done ← newLabel
  r32 0 d11MacCtl
  andi 0 mctlEnMac
  br .eq 0 0 ok
  fail Fail.macRunning
  place ok
  phyRead 0 0xa2
  andi 0 (~~~0xf0 &&& 0xffff)
  ori 0 ((mask &&& 0x3) <<< 4)
  phyWriteR 0xa2 0
  if mask &&& 0x3 != 0x3 then
    phyWrite 0x20e 1
    ld 1 0 Scr.biasEntry
    br .ne 0 0xFF done
    -- brcmsmac reads all 16 RFSEQ entries at 80 first, then scans; reads
    -- have no side effects, so they are interleaved with the scan here.
    for i in [0:16] do
      let notBias ← newLabel
      NPhy.tableRead 1 7 (80 + i.toUInt32) 16
      br .ne 1 0xf notBias                     -- NPHY_REV3_RFSEQ_CMD_CLR_RXRX_BIAS
      stI 1 Scr.biasEntry i.toUInt32
      -- brcmsmac writes the NOP at RFSEQ offset `i` (not 80 + i) and later
      -- restores at `rx2tx_biasentry`; ported as written.
      tableWrite cfg 7 (i.toUInt32) 16 #[0]    -- NPHY_REV3_RFSEQ_CMD_NOP
      jmp done
      place notBias
      br .eq 1 0x1f done                       -- NPHY_REV3_RFSEQ_CMD_END
  else
    phyWrite 0x20e 30
    ld 1 0 Scr.biasEntry
    br .eq 0 0xFF done
    addi 0 ((7 : UInt32) <<< 10)
    phyWriteR tblAddr 0
    phyWrite tblDataLo 0xf
    stI 1 Scr.biasEntry 0xFF
  place done
  wlcPhyForceRfseqNphy cfg .reset2rx

/-! ## RC filter sweep -/

/-- `wlc_phy_rc_sweep_nphy(pi, coreIdx, loopbackType)` (phy_n.c:27064-27301),
rev < 7, 20 MHz. The step-size sequence (16, 8, 4, 2, 1, 0) does not depend
on measurements, so the loop is unrolled; the RC value is run-time. Leaves
`best_rccal_val - 0x80` (u8) in `Scr.bestRccal`. -/
def rcSweep (subs : Subs) (coreIdx loopbackType : Nat) : ProgM Unit := do
  let targetBw := 9500
  let refTone := 3000
  let targetPwrRatio : UInt32 := 28606
  let rxLpfBw : UInt32 := 2
  let txLpfBw : UInt32 := 4
  let lpfHpc : UInt32 := 7
  let hpvgaHpc : UInt32 := 7
  let logNumSamps : UInt32 := 10
  let rx := rxBlk coreIdx
  let tx := if coreIdx == 0 then (if loopbackType == 0 then tx0 else tx1)
    else (if loopbackType == 0 then tx1 else tx0)
  let c0 := coreIdx == 0
  let e0 : UInt32 := if c0 then 0xe7 else 0xec
  let e1 : UInt32 := if c0 then 0xec else 0xe7
  let rssiReg : UInt32 := if c0 then 0x7a else 0x7d
  let filtRegs : Array UInt32 := #[0x267, 0x268, 0x269, 0x26a, 0x26b, 0x26c, 0x26d, 0x26e, 0x26f, 0x270]
  radioRead 0 (0x69 ||| tx)                   -- TX_TXLPF_RCCAL
  st 2 Scr.rcOrigTxlpf 0
  radioRead 0 (0x62 ||| rx)                   -- RX_RXLPF_RCCAL_HPC
  st 2 Scr.rcOrigRxhpc 0
  phyRead 0 0x48
  shri 0 8
  andi 0 1
  st 2 Scr.rcOrigDcBypass 0
  for h : k in [0:filtRegs.size] do
    phyRead 0 filtRegs[k]
    st 2 (Scr.rcOrigFilt + 2 * k.toUInt32) 0
  phyRead 0 0xe7
  st 2 Scr.rcOrigOvr 0
  phyRead 0 0xec
  st 2 (Scr.rcOrigOvr + 2) 0
  phyRead 0 0xf8
  st 2 Scr.rcOrigAux 0
  phyRead 0 0xfa
  st 2 (Scr.rcOrigAux + 2) 0
  phyRead 0 rssiReg
  st 2 Scr.rcOrigRssiOthers 0
  radioWrite (0x69 ||| tx) 128                 -- txlpf_rccal_lpc_ovr_val
  radioWrite (0x62 ||| rx) 159                 -- rxlpf_rccal_hpc_ovr_val
  phyMod 0x48 0x100 0x100
  let filtVals : Array UInt32 := #[0x02d4, 0, 0, 0, 0, 0x02d4, 0, 0, 0, 0]
  for h : k in [0:filtRegs.size] do
    phyWrite filtRegs[k] (filtVals.getD k 0)
  phyOr e0 0x100
  phyOr e1 0x8000
  phyOr e0 0x200
  phyOr e0 0x400
  phyMod (if c0 then 0xfa else 0xf8) 0x1c00 (txLpfBw <<< 10)
  phyMod (if c0 then 0xf8 else 0xfa) 0x7 hpvgaHpc
  phyMod (if c0 then 0xf8 else 0xfa) 0x70 (lpfHpc <<< 4)
  phyMod rssiReg 0x700 (rxLpfBw <<< 8)
  stI 4 Scr.rcVal (128 + 16)                   -- start_rccal_ovr_val + stepsize
  stI 4 Scr.rcLastVal 0
  stI 4 Scr.rcLastRatio 0
  stI 4 Scr.rcBest 0
  -- (est.i_pwr + est.q_pwr) >> (log_num_samps + 1) for this core, into `d`.
  let pwrSum (d t : Reg) : ProgM Unit := do
    ld 4 d (Scr.est + 12 * coreIdx.toUInt32)
    ld 4 t (Scr.est + 12 * coreIdx.toUInt32 + 4)
    alu .add d t
    shri d (logNumSamps + 1)
  for step in [16, 8, 4, 2, 1, 0] do
    ld 4 0 Scr.rcVal
    radioWriteR (0x6b ||| rx) 0                -- RX_RXLPF_RCCAL_LPC
    if step == 16 then
      subs.tone refTone 1
      delay 2
      call subs.iqEst1024
      pwrSum 0 1
      let ge1 ← newLabel
      br .geu 0 1 ge1
      li 0 1
      place ge1
      st 4 Scr.rcRef 0
      subs.tone targetBw 1
      delay 2
    call subs.iqEst1024
    pwrSum 0 1
    shli 0 16
    ld 4 1 Scr.rcRef
    alu .udiv 0 1                              -- pwr_ratio
    st 4 Scr.rcRatio 0
    -- rccal_val update (pwr_ratio in r0)
    let down ← newLabel
    let upd ← newLabel
    if step == 1 then
      ld 4 1 Scr.rcVal
      st 4 Scr.rcLastVal 1
      st 4 Scr.rcLastRatio 0
    if step != 0 then
      let delta : UInt32 := if step == 1 then 1 else (step / 2).toUInt32
      ld 4 1 Scr.rcVal
      br .ltu 0 (targetPwrRatio + 1) down      -- pwr_ratio <= target
      addi 1 delta
      jmp upd
      place down
      aluI .sub 1 delta
      place upd
      andi 1 0xffff                            -- u16 rccal_val
      st 4 Scr.rcVal 1
    else
      -- stepsize -1: pick the closer of the last two ratios.
      let useLast ← newLabel
      let chosen ← newLabel
      let absA ← newLabel
      let absB ← newLabel
      ld 4 1 Scr.rcLastRatio
      aluI .sub 1 targetPwrRatio
      br .ges 1 0 absA
      li 2 0
      alu .sub 2 1
      mov 1 2
      place absA
      ld 4 2 Scr.rcRatio
      aluI .sub 2 targetPwrRatio
      br .ges 2 0 absB
      li 3 0
      alu .sub 3 2
      mov 2 3
      place absB
      brR .lts 1 2 useLast
      ld 4 0 Scr.rcVal
      jmp chosen
      place useLast
      ld 4 0 Scr.rcLastVal
      place chosen
      let clampIt ← newLabel
      let inRange ← newLabel
      br .ltu 0 137 clampIt
      br .ltu 0 143 inRange
      place clampIt
      li 0 140
      place inRange
      st 4 Scr.rcBest 0
      radioWriteR (0x6b ||| rx) 0
  call subs.stopPlayback
  ld 2 0 Scr.rcOrigTxlpf
  radioWriteR (0x69 ||| tx) 0
  ld 2 0 Scr.rcOrigRxhpc
  radioWriteR (0x62 ||| rx) 0
  ld 2 0 Scr.rcOrigDcBypass
  shli 0 8
  phyModR 0x48 0x100 0
  for h : k in [0:filtRegs.size] do
    ld 2 0 (Scr.rcOrigFilt + 2 * k.toUInt32)
    phyWriteR filtRegs[k] 0
  ld 2 0 Scr.rcOrigOvr
  phyWriteR 0xe7 0
  ld 2 0 (Scr.rcOrigOvr + 2)
  phyWriteR 0xec 0
  ld 2 0 Scr.rcOrigAux
  phyWriteR 0xf8 0
  ld 2 0 (Scr.rcOrigAux + 2)
  phyWriteR 0xfa 0
  ld 2 0 Scr.rcOrigRssiOthers
  phyWriteR rssiReg 0
  -- pi->nphy_anarxlpf_adjusted = false (not carried; 40 MHz only)
  ld 4 0 Scr.rcBest
  aluI .sub 0 0x80
  andi 0 0xff
  st 4 Scr.bestRccal 0
  print Tag.rccal 0

/-! ## Top level -/

/-- True when this port carries the board's path. -/
def supported (cfg : PhyCfg) : Bool :=
  cfg.phyRev >= 3 && cfg.phyRev < 7 && cfg.radioRev >= 5 && cfg.ipa2g &&
    cfg.channel >= 1 && cfg.channel <= 14

/-- Emit the shared subroutines (each jumped over) and return their labels. -/
def mkSubs (cfg : PhyCfg) : ProgM Subs := do
  let reset2rx ← subroutine (wlcPhyForceRfseqNphy cfg .reset2rx)
  let resetCcaL ← subroutine (resetCca cfg)
  let tpcOff ← subroutine (txpwrctrlOff cfg)
  let nbits ← subroutine nbitsBody
  let isqrt ← subroutine isqrtBody
  let iqCompMath ← subroutine (iqCompMathBody nbits isqrt)
  let iqEst1024 ← subroutine (iqEstBody 1024)
  let iqEst16k ← subroutine (iqEstBody 0x4000)
  let stopPlayback ← subroutine stopPlaybackBody
  let mut tones := #[]
  for (f, mode) in [(2000, 0), (2000, 1), (3000, 1), (9500, 1)] do
    let l ← subroutine (txToneBody f mode)
    tones := tones.push ((f, mode), l)
  let mut txpwrIndex := #[]
  for core in [0:2] do
    txpwrIndex := txpwrIndex.push (← subroutine (txpwrIndexBody cfg core tpcOff))
  return { resetCca := resetCcaL, reset2rx, tpcOff, nbits, isqrt, iqCompMath, iqEst1024,
           iqEst16k, stopPlayback, tones, txpwrIndex }

/-- Initialise the `pi->` state this routine relies on (module header). -/
def initState (cfg : PhyCfg) : ProgM Unit := do
  stI 4 Scr.bbMultSave 0
  stI 1 Scr.biasEntry 0xFF
  let tbl ← ipaGainTbl cfg
  let g := tbl.getD (fixTxPwrIndex cfg) 0
  for core in [0:2] do
    let base := Scr.txpwrIdx + 16 * core.toUInt32
    stI 4 base 0                                -- index >= 0
    stI 2 (base + 4) ((g >>> 8) &&& 0x3f)      -- AfeCtrlDacGain
    stI 2 (base + 6) ((g >>> 16) &&& 0xffff)   -- rad_gain
    stI 2 (base + 8) (g &&& 0xff)              -- bbmult

/-- Clamp the u8 in `r` to at most 31 (`min_t(u8, x, 31)`), then OR 0x80. -/
def clamp31Or80 (r : Reg) : ProgM Unit := do
  let ok ← newLabel
  andi r 0xff
  br .ltu r 32 ok
  li r 31
  place ok
  ori r 0x80

/-- `wlc_phy_cal_rxiq_nphy(pi, target_gain, 2, false)` (phy_n.c:27683-27694)
→ `wlc_phy_cal_rxiq_nphy_rev3` (phy_n.c:27304-27463) for this board. The
target gain is read from `txGainsSlot` (0x5C00). Leaves r0 = 0 (brcmsmac
always returns 0 on this path). Clobbers r0-r14 and scratch 0x5800-0x5BFF. -/
def rxiqCal (cfg : PhyCfg) : ProgM Unit := do
  if !supported cfg then
    fail Fail.unsupported
    return
  let subs ← mkSubs cfg
  let gc00 ← subroutine (gainctrlBody subs 0 0)
  let gc10 ← subroutine (gainctrlBody subs 1 0)
  let gc11 ← subroutine (gainctrlBody subs 1 1)
  initState cfg
  phyRead 0 0x01                               -- orig_BBConfig
  st 2 Scr.origBBConfig 0
  phyMod 0x01 0x8000 0
  stayInCarrierSearch cfg true subs.resetCca
  -- rev >= 4: phyhang_avoid (false) is saved and cleared: no effect.
  tableReadSeq cfg 7 0x110 16 #[0, 1]          -- gain_save (NPHY_TBL_ID_RFSEQ)
  st 2 Scr.gainSave 0
  st 2 (Scr.gainSave + 2) 1
  -- wlc_phy_iqcal_gainparams_nphy (phy_n.c:23377-23431), rev 3..6:
  -- cal_gain = txgm << 12 | pga << 8 | pad << 4 | ipa
  for core in [0:2] do
    let c := core.toUInt32
    let r : Reg := 2 + core
    ld 2 r (txGainsSlot + 4 + 2 * c)
    shli r 12
    ld 2 4 (txGainsSlot + 8 + 2 * c)
    shli 4 8
    alu .or r 4
    ld 2 4 (txGainsSlot + 12 + 2 * c)
    shli 4 4
    alu .or r 4
    ld 2 4 (txGainsSlot + 16 + 2 * c)
    alu .or r 4
  phyWrite tblAddr (((7 : UInt32) <<< 10) ||| 0x110)
  phyWriteR tblDataLo 2
  phyWriteR tblDataLo 3
  -- rxcore_state = wlc_phy_rxcore_getstate_nphy (phy_n.c:19705-19714)
  phyRead 0 0xa2
  shri 0 4
  andi 0 0xf
  st 2 Scr.rxcoreState 0
  for rxCore in [0:2] do
    let skip ← newLabel
    rxcalPhySetup cfg rxCore
    rxcalRadioSetup rxCore
    ld 2 0 Scr.rxcoreState
    andi 0 ((1 : UInt32) <<< rxCore.toUInt32)
    br .eq 0 0 skip                            -- skip_rxiqcal
    call (if rxCore == 0 then gc00 else gc10)
    -- NPHY_RXCAL_TONEFREQ_20MHz; dac_test_mode = cal_type = 2 plays like 0.
    subs.tone 2000 0
    calcRxIqComp subs rxCore
    call subs.stopPlayback
    place skip
    if rxCore == 1 then                        -- cal_type 2, rev < 7
      let n1 ← newLabel
      let n2 ← newLabel
      ld 2 0 Scr.rxcoreState
      br .ne 0 1 n1
      rxcoreSetstate cfg 3
      place n1
      call gc11
      rcSweep subs 1 1
      ld 4 0 Scr.bestRccal
      st 4 Scr.rccalValue 0                    -- pi->nphy_rccal_value
      ld 2 0 Scr.rxcoreState
      br .ne 0 1 n2
      rxcoreSetstate cfg 1
      place n2
    rxcalRadioCleanup rxCore
    rxcalPhyCleanup rxCore
    call subs.reset2rx
  -- best_rccal[0] = best_rccal[1]
  ld 4 0 Scr.bestRccal
  ori 0 0x80
  radioWriteR (0x6b ||| rx0) 0                 -- RX_RXLPF_RCCAL_LPC
  for rxCore in [0:2] do
    -- rxlpf_rccal_hpc = ((best - 12) >> 1) + 10 (s8)
    ld 4 0 Scr.bestRccal
    aluI .sub 0 12
    aluI .sar 0 1
    addi 0 10
    -- txlpf_rccal_lpc = (best - 12) + 10, + 12 for IPA at 20 MHz (s8)
    ld 4 1 Scr.bestRccal
    aluI .sub 1 12
    addi 1 (10 + 12)
    radioWrite (0x78 ||| txBlk rxCore) 0x13    -- TX_TXLPF_IDAC_4 (IPA, 20 MHz)
    clamp31Or80 0
    clamp31Or80 1
    radioWriteR (0x62 ||| rxBlk rxCore) 0      -- RX_RXLPF_RCCAL_HPC
    radioWriteR (0x69 ||| txBlk rxCore) 1      -- TX_TXLPF_RCCAL
  ld 2 0 Scr.origBBConfig
  phyWriteR 0x01 0
  call subs.resetCca
  rfctrlOverride 0x1000 (.imm 0) 3 true
  call subs.reset2rx
  ld 2 0 Scr.gainSave
  ld 2 1 (Scr.gainSave + 2)
  phyWrite tblAddr (((7 : UInt32) <<< 10) ||| 0x110)
  phyWriteR tblDataLo 0
  phyWriteR tblDataLo 1
  stayInCarrierSearch cfg false subs.resetCca
  li 0 0

end LeanOS.Wifi.NPhyRxCal
