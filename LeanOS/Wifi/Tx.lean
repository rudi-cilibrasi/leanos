import LeanOS.Wifi.Mac
import LeanOS.Wifi.NPhyInit

/-
Transmit path for the BCM43224: the D11 transmit descriptor (`struct d11txh`
plus PLCP header), the MAC/ucode state the microcode needs to transmit and to
answer with ACKs, the N-PHY transmit power target, and transmit status.

Ported from Linux brcmsmac (ISC license), Copyright (c) 2010 Broadcom
Corporation; see drivers/net/wireless/broadcom/brcm80211/brcmsmac at Linux
commit fd179f8a05be3ccae366b9b96e176b51fbe54aab.

Scope (generation-time pruned for the Qotom board, `PhyCfg`): one non-QoS,
non-aggregated, unencrypted, unfragmented MPDU at 1 Mb/s CCK (long preamble)
or 6 Mb/s OFDM, 20 MHz, 2.4 GHz, no RTS/CTS, fallback rate = primary rate
(mac80211 gives brcmsmac a fallback only through rate control; with a single
rate `txrate[1] = txrate[0]`, main.c:6212-6213).

## Buffer layout handed to the transmit FIFO (brcms_c_d11hdrs_mac80211)

    [0, 112)    struct d11txh      (d11.h:751-786, D11_TXH_LEN = 112)
    [112, 118)  PLCP header        (D11_PHY_HDR_LEN = 6; pushed first, so it
                                    sits between the descriptor and the frame)
    [118, ...)  802.11 MPDU without FCS (the MAC appends the FCS)

`TXOFF = D11_TXH_LEN + D11_PHY_HDR_LEN = 118` (main.h:45). Every multi-byte
descriptor field is little endian.

## Which FIFO

brcmsmac picks the FIFO from the mac80211 queue: `brcms_ac_to_fifo`
(main.c:322-342): AC_VO → `TX_AC_VO_FIFO` (3), AC_VI → 2, AC_BE → 1,
AC_BK → 0. brcmsmac registers 4 mac80211 queues (mac80211_if.c:41, 1098), so
mac80211 queues management frames and EAPOL (control-port) frames on AC_VO:
probe request, authentication, association request and EAPOL-Key go to
**FIFO 3** (`TX_AC_VO_FIFO`, alias `TX_CTL_FIFO`, d11.h:44), ordinary best-effort
data to **FIFO 1** (`TX_AC_BE_FIFO`, alias `TX_DATA_FIFO`). The BCMC FIFO (4)
is for AP-mode broadcast and is never used by a STA (main.c:6178-6183).

## Transmit PIO (documented finding)

brcmsmac never transmits by programmed I/O. `struct fifo64` (d11.h:97-102)
places a `struct pio4regs piotx` {fifocontrol, fifodata} at +0x18 of each
0x40-byte FIFO block (so FIFO n: 0x218 + 0x40·n / 0x21C + 0x40·n), but no
brcmsmac code touches it and no transmit control bit for it is defined. The
only direct-FIFO bit brcmsmac defines is on the *receive* engine,
`D64_RC_FM = 0x100` ("direct fifo receive (pio) mode", dma.c:89-90). The
64-bit DMA *transmit* control bits it defines are only `D64_XC_XE` (0x1),
`D64_XC_SE` (0x2), `D64_XC_LE` (0x4), `D64_XC_FL` (0x10), `D64_XC_PD` (0x800)
and `D64_XC_AE` (0x30000) (dma.c:52-58). This module therefore defines the
PIO register *offsets* (`txPioCtl`/`txPioData`) but no PIO transmit sequence
and no control-bit semantics: brcmsmac does not document them.
-/
namespace LeanOS.Wifi.Tx

open LeanOS.Wifi.Bytecode LeanOS.Wifi.Bcm43224 LeanOS.Wifi.NPhy

/-! ## Diagnostics -/

namespace Fail
/-- `emitTxHeader`/`readTxStatus` were given a register they clobber. -/
def badRegs : UInt32 := 0x7E60
/-- A generation-time parameter is outside what this port supports. -/
def unsupported : UInt32 := 0x7E61
end Fail

namespace Tag
/-- `readTxStatus`: a valid status for a different frame id (value: frmtxstatus). -/
def txsOther : UInt32 := 0x0C00
/-- `readTxStatus`: intermediate non-AMPDU status discarded (value: frmtxstatus). -/
def txsIntermediate : UInt32 := 0x0C01
/-- `readTxStatus`: frmtxstatus read 0xffffffff (brcmsmac "dead chip"). -/
def txsDead : UInt32 := 0x0C02
/-- `txpowerRecalcTargetNphy`: target written to PHY 0x1ea (value: qdBm). -/
def txPwrTarget : UInt32 := 0x0C10
end Tag

/-! ## FIFOs and register offsets (d11.h) -/

def txAcBkFifo : Nat := 0
def txAcBeFifo : Nat := 1
def txAcViFifo : Nat := 2
def txAcVoFifo : Nat := 3
def txBcmcFifo : Nat := 4
def txAtimFifo : Nat := 5
/-- NFIFO. -/
def nFifo : Nat := 6

/-- 64-bit DMA transmit control of FIFO `n` (`fifo64regs[n].dmaxmt.control`). -/
def txDmaCtl (n : Nat) : UInt32 := 0x200 + 0x40 * n.toUInt32
/-- `fifo64regs[n].piotx.fifocontrol` (unused by brcmsmac; see module header). -/
def txPioCtl (n : Nat) : UInt32 := 0x200 + 0x40 * n.toUInt32 + 0x18
/-- `fifo64regs[n].piotx.fifodata` (unused by brcmsmac; see module header). -/
def txPioData (n : Nat) : UInt32 := 0x200 + 0x40 * n.toUInt32 + 0x1C

def d11FrmTxStatus : UInt32 := 0x170
def d11FrmTxStatus2 : UInt32 := 0x174
def d11TplateWrPtr : UInt32 := 0x130
def d11TplateWrData : UInt32 := 0x134
def d11RfDisableDly : UInt32 := 0x3DC
def d11RcmCtl : UInt32 := 0x420
def d11RcmMatData : UInt32 := 0x422
def d11XmtFifoDef : UInt32 := 0x520
def d11XmtFifoDef1 : UInt32 := 0x52C
def d11XmtFifoCmd : UInt32 := 0x540
def d11TsfRandom : UInt32 := 0x65A
def d11IfsSlot : UInt32 := 0x684
def d11IfsCtl : UInt32 := 0x688

def objScr : UInt32 := 0x00020000

/-! ### Shared memory byte offsets (d11.h:1080-1365) -/

def mDot11Slot : UInt32 := 0x008 * 2
def mRspPctlwd : UInt32 := 0x011 * 2
def mSfrmTxCntFbrThsd : UInt32 := 0x022 * 2
def mLfrmTxCntFbrThsd : UInt32 := 0x023 * 2
def mMaxAntCnt : UInt32 := 0x02e * 2
def mHostFlags1 : UInt32 := 0x02f * 2
def mPrsMaxTime : UInt32 := 0x03a * 2
def mMburstSize : UInt32 := 0x40 * 2
def mMburstTxop : UInt32 := 0x41 * 2
def mFifoSize0 : UInt32 := 0x4c * 2
def mTxIdleBusyRatioCck : UInt32 := 0x52 * 2
def mTxIdleBusyRatioOfdm : UInt32 := 0x5A * 2
def mCtxprsBlk : UInt32 := 0xc0 * 2
def cCtxPctlwdPos : UInt32 := 0x4 * 2
def mRtDirmapA : UInt32 := 0xe0 * 2
def mRtBbrsmapA : UInt32 := 0xf0 * 2
def mRtDirmapB : UInt32 := 0x100 * 2
def mRtBbrsmapB : UInt32 := 0x110 * 2
def mRtOfdmPctl1Pos : UInt32 := 18
def mEdcfQinfo : UInt32 := 0x120 * 2
def mEdcfQlen : UInt32 := 16 * 2
def mEdcfStatusOff : UInt32 := 0x007 * 2

/-- PSM scratch registers (`enum _ePsmScratchPadRegDefinitions`, d11.h:1586-1598). -/
def sDot11CwMin : UInt32 := 3
def sDot11CwMax : UInt32 := 4
def sDot11SrcLmt : UInt32 := 6
def sDot11LrcLmt : UInt32 := 7

/-! ## Descriptor constants -/

/- MacTxControlLow bits (d11.h:806-818). -/
namespace Txc
def amic : UInt16 := 0x8000
def sendCts : UInt16 := 0x0800
def ampduMask : UInt16 := 0x0600
def bw40 : UInt16 := 0x0100
def freqBand5g : UInt16 := 0x0080
def dfcs : UInt16 := 0x0040
def ignorePmq : UInt16 := 0x0020
/-- Hardware sequence numbering. brcmsmac never sets it (sequence numbers
come from mac80211 or `scb->seqnum`, main.c:6176-6201). -/
def hwSeq : UInt16 := 0x0010
def startMsdu : UInt16 := 0x0008
def sendRts : UInt16 := 0x0004
def longFrame : UInt16 := 0x0002
def immedAck : UInt16 := 0x0001
/-- MacTxControlHigh: "use alternate txpwr at M_ALT_TXPWR_IDX"; not set by
brcmsmac (d11.h:835). -/
def altTxPwr : UInt16 := 0x0008
end Txc

/-- TxFrameID fields (main.h:91-96). -/
def txfidQueueMask : UInt16 := 0x0007
def txfidSeqMask : UInt16 := 0x7FE0
def txfidSeqShift : UInt16 := 5

/-- Frame types for PhyTxControlWord / XtraFrameTypes (d11.h:790-794). -/
def ftCck : UInt16 := 0
def ftOfdm : UInt16 := 1

/-- PhyTxControlWord_1 fields (d11.h:862-874). -/
def phyTxc1Bw20 : UInt16 := 2
def phyTxc1ModeShift : UInt16 := 3
def stfSiso : UInt16 := 0
def stfCdd : UInt16 := 1
def xftsChannelShift : UInt16 := 8
def phyTxcAntShift : UInt16 := 6
def phyTxcAntMask : UInt16 := 0x03C0

/- `struct d11txh` byte offsets (d11.h:751-786; the comments there give
16-bit word indices). -/
namespace Off
def macTxControlLow : Nat := 0
def macTxControlHigh : Nat := 2
def macFrameControl : Nat := 4
def txFesTimeNormal : Nat := 6
def phyTxControlWord : Nat := 8
def phyTxControlWord1 : Nat := 10
def phyTxControlWord1Fbr : Nat := 12
def phyTxControlWord1Rts : Nat := 14
def phyTxControlWord1FbrRts : Nat := 16
def mainRates : Nat := 18
def xtraFrameTypes : Nat := 20
def iv : Nat := 22            -- 16 bytes
def txFrameRA : Nat := 38     -- 6 bytes
def txFesTimeFallback : Nat := 44
def rtsPlcpFallback : Nat := 46   -- 6 bytes
def rtsDurFallback : Nat := 52
def fragPlcpFallback : Nat := 54  -- 6 bytes
def fragDurFallback : Nat := 60
def mModeLen : Nat := 62
def mModeFbrLen : Nat := 64
def tstampLow : Nat := 66
def tstampHigh : Nat := 68
def abiMimoAntSel : Nat := 70
def preloadSize : Nat := 72
def ampduSeqCtl : Nat := 74
def txFrameID : Nat := 76
def txStatus : Nat := 78
def maxNMpdus : Nat := 80
def maxABytesMrt : Nat := 82
def maxABytesFbr : Nat := 84
def minMBytes : Nat := 86
def rtsPhyHeader : Nat := 88  -- 6 bytes
def rtsFrame : Nat := 94      -- struct ieee80211_rts, 16 bytes
def pad : Nat := 110
/-- D11_TXH_LEN. -/
def txhLen : Nat := 112
/-- PLCP header (D11_PHY_HDR_LEN = 6 bytes) directly after the descriptor. -/
def plcp : Nat := 112
/-- TXOFF: start of the 802.11 frame. -/
def frame : Nat := 118
end Off

/- 802.11 header byte offsets inside the frame. -/
namespace Hdr
def frameControl : Nat := 0
def durationId : Nat := 2
def addr1 : Nat := 4
def seqCtrl : Nat := 22
end Hdr

/-! ## Rates (rate.c, main.c) -/

/-- The transmit rates this port supports. -/
inductive TxRate where
  /-- 1 Mb/s DSSS, long preamble (`BRCM_RATE_1M` = 2 × 500 kb/s). -/
  | cck1
  /-- 6 Mb/s OFDM (`BRCM_RATE_6M` = 12 × 500 kb/s). -/
  | ofdm6
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Rate in 500 kb/s units (brcmu_wifi.h:172-183). -/
def TxRate.rate500 : TxRate → Nat
  | .cck1 => 2
  | .ofdm6 => 12

def TxRate.isOfdm : TxRate → Bool
  | .cck1 => false
  | .ofdm6 => true

/-- `frametype` (main.c:360-365). -/
def TxRate.frameType (r : TxRate) : UInt16 := if r.isOfdm then ftOfdm else ftCck

/-- PLCP SIGNAL rate code: CCK `rate_500 * 5` (main.c:5951), OFDM
`rate_info[rate] & BRCMS_RATE_MASK` = 0x8b & 0x7f = 0x0b for 6 Mb/s
(rate.c:25-37, main.c:5985). -/
def TxRate.plcpSignal : TxRate → UInt32
  | .cck1 => 10
  | .ofdm6 => 0x0B

/-- `brcms_c_rate_legacy_phyctl` (rate.c): tx_phy_ctl3 of `legacy_phycfg_table`. -/
def TxRate.legacyPhyCfg : TxRate → UInt16
  | .cck1 => 0x00
  | .ofdm6 => 0x00

/-- `brcms_basic_rate` (main.c:352-358) for the ACK. With brcmsmac's
`brcms_c_rate_lookup_init` (main.c:3372-3464) the basic rate of 1 Mb/s is
1 Mb/s (every CCK rate is its own mandatory rate) and of 6 Mb/s is 6 Mb/s
(basic, or else the mandatory 6 Mb/s), whatever the BSS basic rate set. -/
def TxRate.basic (r : TxRate) : TxRate := r

/-- Timing constants (main.c:84-108). -/
def aphySymbolTime : Nat := 4
def aphyPreambleTime : Nat := 16
def aphySignalTime : Nat := 4
def aphyServiceNbits : Nat := 16
def aphyTailNbits : Nat := 6
def bphySifsTime : Nat := 10
def bphyPlcpTime : Nat := 192
def dot11AckLen : Nat := 10
def dot11OfdmSignalExtension : Nat := 6
def fcsLen : Nat := 4

/-- `brcms_c_calc_frame_time` (main.c:579-642), 2.4 GHz band, long preamble. -/
def calcFrameTime (r : TxRate) (macLen : Nat) : Nat :=
  let rate := r.rate500
  if r.isOfdm then
    let ndps := rate * 2
    let nsyms := (aphyServiceNbits + 8 * macLen + aphyTailNbits + ndps - 1) / ndps
    aphyPreambleTime + aphySignalTime + aphySymbolTime * nsyms + dot11OfdmSignalExtension
  else
    (macLen * 8 * 2 + rate - 1) / rate + bphyPlcpTime

/-- `get_sifs` (main.c:368-372): 2.4 GHz → BPHY_SIFS_TIME. -/
def sifs : Nat := bphySifsTime

/-- `brcms_c_calc_ack_time` (main.c:5644-5660). -/
def ackTime (r : TxRate) : Nat := calcFrameTime r.basic (dot11AckLen + fcsLen)

/-- `brcms_c_compute_frame_dur` (main.c:5696-5716), `next_frag_len = 0`:
SIFS + ACK. Independent of the frame length. -/
def frameDur (r : TxRate) : UInt16 := (sifs + ackTime r).toUInt16

/-! ## Board-derived antenna / stf state (stf.c, main.c attach) -/

/-- SROM rev 8 `txchain` (TXRXC word, byte 0xA2, bits 0..3). -/
def sromTxChain (cfg : PhyCfg) : Nat := (cfg.srom16 0xA2 &&& 0xF).toNat
/-- SROM rev 8 `ant_available_bg` (byte 0x9C, bits 0..7). -/
def antAvailBg (cfg : PhyCfg) : Nat := (cfg.srom16 0x9C &&& 0xFF).toNat

/-- `wlc->stf->txchain` (`brcms_c_stf_phy_chain_calc`, stf.c:370-405):
SROM txchain, or TXCHAIN_DEF_NPHY (3) when 0 or 0xf. -/
def txChain (cfg : PhyCfg) : Nat :=
  let t := sromTxChain cfg
  if t == 0 || t == 0xF then 3 else t

/-- Transmit antenna bits of PhyTxControlWord for this board.

`wlc->stf->txant` starts as ANT_TX_DEF (main.c:4281); `aa == 3` leaves it
(`brcms_c_attach_stf_ant_init`, main.c:4651-4690) and two tx streams skip the
`txant = hw_txchain - 1` rule (main.c:7914-7916). `brcms_c_stf_d11hdrs_phyctl_txant`
→ `_brcms_c_stf_phytxchain_sel` (stf.c:407-437) then gives
`txchain << PHY_TXC_ANT_SHIFT` for SISO (txant == ANT_TX_DEF) and non-SISO
rates alike: 0x00C0 (both cores) for CCK *and* OFDM.

BFL2_SINGLEANT_CCK (0x1000, set on this board) is defined in brcmsmac
(types.h:73) but **never used**; likewise MHF4_BPHY_TXCORE0 (d11.h:1356).
brcmsmac therefore sends CCK with both antenna bits set; we do the same.

Assumes `ant_available_bg` ∉ {1, 2} (it is 3 here, `antAvailBg`); boards with
a forced single tx antenna take other brcmsmac branches not ported. -/
def phyTxAnt (cfg : PhyCfg) : UInt16 :=
  ((txChain cfg).toUInt16 <<< phyTxcAntShift) &&& phyTxcAntMask

/-! ## Descriptor fields -/

/-- Generation-time transmit configuration (everything that does not depend
on the individual frame). -/
structure TxConfig where
  rate : TxRate := .cck1
  /-- Transmit FIFO; `txAcVoFifo` for management/EAPOL, `txAcBeFifo` for data. -/
  fifo : Nat := txAcVoFifo
  /-- 2.4 GHz channel (XtraFrameTypes bits 8..15). -/
  channel : Nat := 6
  /-- PhyTxControlWord antenna bits (`phyTxAnt`). -/
  txAnt : UInt16 := 0x00C0
  /-- `wlc->stf->ss_opmode` applied to OFDM rates (main.c:6261-6285):
  SISO (0) or CDD (1). See `ssOpmodeUp`. -/
  ofdmStf : UInt16 := stfCdd
  /-- First (only) fragment: TXC_STARTMSDU (`frag == 0`, main.c:6444-6445). -/
  first : Bool := true
  deriving Repr, Inhabited

/-- Per-frame parameters for the generation-time `txHeader`. -/
structure TxParams extends TxConfig where
  /-- MPDU length in bytes *without* FCS (`p->len` before the pushes). -/
  frameLen : Nat
  /-- 802.11 frame control, as stored little endian in the frame. -/
  frameControl : UInt16
  /-- Receiver address (addr1), 6 bytes. -/
  ra : ByteArray
  /-- Sequence control of the frame (seqnum << 4 | fragnum). -/
  seqCtl : UInt16 := 0
  /-- Duration/ID the caller put in the frame (kept for multicast and PS-Poll). -/
  durationIn : UInt16 := 0

/-- PhyTxControlWord (main.c:6620-6629): frame type, no short header (long
preamble at 1 Mb/s; OFDM ignores it), antenna bits. Power bits (0xFC00) are
not set by brcmsmac. -/
def TxConfig.phyCtl (c : TxConfig) : UInt16 := c.rate.frameType ||| c.txAnt

/-- `brcms_c_phytxctl1_calc` (main.c:6064-6112), 20 MHz, N-PHY. CCK: bw |
stf << 3 with stf 0 (the stf policy is applied to OFDM/MCS only); OFDM:
bw | legacy phycfg << 8 | stf << 3. -/
def TxConfig.phyCtl1 (c : TxConfig) : UInt16 :=
  if c.rate.isOfdm then
    phyTxc1Bw20 ||| (c.rate.legacyPhyCfg <<< 8) ||| (c.ofdmStf <<< phyTxc1ModeShift)
  else
    phyTxc1Bw20 ||| (stfSiso <<< phyTxc1ModeShift)

/-- MainRates (main.c:6411-6413): OFDM `plcp[0] & 0xf`, CCK `plcp[0]`. -/
def TxConfig.mainRates (c : TxConfig) : UInt16 := c.rate.plcpSignal.toUInt16

/-- XtraFrameTypes (main.c:6612-6617): fallback frame type, RTS types of the
unused `rts_rspec[] = BRCM_RATE_1M` (FT_CCK = 0), channel << 8. -/
def TxConfig.xtraFrameTypes (c : TxConfig) : UInt16 :=
  c.rate.frameType ||| (ftCck <<< 2) ||| (ftCck <<< 4) ||| (c.channel.toUInt16 <<< xftsChannelShift)

/-- TxFrameID for the `IEEE80211_TX_CTL_ASSIGN_SEQ` path (main.c:6176-6201):
`((seq_ctrl << TXFID_SEQ_SHIFT) & TXFID_SEQ_MASK) | (queue & TXFID_QUEUE_MASK)`,
i.e. fragment number and the low 6 bits of the sequence number in bits 5..14
and the FIFO in bits 0..2. The status for the frame carries the same id. -/
def txFrameId (fifo : Nat) (seqCtl : UInt16) : UInt16 :=
  ((seqCtl <<< txfidSeqShift) &&& txfidSeqMask) ||| (fifo.toUInt16 &&& txfidQueueMask)

/-- `is_multicast_ether_addr(addr1)`. -/
def isMulticast (ra : ByteArray) : Bool := (ra.get! 0) &&& 1 != 0
/-- `ieee80211_is_pspoll` / `ieee80211_is_beacon` on the stored frame control. -/
def isPsPoll (fc : UInt16) : Bool := fc &&& 0x00FC == 0x00A4
def isBeacon (fc : UInt16) : Bool := fc &&& 0x00FC == 0x0080

/-- The PLCP header for `phylen` = MPDU + FCS bytes: `brcms_c_cck_plcp_set`
(main.c:5914-5959, 1 Mb/s: usec = len << 3, service = LOCKED) and
`brcms_c_compute_ofdm_plcp` (main.c:5977-5995: rate nibble | length << 5). -/
def plcpBytes (r : TxRate) (phylen : Nat) : ByteArray :=
  match r with
  | .cck1 =>
    let usec := phylen <<< 3
    ⟨#[10, 0x04, (usec &&& 0xff).toUInt8, ((usec >>> 8) &&& 0xff).toUInt8, 0, 0]⟩
  | .ofdm6 =>
    let v := r.plcpSignal.toNat ||| ((phylen &&& 0xfff) <<< 5)
    ⟨#[(v &&& 0xff).toUInt8, ((v >>> 8) &&& 0xff).toUInt8, ((v >>> 16) &&& 0xff).toUInt8, 0, 0, 0]⟩

private def put16 (b : ByteArray) (off : Nat) (v : UInt16) : ByteArray :=
  (b.set! off v.toUInt8).set! (off + 1) (v >>> 8).toUInt8

private def putBytes (b : ByteArray) (off : Nat) (src : ByteArray) : ByteArray := Id.run do
  let mut out := b
  for i in [0:src.size] do out := out.set! (off + i) (src.get! i)
  return out

/-- The Duration/ID brcmsmac writes into the frame header (main.c:6414-6430),
or `none` when it leaves the caller's value (multicast RA, PS-Poll). -/
def durationId (p : TxParams) : Option UInt16 :=
  if !isPsPoll p.frameControl && !isMulticast p.ra then some (frameDur p.rate) else none

/-- **Generation-time transmit header**: `struct d11txh` followed by the PLCP
header (118 bytes), exactly as `brcms_c_d11hdrs_mac80211` (main.c:6124-6759)
builds it for this configuration. The frame's Duration/ID must additionally be
set to `durationId p` when that is `some`.

Field by field (zero unless listed; main.c line numbers):
* MacTxControlLow: TXC_IGNOREPMQ for beacons (6202-6203), TXC_STARTMSDU when
  `first` (6444-6445), TXC_IMMEDACK unless addr1 is multicast (6447-6448).
  No 5 GHz, 40 MHz, AMIC, RTS/CTS, AMPDU or HWSEQ bits.
* MacTxControlHigh: 0 (long preamble, no RTS; 6455-6466, 6603).
* MacFrameControl: the frame's frame control (6473).
* TxFesTimeNormal / TxFesTimeFallback: 0 (6474-6476; the WME TXOP block at
  6668 needs a QoS frame).
* PhyTxControlWord / _1 / _1_Fbr: `phyCtl` (6620-6629) / `phyCtl1`
  (6632-6641). _1_Rts, _1_FbrRts: 0 (no RTS).
* MainRates (6411-6413, 6609) / XtraFrameTypes (6612-6617).
* IV: 0 (unencrypted). TxFrameRA: addr1 (6479).
* FragPLCPFallback: the fallback-rate PLCP; for CCK its CRC bytes carry
  phylen (6399-6408). FragDurFallback: SIFS+ACK for unicast, 0 for
  multicast, the frame's Duration/ID for PS-Poll (6432-6441).
* MModeLen/MModeFbrLen: 0 (not MCS, 6648-6663). ABI_MimoAntSel: 0 (the
  antcfg computed at 6255 is never stored).
* TxFrameID: `txFrameId` (6176-6199, 6482). TxStatus: 0 (6488). AMPDU
  fields: 0.
* RTS PLCP/frame/fallbacks: zero (6584-6588). -/
def txHeader (p : TxParams) : ByteArray := Id.run do
  let c := p.toTxConfig
  let phylen := p.frameLen + fcsLen
  let mcast := isMulticast p.ra
  let pspoll := isPsPoll p.frameControl
  let mut mcl : UInt16 := 0
  if isBeacon p.frameControl then mcl := mcl ||| Txc.ignorePmq
  if c.first then mcl := mcl ||| Txc.startMsdu
  if !mcast then mcl := mcl ||| Txc.immedAck
  let plcp := plcpBytes c.rate phylen
  let mut fb := plcp
  if !c.rate.isOfdm then
    fb := (fb.set! 4 (phylen &&& 0xff).toUInt8).set! 5 ((phylen >>> 8) &&& 0xff).toUInt8
  let fragDurFb : UInt16 :=
    if pspoll then p.durationIn else if mcast then 0 else frameDur c.rate
  let mut b := ByteArray.mk (Array.replicate Off.frame 0)
  b := put16 b Off.macTxControlLow mcl
  b := put16 b Off.macFrameControl p.frameControl
  b := put16 b Off.phyTxControlWord c.phyCtl
  b := put16 b Off.phyTxControlWord1 c.phyCtl1
  b := put16 b Off.phyTxControlWord1Fbr c.phyCtl1
  b := put16 b Off.mainRates c.mainRates
  b := put16 b Off.xtraFrameTypes c.xtraFrameTypes
  b := putBytes b Off.txFrameRA (p.ra.extract 0 6)
  b := putBytes b Off.fragPlcpFallback fb
  b := put16 b Off.fragDurFallback fragDurFb
  b := put16 b Off.txFrameID (txFrameId c.fifo p.seqCtl)
  b := putBytes b Off.plcp plcp
  return b

/-! ## Run-time descriptor -/

/-- **Run-time transmit header.** The 802.11 frame (without FCS) must already
be in scratch RAM at `r(base) + 118`; its length in bytes is in `lenReg`.
Writes the 118-byte descriptor + PLCP at `r(base)` and, like brcmsmac, the
Duration/ID of the frame. Generation-time constants come from `c`; frame
control, addr1, sequence control, the multicast/PS-Poll/beacon decisions and
all length-dependent fields (PLCP LENGTH/usec, the CCK fallback length) are
computed in bytecode. Produces the same bytes as `txHeader`.

Clobbers r0–r2; `base` and `lenReg` must be other registers and are
preserved. -/
def emitTxHeader (c : TxConfig) (base lenReg : Reg) : ProgM Unit := do
  if base < 3 || lenReg < 3 || base == lenReg || base > 15 || lenReg > 15 then
    fail Fail.badRegs
    return
  if c.fifo >= nFifo then
    fail Fail.unsupported
    return
  let st (w : Nat) (off : Nat) (v : UInt32) : ProgM Unit :=
    emit (.memStore w base off.toUInt32 (.imm v))
  let stR (w : Nat) (off : Nat) (r : Reg) : ProgM Unit :=
    emit (.memStore w base off.toUInt32 (.reg r))
  let ld (w : Nat) (dst : Reg) (off : Nat) : ProgM Unit :=
    emit (.memLoad w dst base off.toUInt32)
  -- memset(txh, 0, D11_TXH_LEN)
  for k in [0:Off.txhLen / 4] do st 4 (4 * k) 0
  -- Constant fields.
  st 2 Off.phyTxControlWord c.phyCtl.toUInt32
  st 2 Off.phyTxControlWord1 c.phyCtl1.toUInt32
  st 2 Off.phyTxControlWord1Fbr c.phyCtl1.toUInt32
  st 2 Off.mainRates c.mainRates.toUInt32
  st 2 Off.xtraFrameTypes c.xtraFrameTypes.toUInt32
  -- MacFrameControl and TxFrameRA from the frame.
  ld 2 0 (Off.frame + Hdr.frameControl)
  stR 2 Off.macFrameControl 0
  for k in [0:3] do
    ld 2 1 (Off.frame + Hdr.addr1 + 2 * k)
    stR 2 (Off.txFrameRA + 2 * k) 1
  -- TxFrameID from the frame's sequence control.
  ld 2 1 (Off.frame + Hdr.seqCtrl)
  shli 1 txfidSeqShift.toUInt32
  andi 1 txfidSeqMask.toUInt32
  ori 1 (c.fifo.toUInt32 &&& txfidQueueMask.toUInt32)
  stR 2 Off.txFrameID 1
  -- PLCP (main PLCP and fallback PLCP) from phylen = len + FCS_LEN.
  mov 1 lenReg
  addi 1 fcsLen.toUInt32
  match c.rate with
  | .cck1 =>
    mov 2 1
    shli 2 3                                       -- usec = phylen << 3
    for off in [Off.plcp, Off.fragPlcpFallback] do
      st 2 off (0x0400 ||| c.rate.plcpSignal)      -- signal, service = LOCKED
      stR 2 (off + 2) 2
    st 2 (Off.plcp + 4) 0
    stR 2 (Off.fragPlcpFallback + 4) 1              -- length in the CCK FBR CRC field
  | .ofdm6 =>
    mov 2 1
    andi 2 0xfff
    shli 2 5
    ori 2 c.rate.plcpSignal
    for off in [Off.plcp, Off.fragPlcpFallback] do
      stR 4 off 2
      st 2 (off + 4) 0
  -- MacTxControlLow, Duration/ID, FragDurFallback.
  -- r0 = frame control (still loaded), r1 = mcl, r2 = scratch.
  li 1 (if c.first then Txc.startMsdu.toUInt32 else 0)
  mov 2 0
  andi 2 0xFC
  let notBeacon ← newLabel
  emit (.branch .ne 2 (.imm 0x80) notBeacon)
  ori 1 Txc.ignorePmq.toUInt32
  place notBeacon
  let mcast ← newLabel
  let done ← newLabel
  ld 1 2 (Off.frame + Hdr.addr1)
  andi 2 1
  emit (.branch .ne 2 (.imm 0) mcast)
  -- unicast: immediate ACK
  ori 1 Txc.immedAck.toUInt32
  stR 2 Off.macTxControlLow 1
  mov 2 0
  andi 2 0xFC
  let pspoll ← newLabel
  emit (.branch .eq 2 (.imm 0xA4) pspoll)
  st 2 (Off.frame + Hdr.durationId) (frameDur c.rate).toUInt32
  st 2 Off.fragDurFallback (frameDur c.rate).toUInt32
  emit (.jump done)
  place pspoll
  ld 2 2 (Off.frame + Hdr.durationId)
  stR 2 Off.fragDurFallback 2
  emit (.jump done)
  -- multicast: no ACK; FragDurFallback 0 (PS-Poll to a group address is
  -- not a valid frame, brcmsmac would copy its duration: do the same).
  place mcast
  stR 2 Off.macTxControlLow 1
  mov 2 0
  andi 2 0xFC
  emit (.branch .ne 2 (.imm 0xA4) done)
  ld 2 2 (Off.frame + Hdr.durationId)
  stR 2 Off.fragDurFallback 2
  place done

/-! ## MAC-side transmit state (main.c) -/

/-- `shm16[r(addr)]` → `dst` for a run-time, 2-aligned SHM byte address.
Uses `t` (≠ dst, addr). -/
def shmRead16At (dst addr t : Reg) : ProgM Unit := do
  mov t addr
  shri t 2
  ori t objShm
  emit (.write32 d11ObjAddr (.reg t))
  r32 t d11ObjAddr
  mov t addr
  andi t 2
  let hi ← newLabel
  let done ← newLabel
  emit (.branch .ne t (.imm 0) hi)
  r16 dst d11ObjData
  emit (.jump done)
  place hi
  r16 dst (d11ObjData + 2)
  place done

/-- `shm16[r(addr)] := r(val)` for a run-time SHM byte address. Uses `t`. -/
def shmWrite16At (addr val t : Reg) : ProgM Unit := do
  mov t addr
  shri t 2
  ori t objShm
  emit (.write32 d11ObjAddr (.reg t))
  r32 t d11ObjAddr
  mov t addr
  andi t 2
  let hi ← newLabel
  let done ← newLabel
  emit (.branch .ne t (.imm 0) hi)
  emit (.write16 d11ObjData (.reg val))
  emit (.jump done)
  place hi
  emit (.write16 (d11ObjData + 2) (.reg val))
  place done

/-- Write a PSM scratch register (objaddr SCR select), as the SCR writes of
`brcms_b_set_cwmin` (main.c:1518-1526) and `brcms_b_coreinit` (3271-3279). -/
def scrWrite (idx v : UInt32) : ProgM Unit := do
  w32 d11ObjAddr (objScr ||| idx)
  r32 12 d11ObjAddr
  w32 d11ObjData v

/-- `xmtfifo_sz[]` for core rev 23 in 256-byte blocks (main.c:283-284):
BK 20, BE 192, VI 192, VO 21, BCMC 17, ATIM 5. -/
def xmtFifoSz : Array Nat := #[20, 192, 192, 21, 17, 5]

/-- `brcms_b_corerev_fifofixup` (main.c:2036-2081): reset each TX FIFO, set
its start/end block (TXFIFO_START_BLK = 6), reset again, then mirror the
sizes into M_FIFOSIZE0..3. -/
def brcmsBCorerevFifofixup : ProgM Unit := do
  let mut start := 6
  for fifo in [0:nFifo] do
    let endBlk := start + xmtFifoSz[fifo]!
    let def0 := (start &&& 0xff) ||| (((endBlk - 1) &&& 0xff) <<< 8)
    let def1 := ((start >>> 8) &&& 1) ||| ((((endBlk - 1) >>> 8) &&& 1) <<< 8)
    let cmd := 0x8000 ||| (fifo <<< 8)
    w16 d11XmtFifoCmd cmd.toUInt32
    w16 d11XmtFifoDef def0.toUInt32
    w16 d11XmtFifoDef1 def1.toUInt32
    w16 d11XmtFifoCmd cmd.toUInt32
    start := endBlk
  shmWrite16 mFifoSize0 (xmtFifoSz[txAcBeFifo]!).toUInt32
  shmWrite16 (mFifoSize0 + 2) (xmtFifoSz[txAcViFifo]!).toUInt32
  shmWrite16 (mFifoSize0 + 4)
    ((xmtFifoSz[txAcVoFifo]! <<< 8) ||| xmtFifoSz[txAcBkFifo]!).toUInt32
  shmWrite16 (mFifoSize0 + 6)
    ((xmtFifoSz[txAtimFifo]! <<< 8) ||| xmtFifoSz[txBcmcFifo]!).toUInt32

/-- Retry limits: RETRY_SHORT_DEF 7, RETRY_LONG_DEF 4, fallback thresholds
RETRY_SHORT_FB 3, RETRY_LONG_FB 2 (main.c:143-147, `brcms_b_info_init`
main.c:1178-1183). mac80211's default short/long limits (7/4) re-set the same
values through `brcms_c_set_rate_limit`. -/
def retryShortDef : UInt32 := 7
def retryLongDef : UInt32 := 4
def retryShortFb : UInt32 := 3
def retryLongFb : UInt32 := 2

/-- The transmit-relevant parts of `brcms_b_coreinit` (main.c:3127-3297) that
`Mac.coreInitTail` does not carry: FIFO size fixup (right after the init
values in brcmsmac), frame burst size and antenna swap threshold
(3231-3233), SRL/LRL into the PSM scratch registers (3271-3279) and the rate
fallback thresholds (3281-3283). DMA engine init (3288-3296) is skipped: no
DMA. Call with the PSM suspended, after `Bcm43224.ucodeStart`. -/
def coreInitTx : ProgM Unit := do
  brcmsBCorerevFifofixup
  shmWrite16 mMburstSize 8           -- MAXTXFRAMEBURST (main.h:127)
  shmWrite16 mMaxAntCnt 10           -- ANTCNT (main.c:122)
  scrWrite sDot11SrcLmt retryShortDef
  scrWrite sDot11LrcLmt retryLongDef
  shmWrite16 mSfrmTxCntFbrThsd retryShortFb
  shmWrite16 mLfrmTxCntFbrThsd retryLongFb

/-- `brcms_c_ucode_txant_set` (main.c:1573-1588) with `bmac_phytxant` =
`phyTxAnt cfg` (set at attach by `_brcms_c_stf_phy_txant_upd`, stf.c:226-262,
and pushed by `brcms_b_txant_set`, main.c:2260-2270): antenna bits of the
probe-response and ACK/CTS phy control words in SHM. -/
def brcmsCUcodeTxantSet (cfg : PhyCfg) : ProgM Unit := do
  let ant := (phyTxAnt cfg).toUInt32
  for off in [mCtxprsBlk + cCtxPctlwdPos, mRspPctlwd] do
    shmRead16 0 off
    andi 0 ((~~~phyTxcAntMask.toUInt32) &&& 0xffff)
    ori 0 ant
    Mac.shmWrite16R off 0

/-- `brcms_b_set_cwmin` / `brcms_b_set_cwmax` (main.c:1518-1536) with the
band defaults APHY_CWMIN = 15, PHY_CWMAX = 1023 (main.c:149-150, 7938-7939). -/
def brcmsBSetCw : ProgM Unit := do
  scrWrite sDot11CwMin 15
  scrWrite sDot11CwMax 1023

/-- `brcms_b_update_slot_timing` (main.c:559-573). brcmsmac starts with a long
slot (`shortslot = false`) until mac80211 reports the BSS's short-slot
capability after association. -/
def brcmsBUpdateSlotTiming (shortSlot : Bool) : ProgM Unit := do
  if shortSlot then
    w16 d11IfsSlot 0x0207
    shmWrite16 mDot11Slot 9      -- APHY_SLOT_TIME
  else
    w16 d11IfsSlot 0x0212
    shmWrite16 mDot11Slot 20     -- BPHY_SLOT_TIME

/-- OFDM RATE sub-field of the PLCP SIGNAL for 6..54 Mb/s
(`brcms_b_ofdm_ratetable_offset` lookup, main.c:1599-1608). -/
def ofdmPlcpRates : Array (Nat × UInt32) :=
  #[(12, 0xB), (18, 0xF), (24, 0xA), (36, 0xE), (48, 0x9), (72, 0xD), (96, 0x8), (108, 0xC)]

/-- `brcms_upd_ofdm_pctl1_table` (main.c:1624-1656) with
`brcms_b_ofdm_ratetable_offset` (1590-1622): set the stf mode bits of the
OFDM PCTL1 word of every OFDM entry of the ucode rate table (used for
ucode-generated responses). `stf` = `wlc_hw->hw_stf_ss_opmode`; at brcmsmac's
init-time bsinit this is still SISO (0) (see `ssOpmodeUp`). Uses r0–r3. -/
def brcmsUpdOfdmPctl1Table (stf : UInt16) : ProgM Unit := do
  for (_, plcpRate) in ofdmPlcpRates do
    shmRead16 0 (mRtDirmapA + plcpRate * 2)
    shli 0 1                                   -- entry_ptr = 2 * shm[...]
    addi 0 mRtOfdmPctl1Pos
    shmRead16At 1 0 2
    andi 1 ((~~~(0x0038 : UInt32)) &&& 0xffff)
    ori 1 (stf.toUInt32 <<< 3)
    shmWrite16At 0 1 2

/-- `rate_info[rate] & BRCMS_RATE_MASK & 0xf` (rate.c:25-37) for the
hardware rates: the direct-map index of each rate. -/
def rateIndex (rate : Nat) : UInt32 :=
  match rate with
  | 2 => 0xA | 4 => 0x4 | 11 => 0x7 | 22 => 0xE
  | 12 => 0xB | 18 => 0xF | 24 => 0xA | 36 => 0xE
  | 48 => 0x9 | 72 => 0xD | 96 => 0x8 | 108 => 0xC
  | _ => 0

def isOfdmRate (rate : Nat) : Bool := rate == 12 || rate == 18 || rate == 24 || rate == 36 ||
  rate == 48 || rate == 72 || rate == 96 || rate == 108

/-- The hardware rate set `cck_ofdm_mimo_rates` (rate.c) in 500 kb/s units, in
table order, with brcmsmac's default basic rates (0x80 flag): 1, 2, 5.5, 11. -/
def hwRates : Array (Nat × Bool) :=
  #[(2, true), (4, true), (11, true), (12, false), (18, false), (22, true),
    (24, false), (36, false), (48, false), (72, false), (96, false), (108, false)]

/-- `brcms_c_rate_lookup_init` (main.c:3372-3464): the best basic rate for
every hardware rate, given which rates are basic. -/
def basicRateTable (rates : Array (Nat × Bool)) : Array (Nat × Nat) := Id.run do
  let mut cckBasic := 0
  let mut ofdmBasic := 0
  let mut out := #[]
  for (r, basic) in rates do
    if basic then
      if isOfdmRate r then ofdmBasic := r else cckBasic := r
      out := out.push (r, r)
    else
      let b := if isOfdmRate r then ofdmBasic else cckBasic
      if b != 0 then out := out.push (r, b)
      else
        let mandatory := if isOfdmRate r then (if r >= 48 then 48 else if r >= 24 then 24 else 12)
          else r
        out := out.push (r, mandatory)
  return out

/-- `brcms_c_set_ratetable` (main.c:3620-3648) with `brcms_c_write_rate_shm`
(3568-3600): for every hardware rate, copy the direct-map pointer of its
basic (ACK/CTS) rate into the BSS-basic-rate map. The pointers are read from
SHM at run time. `rates` defaults to brcmsmac's initial basic set; after
association brcmsmac repeats this with the AP's basic rates. Uses r0. -/
def brcmsCSetRatetable (rates : Array (Nat × Bool) := hwRates) : ProgM Unit := do
  for (rate, basic) in basicRateTable rates do
    let dirTable := if isOfdmRate basic then mRtDirmapA else mRtDirmapB
    let basicTable := if isOfdmRate rate then mRtBbrsmapA else mRtBbrsmapB
    shmRead16 0 (dirTable + rateIndex basic * 2)
    Mac.shmWrite16R (basicTable + rateIndex rate * 2) 0

/-- `brcms_b_rate_shm_offset` (main.c:5599-5620): SHM byte address of the
ucode rate table entry of `rate` into `dst`. -/
def brcmsBRateShmOffset (dst : Reg) (rate : Nat) : ProgM Unit := do
  shmRead16 dst ((if isOfdmRate rate then mRtDirmapA else mRtDirmapB) + rateIndex rate * 2)
  shli dst 1

/-- `brcms_b_set_addrmatch` (main.c:1459-1479): write a MAC address into the
RXE match registers at `matchOffset` (RCM_MAC_OFFSET = 0, RCM_BSSID_OFFSET = 3). -/
def brcmsBSetAddrmatch (matchOffset : UInt32) (addr : ByteArray) : ProgM Unit := do
  w16 d11RcmCtl (0x0020 ||| matchOffset)        -- RCM_INC_DATA
  for k in [0:3] do
    w16 d11RcmMatData ((addr.get! (2 * k)).toUInt32 ||| ((addr.get! (2 * k + 1)).toUInt32 <<< 8))

/-- `brcms_b_set_addrmatch` with the address taken from scratch RAM at
`r(base) + off` (e.g. a BSSID learnt from a beacon). Uses r0. -/
def brcmsBSetAddrmatchR (matchOffset : UInt32) (base : Reg) (off : UInt32) : ProgM Unit := do
  w16 d11RcmCtl (0x0020 ||| matchOffset)
  for k in [0:3] do
    emit (.memLoad 2 0 base (off + 2 * k.toUInt32))
    emit (.write16 d11RcmMatData (.reg 0))

def rcmMacOffset : UInt32 := 0
def rcmBssidOffset : UInt32 := 3

/-- `brcms_c_ampdu_macaddr_upd` (ampdu.c:1041-1051): our address as the TA
of the block-ack template (T_BA_TPL_BASE + 16 = 72), written through the
template RAM port as little-endian words (`brcms_b_write_template_ram`,
main.c:1482-1516; MCTL_BIGEND is never set by these programs). -/
def brcmsCAmpduMacaddrUpd (mac : ByteArray) : ProgM Unit := do
  let b (i : Nat) : UInt32 := (mac.get! i).toUInt32
  w32 d11TplateWrPtr (0x1c * 2 + 16)
  w32 d11TplateWrData (b 0 ||| (b 1 <<< 8) ||| (b 2 <<< 16) ||| (b 3 <<< 24))
  w32 d11TplateWrData (b 4 ||| (b 5 <<< 8))

/-- `brcms_c_set_mac` (main.c:3725-3733): our MAC address into RCMTA entry
RCM_MAC_OFFSET, so the ucode recognises (and ACKs) frames addressed to us. -/
def brcmsCSetMac (mac : ByteArray) : ProgM Unit := do
  brcmsBSetAddrmatch rcmMacOffset mac
  brcmsCAmpduMacaddrUpd mac

/-- `brcms_c_set_bssid` (main.c:3738-3742). All zero until associated. -/
def brcmsCSetBssid (bssid : ByteArray) : ProgM Unit := brcmsBSetAddrmatch rcmBssidOffset bssid

/-- EDCF parameters of one access category (`struct ieee80211_tx_queue_params`). -/
structure EdcfParams where
  /-- TXOP limit in units of 32 µs. -/
  txop : Nat
  aifs : Nat
  cwMin : Nat
  cwMax : Nat

/-- The STA defaults of `brcms_c_edcf_setparams` (main.c:65-80, 4065-4098),
per FIFO: BK (ACI 0x27, ECW 0xA4), BE (0x03, 0xA4), VI (0x42, 0x43, TXOP
0x5e), VO (0x62, 0x32, TXOP 0x2f); CW = 2^ECW − 1.

Note: `brcms_c_edcf_setparams` indexes `wme_ac2fifo[]` (mac80211 AC order)
with the 802.11 ACI from these bytes, so its own init-time call lands the BE
set on FIFO 3, BK on 2, VI on 1 and VO on 0. mac80211 then calls
`brcms_ops_conf_tx` → `brcms_c_wme_setparams` for every queue with the same
standard values in mac80211 AC order (mac80211_if.c:792-800), which is the
per-FIFO assignment below; we write that end state directly. -/
def edcfDefaults : Array (Nat × EdcfParams) :=
  #[(txAcBkFifo, ⟨0, 7, 15, 1023⟩), (txAcBeFifo, ⟨0, 3, 15, 1023⟩),
    (txAcViFifo, ⟨0x5e, 2, 7, 15⟩), (txAcVoFifo, ⟨0x2f, 2, 3, 7⟩)]

/-- `brcms_c_wme_setparams` (main.c:4000-4063) for the FIFO `fifo`, without
the beacon/probe-response template updates (AP only). `bslots` =
`tsf_random & cwcur` is read at run time. `isVi` applies the AC_VI AIFS
increment for a zero TXOP. Uses r0–r2. -/
def brcmsCWmeSetparams (fifo : Nat) (p : EdcfParams) (isVi : Bool := false) : ProgM Unit := do
  let txop := p.txop <<< 5                      -- EDCF_TXOP2USEC
  let mut aifs := p.aifs &&& 0xf
  if isVi && txop == 0 && aifs < 15 then aifs := aifs + 1
  if aifs < 1 || aifs > 15 then
    fail Fail.unsupported
    return
  let base := mEdcfQinfo + fifo.toUInt32 * mEdcfQlen
  -- bslots (r1) and reggap (r2)
  r16 1 d11TsfRandom
  andi 1 p.cwMin.toUInt32
  mov 2 1
  addi 2 aifs.toUInt32
  -- status (r0)
  shmRead16 0 (base + mEdcfStatusOff)
  ori 0 0x0100                                  -- WME_STATUS_NEWAC
  shmWrite16 base txop.toUInt32
  shmWrite16 (base + 2) p.cwMin.toUInt32
  shmWrite16 (base + 4) p.cwMax.toUInt32
  shmWrite16 (base + 6) p.cwMin.toUInt32       -- cwcur
  shmWrite16 (base + 8) aifs.toUInt32
  Mac.shmWrite16R (base + 10) 1
  Mac.shmWrite16R (base + 12) 2
  Mac.shmWrite16R (base + 14) 0
  for k in [0:8] do shmWrite16 (base + 16 + 2 * k.toUInt32) 0

/-- EDCF enable of `brcms_c_init` (main.c:7820-7821): IFS_USEEDCF in
ifs_ctl, then the per-FIFO parameters. Also sets MHF1_EDCF in host flags 1
(`brcms_c_up`, main.c:5020, written by the band init host-flag write in
brcmsmac; `Mac.bandInit` writes zeros so we OR it in afterwards). -/
def edcfInit : ProgM Unit := do
  shmRead16 0 mHostFlags1
  ori 0 0x0100                                  -- MHF1_EDCF
  Mac.shmWrite16R mHostFlags1 0
  maskSet16 d11IfsCtl 0xFFFF 0x0004             -- IFS_USEEDCF
  for (fifo, p) in edcfDefaults do
    brcmsCWmeSetparams fifo p (fifo == txAcViFifo)

/-- Transmit-related tail of `brcms_c_init` (main.c:7760-7857) after
`brcms_c_bandinit_ordered`: probe response timeout (BRCMS_PRB_RESP_TIMEOUT =
0), frame-burst TXOP (MAXFRAMEBURST_TXOP = 10000 µs, `_rifs` false), zero
duty-cycle limits (`brcms_c_duty_cycle_set`, 3669-3694), the ACK/CTS rate
table (`brcms_c_bsinit` → `brcms_c_set_ratetable`; `brcms_c_ucode_mac_upd`
does nothing while unassociated and `brcms_c_antsel_init` nothing for
ANTSEL_NA: SROM antswitch = 0), EDCF. Not ported: `brcms_c_bcn_li_upd`
(power save), `brcms_c_ampdu_shm_upd` (A-MPDU receive). -/
def cInitTxTail : ProgM Unit := do
  shmWrite16 mPrsMaxTime 0
  shmWrite16 mMburstTxop 10000
  shmWrite16 mTxIdleBusyRatioOfdm 0
  shmWrite16 mTxIdleBusyRatioCck 0
  brcmsCSetRatetable
  edcfInit

/-! ## Transmit power target (phy_cmn.c, phy_n.c, channel.c) -/

namespace Power

/-- TXP_* rate indices (phy_int.h:68-95). -/
def firstCck : Nat := 0
def lastCck : Nat := 3
def firstOfdm : Nat := 4
def lastOfdm : Nat := 11
def firstOfdm20Cdd : Nat := 12
def lastOfdm20Cdd : Nat := 19
def firstMcs20Siso : Nat := 20
def lastMcs20Siso : Nat := 27
def firstMcs20Cdd : Nat := 28
def lastMcs20Cdd : Nat := 35
def firstMcs20Stbc : Nat := 36
def lastMcs20Stbc : Nat := 43
def firstMcs20Sdm : Nat := 44
def lastMcs20Sdm : Nat := 51
def firstOfdm40Siso : Nat := 52
def lastOfdm40Siso : Nat := 59
def firstOfdm40Cdd : Nat := 60
def lastOfdm40Cdd : Nat := 67
def firstMcs40Siso : Nat := 68
def lastMcs40Siso : Nat := 75
def firstMcs40Cdd : Nat := 76
def lastMcs40Cdd : Nat := 83
def firstMcs40Stbc : Nat := 84
def lastMcs40Stbc : Nat := 91
def firstMcs40Sdm : Nat := 92
def lastMcs40Sdm : Nat := 99
def mcs32 : Nat := 100
def numRates : Nat := 101

/-- `u8` subtraction as in C (wraps modulo 256). -/
def sub8 (a b : Nat) : Nat := (a % 256 + 256 - b % 256) % 256

/-- SROM rev 8 byte offsets (ssb_regs.h `SSB_SPROM8_*`/`SSB_SROM8_*`; the
header is not in the source checkout, values recorded here): per-core power
info at 0xC0/0xE0 (`maxp2ga` = low byte of +0), CCK2GPO 0x140, OFDM2GPO
0x142 (32 bit, low word first), 2G_MCSPO 0x152 (8 words), CDDPO 0x192,
STBCPO 0x194, BW40PO 0x196, AGAIN01 0x9E (antenna gain 0 = low byte). -/
structure Srom where
  maxPwr2g : Array Nat
  cck2gpo : Nat
  ofdm2gpo : Nat
  mcs2gpo : Array Nat
  cddpo : Nat
  stbcpo : Nat
  bw40po : Nat
  antGain0 : Nat

def Srom.ofCfg (cfg : PhyCfg) : Srom :=
  let w (o : Nat) : Nat := (cfg.srom16 o).toNat
  { maxPwr2g := #[w 0xC0 &&& 0xff, w 0xE0 &&& 0xff]
    cck2gpo := w 0x140
    ofdm2gpo := w 0x142 ||| (w 0x144 <<< 16)
    mcs2gpo := (List.range 8).toArray.map fun k => w (0x152 + 2 * k)
    cddpo := w 0x192
    stbcpo := w 0x194
    bw40po := w 0x196
    antGain0 := w 0x9E &&& 0xff }

/-- `wlc_phy_txpwr_nphy_srom_convert` (phy_n.c:27840-27855). -/
def sromConvert (a : Array Nat) (offs : Array Nat) (maxPwr start stop : Nat) : Array Nat := Id.run do
  let mut a := a
  for rate in [start:stop + 1] do
    let w := offs.getD ((rate - start) >>> 2) 0
    let nib := (w >>> (4 * ((rate - start) &&& 3))) &&& 0xf
    a := a.set! rate (sub8 maxPwr (2 * nib))
  return a

/-- `wlc_phy_txpwr_nphy_po_apply` (phy_n.c:27858-27865). -/
def poApply (a : Array Nat) (po start stop : Nat) : Array Nat := Id.run do
  let mut a := a
  for rate in [start:stop + 1] do a := a.set! rate (sub8 a[rate]! (2 * po))
  return a

/-- `wlc_phy_ofdm_to_mcs_powers_nphy` (phy_n.c). -/
def ofdmToMcs (p : Array Nat) (mcsStart mcsEnd ofdmStart : Nat) : Array Nat := Id.run do
  let mut p := p
  let mut rate2 := ofdmStart
  for rate1 in [mcsStart:mcsEnd] do
    p := p.set! rate1 p[rate2]!
    rate2 := rate2 + (if rate1 == mcsStart then 2 else 1)
  p := p.set! mcsEnd p[mcsEnd - 1]!
  return p

/-- `wlc_phy_mcs_to_ofdm_powers_nphy` (phy_n.c): the first MCS value feeds the
first two OFDM rates. -/
def mcsToOfdm (p : Array Nat) (ofdmStart ofdmEnd mcsStart : Nat) : Array Nat := Id.run do
  let mut p := p
  let mut rate1 := ofdmStart
  let mut rate2 := mcsStart
  for _ in [0:ofdmEnd - ofdmStart + 1] do
    if rate1 <= ofdmEnd then
      p := p.set! rate1 p[rate2]!
      if rate1 == ofdmStart then
        rate1 := rate1 + 1
        p := p.set! rate1 p[rate2]!
      rate1 := rate1 + 1
      rate2 := rate2 + 1
  return p

/-- `tx_srom_max_rate_2g[]`: `wlc_phy_txpwr_srom_read_ppr_nphy`
(phy_n.c:14374-14547) → `wlc_phy_txpwr_apply_nphy` (27895-28088), band 0
(2.4 GHz), N-PHY rev 6 (rev ≥ 3 offsets applied, SROM re-interpretation on
since rev ≥ 5). -/
def sromMaxRate2g (s : Srom) (phyRev : Nat) : Array Nat := Id.run do
  let maxPwr := min (s.maxPwr2g.getD 0 0) (s.maxPwr2g.getD 1 0)
  let cdd := s.cddpo &&& 0xf
  let stbc := s.stbcpo &&& 0xf
  let bw40 := s.bw40po &&& 0xf
  let ofdmOffs := #[s.ofdm2gpo &&& 0xffff, (s.ofdm2gpo >>> 16) &&& 0xffff]
  let mcs := s.mcs2gpo
  let mut a := Array.replicate numRates 0
  a := sromConvert a #[s.cck2gpo] maxPwr firstCck lastCck
  a := sromConvert a ofdmOffs maxPwr firstOfdm lastOfdm
  a := ofdmToMcs a firstMcs20Siso lastMcs20Siso firstOfdm
  a := sromConvert a mcs maxPwr firstMcs20Cdd lastMcs20Cdd
  if phyRev >= 3 then a := poApply a cdd firstMcs20Cdd lastMcs20Cdd
  a := mcsToOfdm a firstOfdm20Cdd lastOfdm20Cdd firstMcs20Cdd
  a := sromConvert a mcs maxPwr firstMcs20Stbc lastMcs20Stbc
  if phyRev >= 3 then a := poApply a stbc firstMcs20Stbc lastMcs20Stbc
  a := sromConvert a (mcs.extract 2 8) maxPwr firstMcs20Sdm lastMcs20Sdm
  if phyRev >= 5 then
    a := sromConvert a (mcs.extract 4 8) maxPwr firstMcs40Siso lastMcs40Siso
    a := mcsToOfdm a firstOfdm40Siso lastOfdm40Siso firstMcs40Siso
    a := sromConvert a (mcs.extract 4 8) maxPwr firstMcs40Cdd lastMcs40Cdd
    a := poApply a cdd firstMcs40Cdd lastMcs40Cdd
    a := mcsToOfdm a firstOfdm40Cdd lastOfdm40Cdd firstMcs40Cdd
    a := sromConvert a (mcs.extract 4 8) maxPwr firstMcs40Stbc lastMcs40Stbc
    a := poApply a stbc firstMcs40Stbc lastMcs40Stbc
    a := sromConvert a (mcs.extract 6 8) maxPwr firstMcs40Sdm lastMcs40Sdm
  else
    let mut rate2 := firstOfdm
    for rate1 in [firstOfdm40Siso:lastMcs40Sdm + 1] do
      a := a.set! rate1 a[rate2]!
      rate2 := rate2 + 1
  if phyRev >= 3 then a := poApply a bw40 firstOfdm40Siso lastMcs40Sdm
  a := a.set! mcs32 a[firstMcs40Cdd]!
  return a

/-- Antenna gain in quarter dB from the SROM byte (the bcma SROM parser's
Q5.2 conversion feeding `sprom->antenna_gain.a0`; 0xff means 2 dBm). -/
def antGainQdb (g : Nat) : Nat :=
  if g == 0xff then 8 else ((g &&& 0xC0) >>> 6) ||| ((g &&& 0x3F) <<< 2)

/-- `struct txpwr_limits` (only the fields brcmsmac fills for 2.4 GHz). -/
structure Limits where
  cck : Array Nat
  ofdm : Array Nat
  ofdmCdd : Array Nat
  ofdm40Siso : Array Nat
  ofdm40Cdd : Array Nat
  mcs20Siso : Array Nat
  mcs20Cdd : Array Nat
  mcs20Stbc : Array Nat
  mcs20Mimo : Array Nat
  mcs40Siso : Array Nat
  mcs40Cdd : Array Nat
  mcs40Stbc : Array Nat
  mcs40Mimo : Array Nat
  mcs32 : Nat

/-- `locale_bn` 2.4 GHz MIMO limits (channel.c:119-126), qdBm, index chan-1. -/
def localeBnMaxpwr20 : Array Nat := #[52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 0]
def localeBnMaxpwr40 : Array Nat := #[0, 0, 52, 52, 52, 52, 52, 52, 52, 52, 52, 0, 0, 0]

/-- The C loop that fills a 40 MHz OFDM array from MCS values
(channel.c:529-537 / 546-554): `a[0] = a[1] = m[0]`, `a[i] = m[i-1]`, only
where `a[i]` is 0. -/
def fill40 (a m : Array Nat) : Array Nat := Id.run do
  let mut a := a
  let mut i := 0
  let mut j := 0
  for _ in [0:8] do
    if i < 8 then
      if a[i]! == 0 then a := a.set! i m[j]!
      if i == 0 then
        i := 1
        if a[i]! == 0 then a := a.set! i m[j]!
      i := i + 1
      j := j + 1
  return a

/-- `brcms_c_channel_reg_limits` (channel.c:398-568) for a 2.4 GHz 20 MHz
channel of the worldwide "X2" locale (`locale_bn`), with the mac80211
channel `max_power` of 19 dBm (mac80211_if.c:52-59), followed by
`brcms_c_channel_min_txpower_limits_with_local_constraint` with
BRCMS_TXPWR_MAX (channel.c:229-298; no change). -/
def regLimits (chan antGain : Nat) (chMaxPowerDbm : Nat := 19) : Limits := Id.run do
  let rep (v : Nat) : Array Nat := Array.replicate 8 v
  let conductedMax := 22 * 4
  let maxpwr := min (if chMaxPowerDbm * 4 ≥ antGain then chMaxPowerDbm * 4 - antGain else 0)
    conductedMax
  let delta := if antGain > 24 then antGain - 24 else 0
  let idx := chan - 1
  let m20 := localeBnMaxpwr20.getD idx 0
  let m40 := localeBnMaxpwr40.getD idx 0
  let maxpwr20 := if m20 ≥ delta then m20 - delta else 0
  let maxpwr40 := if m40 ≥ delta then m40 - delta else 0
  -- locale_bn: SISO expressed in the table, overriding CDD later.
  let siso20 := 16 * 4
  let siso40 := if chan >= 3 && chan <= 11 then 16 * 4 else 0
  let mcs40Cdd := rep maxpwr40
  let mcs40Siso := (rep siso40).map fun v => if v == 0 then maxpwr40 else v
  let mcs20Cdd := rep maxpwr20
  let lim : Limits :=
    { cck := Array.replicate 4 maxpwr, ofdm := rep maxpwr, ofdmCdd := rep maxpwr
      ofdm40Siso := fill40 (rep 0) mcs40Siso
      ofdm40Cdd := fill40 (rep 0) mcs40Cdd
      mcs20Siso := rep siso20, mcs20Cdd
      mcs20Stbc := mcs20Cdd                     -- stbc 0 → copied from CDD
      mcs20Mimo := rep siso20                   -- maxpwr20 reassigned by locale_bn
      mcs40Siso, mcs40Cdd
      mcs40Stbc := mcs40Cdd
      mcs40Mimo := rep siso40
      mcs32 := siso40 }
  return lim

/-- `wlc_phy_txpower_reg_limit_calc` (phy_cmn.c:1412-1566), N-PHY. -/
def regLimitCalc (t : Limits) : Array Nat := Id.run do
  let mut l := Array.replicate numRates 0
  for k in [0:4] do l := l.set! (firstCck + k) t.cck[k]!
  for k in [0:8] do l := l.set! (firstOfdm + k) t.ofdm[k]!
  -- MCS → OFDM
  for (p1, p2, start) in [(t.mcs20Siso, t.ofdm, firstOfdm), (t.mcs20Cdd, t.ofdmCdd, firstOfdm20Cdd),
      (t.mcs40Siso, t.ofdm40Siso, firstOfdm40Siso), (t.mcs40Cdd, t.ofdm40Cdd, firstOfdm40Cdd)] do
    let tmp := mcsToOfdm (Array.replicate 8 0 ++ p1) 0 7 8
    for r in [0:8] do l := l.set! (start + r) (min p2[r]! tmp[r]!)
  -- OFDM → MCS
  for (p1, p2, start) in [(t.ofdm, t.mcs20Siso, firstMcs20Siso), (t.ofdmCdd, t.mcs20Cdd, firstMcs20Cdd),
      (t.ofdm40Siso, t.mcs40Siso, firstMcs40Siso), (t.ofdm40Cdd, t.mcs40Cdd, firstMcs40Cdd)] do
    let tmp := ofdmToMcs (Array.replicate 8 0 ++ p1) 0 7 8
    for r in [0:8] do l := l.set! (start + r) (min p2[r]! tmp[r]!)
  for r in [0:8] do
    l := l.set! (firstMcs20Stbc + r) t.mcs20Stbc[r]!
    l := l.set! (firstMcs40Stbc + r) t.mcs40Stbc[r]!
    l := l.set! (firstMcs20Sdm + r) t.mcs20Mimo[r]!
    l := l.set! (firstMcs40Sdm + r) t.mcs40Mimo[r]!
  l := l.set! mcs32 t.mcs32
  l := l.set! firstMcs40Cdd (min l[firstMcs40Cdd]! l[mcs32]!)
  l := l.set! mcs32 l[firstMcs40Cdd]!
  return l

/-- Result of `wlc_phy_txpower_recalc_target`. -/
structure Targets where
  target : Array Nat
  max : Nat
  min : Nat
  maxRateInd : Nat
  offset : Array Nat

/-- `wlc_phy_txpower_recalc_target` (phy_cmn.c:1299-1409), N-PHY: per rate,
min(SROM max, regulatory limit) − 6 qdB, capped by the user target, floored at
`min_txpower` = PHY_TXPWR_MIN_NPHY (8 dBm = 32 qdBm, phy_cmn.c:495), capped
by the environment limit BRCMS_TXPWR_MAX. `txpwr_percent` = 100,
`pactrl` = 0, `user_txpwr_at_rfport` = false (phy_cmn.c:432, 523). N-PHY
offsets are `tx_power_max − target`. -/
def recalcTarget (srom limit : Array Nat) (userTarget : Nat) : Targets := Id.run do
  let minPwr := 8 * 4
  let mut tgt := Array.replicate numRates 0
  let mut mx := 0
  let mut mn := 255
  let mut ind := 0
  for rate in [0:numRates] do
    let mut m := min srom[rate]! limit[rate]!
    m := if m > 6 then m - 6 else 0
    m := min m userTarget
    m := m * 100 / 100
    let t := min (max m minPwr) 127
    tgt := tgt.set! rate t
    if t > mx then ind := rate
    mx := max mx t
    mn := min mn t
  let offset := tgt.map fun t => mx - t
  return { target := tgt, max := mx, min := mn, maxRateInd := ind, offset }

/-- `wlc_phy_txpwr_limit_to_tbl_nphy` (phy_n.c:17468-17559), 20 MHz:
`adj_pwr_tbl_nphy[84]` from the per-rate offsets. -/
def limitToTbl (off : Array Nat) : Array Nat := Id.run do
  let mut t := Array.replicate 84 0
  for i in [firstCck:lastCck + 1] do t := t.set! i off[i]!
  for i in [0:4] do
    let (start, delta) := match i with
      | 0 => (firstOfdm, 1)
      | 1 => (firstMcs20Cdd, 0)
      | 2 => (firstMcs20Stbc, 0)
      | _ => (firstMcs20Sdm, 0)
    let mut idx := start
    let mut vals : Array Nat := #[]
    vals := vals.push off[idx]!
    idx := idx + delta
    vals := vals.push off[idx]!
    vals := vals.push off[idx]!
    vals := vals.push off[idx]!; idx := idx + 1
    vals := vals.push off[idx]!; idx := idx + 1
    vals := vals.push off[idx]!
    vals := vals.push off[idx]!
    vals := vals.push off[idx]!; idx := idx + 1
    vals := vals.push off[idx]!; idx := idx + 1
    vals := vals.push off[idx]!
    vals := vals.push off[idx]!
    vals := vals.push off[idx]!; idx := idx + 1
    vals := vals.push off[idx]!
    vals := vals.push off[idx]!; idx := idx + 1
    vals := vals.push off[idx]!
    idx := idx + 1 - delta
    for _ in [0:5] do vals := vals.push off[idx]!
    for h : k in [0:vals.size] do t := t.set! (4 + 4 * k + i) vals[k]
  return t

/-- mac80211's configured power for the channel: `conf->power_level` =
channel `max_power` 19 dBm (mac80211_if.c:58) → `brcms_c_set_tx_power`
(main.c:7537-7544) → `tx_user_target[] = 76` qdBm. (Before that call
brcmsmac's attach default is BRCMS_TXPWR_MAX = 127; either value exceeds the
limited targets, so the result is the same.) -/
def userTargetDefault : Nat := 19 * 4

/-- All of the above for `cfg` (2.4 GHz channel `cfg.channel`, 20 MHz). -/
def targets (cfg : PhyCfg) (userTarget : Nat := userTargetDefault) : Targets :=
  let s := Srom.ofCfg cfg
  let srom := sromMaxRate2g s cfg.phyRev
  let lim := regLimitCalc (regLimits cfg.channel (antGainQdb s.antGain0))
  recalcTarget srom lim userTarget

/-- `adj_pwr_tbl_nphy` for `cfg`. -/
def adjPwrTbl (cfg : PhyCfg) (userTarget : Nat := userTargetDefault) : Array UInt32 :=
  (limitToTbl (targets cfg userTarget).offset).map (·.toUInt32)

end Power

/-- `wlc->stf->ss_opmode` once brcmsmac is up: `brcms_c_stf_ss_algo_channel_get`
(stf.c:87-129) picks CDD unless the 20 MHz SISO MCS target exceeds the CDD
target by more than 12 qdB, and `brcms_c_stf_ss_update` (stf.c:307-335) uses
it with two tx streams. For this board (targets 58 vs 46 qdBm) → CDD. -/
def ssOpmodeUp (cfg : PhyCfg) : UInt16 :=
  let t := (Power.targets cfg).target
  if txChain cfg == 1 || txChain cfg == 2 then stfSiso
  else if t[Power.firstMcs20Siso]! > t[Power.firstMcs20Cdd]! + 12 then stfSiso else stfCdd

/-- The board's `TxConfig` for `rate` on `fifo`. -/
def TxConfig.ofPhy (cfg : PhyCfg) (rate : TxRate) (fifo : Nat := txAcVoFifo) : TxConfig :=
  { rate, fifo, channel := cfg.channel, txAnt := phyTxAnt cfg, ofdmStf := ssOpmodeUp cfg }

/-- `wlc_phy_txpower_recalc_target` → `wlc_phy_txpower_recalc_target_nphy`
(phy_n.c:28090-28108) as emitted register writes for this board:
`wlc_phy_txpwr_limit_to_tbl_nphy` (generation time), then
`wlc_phy_txpwrctrl_pwr_setup_nphy` (phy_n.c:17561-17769; core rev 23, SROM
rev 8, 2.4 GHz, rev 3..6, IPA, `phyhang_avoid` false) with target
`tx_power_max`, then `wlc_phy_txpwrctrl_enable_nphy(ON)` (28150-28292,
`NPhyInit.txpwrctrlOn`).

The idle TSSI written to 0x1e9 comes from `pi->nphy_pwrctrl_info[].idle_tssi_2g`
measured during the PHY init; the program has no memory of it, so 0x1e9 is
read back at the start (its value is exactly the last init write,
`0x8000 | idle0 | idle1 << 8`, which pwr_setup rewrites unchanged). Requires
the MAC to be suspended (brcmsmac: `wlc_phy_txpower_limit_set` suspends).
For this board: target 62 qdBm (15.5 dBm) on both cores, CCK offset 0, OFDM
offset 4 qdB. Uses r0. -/
def txpowerRecalcTargetNphy (cfg : PhyCfg) (userTarget : Nat := Power.userTargetDefault) :
    ProgM Unit := do
  if !(cfg.phyRev >= 3 && cfg.phyRev < 7 && NPhyInit.ipa cfg && cfg.channel >= 1 &&
      cfg.channel <= 13) then
    fail Fail.unsupported
    return
  let t := Power.targets cfg userTarget
  let adj := Power.adjPwrTbl cfg userTarget
  let tgt : UInt32 := (t.max % 256).toUInt32
  phyRead 0 0x1e9
  -- wlc_phy_txpwrctrl_pwr_setup_nphy
  phyOr 0x122 0x1
  phyAnd 0x1e7 0x7fff
  if cfg.fem2g &&& 1 != 0 then phyOr 0x1e9 0x4000     -- srom_fem2g.tssipos
  radioWrite (0x2d ||| 0x2000) 0xe                     -- TX0 TX_SSI_MUX (IPA, 2 GHz)
  radioWrite (0x2d ||| 0x3000) 0xe                     -- TX1 TX_SSI_MUX
  phyMod 0x1e7 0x7f 0x40                               -- NPHY_TxPwrCtrlCmd_pwrIndex_init
  phyMod 0x222 0xff 0x40
  phyWrite 0x1e8 (((0x3 : UInt32) <<< 8) ||| 240)
  ori 0 0x8000
  phyWriteR 0x1e9 0
  phyWrite 0x1ea (tgt ||| (tgt <<< 8))
  printImm Tag.txPwrTarget tgt
  tableWrite cfg 26 0 32 (NPhyInit.pwrEstTable cfg 0)
  tableWrite cfg 27 0 32 (NPhyInit.pwrEstTable cfg 1)
  tableWrite cfg 26 64 8 adj
  tableWrite cfg 27 64 8 adj
  -- wlc_phy_txpwrctrl_enable_nphy(pi, PHY_TPC_HW_ON)
  NPhyInit.txpwrctrlOn cfg adj

/-! ## Composition -/

/-- The transmit set-up brcmsmac performs between microcode start and
`brcms_c_enable_mac`, in brcmsmac order, for a MAC that `Driver.listen`-style
programs have brought up with `ucodeStart`, `Mac.coreInitTail` and
`Mac.bandInit` (PSM still suspended):

1. `coreInitTx` (rest of `brcms_b_coreinit`),
2. from `brcms_b_bsinit` (main.c:1659-1695): `brcmsCUcodeTxantSet`,
   cwmin/cwmax, long-slot timing, `brcmsUpdOfdmPctl1Table` (SISO, the
   init-time `hw_stf_ss_opmode`),
3. `brcms_c_init`: `brcmsCSetMac`, `brcmsCSetBssid`, then
   `brcms_c_bandinit_ordered` → `brcms_c_set_phy_chanspec` →
   `wlc_phy_txpower_limit_set` (`txpowerRecalcTargetNphy`), then
   `cInitTxTail`,
4. the RF-disable delay (brcmsmac writes it just after `brcms_c_enable_mac`;
   the register is independent of the MAC state).

`M_CURCHANNEL` is already written by `Radio2056.radioOn`
(`wlc_phy_chanspec_set`), so the ucode does not suppress frames whose
XtraFrameTypes channel is 6 (TX_STATUS_SUPR_BADCH). Uses r0–r3. -/
def txSetup (cfg : PhyCfg) (mac bssid : ByteArray) : ProgM Unit := do
  coreInitTx
  brcmsCUcodeTxantSet cfg
  brcmsBSetCw
  brcmsBUpdateSlotTiming false
  brcmsUpdOfdmPctl1Table stfSiso
  brcmsCSetMac mac
  brcmsCSetBssid bssid
  txpowerRecalcTargetNphy cfg
  cInitTxTail
  w32 d11RfDisableDly 10000000                  -- RFDISABLE_DEFAULT (main.c:7843)

/-- Our address, from SROM rev 8 bytes 0x8C..0x91 (`il0mac`), big-endian
per 16-bit word: 10:0d:7f:c9:75:f1 on the Qotom card. -/
def macAddr (cfg : PhyCfg) : ByteArray :=
  let w (o : Nat) := cfg.srom16 o
  ⟨#[(w 0x8C >>> 8).toUInt8, (w 0x8C).toUInt8, (w 0x8E >>> 8).toUInt8, (w 0x8E).toUInt8,
     (w 0x90 >>> 8).toUInt8, (w 0x90).toUInt8]⟩

/-! ## Transmit status (main.c:986-1028, d11.h) -/

/- TX status bits: frmtxstatus (d11.h:623-627) = `frameid << 16 | status`,
status (d11.h:909-933):
* bit 0 `TX_STATUS_VALID` (TXS_V),
* bit 1 `TX_STATUS_ACK_RCV`,
* bits 2..4 suppress reason (1 PMQ, 2 flush, 3 frag/TBTT, 4 bad channel,
  5 lifetime expiry, 6 underflow),
* bit 5 `TX_STATUS_AMPDU`, bit 6 `TX_STATUS_INTERMEDIATE`,
  bit 7 `TX_STATUS_PMINDCTD`,
* bits 8..11 RTS transmit count, bits 12..15 frame transmit count
  (attempts; brcmsmac reports it to mac80211 as the rate's try count).
frmtxstatus2 (d11.h:629-634): bits 0..15 sequence, 16..23 PHY tx error,
bit 24 MU. -/
namespace Txs
def valid : UInt32 := 0x0001
def ackRcv : UInt32 := 0x0002
def suprMask : UInt32 := 0x001C
def ampdu : UInt32 := 0x0020
def intermediate : UInt32 := 0x0040
def frmRtxShift : UInt32 := 12
end Txs

/-- Poll the MAC's transmit status (`brcms_b_txstatus`, main.c:986-1028) for
the frame whose TxFrameID is in `fidReg`, at most `tries` polls `us`
microseconds apart. Like brcmsmac: a read of 0xffffffff is a dead chip;
frmtxstatus2 is read only for a valid status; intermediate non-AMPDU
statuses are discarded (`brcms_c_dotxstatus`, main.c:821-828). Statuses of
other frame ids are printed (`Tag.txsOther`) and skipped.

Results: r0 = 1 found, 0 timeout, 2 dead chip; r1 = status (low 16 bits);
r2 = 1 if ACK received; r3 = frame transmit count (status >> 12);
r4 = suppress reason ((status & 0x1c) >> 2, 0 = none); r5 = frmtxstatus2.
Clobbers r0–r7 (no accessor registers); `fidReg` must be one of r8–r15. -/
def readTxStatus (fidReg : Reg) (tries us : UInt32) : ProgM Unit := do
  if fidReg < 8 || fidReg > 15 then
    fail Fail.badRegs
    return
  let top ← newLabel
  let next ← newLabel
  let timeout ← newLabel
  let dead ← newLabel
  let found ← newLabel
  let done ← newLabel
  li 6 tries
  place top
  r32 7 d11FrmTxStatus
  emit (.branch .eq 7 (.imm 0xFFFFFFFF) dead)
  mov 0 7
  andi 0 Txs.valid
  emit (.branch .eq 0 (.imm 0) next)
  r32 5 d11FrmTxStatus2
  mov 1 7
  andi 1 0xFFFF
  -- intermediate but not AMPDU: discard
  mov 0 1
  andi 0 (Txs.ampdu ||| Txs.intermediate)
  let notInter ← newLabel
  emit (.branch .ne 0 (.imm Txs.intermediate) notInter)
  print Tag.txsIntermediate 7
  emit (.jump next)
  place notInter
  mov 0 7
  shri 0 16
  emit (.branch .eq 0 (.reg fidReg) found)
  print Tag.txsOther 7
  place next
  delay us
  emit (.alu .sub 6 (.imm 1))
  emit (.branch .ne 6 (.imm 0) top)
  place timeout
  li 0 0
  emit (.jump done)
  place dead
  print Tag.txsDead 7
  li 0 2
  emit (.jump done)
  place found
  li 0 1
  mov 2 1
  andi 2 Txs.ackRcv
  shri 2 1
  mov 3 1
  shri 3 Txs.frmRtxShift
  mov 4 1
  andi 4 Txs.suprMask
  shri 4 2
  place done

end LeanOS.Wifi.Tx
