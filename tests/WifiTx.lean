import LeanOS.Wifi.Tx
import LeanOS.Wifi.Sim
import LeanOS.Wifi.Bytes

/-! Hosted checks for `LeanOS.Wifi.Tx` (no hardware).

* Generation-time `txHeader` against descriptor bytes worked out by hand
  from brcmsmac's `brcms_c_d11hdrs_mac80211` (see the comments by each
  expected value).
* The run-time `emitTxHeader`, executed by `LeanOS.Wifi.Sim`, produces the
  same 118 bytes (and the same frame Duration/ID) for several lengths,
  rates, unicast/multicast, beacon and PS-Poll frames.
* The transmit power model for the Qotom card on channel 6.
* `readTxStatus` against a small frmtxstatus FIFO model.
* The composed `txSetup` program builds. -/

open LeanOS.Wifi LeanOS.Wifi.Tx LeanOS.Wifi.Bytecode LeanOS.Wifi.NPhy
open LeanOS.Wifi.Bytes (ofHex toHex)

structure Ctx where
  failures : IO.Ref Nat

def check (ctx : Ctx) (name : String) (ok : Bool) (detail : String := "") : IO Unit := do
  if ok then
    IO.println s!"PASS {name}"
  else
    ctx.failures.modify (· + 1)
    IO.println s!"FAIL {name}{if detail.isEmpty then "" else ": " ++ detail}"

def checkBytes (ctx : Ctx) (name : String) (got want : ByteArray) : IO Unit :=
  check ctx name (Bytes.beq got want) s!"\n got  {toHex got}\n want {toHex want}"

/-- `n` zero bytes as hex. -/
def z (n : Nat) : String := String.join (List.replicate n "00")

/-- The brcmsmac reference vectors below were computed with brcmsmac's own
chain selection, so they use the Qotom SROM without the lab's transmit-chain
override (`PhyCfg.txChainOverride`); `qotom6Lab` checks the override. -/
def qotom6 : PhyCfg := { qotom 6 with txChainOverride := none }

/-- The configuration the lab programs actually use. -/
def qotom6Lab : PhyCfg := qotom 6
def bcast : ByteArray := ofHex "ffffffffffff"
def ap : ByteArray := ofHex "001122334455"

/-! ## Hand-computed descriptors -/

/-- Broadcast probe request, 1 Mb/s, 37-byte MPDU (phylen 41), seq 1, FIFO 3.
mcl = STARTMSDU (0x0008, no IMMEDACK: multicast RA); PhyTxControlWord =
FT_CCK | antenna 0xC0; PhyTxControlWord_1(/_Fbr) = BW20 (2); MainRates = PLCP
signal 0x0A; XtraFrameTypes = 6 << 8; FragPLCPFallback = 0a 04, usec 41*8 =
0x148, CRC field = phylen 0x29; FragDurFallback 0 (multicast);
TxFrameID = (0x0010 << 5) & 0x7FE0 | 3 = 0x0203; PLCP 0a 04 48 01 00 00. -/
def probeParams : TxParams :=
  { toTxConfig := TxConfig.ofPhy qotom6 .cck1 txAcVoFifo
    frameLen := 37, frameControl := 0x0040, ra := bcast, seqCtl := 0x0010 }
def probeWant : String :=
  "0800" ++ "0000" ++ "4000" ++ "0000" ++ "c000" ++ "0200" ++ "0200" ++ z 4 ++ "0a00" ++ "0006" ++
  z 16 ++ "ffffffffffff" ++ z 10 ++ "0a0448012900" ++ z 16 ++ "0302" ++ z 34 ++ "0a0448010000"

/-- Unicast authentication, 1 Mb/s, 30-byte MPDU (phylen 34), seq 2, FIFO 3.
mcl = STARTMSDU | IMMEDACK; usec = 272 = 0x110; FragDurFallback = SIFS 10 +
ACK at 1 Mb/s (192 + 112) = 314 = 0x013a; TxFrameID 0x0403. -/
def authParams : TxParams :=
  { toTxConfig := TxConfig.ofPhy qotom6 .cck1 txAcVoFifo
    frameLen := 30, frameControl := 0x00b0, ra := ap, seqCtl := 0x0020 }
def authWant : String :=
  "0900" ++ "0000" ++ "b000" ++ "0000" ++ "c000" ++ "0200" ++ "0200" ++ z 4 ++ "0a00" ++ "0006" ++
  z 16 ++ "001122334455" ++ z 10 ++ "0a0410012200" ++ "3a01" ++ z 14 ++ "0304" ++ z 34 ++
  "0a0410010000"

/-- Unicast data at 6 Mb/s OFDM on FIFO 1 (BE), 30-byte MPDU (phylen 34), seq
0x35. PhyTxControlWord = FT_OFDM | 0xC0 = 0xC1; PhyTxControlWord_1 = BW20 |
CDD << 3 = 0x0A; MainRates = rate nibble 0xB; XtraFrameTypes 0x0601; PLCP =
0xB | 34 << 5 = 0x44B; FragDurFallback = 10 + (16 + 4 + 4*6 + 6) = 60;
TxFrameID = (0x0350 << 5) & 0x7FE0 | 1 = 0x6A01. -/
def dataParams : TxParams :=
  { toTxConfig := TxConfig.ofPhy qotom6 .ofdm6 txAcBeFifo
    frameLen := 30, frameControl := 0x0008, ra := ap, seqCtl := 0x0350 }
def dataWant : String :=
  "0900" ++ "0000" ++ "0800" ++ "0000" ++ "c100" ++ "0a00" ++ "0a00" ++ z 4 ++ "0b00" ++ "0106" ++
  z 16 ++ "001122334455" ++ z 10 ++ "4b0400000000" ++ "3c00" ++ z 14 ++ "016a" ++ z 34 ++
  "4b0400000000"

def headerTests (ctx : Ctx) : IO Unit := do
  checkBytes ctx "txHeader probe request 1M broadcast" (txHeader probeParams) (ofHex probeWant)
  checkBytes ctx "txHeader auth 1M unicast" (txHeader authParams) (ofHex authWant)
  checkBytes ctx "txHeader data 6M unicast" (txHeader dataParams) (ofHex dataWant)
  check ctx "header size 118" ((txHeader probeParams).size == 118 && (ofHex probeWant).size == 118)
  check ctx "durationId probe = none" (durationId probeParams == none)
  check ctx "durationId auth = 314" (durationId authParams == some 314)
  check ctx "durationId data 6M = 60" (durationId dataParams == some 60)
  check ctx "frameDur 1M = 314, 6M = 60" (frameDur .cck1 == 314 && frameDur .ofdm6 == 60)

/-! ## Run-time header in the simulator -/

/-- A frame body: frame control, duration, addr1, addr2 = our MAC, addr3,
sequence control, then filler up to `len`. -/
def mkFrame (fc : UInt16) (dur : UInt16) (ra : ByteArray) (seq : UInt16) (len : Nat) : ByteArray :=
  Id.run do
    let mut b := ByteArray.mk (Array.replicate len 0)
    let put (b : ByteArray) (i : Nat) (v : UInt8) := if i < b.size then b.set! i v else b
    b := put b 0 fc.toUInt8
    b := put b 1 (fc >>> 8).toUInt8
    b := put b 2 dur.toUInt8
    b := put b 3 (dur >>> 8).toUInt8
    for i in [0:6] do b := put b (4 + i) (ra.get! i)
    let me := macAddr qotom6
    for i in [0:6] do b := put b (10 + i) (me.get! i)
    for i in [0:6] do b := put b (16 + i) (ra.get! i)
    b := put b 22 seq.toUInt8
    b := put b 23 (seq >>> 8).toUInt8
    for i in [24:len] do b := put b i (0xA0 + i % 16).toUInt8
    return b

def simBase : Nat := 0x200

/-- Run `emitTxHeader` over `frame` in scratch at `simBase + 118`; return the
118 descriptor bytes and the frame as left in memory. -/
def runEmit (c : TxConfig) (frame : ByteArray) : Except String (ByteArray × ByteArray) := do
  let prog ← build (do emitTxHeader c 5 6; halt)
  let init (m : Sim.Machine Unit) : Sim.Machine Unit := Id.run do
    let mut m := m.setReg 5 simBase.toUInt32
    m := m.setReg 6 frame.size.toUInt32
    let mut mem := m.mem
    -- garbage where the descriptor goes, to prove every byte is written
    for i in [0:118] do mem := mem.set! (simBase + i) 0x5A
    for i in [0:frame.size] do mem := mem.set! (simBase + 118 + i) (frame.get! i)
    return { m with mem }
  let (st, m) := Sim.run prog Sim.Device.none () (init := init)
  if st != .halt then throw s!"status {repr st}"
  if m.regs[5]! != simBase.toUInt32 || m.regs[6]! != frame.size.toUInt32 then
    throw "base/len registers clobbered"
  return (m.mem.extract simBase (simBase + 118), m.mem.extract (simBase + 118) (simBase + 118 + frame.size))

def emitCase (ctx : Ctx) (name : String) (c : TxConfig) (fc dur : UInt16) (ra : ByteArray)
    (seq : UInt16) (len : Nat) : IO Unit := do
  let frame := mkFrame fc dur ra seq len
  let p : TxParams := { toTxConfig := c, frameLen := len, frameControl := fc, ra, seqCtl := seq,
                        durationIn := dur }
  let want := txHeader p
  let wantFrame := match durationId p with
    | some d => (frame.set! 2 d.toUInt8).set! 3 (d >>> 8).toUInt8
    | none => frame
  match runEmit c frame with
  | .error e => check ctx s!"emitTxHeader {name}" false e
  | .ok (got, gotFrame) =>
    checkBytes ctx s!"emitTxHeader = txHeader {name}" got want
    checkBytes ctx s!"emitTxHeader frame duration {name}" gotFrame wantFrame

def emitTests (ctx : Ctx) : IO Unit := do
  let cck := TxConfig.ofPhy qotom6 .cck1 txAcVoFifo
  let ofdm := TxConfig.ofPhy qotom6 .ofdm6 txAcBeFifo
  for len in [24, 37, 30, 99, 256, 1500] do
    emitCase ctx s!"probe 1M bcast len {len}" cck 0x0040 0 bcast 0x0010 len
    emitCase ctx s!"auth 1M ucast len {len}" cck 0x00b0 0 ap 0x0a30 len
    emitCase ctx s!"data 6M ucast len {len}" ofdm 0x0108 0 ap 0xfff0 len
    emitCase ctx s!"data 6M mcast len {len}" ofdm 0x0208 0 (ofHex "01005e000001") 0x1230 len
  emitCase ctx "beacon 1M" cck 0x0080 0 bcast 0x0040 60
  emitCase ctx "ps-poll 1M" cck 0x00a4 0xc005 ap 0 16
  emitCase ctx "eapol-key 1M not-first" { cck with first := false } 0x0108 0 ap 0x0070 121
  -- the hand-computed vectors through the simulator as well
  emitCase ctx "probe (hand vector)" cck 0x0040 0 bcast 0x0010 37
  match runEmit cck (mkFrame 0x0040 0 bcast 0x0010 37) with
  | .ok (got, _) => checkBytes ctx "emitTxHeader probe = hand vector" got (ofHex probeWant)
  | .error e => check ctx "emitTxHeader probe = hand vector" false e
  -- register misuse is rejected at generation time (program is a fail)
  match build (emitTxHeader cck 1 6) with
  | .ok p => check ctx "emitTxHeader rejects r1 base" (p.words.size == 1 && p.words[0]!.op == 1)
  | .error e => check ctx "emitTxHeader rejects r1 base" false e

/-! ## Power model -/

def powerTests (ctx : Ctx) : IO Unit := do
  let s := Power.Srom.ofCfg qotom6
  -- SROM: maxp2ga 0x4c (19 dBm) on both cores, cck2gpo 0, ofdm2gpo 0x44444444,
  -- mcs2gpo 0x4444 x8, cdd/stbc 0, bw40po 0x22, antenna gain byte 2.
  check ctx "srom fields" (s.maxPwr2g == #[76, 76] && s.cck2gpo == 0 && s.ofdm2gpo == 0x44444444 &&
    s.mcs2gpo == Array.replicate 8 0x4444 && s.cddpo == 0 && s.stbcpo == 0 && s.bw40po == 0x22 &&
    s.antGain0 == 2) s!"{s.maxPwr2g} {s.cck2gpo} {s.ofdm2gpo} {s.mcs2gpo} {s.bw40po} {s.antGain0}"
  let srom := Power.sromMaxRate2g s 6
  -- CCK 76; OFDM/20 MHz MCS 76 - 2*4 = 68; 40 MHz: 68 - 2*2 = 64.
  let wantSrom := Array.replicate 4 76 ++ Array.replicate 48 68 ++ Array.replicate 49 64
  check ctx "tx_srom_max_rate_2g" (srom == wantSrom) s!"{srom}"
  let lim := Power.regLimitCalc (Power.regLimits 6 (Power.antGainQdb 2))
  -- maxpwr = 76 - 8 = 68 (CCK); OFDM SISO min(68, MCS SISO 64) = 64; CDD 52;
  -- locale_bn SISO/SDM 64; STBC = CDD 52; MCS32 min(64, 52) = 52.
  let wantLim := Array.replicate 4 68 ++ Array.replicate 8 64 ++ Array.replicate 8 52 ++
    Array.replicate 8 64 ++ Array.replicate 8 52 ++ Array.replicate 8 52 ++ Array.replicate 8 64 ++
    Array.replicate 8 64 ++ Array.replicate 8 52 ++ Array.replicate 8 64 ++ Array.replicate 8 52 ++
    Array.replicate 8 52 ++ Array.replicate 8 64 ++ #[52]
  check ctx "txpwr_limit ch6" (lim == wantLim) s!"{lim}"
  let t := Power.targets qotom6
  -- per rate: min(srom, limit) - 6: CCK 62, OFDM 58, CDD 46, ...; max 62.
  check ctx "tx_power_max = 62 qdBm" (t.max == 62 && t.maxRateInd == 0) s!"{t.max} {t.maxRateInd}"
  check ctx "targets CCK 62 / OFDM 58 / MCS20 SISO 58 / MCS20 CDD 46"
    (t.target[0]! == 62 && t.target[4]! == 58 && t.target[20]! == 58 && t.target[28]! == 46)
  let adj := Power.adjPwrTbl qotom6
  -- adj[0..3] = CCK offsets 0; adj[4 + 4k + i] = OFDM 4, CDD 16, STBC 16, SDM 4.
  let wantAdj : Array UInt32 := #[0, 0, 0, 0] ++
    (List.replicate 20 #[4, 16, 16, 4]).toArray.flatten
  check ctx "adj_pwr_tbl_nphy" (adj == wantAdj) s!"{adj}"
  check ctx "ss_opmode after up = CDD" (ssOpmodeUp qotom6 == stfCdd)
  check ctx "phy tx antenna bits 0xC0" (phyTxAnt qotom6 == 0x00C0 && antAvailBg qotom6 == 3 &&
    txChain qotom6 == 3)
  -- The lab override (`txChainOverride := some 2`) transmits on chain 1 only.
  check ctx "lab override: chain 1, antenna bits 0x80, not CDD"
    (txChain qotom6Lab == 2 && phyTxAnt qotom6Lab == 0x0080 && ssOpmodeUp qotom6Lab != stfCdd)
  check ctx "SROM MAC 10:0d:7f:c9:75:f1" (Bytes.beq (macAddr qotom6) (ofHex "100d7fc975f1"))
  check ctx "rate table basic map" (basicRateTable hwRates ==
    #[(2, 2), (4, 4), (11, 11), (12, 12), (18, 12), (22, 22), (24, 24), (36, 24), (48, 48),
      (72, 48), (96, 48), (108, 48)])

/-! ## TX status -/

/-- frmtxstatus FIFO model: 0x170 shows the head status (0 when empty),
reading 0x174 returns its second word and pops it. `dead` makes 0x170 read
all-ones. -/
structure TxsDev where
  q : List (UInt32 × UInt32) := []
  dead : Bool := false
  deriving Inhabited

def txsDevice : Sim.Device TxsDev where
  read32 s off :=
    if off == d11FrmTxStatus then
      (if s.dead then 0xFFFFFFFF else match s.q with | (a, _) :: _ => a | [] => 0, s)
    else if off == d11FrmTxStatus2 then
      match s.q with | (_, b) :: rest => (b, { s with q := rest }) | [] => (0, s)
    else (0, s)
  read16 s _ := (0, s)
  write32 s _ _ := s
  write16 s _ _ := s
  cfgRead32 s _ := (0, s)
  cfgWrite32 s _ _ := s

def runTxs (dev : TxsDev) (fid : UInt32) : Except String (Sim.Status × Sim.Machine TxsDev) := do
  let prog ← build (do li 8 fid; readTxStatus 8 50 10; halt)
  return Sim.run prog txsDevice dev

def txsTests (ctx : Ctx) : IO Unit := do
  let other := ((0x0201 : UInt32) <<< 16 ||| 0x1003, (5 : UInt32))
  let inter := ((0x0203 : UInt32) <<< 16 ||| 0x0041, (6 : UInt32))
  let ours := ((0x0203 : UInt32) <<< 16 ||| 0x2003, (0x00120007 : UInt32))
  match runTxs { q := [other, inter, ours] } 0x0203 with
  | .ok (.halt, m) =>
    check ctx "readTxStatus ACKed after 2 tries, skips other/intermediate"
      (m.regs[0]! == 1 && m.regs[1]! == 0x2003 && m.regs[2]! == 1 && m.regs[3]! == 2 &&
       m.regs[4]! == 0 && m.regs[5]! == 0x00120007 &&
       m.prints == #[(Tag.txsOther, other.1), (Tag.txsIntermediate, inter.1)])
      s!"{m.regs} {m.prints}"
  | _ => check ctx "readTxStatus acked" false
  -- no ACK, 7 attempts, suppressed for bad channel (4 << 2)
  match runTxs { q := [((0x0403 : UInt32) <<< 16 ||| 0x7011, 0)] } 0x0403 with
  | .ok (.halt, m) =>
    check ctx "readTxStatus no-ack/supr" (m.regs[0]! == 1 && m.regs[2]! == 0 && m.regs[3]! == 7 &&
      m.regs[4]! == 4) s!"{m.regs}"
  | _ => check ctx "readTxStatus no-ack/supr" false
  match runTxs {} 0x0403 with
  | .ok (.halt, m) => check ctx "readTxStatus timeout" (m.regs[0]! == 0) s!"{m.regs}"
  | _ => check ctx "readTxStatus timeout" false
  match runTxs { dead := true } 0x0403 with
  | .ok (.halt, m) => check ctx "readTxStatus dead chip" (m.regs[0]! == 2) s!"{m.regs}"
  | _ => check ctx "readTxStatus dead chip" false

/-! ## Programs build -/

def buildTests (ctx : Ctx) : IO Unit := do
  let mac := macAddr qotom6
  for (name, p) in [("txSetup", txSetup qotom6 mac (ByteArray.mk (Array.replicate 6 0))),
      ("txpowerRecalcTargetNphy", txpowerRecalcTargetNphy qotom6),
      ("emitTxHeader cck1", emitTxHeader (TxConfig.ofPhy qotom6 .cck1) 8 9),
      ("readTxStatus", readTxStatus 8 1000 10)] do
    match build p with
    | .ok prog =>
      let fails := prog.words.filter fun w => w.op &&& 0xFF == 1
      check ctx s!"build {name}" (fails.isEmpty) s!"{fails.size} fail instructions"
      IO.println s!"  {name}: {prog.words.size} instructions"
    | .error e => check ctx s!"build {name}" false e

def main : IO UInt32 := do
  let ctx : Ctx := { failures := ← IO.mkRef 0 }
  headerTests ctx
  emitTests ctx
  powerTests ctx
  txsTests ctx
  buildTests ctx
  let n ← ctx.failures.get
  IO.println s!"{n} failure(s)"
  return if n == 0 then 0 else 1
