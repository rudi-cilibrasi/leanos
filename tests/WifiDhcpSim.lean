import LeanOS.Wifi.Handshake
import LeanOS.Wifi.DevCcmp
import LeanOS.Wifi.DevDhcp
import LeanOS.Wifi.Sim
import LeanOS.Wifi.Pbkdf2

/-! End-to-end simulation: WPA2 4-way handshake, then DHCP over CCMP.

The device program runs `Handshake.fourWay`, then sends a CCMP-protected
DHCPDISCOVER (`DevDhcp` + `DevCcmp`), accepts the AP's group-key-protected
broadcast DHCPOFFER, sends a protected DHCPREQUEST and accepts the
pairwise-key-protected QoS DHCPACK, ending with the leased address in
scratch. The model access point (PIO receive/transmit FIFOs, as in
`tests/WifiHsSim.lean`) uses only the reference library (`Eapol`, `Aes`,
`Ieee80211.ccmpEncap`/`ccmpDecap`, `Dhcp`) for its side. -/

open LeanOS.Wifi LeanOS.Wifi.Bytecode LeanOS.Wifi.Bytes

def bssid : ByteArray := ByteArray.mk #[0x02, 0x11, 0x22, 0x33, 0x44, 0x55]
def sta : ByteArray := ByteArray.mk Mlme.ourMac.data
def pmk : ByteArray := Pbkdf2.pmkOfPassphrase "correct horse".toUTF8 "QUAIL".toUTF8
def anonce : ByteArray := ByteArray.mk ((List.range 32).map (fun i => (0x30 + i).toUInt8)).toArray
def gtk : ByteArray := ByteArray.mk ((List.range 16).map (fun i => (0xa0 + i).toUInt8)).toArray
def gtkId : UInt8 := 1
def rsnIe : ByteArray := Ieee80211.wpa2PskCcmpRsnIe

def offeredIp : UInt32 := 0xc0a80164
def serverIp : UInt32 := 0xc0a80101
def netmask : UInt32 := 0xffffff00
def leaseSecs : UInt32 := 3600

/-! ## Scratch used by this program (besides the libraries' regions) -/

/-- Plaintext frame under construction (0x4000–0x47FF). -/
def plainBuf : UInt32 := 0x4000
/-- Our transmit PN (6 bytes little-endian). -/
def txPnAt : UInt32 := 0x0C00
/-- Leased IPv4 address (4 bytes, network order). -/
def leasedIpAt : UInt32 := 0x0C08

/-! ## Model access point -/

def fromAp (eapol : ByteArray) : ByteArray :=
  ByteArray.mk #[0x08, 0x02, 0, 0] ++ sta ++ bssid ++ bssid ++ ByteArray.mk #[0x10, 0x00] ++
    Ieee80211.llcSnap Ieee80211.ethertypeEapol ++ eapol

def rxStream (mpdu : ByteArray) : ByteArray :=
  let len := 6 + mpdu.size + 4
  ByteArray.mk #[len.toUInt8, (len / 256).toUInt8] ++ zeros 22 ++ zeros 6 ++ mpdu ++ zeros 4

structure Ap where
  rxq : List ByteArray := []
  cur : Option (ByteArray × Nat) := none
  txCtl : UInt32 := 0
  txBuf : ByteArray := .empty
  log : Array String := #[]
  ptk : Option Eapol.Ptk := none
  hsDone : Bool := false
  apPn : UInt64 := 0x100
  staPn : Option UInt64 := none
  xid : Option UInt32 := none
  discoverOk : Bool := false
  requestOk : Bool := false
  deriving Inhabited

def msg1 : ByteArray :=
  ({ protocolVersion := 2, keyInfo := 0x008a, keyLength := 16, replayCounter := 1, nonce := anonce,
     keyData := .empty } : Eapol.KeyFrame).encode

def handleEapol (ap : Ap) (mpdu : ByteArray) : Ap := Id.run do
  let eapol := mpdu.extract 32 mpdu.size
  match Eapol.parseKeyFrame eapol with
  | none => return { ap with log := ap.log.push "tx: not EAPOL-Key" }
  | some f =>
    if f.keyInfo &&& Eapol.KeyInfo.secure == 0 then
      let ptk := Eapol.derivePtk pmk bssid sta anonce f.nonce
      let micOk := Eapol.micValid ptk.kck eapol
      let kd := Eapol.padKeyData (rsnIe ++ Eapol.gtkKde gtkId gtk)
      let wrapped := (Aes.keyWrap ptk.kek kd).getD .empty
      let m3 := (({ protocolVersion := 2, keyInfo := 0x13ca, keyLength := 16, replayCounter := 2,
                    nonce := anonce, keyData := wrapped } : Eapol.KeyFrame).sign ptk.kck).encode
      return { ap with ptk := some ptk, rxq := ap.rxq ++ [rxStream (fromAp m3)],
                       log := ap.log.push s!"msg2: mic={micOk}" }
    else
      match ap.ptk with
      | none => return { ap with log := ap.log.push "msg4 before msg2" }
      | some ptk =>
        let micOk := Eapol.micValid ptk.kck eapol
        return { ap with hsDone := micOk, log := ap.log.push s!"msg4: mic={micOk}" }

/-- A BOOTREPLY from our server. -/
def bootReply (xid : UInt32) (msgType : UInt8) : ByteArray :=
  concat [ByteArray.mk #[2, 1, 6, 0], u32be xid, zeros 4, zeros 4, u32be offeredIp,
    u32be serverIp, zeros 4, take (sta ++ zeros 16) 16, zeros 192, Dhcp.magicCookie,
    -- deliberately not in the usual order, with padding and extra options
    Dhcp.opt 51 (u32be leaseSecs), ByteArray.mk #[0, 0], Dhcp.opt 53 (ByteArray.mk #[msgType]),
    Dhcp.opt 6 (u32be 0x08080808), Dhcp.opt 1 (u32be netmask), Dhcp.opt 3 (u32be serverIp),
    Dhcp.opt 54 (u32be serverIp), ByteArray.mk #[255], zeros 20]

/-- Protected downlink data frame (FromDS) carrying an IPv4 datagram. -/
def downlink (ap : Ap) (key : ByteArray) (keyId : UInt8) (qos : Bool) (da : ByteArray)
    (ip : ByteArray) : ByteArray × Ap :=
  let pn := ap.apPn
  let fc : ByteArray := if qos then ByteArray.mk #[0x88, 0x02] else ByteArray.mk #[0x08, 0x02]
  let hdr := concat [fc, zeros 2, da, bssid, bssid, u16le (Ieee80211.seqCtl pn.toUInt16),
    if qos then ByteArray.mk #[0x05, 0x00] else .empty]
  let plain := hdr ++ Ieee80211.llcSnap Ieee80211.ethertypeIPv4 ++ ip
  ((Ieee80211.ccmpEncap key pn keyId plain).getD .empty, { ap with apPn := pn + 1 })

def handleData (ap : Ap) (mpdu : ByteArray) : Ap := Id.run do
  let some ptk := ap.ptk | return { ap with log := ap.log.push "data before keys" }
  match Ieee80211.ccmpDecap ptk.tk mpdu with
  | none => return { ap with log := ap.log.push "data: CCMP MIC failed" }
  | some p =>
    let pnOk := Ieee80211.pnAcceptable ap.staPn p.pn && p.keyId == 0
    let ap := { ap with staPn := some p.pn }
    let some d := Ieee80211.parseData p.mpdu | return { ap with log := ap.log.push "data: bad frame" }
    let addrOk := beq d.addr1 bssid && beq d.addr2 sta && beq d.addr3 Ieee80211.broadcastMac &&
      d.fc.has Ieee80211.Flags.toDS
    let some e := Ieee80211.toEth d | return { ap with log := ap.log.push "data: not LLC/SNAP" }
    let some u := Dhcp.parseIpv4Udp e.payload | return { ap with log := ap.log.push "data: not IPv4/UDP" }
    let some m := Dhcp.parseMessage u.payload | return { ap with log := ap.log.push "data: not DHCP" }
    let exact (want : ByteArray) := beq e.payload want
    match m.type? with
    | some 1 =>
      let ok := pnOk && addrOk && exact (Dhcp.discover sta m.xid)
      let (f, ap) := downlink ap gtk gtkId false Ieee80211.broadcastMac
        (Dhcp.ipv4Udp serverIp Dhcp.ipBroadcast 67 68 1 (bootReply m.xid Dhcp.MsgType.offer))
      return { ap with xid := some m.xid, discoverOk := ok, rxq := ap.rxq ++ [rxStream f],
                       log := ap.log.push s!"discover: pn={p.pn} pnOk={pnOk} addr={addrOk} exact={ok} xid={m.xid}" }
    | some 3 =>
      let ok := pnOk && addrOk && ap.xid == some m.xid &&
        exact (Dhcp.request sta m.xid offeredIp serverIp)
      let (f, ap) := downlink ap ptk.tk 0 true sta
        (Dhcp.ipv4Udp serverIp Dhcp.ipBroadcast 67 68 2 (bootReply m.xid Dhcp.MsgType.ack))
      return { ap with requestOk := ok, rxq := ap.rxq ++ [rxStream f],
                       log := ap.log.push s!"request: pn={p.pn} pnOk={pnOk} addr={addrOk} exact={ok}" }
    | t => return { ap with log := ap.log.push s!"data: DHCP type {t}" }

def handleTx (ap : Ap) (mpdu : ByteArray) : Ap :=
  if at! mpdu 1 &&& 0x40 != 0 then handleData ap mpdu else handleEapol ap mpdu

def le32At (b : ByteArray) (i : Nat) : UInt32 :=
  (b.get! i).toUInt32 ||| ((b.get! (i+1)).toUInt32 <<< 8) ||| ((b.get! (i+2)).toUInt32 <<< 16) |||
    ((b.get! (i+3)).toUInt32 <<< 24)

def device : Sim.Device Ap where
  read32 ap off :=
    if off == Mac.rxPioCtl then
      match ap.cur with
      | some _ => (3, ap)
      | none => (if ap.rxq.isEmpty then 0 else 1, ap)
    else if off == Mac.rxPioData then
      match ap.cur with
      | some (b, p) => (le32At (b ++ zeros 4) p, { ap with cur := some (b, p + 4) })
      | none => (0, ap)
    else (0, ap)
  read16 ap _ := (0, ap)
  write32 ap off v :=
    if off == Mac.rxPioCtl then
      if v == 1 then
        match ap.rxq with
        | b :: rest => { ap with cur := some (b, 0), rxq := rest }
        | [] => ap
      else if v == 2 then { ap with cur := none } else ap
    else if off == Mac.txPioCtl 1 then
      let ap := { ap with txCtl := v }
      if v &&& Mac.txCtlEof != 0 then
        let ap' := handleTx ap ap.txBuf
        { ap' with txBuf := .empty }
      else ap
    else if off == Mac.txPioData 1 then
      let n := if ap.txCtl &&& 0xF == 0xF then 4 else if ap.txCtl &&& 0xF == 7 then 3
               else if ap.txCtl &&& 0xF == 3 then 2 else 1
      let bytes := ByteArray.mk #[v.toUInt8, (v >>> 8).toUInt8, (v >>> 16).toUInt8, (v >>> 24).toUInt8]
      { ap with txBuf := ap.txBuf ++ bytes.extract 0 n }
    else ap
  write16 ap _ _ := ap
  cfgRead32 ap _ := (0, ap)
  cfgWrite32 ap _ _ := ap

/-! ## Device program -/

/-- Raw PIO transmit of the MPDU at `txMpdu` (generation-time length). -/
def send (n : Nat) : ProgM Unit := do
  li 11 Mlme.txMpdu
  li 12 n.toUInt32
  Mac.pioTx 1 11 12

namespace Fail
def noReply : UInt32 := 0x7E01
def nak : UInt32 := 0x7E02
def encap : UInt32 := 0x7E03
end Fail

namespace Tag
def discoverSent : UInt32 := 0x0E01
def offer : UInt32 := 0x0E02
def requestSent : UInt32 := 0x0E03
def ack : UInt32 := 0x0E04
def leasedIp : UInt32 := 0x0E05
def dropped : UInt32 := 0x0E06
end Tag

/-- Build the frame with `build` (a DevDhcp call leaving the length in r0)
at `plainBuf`, protect it with the TK into `txMpdu`, and transmit it. -/
def sendProtected (C : DevCcmp.CcmpLib) (build : ProgM Unit) : ProgM Unit := do
  build
  mov 2 0
  DevCcmp.callEncap C (.imm plainBuf) (.reg 2) (.imm Mlme.txMpdu) (.imm Handshake.tkAt)
    (.imm txPnAt) (.imm 0)
  let ok ← newLabel
  emit (.branch .ne 0 (.imm 0) ok)
  fail Fail.encap
  place ok
  li 11 Mlme.txMpdu
  mov 12 0
  Mac.pioTx 1 11 12

/-- Receive frames until a protected data frame from the BSSID decrypts
(TK or GTK) to a DHCP reply of our transaction; fail with `Fail.noReply`
after `frames` frames. Ends with r0 = the DHCP message type. -/
def waitDhcp (C : DevCcmp.CcmpLib) (D : DevDhcp.DhcpLib) (frames tries : UInt32) : ProgM Unit := do
  let top ← newLabel
  let skip ← newLabel
  let give ← newLabel
  let done ← newLabel
  li 0 0
  emit (.memStore 4 0 (leasedIpAt + 4) (.imm frames))
  place top
  li 0 0
  emit (.memLoad 4 6 0 (leasedIpAt + 4))
  emit (.branch .eq 6 (.imm 0) give)
  emit (.alu .sub 6 (.imm 1))
  emit (.memStore 4 0 (leasedIpAt + 4) (.reg 6))
  Mlme.rxFrame tries
  emit (.branch .ltu 5 (.imm (24 + 16 + 4)) skip)
  -- data frame, protected, from the BSSID
  li 0 0
  emit (.memLoad 1 1 0 Mlme.rxMpdu)
  andi 1 0x0C
  emit (.branch .ne 1 (.imm 0x08) skip)
  emit (.memLoad 1 1 0 (Mlme.rxMpdu + 1))
  andi 1 0x40
  emit (.branch .eq 1 (.imm 0) skip)
  Mlme.matchScratch (Mlme.rxMpdu + 10) Mlme.bssidAt 6 skip
  mov 2 5
  emit (.alu .sub 2 (.imm 4))                       -- strip FCS
  li 0 0
  emit (.memLoad 1 5 0 Handshake.gtkIdAt)
  DevCcmp.callDecap C (.imm Mlme.rxMpdu) (.reg 2) (.imm Handshake.tkAt) (.imm Handshake.gtkAt)
    (.reg 5)
  emit (.branch .eq 0 (.imm 0) skip)
  DevDhcp.callParse D (.reg 1) (.reg 2)
  emit (.branch .ne 0 (.imm 0) done)
  place skip
  printImm Tag.dropped 0
  emit (.jump top)
  place give
  fail Fail.noReply
  place done

def prog : ProgM Unit := do
  let L ← DevCrypto.install
  let C ← DevCcmp.install L
  let D ← DevDhcp.install
  Mlme.putBytes "bssid" Mlme.bssidAt bssid
  Handshake.fourWay L pmk rsnIe send 50
  -- Transaction id: 4 bytes of the second SHA-1 entropy digest that the
  -- SNonce does not use.
  Handshake.copyFrom 0 (Handshake.entropy2At + 12) DevDhcp.xidAt 4
  sendProtected C (DevDhcp.callDiscover D (.imm plainBuf))
  printImm Tag.discoverSent 0
  let gotOffer ← newLabel
  waitDhcp C D 20 50
  emit (.branch .eq 0 (.imm 2) gotOffer)
  fail Fail.noReply
  place gotOffer
  printImm Tag.offer 0
  sendProtected C (DevDhcp.callRequest D (.imm plainBuf))
  printImm Tag.requestSent 0
  let gotAck ← newLabel
  waitDhcp C D 20 50
  emit (.branch .eq 0 (.imm 5) gotAck)
  fail Fail.nak
  place gotAck
  printImm Tag.ack 0
  li 0 0
  emit (.memLoad 4 1 0 DevDhcp.yiaddrAt)
  emit (.memStore 4 0 leasedIpAt (.reg 1))
  print Tag.leasedIp 1
  halt

def main : IO UInt32 := do
  match build prog with
  | .error e => IO.eprintln e; return 1
  | .ok p =>
    let (st, m) := Sim.run p device { rxq := [rxStream (fromAp msg1)] }
    for l in m.dev.log do IO.println l
    for (t, v) in m.prints do IO.println s!"print {String.ofList (Nat.toDigits 16 t.toNat)} {v}"
    let slot (a : UInt32) := m.mem.extract a.toNat (a.toNat + 4)
    let leaseOk := beq (slot leasedIpAt) (u32be offeredIp) &&
      beq (slot DevDhcp.serverIdAt) (u32be serverIp) && beq (slot DevDhcp.routerAt) (u32be serverIp) &&
      beq (slot DevDhcp.subnetAt) (u32be netmask) && beq (slot DevDhcp.leaseAt) (u32be leaseSecs)
    let ok := st == .halt && m.dev.hsDone && m.dev.discoverOk && m.dev.requestOk && leaseOk
    IO.println s!"status {repr st} steps {m.steps} (~{m.steps * 20 / 1000000} ms at 20 ns/step) handshake {m.dev.hsDone} discover {m.dev.discoverOk} request {m.dev.requestOk} lease {leaseOk} ip {Dhcp.Ipv4.show (getU32be (slot leasedIpAt) 0)}"
    IO.println (if ok then "PASS dhcp over ccmp end to end" else "FAIL dhcp over ccmp end to end")
    return if ok then 0 else 1
