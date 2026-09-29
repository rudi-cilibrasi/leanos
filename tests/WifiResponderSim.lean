import LeanOS.Wifi.Responder
import LeanOS.Wifi.Sim

/-! Simulator test for the IPv4 responder (`LeanOS/Wifi/Responder.lean`).

The station's keys, BSSID and leased address are placed in scratch directly
(the handshake and DHCP have their own simulator tests). An access-point
model feeds CCMP-protected downlink frames through the receive FIFO, advances
the TSF so the responder's window ends, strips the d11 transmit header from
each transmitted frame and decrypts it with the TK. The test requires:

* a UDP datagram to port 7 is echoed with addresses and ports swapped, the
  payload unchanged, and both the IPv4 and the UDP checksum still valid;
* a UDP datagram to another port is ignored;
* an ICMP echo request is still answered;
* group-key rotation: a group-key message 1 (TK-protected, GTK KDE wrapped
  with the KEK, MIC with the KCK) is answered with a valid message 2 echoing
  its replay counter; a broadcast ARP request protected with the *new* GTK
  is then answered; a replayed message 1 and one with a bad MIC are dropped.

usage: leanos-wifi-respsim -/

open LeanOS.Wifi LeanOS.Wifi.Bytecode LeanOS.Wifi.Bytes

def bssid : ByteArray := ByteArray.mk #[0x02, 0x11, 0x22, 0x33, 0x44, 0x55]
def sta : ByteArray := ByteArray.mk Mlme.ourMac.data
def peerMac : ByteArray := ByteArray.mk #[0x1c, 0x69, 0x7a, 0xa8, 0x9b, 0x1e]
def tk : ByteArray := ByteArray.mk ((List.range 16).map (fun i => (0x10 + i).toUInt8)).toArray
def gtk : ByteArray := ByteArray.mk ((List.range 16).map (fun i => (0xa0 + i).toUInt8)).toArray
def gtk2 : ByteArray := ByteArray.mk ((List.range 16).map (fun i => (0xc0 + i).toUInt8)).toArray
def kck : ByteArray := ByteArray.mk ((List.range 16).map (fun i => (0x40 + i).toUInt8)).toArray
def kek : ByteArray := ByteArray.mk ((List.range 16).map (fun i => (0x60 + i).toUInt8)).toArray
/-- Replay counter of the 4-way handshake's message 3 (seeded in scratch). -/
def lastReplay : UInt64 := 2
def ourIp : UInt32 := 0xc0a8061e       -- 192.168.6.30
def peerIp : UInt32 := 0xc0a8063e      -- 192.168.6.62


/-- Ones'-complement sum folded to 16 bits (RFC 1071). -/
def onesSum (b : ByteArray) : Nat := Id.run do
  let mut s := 0
  for i in [0:(b.size + 1) / 2] do
    s := s + (b.get! (2 * i)).toNat * 256 + (if 2 * i + 1 < b.size then (b.get! (2 * i + 1)).toNat else 0)
  while s > 0xFFFF do s := (s &&& 0xFFFF) + (s >>> 16)
  return s

def checksum (b : ByteArray) : UInt16 := (0xFFFF - onesSum b).toUInt16

def getU16 (b : ByteArray) (i : Nat) : Nat := (b.get! i).toNat * 256 + (b.get! (i + 1)).toNat
def getU32 (b : ByteArray) (i : Nat) : UInt32 :=
  ((b.get! i).toUInt32 <<< 24) ||| ((b.get! (i+1)).toUInt32 <<< 16) |||
    ((b.get! (i+2)).toUInt32 <<< 8) ||| (b.get! (i+3)).toUInt32

/-- An IPv4 datagram (protocol `proto`) with a valid header checksum. -/
def ipv4 (src dst : UInt32) (proto : UInt8) (payload : ByteArray) : ByteArray :=
  let hdr := u16be 0x4500 ++ u16be (20 + payload.size).toUInt16 ++ u16be 0x1234 ++
    ByteArray.mk #[0, 0, 64, proto, 0, 0] ++ u32be src ++ u32be dst
  let c := checksum hdr
  (hdr.extract 0 10 ++ u16be c ++ hdr.extract 12 20) ++ payload

/-- UDP with a valid checksum over the IPv4 pseudo-header. -/
def udp (src dst : UInt32) (sport dport : UInt16) (payload : ByteArray) : ByteArray :=
  let len := (8 + payload.size).toUInt16
  let body0 := u16be sport ++ u16be dport ++ u16be len ++ u16be 0 ++ payload
  let pseudo := u32be src ++ u32be dst ++ ByteArray.mk #[0, 17] ++ u16be len
  let c := checksum (pseudo ++ body0)
  let c := if c == 0 then 0xFFFF else c
  ipv4 src dst 17 (u16be sport ++ u16be dport ++ u16be len ++ u16be c ++ payload)

def icmpEcho (src dst : UInt32) : ByteArray :=
  let body0 := ByteArray.mk #[8, 0, 0, 0, 0x12, 0x34, 0, 1] ++ "ping".toUTF8
  let c := checksum body0
  ipv4 src dst 1 (body0.extract 0 2 ++ u16be c ++ body0.extract 4 body0.size)

structure Ap where
  rxq : List ByteArray := []
  cur : Option (ByteArray × Nat) := none
  txBuf : ByteArray := .empty
  txCtl : UInt32 := 0
  tsf : UInt32 := 0
  apPn : UInt64 := 0x100
  replies : Array ByteArray := #[]
  log : Array String := #[]
  deriving Inhabited

/-- Receive-FIFO framing used by the driver (as in `tests/WifiDhcpSim.lean`):
length, the rest of the d11 RX header, the MPDU and a 4-byte FCS. -/
def rxStream (mpdu : ByteArray) : ByteArray :=
  let len := 6 + mpdu.size + 4
  ByteArray.mk #[len.toUInt8, (len / 256).toUInt8] ++ zeros 22 ++ zeros 6 ++ mpdu ++ zeros 4

/-- A protected FromDS data frame to `da` from `sa` carrying `payload` with
`ethertype`, under `key` / `keyId`. -/
def downlinkWith (ap : Ap) (key : ByteArray) (keyId : UInt8) (da sa : ByteArray)
    (ethertype : UInt16) (payload : ByteArray) : ByteArray × Ap :=
  let pn := ap.apPn
  let hdr := ByteArray.mk #[0x08, 0x02] ++ zeros 2 ++ da ++ bssid ++ sa ++
    ByteArray.mk #[(pn * 16).toUInt8, ((pn * 16) >>> 8).toUInt8]
  let plain := hdr ++ Ieee80211.llcSnap ethertype ++ payload
  ((Ieee80211.ccmpEncap key pn keyId plain).getD .empty, { ap with apPn := pn + 1 })

def downlink (ap : Ap) (ip : ByteArray) : ByteArray × Ap :=
  downlinkWith ap tk 0 sta peerMac Ieee80211.ethertypeIPv4 ip

/-- Group-key message 1 carrying `newGtk` as key `keyId`. -/
def groupMsg1 (replay : UInt64) (keyId : UInt8) (newGtk : ByteArray) : ByteArray :=
  let wrapped := (Aes.keyWrap kek (Eapol.padKeyData (Eapol.gtkKde keyId newGtk))).getD .empty
  let f : Eapol.KeyFrame :=
    { protocolVersion := 2
      keyInfo := Eapol.KeyInfo.versionHmacSha1Aes ||| Eapol.KeyInfo.ack ||| Eapol.KeyInfo.mic |||
        Eapol.KeyInfo.secure ||| Eapol.KeyInfo.encryptedKeyData
      keyLength := 0, replayCounter := replay, nonce := zeros 32, keyData := wrapped }
  (f.sign kck).encode

def arpRequest : ByteArray :=
  ByteArray.mk #[0, 1, 8, 0, 6, 4, 0, 1] ++ peerMac ++ u32be peerIp ++ zeros 6 ++ u32be ourIp

def le32At (b : ByteArray) (i : Nat) : UInt32 :=
  (b.get! i).toUInt32 ||| ((b.get! (i+1)).toUInt32 <<< 8) ||| ((b.get! (i+2)).toUInt32 <<< 16) |||
    ((b.get! (i+3)).toUInt32 <<< 24)

def handleTx (ap : Ap) (frame : ByteArray) : Ap :=
  let mpdu := frame.extract 118 frame.size
  match Ieee80211.ccmpDecap tk mpdu with
  | none => { ap with log := ap.log.push "tx: CCMP failed" }
  | some p => { ap with replies := ap.replies.push p.mpdu }

def device : Sim.Device Ap where
  read32 ap off :=
    if off == 0x180 then (ap.tsf, { ap with tsf := ap.tsf + 50 })
    else if off == Mac.rxPioCtl then
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
      if v &&& Mac.txCtlEof != 0 then { handleTx ap ap.txBuf with txBuf := .empty } else ap
    else if off == Mac.txPioData 1 then
      let n := if ap.txCtl &&& 0xF == 0xF then 4 else if ap.txCtl &&& 0xF == 7 then 3
               else if ap.txCtl &&& 0xF == 3 then 2 else 1
      let bytes := ByteArray.mk #[v.toUInt8, (v >>> 8).toUInt8, (v >>> 16).toUInt8, (v >>> 24).toUInt8]
      { ap with txBuf := ap.txBuf ++ bytes.extract 0 n }
    else ap
  write16 ap _ _ := ap
  cfgRead32 ap _ := (0, ap)
  cfgWrite32 ap _ _ := ap

def prog : ProgM Unit := do
  let L ← DevCrypto.install
  let C ← DevCcmp.install L
  Responder.respond L C (Tx.TxConfig.ofPhy (NPhy.qotom 6) .ofdm6 Tx.txAcBeFifo) 200000
  halt

/-- Pre-seed scratch: keys, BSSID, our address (network order in memory). -/
def seed (m : Sim.Machine Ap) : Sim.Machine Ap := Id.run do
  let mut mem := m.mem
  for i in [0:16] do
    mem := mem.set! (Handshake.kckAt.toNat + i) (kck.get! i)
    mem := mem.set! (Handshake.kekAt.toNat + i) (kek.get! i)
    mem := mem.set! (Handshake.tkAt.toNat + i) (tk.get! i)
    mem := mem.set! (Handshake.gtkAt.toNat + i) (gtk.get! i)
  mem := mem.set! Handshake.gtkIdAt.toNat 1
  for i in [0:8] do
    mem := mem.set! (Handshake.replayAt.toNat + i) ((lastReplay >>> (8 * (7 - i)).toUInt64).toUInt8)
  for i in [0:6] do mem := mem.set! (Mlme.bssidAt.toNat + i) (bssid.get! i)
  let ip := u32be ourIp
  for i in [0:4] do mem := mem.set! (DevDhcp.yiaddrAt.toNat + i) (ip.get! i)
  return { m with mem }

def main : IO UInt32 := do
  match build prog with
  | .error e => IO.eprintln e; return 1
  | .ok p =>
    let payload := "lean over udp".toUTF8
    let ap : Ap := {}
    let (f1, ap) := downlink ap (udp peerIp ourIp 5555 7 payload)
    let (f2, ap) := downlink ap (udp peerIp ourIp 5555 9 payload)       -- not echo
    let (f3, ap) := downlink ap (icmpEcho peerIp ourIp)
    -- group-key rotation to key 2, then a replay and a forged copy
    let good := groupMsg1 5 2 gtk2
    let (g1, ap) := downlinkWith ap tk 0 sta bssid Ieee80211.ethertypeEapol good
    let (g2, ap) := downlinkWith ap tk 0 sta bssid Ieee80211.ethertypeEapol good
    let (g3, ap) := downlinkWith ap tk 0 sta bssid Ieee80211.ethertypeEapol
      (groupMsg1 6 1 gtk |>.set! 90 0)                            -- corrupted MIC
    let (a1, ap) := downlinkWith ap gtk2 2 Ieee80211.broadcastMac peerMac
      0x0806 arpRequest
    let ap := { ap with rxq := [rxStream f1, rxStream f2, rxStream f3, rxStream g1, rxStream g2,
      rxStream g3, rxStream a1] }
    let (st, m) := Sim.run p device ap 200000000 (init := seed)
    for l in m.dev.log do IO.println l
    let mut failures := 0
    let check (name : String) (ok : Bool) : IO Unit := IO.println s!"{if ok then "PASS" else "FAIL"} {name}"
    let replies := m.dev.replies
    let ok0 := st == .halt
    check s!"responder halts ({repr st})" ok0; if !ok0 then failures := failures + 1
    let ok1 := replies.size == 4
    check s!"four replies (udp echo, icmp, group msg 2, arp) — got {replies.size}" ok1
    if !ok1 then failures := failures + 1
    -- body after the 24-byte header and 8-byte LLC/SNAP
    let ips := replies.map fun r => r.extract 32 r.size
    let udpReply := ips.find? fun ip => ip.size > 28 && ip.get! 9 == 17
    let ok2 := match udpReply with
      | none => false
      | some ip =>
        let len := getU16 ip 2
        let seg := ip.extract 20 len
        let pseudo := ip.extract 12 20 ++ ByteArray.mk #[0, 17] ++ u16be (len - 20).toUInt16
        getU32 ip 12 == ourIp && getU32 ip 16 == peerIp &&
          getU16 seg 0 == 7 && getU16 seg 2 == 5555 &&
          (seg.extract 8 seg.size).data == payload.data &&
          onesSum (ip.extract 0 20) == 0xFFFF && onesSum (pseudo ++ seg) == 0xFFFF
    check "UDP echo: swapped addresses and ports, same payload, both checksums valid" ok2
    if !ok2 then failures := failures + 1
    let ok3 := ips.any fun ip => ip.size > 20 && ip.get! 9 == 1 && ip.get! 20 == 0
    check "ICMP echo reply still sent" ok3; if !ok3 then failures := failures + 1
    -- group-key message 2
    let eapols := replies.filter fun r => r.size > 32 && r.get! 30 == 0x88 && r.get! 31 == 0x8E
    let ok5 := match eapols.toList with
      | [r] =>
        let e := r.extract 32 r.size
        match Eapol.parseKeyFrame e with
        | some f => f.keyInfo == (Eapol.KeyInfo.versionHmacSha1Aes ||| Eapol.KeyInfo.mic |||
              Eapol.KeyInfo.secure) && f.replayCounter == 5 && f.keyData.size == 0 &&
            Eapol.micValid kck e
        | none => false
      | _ => false
    check "group-key message 2: MIC | secure, replay counter echoed, MIC valid (one answer only)" ok5
    if !ok5 then failures := failures + 1
    let arps := replies.filter fun r => r.size > 32 && r.get! 30 == 0x08 && r.get! 31 == 0x06
    let ok6 := arps.size == 1
    check "broadcast ARP under the new GTK (key 2) answered" ok6; if !ok6 then failures := failures + 1
    let dropped := (m.prints.filter (·.1 == Responder.Tag.rekeyDropped)).size
    let ok7 := dropped == 2
    check s!"replayed and bad-MIC group messages dropped ({dropped})" ok7
    if !ok7 then failures := failures + 1
    let summary := m.prints.filter (·.1 == Responder.Tag.summaryUdp)
    let ok4 := summary.toList.map (·.2) == [1]
    check "UDP summary counts one echo" ok4; if !ok4 then failures := failures + 1
    IO.println s!"{failures} failure(s)"
    return if failures == 0 then 0 else 1
