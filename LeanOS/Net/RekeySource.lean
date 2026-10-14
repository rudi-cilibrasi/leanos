import LeanOS.Net.FrameSource
import LeanOS.Wifi.Endpoint
import LeanOS.GtkRekey

/-!
# A deterministic frame source that rotates the group key (issue #557)

The q35 `gtk-rekey` image exercises the driver's group-key rotation on the
frame-source path without WiFi hardware. Its driver program is this frame
source: like `LeanOS.Net.FrameSource.program` it drives no device (target
identity `0xffffffff`, policy `q35FrameSourcePolicy`) and fills the frame
endpoint's layout. Unlike that source it does not hand the endpoint
Ethernet frames it made up: it runs the BCM43224 driver's own receive path,
`LeanOS.Wifi.Endpoint.handleFrame`, on CCMP-protected 802.11 data frames,
and its own transmit path, `Endpoint.takeTx`, on the network subject's
replies. Only the radio is replaced: a received frame is stored where
`Mlme.rxFrame` would leave it, and a transmitted MPDU is compared, byte for
byte, with the one the reference library (`Wifi.Ieee80211.ccmpEncap`,
`Wifi.Eapol`) builds, instead of entering the transmit FIFO.

The frames are `LeanOS.GtkRekey.scenario` with concrete test keys (none is a
network secret): broadcast ARP under the first GTK (key id 1); a group
message 1 rotating to key id 2, answered with message 2; a broadcast under
the old key id, one at the new key's Key RSC and a replayed one, all
dropped; broadcast ARP under the new key, answered by the ring-3 echo
subject; a retransmitted and a forged message 1, dropped; a unicast ping;
a rotation back to key id 1, answered; broadcasts under the stale key
material and the retired key id, dropped; broadcast ARP under the newest
key, answered; and a message 1 for key id 0, which advances the replay
counter but installs nothing.

For every frame the program checks the outcome against the model
(`GtkRekey.step`): delivered to the endpoint or not, message 2 transmitted
or not, and afterwards the driver's whole key state (key id, GTK, replay
counter, both packet-number floors) equal to the model's. For every
delivered frame it checks the network subject's reply against the
reference responder `LeanOS.Net.Echo.replyFrame` and the protected MPDU the
driver then transmits against the reference. The scenario's outcomes are
`GtkRekey.scenario_outcomes`.
-/
namespace LeanOS.Net.RekeySource

open LeanOS.Wifi LeanOS.Wifi.Bytecode LeanOS.Net.FrameSource
open LeanOS.GtkRekey (State Frame Body Out GroupMsg1)

/-! ## Records and fail codes -/

namespace Tag
/-- The driver transmitted the reference MPDU; value: its length. -/
def transmitMatched : UInt32 := 0x5103
/-- Frame `i` reached no endpoint, as the model says; value: `i`. -/
def notDelivered : UInt32 := 0x5104
/-- After frame `i` the driver's key state is the model's; value: `i`. -/
def stateMatched : UInt32 := 0x5105
end Tag

/-- Fail codes; the frame index is added. -/
def failOutcome : UInt32 := 0x51300
def failState : UInt32 := 0x51400
def failTransmit : UInt32 := 0x51500
def failUnexpectedTransmit : UInt32 := 0x51600
def failReply : UInt32 := 0x51700

/-! ## Scratch beside the endpoint layout -/

/-- The MPDU the next transmission must equal, and its length (0: none). -/
def expTxAt : UInt32 := 0x3D000
def expTxLenAt : UInt32 := 0x3F010

/-! ## Keys and addresses (test values, not network secrets) -/

/-- The 16 bytes of abstract key `k`. -/
def keyBytes (k : GtkRekey.Key) : ByteArray :=
  ⟨((List.range 16).map fun i => (k * 16 + i * 7 + 3).toUInt8).toArray⟩

def kck : ByteArray := ⟨((List.range 16).map fun i => (0x40 + i).toUInt8).toArray⟩
def kek : ByteArray := ⟨((List.range 16).map fun i => (0x60 + i).toUInt8).toArray⟩
def bssid : ByteArray := ⟨#[0x02, 0x11, 0x22, 0x33, 0x44, 0x55]⟩
/-- Our hardware address: the driver's (`Mlme.ourMac`). -/
def hostMac : ByteArray := ByteArray.mk Mlme.ourMac.data

def macU64 (b : ByteArray) : UInt64 :=
  (List.range 6).foldl (fun acc i => (acc <<< 8) ||| b[i]!.toUInt64) 0

def bytes (l : List UInt8) : ByteArray := ⟨l.toArray⟩

/-- The host configuration record: our hardware address and 10.0.2.15. -/
def config : ByteArray := hostMac ++ bytes (ipBytes ip)

/-- An ARP request (28 bytes, as on the air) from the peer at `spa` for us. -/
def arpFrom (spa : UInt32) : ByteArray :=
  bytes (ethernet Echo.broadcast peerMac 0x0806
    ([0, 1, 8, 0, 6, 4, 0, 1] ++ macBytes peerMac ++ ipBytes spa ++ macBytes 0 ++ ipBytes ip))

/-- The Ethernet II frame each data payload of the scenario stands for. -/
def payloadFrame (p : Nat) : ByteArray :=
  if p = GtkRekey.ping then
    bytes (icmpEcho (macU64 hostMac) peerMac peerIp ip 0x4c45 7 (ascii "ping after rekey"))
  else arpFrom (peerIp + p.toUInt32)

/-- EAPOL-Key group message 1 for `m`, as the access point sends it. -/
def groupMsg1 (m : GroupMsg1) : ByteArray :=
  let kd := Eapol.padKeyData (Eapol.gtkKde m.keyId.toUInt8 (keyBytes m.gtk))
  let wrapped := (Aes.keyWrap kek kd).getD .empty
  let wrapped := if m.unwrapOk then wrapped else wrapped.set! 3 (wrapped[3]! ^^^ 0x5a)
  let f : Eapol.KeyFrame :=
    { protocolVersion := 2
      keyInfo := Eapol.KeyInfo.versionHmacSha1Aes ||| Eapol.KeyInfo.ack |||
        Eapol.KeyInfo.mic ||| Eapol.KeyInfo.secure ||| Eapol.KeyInfo.encryptedKeyData
      keyLength := 0, replayCounter := m.replay.toUInt64, nonce := Bytes.zeros 32,
      rsc := Bytes.u64le m.rsc.toUInt64, keyData := wrapped }
  let e := (f.sign kck).encode
  if m.micOk then e else e.set! 90 (e[90]! ^^^ 0x01)

/-- The Ethernet II view of a frame's body: what the endpoint yields for a
data frame (destination, source, ethertype, payload). -/
def frameEthernet (f : Frame) : ByteArray :=
  match f.body with
  | .data p => payloadFrame p
  | .groupMsg1 m => hostMac ++ bssid ++ bytes (be16 0x888E) ++ groupMsg1 m

/-- The protected FromDS MPDU carrying `f` (addr1 the destination, addr2 the
BSSID, addr3 the source). -/
def mpdu (f : Frame) : ByteArray :=
  let eth := frameEthernet f
  let seq := f.pn * 16
  let plain := bytes [0x08, 0x02, 0, 0] ++ eth.extract 0 6 ++ bssid ++ eth.extract 6 12 ++
    bytes [seq.toUInt8, (seq / 256).toUInt8] ++ bytes [0xAA, 0xAA, 0x03, 0, 0, 0] ++
    eth.extract 12 14 ++ eth.extract 14 eth.size
  (Ieee80211.ccmpEncap (keyBytes f.key) f.pn.toUInt64 f.keyId.toUInt8 plain).getD .empty

/-- The driver's `n`-th transmission (from 1): the ToDS frame to `dst` with
`ethertype` and `body`, protected with the TK under packet number `n`
(`Responder.replyHeader`, `Responder.sendReply`). -/
def transmitted (n : Nat) (dst : ByteArray) (ethertype : ByteArray) (body : ByteArray) :
    ByteArray :=
  let seq := (n % 4096) * 16
  let plain := bytes [0x08, 0x01, 0, 0] ++ bssid ++ hostMac ++ dst ++
    bytes [seq.toUInt8, (seq / 256).toUInt8] ++ bytes [0xAA, 0xAA, 0x03, 0, 0, 0] ++
    ethertype ++ body
  (Ieee80211.ccmpEncap (keyBytes GtkRekey.tk0) n.toUInt64 0 plain).getD .empty

/-- Group message 2 answering replay counter `r` (`Responder.respond.groupKey`). -/
def msg2 (r : Nat) : ByteArray :=
  let f : Eapol.KeyFrame :=
    { protocolVersion := 2
      keyInfo := Eapol.KeyInfo.versionHmacSha1Aes ||| Eapol.KeyInfo.mic ||| Eapol.KeyInfo.secure
      keyLength := 0, replayCounter := r.toUInt64, nonce := Bytes.zeros 32,
      keyData := .empty }
  (f.sign kck).encode

/-! ## The expected run -/

/-- What frame `i` must do. -/
structure Expect where
  mpdu : ByteArray
  out : Out
  /-- The model's key state after the frame. -/
  after : State
  /-- The MPDU the driver transmits while handling the frame (message 2). -/
  driverTx : Option ByteArray
  /-- For a delivered frame: its delivery index (the configuration record
  is 0), the Ethernet frame, the reference reply and the reply's MPDU. -/
  delivery : Option (Nat × ByteArray × Option ByteArray × Option ByteArray)

/-- Walk the scenario with the model, counting transmissions and
deliveries. -/
def expectations : List Expect := Id.run do
  let mut s := GtkRekey.start
  let mut sent := 0
  let mut delivered := 0
  let mut out : Array Expect := #[]
  for f in GtkRekey.scenario do
    let (s', o) := GtkRekey.step s f
    let mut driverTx := none
    let mut delivery := none
    match o with
    | .msg2 r =>
      sent := sent + 1
      driverTx := some (transmitted sent bssid (bytes (be16 0x888E)) (msg2 r))
    | .deliver _ =>
      delivered := delivered + 1
      let eth := frameEthernet f
      let reply := Echo.replyFrame eth (macU64 hostMac) ip
      let replyTx := reply.map fun r =>
        transmitted (sent + 1) (r.extract 0 6) (r.extract 12 14) (r.extract 14 r.size)
      if reply.isSome then sent := sent + 1
      delivery := some (delivered, eth, reply, replyTx)
    | .drop _ => pure ()
    out := out.push { mpdu := mpdu f, out := o, after := s', driverTx, delivery }
    s := s'
  return out.toList

/-! ## The program -/

def le48 (n : Nat) : ByteArray := (Bytes.u64le n.toUInt64).extract 0 6

/-- Expect the next transmission to be `b` (r0 must be 0). -/
def expectTx (b : Option ByteArray) : ProgM Unit := do
  match b with
  | some b =>
    storeAt expTxAt b
    emit (.memStore 4 0 expTxLenAt (.imm b.size.toUInt32))
  | none => emit (.memStore 4 0 expTxLenAt (.imm 0))

/-- The radio of this source: the `r(12)`-byte MPDU at `Mlme.txMpdu` must
be the expected one, which is then consumed. -/
def radio : Responder.Radio where
  send := do
    let unexpected ← newLabel
    let bad ← newLabel
    let loop ← newLabel
    let done ← newLabel
    li 0 0
    emit (.memLoad 4 1 0 expTxLenAt)
    emit (.branch .eq 1 (.imm 0) unexpected)
    emit (.branch .ne 1 (.reg 12) bad)
    li 2 Mlme.txMpdu
    li 3 expTxAt
    mov 4 12
    place loop
    emit (.branch .eq 4 (.imm 0) done)
    emit (.memLoad 1 6 2 0)
    emit (.memLoad 1 7 3 0)
    emit (.branch .ne 6 (.reg 7) bad)
    addi 2 1
    addi 3 1
    emit (.alu .sub 4 (.imm 1))
    emit (.jump loop)
    place unexpected
    fail failUnexpectedTransmit
    place bad
    fail failTransmit
    place done
    li 0 0
    emit (.memStore 4 0 expTxLenAt (.imm 0))
    print Tag.transmitMatched 12

/-- Jump to `bad` unless the driver's key state is `s` (r0 must be 0). -/
def checkState (s : State) (bad : Nat) : ProgM Unit := do
  checkAt Handshake.gtkIdAt ⟨#[s.gtkId.toUInt8]⟩ bad
  checkAt Handshake.gtkAt (keyBytes s.gtk) bad
  checkAt Handshake.tkAt (keyBytes s.tk) bad
  checkAt Handshake.replayAt (Bytes.u64be s.replay.toUInt64) bad
  checkAt Responder.lastPnTk (le48 s.pnTk) bad
  checkAt Responder.lastPnGtk (le48 s.pnGtk) bad

/-- The frame source over the expected run. -/
def programOf (t : Target) : ProgM Unit := do
  setTarget t
  li 0 0
  emit (.memStore 4 0 txLenAt (.imm 0))
  -- the driver's state after the 4-way handshake
  storeAt Handshake.kckAt kck
  storeAt Handshake.kekAt kek
  storeAt Handshake.tkAt (keyBytes GtkRekey.start.tk)
  storeAt Handshake.gtkAt (keyBytes GtkRekey.start.gtk)
  storeAt Handshake.gtkIdAt ⟨#[GtkRekey.start.gtkId.toUInt8, 0, 0, 0]⟩
  storeAt Handshake.replayAt (Bytes.u64be GtkRekey.start.replay.toUInt64)
  storeAt Mlme.bssidAt (bssid ++ bytes [0, 0])
  storeAt Responder.lastPnTk (Bytes.zeros 16)
  storeAt Connect.txPnAt (Bytes.zeros 8)
  storeAt Responder.seqAt (Bytes.zeros 4)
  storeAt Endpoint.rxCount (Bytes.zeros 8)
  emit (.memStore 4 0 expTxLenAt (.imm 0))
  let L ← DevCrypto.install
  let C ← DevCcmp.install L
  -- the driver's receive path and transmit path, as subroutines
  let handle ← newLabel
  let take ← newLabel
  let over ← newLabel
  emit (.jump over)
  place handle
  let yielded ← newLabel
  let skipped ← newLabel
  Endpoint.handleFrame L C radio yielded skipped
  place yielded
  li 14 1
  emit .ret
  place skipped
  li 14 0
  emit .ret
  place take
  Endpoint.takeTx C radio
  emit .ret
  place over
  -- the host configuration record
  li 0 0
  storeAt rxAt config
  exchange 0 configLen none
  for (i, e) in (List.range expectations.length).zip expectations do
    let badOutcome ← newLabel
    let badState ← newLabel
    let badReply ← newLabel
    let next ← newLabel
    li 0 0
    storeAt Mlme.rxMpdu e.mpdu
    expectTx e.driverTx
    li 5 (e.mpdu.size + 4).toUInt32
    emit (.call handle)
    match e.delivery with
    | some (k, _, reply, replyTx) =>
      emit (.branch .ne 14 (.imm 1) badOutcome)
      -- the network subject's reply, against the reference responder
      li 0 0
      emit (.memLoad 4 2 0 txLenAt)
      match reply with
      | some r =>
        emit (.branch .ne 2 (.imm r.size.toUInt32) badReply)
        checkAt txAt r badReply
      | none => emit (.branch .ne 2 (.imm 0) badReply)
      expectTx replyTx
      emit (.call take)
      li 0 0
      emit (.memLoad 4 1 0 expTxLenAt)
      emit (.branch .ne 1 (.imm 0) badOutcome)
      match reply with
      | some r => printImm FrameSource.Tag.replyMatched ((k.toUInt32 <<< 16) ||| r.size.toUInt32)
      | none => printImm FrameSource.Tag.noReplyMatched k.toUInt32
    | none =>
      emit (.branch .ne 14 (.imm 0) badOutcome)
      li 0 0
      emit (.memLoad 4 1 0 expTxLenAt)
      emit (.branch .ne 1 (.imm 0) badOutcome)
      printImm Tag.notDelivered i.toUInt32
    li 0 0
    checkState e.after badState
    printImm Tag.stateMatched i.toUInt32
    emit (.jump next)
    place badOutcome
    fail (failOutcome + i.toUInt32)
    place badState
    fail (failState + i.toUInt32)
    place badReply
    fail (failReply + i.toUInt32)
    place next
  halt

/-- The q35 frame source of the `gtk-rekey` image (`net-q35-rekey`). -/
def program : ProgM Unit := programOf FrameSource.target

/-- The same frames for the Qotom's BCM43224 (`net-bcm-rekey`): a keyless
smoke test of the rotation on the lab machine's network-subject path that
touches no device register. -/
def bcmProgram : ProgM Unit := programOf bcm43224Target

end LeanOS.Net.RekeySource
