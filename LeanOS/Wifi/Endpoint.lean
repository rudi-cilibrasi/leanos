import LeanOS.Wifi.Responder
import LeanOS.Net.FrameSource

/-!
# The BCM43224 driver as a frame endpoint (issue #450)

After association, the 4-way handshake and DHCP (`Connect.connectDhcpThen`;
the DHCP client stays in the driver program for now, see
`docs/wifi-driver.md`), the driver hands every received data frame to the
ring-3 network subject as an Ethernet II frame and transmits the subject's
replies. It answers nothing itself: the ARP, ICMP echo and UDP echo logic of
`LeanOS.Wifi.Responder.respond` is the network subject's
(`LeanOS.Net.Echo`). The driver keeps the keys: frames are CCMP-decapsulated
before they reach the endpoint and CCMP-protected after they leave it, and
no key ever enters the endpoint's scratch.

The endpoint layout is `LeanOS.Net.FrameSource`'s:

* first the host configuration record at `rxAt`: our hardware address and
  the leased IPv4 address, yielded as 10 bytes;
* then, per received protected data frame from the BSSID that decapsulates,
  passes the replay check and carries LLC/SNAP: Ethernet II at `rxAt`
  (destination = addr1, source = addr3, the SNAP ethertype, the payload),
  yielded as its length; frames that would exceed 1514 bytes are dropped;
* on every resumption, a reply the kernel left at `txAt` (length at
  `txLenAt`) is sent as a ToDS data frame (addr1 = BSSID, addr2 = us,
  addr3 = the reply's destination, LLC/SNAP with the reply's ethertype),
  CCMP-protected with the TK, and the length word is cleared.

EAPOL group-key messages stay with the driver (`Responder.respond.groupKey`).
The loop ends after `us` microseconds of TSF time; the program then halts and
the driver subject's next invocation returns 0.

## Group-key rotation (issue #557)

The per-frame work is `handleFrame`, apart from the radio: the serve loop
calls it on each MPDU the receive FIFO delivers and transmits through the
device (`Responder.Radio.device`), and the deviceless frame source of the
q35 `gtk-rekey` image (`LeanOS.Net.RekeySource`) calls the same code on
synthesized MPDUs and checks what it would transmit. A group message 1
installs the new GTK and its Key RSC and is answered with message 2; from
then on a group frame under the new key id is delivered (and recorded,
`Tag.groupFrame`), and a frame under the previous key id, stale key
material or an old packet number is dropped. `LeanOS.GtkRekey` models this
and `tests/WifiRekeySim.lean` checks `handleFrame` against the model.

## The link-only endpoint (issue #556)

`serveLink` is the same endpoint for a driver that runs no DHCP client
(`Connect.connectThen`): the driver keeps the PMK, the TK, the GTK and the
frame transport, and nothing else. Its first record is the 6-byte **link
record**, our hardware address, instead of the host configuration record:
the driver chooses no IPv4 address. The ring-3 DHCP subject leases one and
hands it to the echo subject over IPC (`LeanOS.DhcpSubject`). Because the
DHCP subject has no clock of its own, the endpoint also yields a 1-byte
**tick** whenever a second of TSF time has passed since the last one; the
DHCP subject retransmits on every third tick without an answer
(`LeanOS.Net.DhcpClient`).
-/
namespace LeanOS.Wifi.Endpoint

open LeanOS.Wifi.Bytecode LeanOS.Wifi.Bcm43224 LeanOS.Wifi.Connect LeanOS.Wifi.Responder
open LeanOS.Net.FrameSource (rxAt txAt txLenAt configLen)

/-! Scratch counters (beside the responder's 0x0C10–0x0C44). -/
def rxCount : UInt32 := 0x0C48
def txCount : UInt32 := 0x0C4C
/-- TSF time of the last tick (`serveLink`). -/
def lastTickAt : UInt32 := 0x0C50

/-- Bytes of the link record: our hardware address. -/
def linkLen : UInt32 := 6
/-- Bytes of a tick record. -/
def tickLen : UInt32 := 1
/-- TSF microseconds between ticks. -/
def tickUs : UInt32 := 1000000

namespace Tag
/-- The endpoint is up; value: the leased address. -/
def ready : UInt32 := 0x0F11
/-- A frame went to the network subject; value: its length. -/
def delivered : UInt32 := 0x0F12
/-- A reply was transmitted; value: its length. -/
def sent : UInt32 := 0x0F13
/-- A received frame or a reply exceeded the Ethernet bounds and was dropped. -/
def oversize : UInt32 := 0x0F14
def summaryRx : UInt32 := 0x0F15
def summaryTx : UInt32 := 0x0F16
/-- The link-only endpoint is up (issue #556); value: 0, no address. -/
def linkReady : UInt32 := 0x0F17
/-- A frame protected with the GTK decapsulated and passed the replay check
(issue #557); value: its key id. -/
def groupFrame : UInt32 := 0x0F18
end Tag

/-- Transmit the reply the kernel left at `txAt`, if any, through `radio`,
and clear its length word. -/
def takeTx (C : DevCcmp.CcmpLib) (radio : Radio) : ProgM Unit := do
  let none ← newLabel
  let bad ← newLabel
  li 0 0
  emit (.memLoad 4 3 0 txLenAt)
  emit (.branch .eq 3 (.imm 0) none)
  emit (.branch .ltu 3 (.imm 14) bad)
  emit (.branch .geu 3 (.imm 1515) bad)
  -- ToDS header with addr3 = the reply's destination, then LLC/SNAP with
  -- the reply's ethertype (replyHeader writes 0, overwritten here).
  copyFixed srcMacAt txAt 6
  replyHeader 0
  copyFixed (plainBuf + 30) (txAt + 12) 2
  -- payload
  li 0 0
  emit (.memLoad 4 3 0 txLenAt)
  emit (.alu .sub 3 (.imm 14))
  mov 12 3
  li 2 (plainBuf + 32)
  li 1 (txAt + 14)
  copyR 2 1 3
  addi 12 32
  sendReply C radio
  li 0 0
  emit (.memLoad 4 3 0 txLenAt)
  print Tag.sent 3
  emit (.memLoad 4 2 0 txCount); addi 2 1; emit (.memStore 4 0 txCount (.reg 2))
  emit (.jump none)
  place bad
  li 0 0
  emit (.memLoad 4 3 0 txLenAt)
  print Tag.oversize 3
  place none
  li 0 0
  emit (.memStore 4 0 txLenAt (.imm 0))

/-- One received MPDU, at `Mlme.rxMpdu` with its length (FCS included) in
r5: a protected data frame from the BSSID that decapsulates under the TK or
the installed GTK (key id at `Handshake.gtkIdAt`) and passes the replay
check is either an EAPOL group-key message, which the driver handles itself
(`Responder.respond.groupKey`: install the new GTK and answer with message 2
through `radio`), or is handed to the endpoint as Ethernet II at `rxAt` and
yielded as its length, after which control continues at `next`. Anything
else jumps to `skip` without a yield. -/
def handleFrame (L : DevCrypto.Lib) (C : DevCcmp.CcmpLib) (radio : Radio)
    (next skip : Nat) : ProgM Unit := do
  emit (.branch .ltu 5 (.imm (24 + 16 + 4)) skip)
  -- protected data from the BSSID
  li 0 0
  emit (.memLoad 1 1 0 Mlme.rxMpdu)
  andi 1 0x0C
  emit (.branch .ne 1 (.imm 0x08) skip)
  emit (.memLoad 1 1 0 (Mlme.rxMpdu + 1))
  andi 1 0x40
  emit (.branch .eq 1 (.imm 0) skip)
  Mlme.matchScratch (Mlme.rxMpdu + 10) Mlme.bssidAt 6 skip
  copyFixed srcMacAt (Mlme.rxMpdu + 16) 6
  mov 2 5
  emit (.alu .sub 2 (.imm 4))
  li 0 0
  emit (.memLoad 1 5 0 Handshake.gtkIdAt)
  DevCcmp.callDecap C (.imm Mlme.rxMpdu) (.reg 2) (.imm Handshake.tkAt) (.imm Handshake.gtkAt)
    (.reg 5)
  emit (.branch .eq 0 (.imm 0) skip)
  li 0 0
  emit (.memStore 4 0 bodyAt (.reg 1))
  emit (.memStore 4 0 lenAt (.reg 2))
  replayCheck skip
  -- a group-addressed frame: record the key id it was protected under
  let pairwise ← newLabel
  emit (.branch .eq 3 (.imm 0) pairwise)
  print Tag.groupFrame 3
  place pairwise
  li 0 0
  emit (.memLoad 4 1 0 bodyAt)
  -- LLC/SNAP
  emit (.memLoad 1 3 1 0); emit (.branch .ne 3 (.imm 0xAA) skip)
  emit (.memLoad 1 3 1 1); emit (.branch .ne 3 (.imm 0xAA) skip)
  emit (.memLoad 1 3 1 6)
  emit (.memLoad 1 4 1 7)
  shli 3 8
  emit (.alu .or 3 (.reg 4))
  let notEapol ← newLabel
  emit (.branch .ne 3 (.imm 0x888E) notEapol)
  respond.groupKey L C radio skip
  emit (.jump skip)
  place notEapol
  -- Ethernet II: 14 + (body length - 8) bytes, at most 1514
  li 0 0
  emit (.memLoad 4 3 0 lenAt)
  emit (.branch .ltu 3 (.imm 8) skip)
  emit (.alu .sub 3 (.imm 8))
  let fits ← newLabel
  emit (.branch .ltu 3 (.imm (1514 - 14 + 1)) fits)
  addi 3 14
  print Tag.oversize 3
  emit (.jump skip)
  place fits
  copyFixed rxAt (Mlme.rxMpdu + 4) 6
  copyFixed (rxAt + 6) (Mlme.rxMpdu + 16) 6
  li 0 0
  emit (.memLoad 4 1 0 bodyAt)
  emit (.memLoad 1 3 1 6); emit (.memStore 1 0 (rxAt + 12) (.reg 3))
  emit (.memLoad 1 3 1 7); emit (.memStore 1 0 (rxAt + 13) (.reg 3))
  addi 1 8
  li 0 0
  emit (.memLoad 4 3 0 lenAt)
  emit (.alu .sub 3 (.imm 8))
  mov 13 3
  li 2 (rxAt + 14)
  copyR 2 1 3
  addi 13 14
  print Tag.delivered 13
  li 0 0
  emit (.memLoad 4 2 0 rxCount); addi 2 1; emit (.memStore 4 0 rxCount (.reg 2))
  emit (.yield (.reg 13))
  emit (.jump next)

/-- Serve the frame endpoint for `us` microseconds: with `link` the
link-only endpoint of issue #556 (the link record, then frames and ticks),
otherwise the issue #450 endpoint (the host configuration record with the
driver's leased address, then frames). -/
def serveWith (link : Bool) (L : DevCrypto.Lib) (C : DevCcmp.CcmpLib)
    (data : LeanOS.Wifi.Tx.TxConfig) (us : UInt32) : ProgM Unit := do
  let radio := Radio.device data
  li 1 0
  r32 2 0x180
  emit (.memStore 4 1 startAt (.reg 2))
  emit (.memStore 4 1 rxCount (.imm 0))
  emit (.memStore 4 1 txCount (.imm 0))
  emit (.memStore 4 1 txLenAt (.imm 0))
  if link then
    -- link record: our hardware address only; the driver leases nothing
    emit (.memStore 4 1 lastTickAt (.reg 2))
    li 2 rxAt
    storeBytes 2 0 (ByteArray.mk Mlme.ourMac.data)
    printImm Tag.linkReady 0
    emit (.yield (.imm linkLen))
  else
    -- host configuration record: our hardware address and the leased address
    li 2 rxAt
    storeBytes 2 0 (ByteArray.mk Mlme.ourMac.data)
    copyFixed (rxAt + 6) DevDhcp.yiaddrAt 4
    li 1 0
    emit (.memLoad 4 2 1 DevDhcp.yiaddrAt)
    print Tag.ready 2
    emit (.yield (.imm configLen))
  let top ← newLabel
  let skip ← newLabel
  let out ← newLabel
  place top
  takeTx C radio
  r32 6 0x180
  li 1 0
  emit (.memLoad 4 7 1 startAt)
  emit (.alu .sub 6 (.reg 7))
  emit (.branch .geu 6 (.imm us) out)
  if link then
    -- a tick once a second of TSF time has passed since the last one
    let noTick ← newLabel
    r32 6 0x180
    mov 8 6
    li 1 0
    emit (.memLoad 4 7 1 lastTickAt)
    emit (.alu .sub 6 (.reg 7))
    emit (.branch .ltu 6 (.imm tickUs) noTick)
    emit (.memStore 4 1 lastTickAt (.reg 8))
    emit (.memStore 1 1 rxAt (.imm 0))
    emit (.yield (.imm tickLen))
    emit (.jump top)
    place noTick
  Mlme.rxFrame 100
  handleFrame L C radio top skip
  place skip
  emit (.jump top)
  place out
  li 1 0
  emit (.memLoad 4 2 1 rxCount); print Tag.summaryRx 2
  emit (.memLoad 4 2 1 txCount); print Tag.summaryTx 2

/-- Serve the issue #450 endpoint (host configuration record) for `us`
microseconds. -/
def serve (L : DevCrypto.Lib) (C : DevCcmp.CcmpLib) (data : LeanOS.Wifi.Tx.TxConfig)
    (us : UInt32) : ProgM Unit :=
  serveWith false L C data us

/-- Serve the link-only endpoint of issue #556 for `us` microseconds. -/
def serveLink (L : DevCrypto.Lib) (C : DevCcmp.CcmpLib) (data : LeanOS.Wifi.Tx.TxConfig)
    (us : UInt32) : ProgM Unit :=
  serveWith true L C data us

/-- Connect, lease an address with the driver's own DHCP client, then serve
the frame endpoint for `us` microseconds (issue #450; the compatibility path
of `LEANOS_WIFI_DRIVER_DHCP`). The image embeds the PMK: never commit it. -/
def connectAndServe (fw : Bcm43224.Firmware) (cfg : LeanOS.Wifi.NPhy.PhyCfg)
    (bssid pmk : ByteArray) (us : UInt32) : ProgM Unit :=
  Connect.connectDhcpThen fw cfg bssid pmk fun L C data => serve L C data us

/-- Connect without a DHCP client, then serve the link-only endpoint for
`us` microseconds (issue #556): the ring-3 DHCP subject leases the address.
The image embeds the PMK: never commit it. -/
def connectAndServeLink (fw : Bcm43224.Firmware) (cfg : LeanOS.Wifi.NPhy.PhyCfg)
    (bssid pmk : ByteArray) (us : UInt32) : ProgM Unit :=
  Connect.connectThen fw cfg bssid pmk fun L C data => serveLink L C data us

end LeanOS.Wifi.Endpoint
