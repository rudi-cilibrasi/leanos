import LeanOS.Net.FrameSource
import LeanOS.Wifi.Dhcp

/-!
# A deterministic frame source for the DHCP subject (issue #556)

The q35 `dhcp-subject` image exercises the DHCP subject and the echo subject
end to end without WiFi hardware. Its driver program is this frame source:
like `LeanOS.Net.FrameSource.program` it drives no device (target identity
`0xffffffff`, policy `q35FrameSourcePolicy`) and fills the frame endpoint's
layout (`rxAt`, `txAt`, `txLenAt`) from a fixed list of records. The issue
#556 endpoint carries three kinds of record:

* the 6-byte **link record**, our hardware address, first;
* 1-byte **ticks**, which the BCM43224 endpoint yields after a second
  without a frame (`LeanOS.Wifi.Endpoint.serveLink`);
* Ethernet II frames.

The driver gives no IPv4 address: the DHCP subject leases one, and hands it
to the echo subject over IPC. For every record the program checks the reply
the kernel left in `txAt`, byte for byte, against a reference computed here
(or checks that there is none):

* while the DHCP subject holds the endpoint, the reference client
  `LeanOS.Wifi.Dhcp.Client` in an Ethernet header (`dhcpRecords`);
* once the lease is handed on, the reference responder
  `LeanOS.Net.Echo.replyFrame` for the leased address (`leased`).

The records walk every transition of the client: a DISCOVER, an OFFER for
another transaction (ignored), an OFFER, a REQUEST, a NAK, a DISCOVER with
the next transaction id, two silent ticks and a retransmission on the third,
an OFFER for another hardware address (ignored), an OFFER, a REQUEST, an ACK
from another server (ignored), and the ACK. Then ARP, ICMP echo and UDP echo
for the leased address draw replies, while the same requests for the address
of the NAKed offer, and a tick, draw none.
-/
namespace LeanOS.Net.DhcpSource

open LeanOS.Wifi.Bytecode LeanOS.Net.FrameSource

/-! ## The fixture -/

/-- The DHCP server: the frame source's peer, 52:54:00:12:34:56 at
10.0.2.2. -/
def serverMac : UInt64 := peerMac
def serverIp : UInt32 := peerIp
/-- Another server, whose ACK the client must ignore. -/
def otherServerIp : UInt32 := 0x0a000203
/-- The address of the first offer, which the server then NAKs: the address
the issue #450 fixture answered for. -/
def nakedIp : UInt32 := ip
/-- The leased address, 10.0.2.16. -/
def leased : UInt32 := 0x0a000210
/-- The router and subnet mask the server offers. -/
def router : UInt32 := 0x0a000202
def subnet : UInt32 := 0xffffff00

def u32 (v : UInt32) : List UInt8 := ipBytes v

/-- A BOOTREPLY of message type `type` for transaction `xid` and hardware
address `chaddr`, offering `yiaddr` from server `sid`, padded to 300 bytes,
from the server's port 67 to the broadcast address's port 68. -/
def reply (type : UInt8) (xid yiaddr sid : UInt32) (chaddr : UInt64) : List UInt8 :=
  let opts : List UInt8 := [53, 1, type] ++ [54, 4] ++ u32 sid ++
    (if type == LeanOS.Wifi.Dhcp.MsgType.nak then []
     else [51, 4, 0, 0, 0x0e, 0x10] ++ [1, 4] ++ u32 subnet ++ [3, 4] ++ u32 router) ++ [255]
  let fixed : List UInt8 := [2, 1, 6, 0] ++ u32 xid ++ [0, 0, 0x80, 0] ++
    List.replicate 4 0 ++ u32 yiaddr ++ u32 sid ++ List.replicate 4 0 ++ macBytes chaddr ++
    List.replicate 10 0 ++ List.replicate 192 0 ++ [0x63, 0x82, 0x53, 0x63]
  let bootp := fixed ++ opts
  udpDatagram Echo.broadcast serverMac serverIp 0xffffffff 67 68
    (bootp ++ List.replicate (300 - bootp.length) 0)

/-! ## The reference client -/

/-- Our hardware address as `Wifi.Dhcp` takes it. -/
def macArray : ByteArray := ⟨(macBytes mac).toArray⟩

/-- A request datagram in the Ethernet header the subject sends it in. -/
def toEthernet (datagram : ByteArray) : ByteArray :=
  ⟨(macBytes Echo.broadcast ++ macBytes mac ++ be16 0x0800).toArray⟩ ++ datagram

/-- The first transaction id (`DhcpClient.xidOf`). -/
def xid0 : UInt32 := mac.toUInt32 ^^^ 0x4c454f53
def xid1 : UInt32 := xid0 + 1

def arr (l : List UInt8) : ByteArray := ⟨l.toArray⟩

/-! ## The records -/

/-- A tick record. -/
def tick : ByteArray := arr [0]

/-- The link record. -/
def link : ByteArray := arr (macBytes mac)

/-- The records the DHCP subject receives, with the expected frame it
transmits, from `Wifi.Dhcp`. -/
def dhcpRecords : List (ByteArray × Option ByteArray) := [
  (link, some (toEthernet (LeanOS.Wifi.Dhcp.discover macArray xid0))),
  (arr (reply LeanOS.Wifi.Dhcp.MsgType.offer (xid0 + 7) nakedIp serverIp mac), none),
  (arr (reply LeanOS.Wifi.Dhcp.MsgType.offer xid0 nakedIp serverIp mac),
    some (toEthernet (LeanOS.Wifi.Dhcp.request macArray xid0 nakedIp serverIp))),
  (arr (reply LeanOS.Wifi.Dhcp.MsgType.nak xid0 0 serverIp mac),
    some (toEthernet (LeanOS.Wifi.Dhcp.discover macArray xid1))),
  (tick, none),
  (tick, none),
  (tick, some (toEthernet (LeanOS.Wifi.Dhcp.discover macArray xid1))),
  (arr (reply LeanOS.Wifi.Dhcp.MsgType.offer xid1 leased serverIp 0x02004c454141), none),
  (arr (reply LeanOS.Wifi.Dhcp.MsgType.offer xid1 leased serverIp mac),
    some (toEthernet (LeanOS.Wifi.Dhcp.request macArray xid1 leased serverIp))),
  (arr (reply LeanOS.Wifi.Dhcp.MsgType.ack xid1 leased otherServerIp mac), none),
  (arr (reply LeanOS.Wifi.Dhcp.MsgType.ack xid1 leased serverIp mac), none)]

/-- The records the echo subject receives after the lease. -/
def echoFrames : List ByteArray := List.map arr [
  arpRequest peerMac peerIp leased,
  icmpEcho mac peerMac peerIp leased 0x4c45 3 (ascii "leased by the dhcp subject"),
  udpDatagram mac peerMac peerIp leased 40002 7 (ascii "echo for the lease"),
  arpRequest peerMac peerIp nakedIp,
  icmpEcho mac peerMac peerIp nakedIp 0x4c45 4 (ascii "not leased")] ++ [tick]

def echoRecords : List (ByteArray × Option ByteArray) :=
  echoFrames.map fun f => (f, if f.size < 14 then none else Echo.replyFrame f mac leased)

/-- Every record, in order, with its expected reply. -/
def records : List (ByteArray × Option ByteArray) := dhcpRecords ++ echoRecords

/-- Records before the lease hand-off: the DHCP subject's. -/
def dhcpRecordCount : Nat := dhcpRecords.length

/-! ## The program -/

/-- The frame source: every record with its expected reply, then halt. -/
def programOf (t : Target) : ProgM Unit := do
  setTarget t
  li 0 0
  emit (.memStore 4 0 txLenAt (.imm 0))
  for (k, f, r) in (List.range records.length).zip records do
    li 0 0
    storeAt rxAt f
    exchange k f.size.toUInt32 r
  halt

/-- The q35 frame source of the `dhcp-subject` image (`net-q35-dhcp`). -/
def program : ProgM Unit := programOf FrameSource.target

/-- The same records for the Qotom's BCM43224 (`net-bcm-dhcp`): a keyless
smoke test of the DHCP and echo subjects on the lab machine that touches no
device register. -/
def bcmProgram : ProgM Unit := programOf bcm43224Target

end LeanOS.Net.DhcpSource
