import LeanOS.Wifi.Bytes

/-!
# Minimal IPv4/UDP/DHCP client (RFC 791, RFC 768, RFC 2131, RFC 2132)

Builds broadcast DHCPDISCOVER/DHCPREQUEST packets (from 0.0.0.0:68 to
255.255.255.255:67, IPv4 header checksum filled, UDP checksum 0 = none) and
parses DHCPOFFER/DHCPACK/DHCPNAK. `Client` is a pure state machine:
`start` → DISCOVER; OFFER → REQUEST; ACK → bound with a `Lease`.

Packets here are IPv4 datagrams (the LLC/SNAP payload for ethertype 0x0800).
IPv4 addresses are `UInt32` in network (big-endian) numeric order.
-/

namespace LeanOS.Wifi.Dhcp

open LeanOS.Wifi.Bytes

abbrev Ipv4 := UInt32

def ipBroadcast : Ipv4 := 0xffffffff

/-- Dotted-quad rendering. -/
def Ipv4.show (a : Ipv4) : String :=
  s!"{(a >>> 24).toNat}.{((a >>> 16) &&& 0xff).toNat}.{((a >>> 8) &&& 0xff).toNat}.{(a &&& 0xff).toNat}"

/-! ## IPv4 and UDP -/

/-- RFC 1071 Internet checksum. -/
def internetChecksum (b : ByteArray) : UInt16 := Id.run do
  let mut sum : UInt32 := 0
  for i in [0:(b.size + 1) / 2] do
    sum := sum + (getU16be b (2 * i)).toUInt32
  while sum >>> (16 : UInt32) != 0 do
    sum := (sum &&& (0xffff : UInt32)) + (sum >>> (16 : UInt32))
  return ~~~ sum.toUInt16

/-- An IPv4 datagram carrying UDP (no options, TTL 64, DF clear, UDP checksum 0). -/
def ipv4Udp (src dst : Ipv4) (srcPort dstPort ident : UInt16) (payload : ByteArray) : ByteArray :=
  let udpLen := 8 + payload.size
  let total := 20 + udpLen
  let hdr := concat [ByteArray.mk #[0x45, 0x00], u16be total.toUInt16, u16be ident,
    ByteArray.mk #[0x00, 0x00, 64, 17, 0, 0], u32be src, u32be dst]
  let hdr := overwrite hdr 10 (u16be (internetChecksum hdr))
  concat [hdr, u16be srcPort, u16be dstPort, u16be udpLen.toUInt16, u16be 0, payload]

structure UdpDatagram where
  src : Ipv4
  dst : Ipv4
  srcPort : UInt16
  dstPort : UInt16
  payload : ByteArray

/-- Parse an IPv4/UDP datagram, checking version, header checksum and lengths. -/
def parseIpv4Udp (p : ByteArray) : Option UdpDatagram := do
  if p.size < 20 || at! p 0 >>> 4 != 4 then none
  let ihl := 4 * (at! p 0 &&& 0x0f).toNat
  let total := (getU16be p 2).toNat
  if ihl < 20 || total < ihl + 8 || total > p.size then none
  if internetChecksum (take p ihl) != 0 then none
  if at! p 9 != 17 then none
  -- Fragments are not reassembled.
  if getU16be p 6 &&& 0x3fff != 0 then none
  let udpLen := (getU16be p (ihl + 4)).toNat
  if udpLen < 8 || ihl + udpLen > total then none
  return { src := getU32be p 12, dst := getU32be p 16, srcPort := getU16be p ihl,
           dstPort := getU16be p (ihl + 2), payload := slice p (ihl + 8) (udpLen - 8) }

/-! ## DHCP messages -/

namespace MsgType
def discover : UInt8 := 1
def offer : UInt8 := 2
def request : UInt8 := 3
def decline : UInt8 := 4
def ack : UInt8 := 5
def nak : UInt8 := 6
def release : UInt8 := 7
end MsgType

namespace Opt
def pad : UInt8 := 0
def subnetMask : UInt8 := 1
def router : UInt8 := 3
def dns : UInt8 := 6
def requestedIp : UInt8 := 50
def leaseTime : UInt8 := 51
def msgType : UInt8 := 53
def serverId : UInt8 := 54
def paramRequest : UInt8 := 55
def clientId : UInt8 := 61
def end_ : UInt8 := 255
end Opt

def magicCookie : ByteArray := ByteArray.mk #[0x63, 0x82, 0x53, 0x63]

def clientPort : UInt16 := 68
def serverPort : UInt16 := 67

def opt (code : UInt8) (body : ByteArray) : ByteArray :=
  ByteArray.mk #[code, body.size.toUInt8] ++ body

/-- BOOTREQUEST with the broadcast flag, padded to the 300-byte BOOTP minimum. -/
def bootRequest (mac : ByteArray) (xid : UInt32) (options : List ByteArray) : ByteArray :=
  let fixedPart := concat [ByteArray.mk #[1, 1, 6, 0], u32be xid, u16be 0, u16be 0x8000,
    zeros 16, take (mac ++ zeros 16) 16, zeros 64, zeros 128, magicCookie]
  let msg := fixedPart ++ concat options ++ ByteArray.mk #[Opt.end_]
  msg ++ zeros (300 - msg.size)

private def commonOptions (mac : ByteArray) (type : UInt8) : List ByteArray :=
  [opt Opt.msgType (ByteArray.mk #[type]), opt Opt.clientId (ByteArray.mk #[1] ++ take mac 6)]

private def paramList : ByteArray :=
  opt Opt.paramRequest (ByteArray.mk #[Opt.subnetMask, Opt.router, Opt.dns, Opt.leaseTime,
    Opt.serverId])

/-- DHCPDISCOVER as an IPv4 datagram. -/
def discover (mac : ByteArray) (xid : UInt32) : ByteArray :=
  ipv4Udp 0 ipBroadcast clientPort serverPort 0
    (bootRequest mac xid (commonOptions mac MsgType.discover ++ [paramList]))

/-- DHCPREQUEST (SELECTING state) as an IPv4 datagram. -/
def request (mac : ByteArray) (xid : UInt32) (requested serverId : Ipv4) : ByteArray :=
  ipv4Udp 0 ipBroadcast clientPort serverPort 0
    (bootRequest mac xid (commonOptions mac MsgType.request ++
      [opt Opt.requestedIp (u32be requested), opt Opt.serverId (u32be serverId), paramList]))

structure Message where
  op : UInt8
  xid : UInt32
  yiaddr : Ipv4
  siaddr : Ipv4
  chaddr : ByteArray
  options : List (UInt8 × ByteArray)

/-- Parse the options field (after the magic cookie). Stops at END. -/
def parseOptions (b : ByteArray) : Option (List (UInt8 × ByteArray)) :=
  let rec go (fuel : Nat) (off : Nat) (acc : List (UInt8 × ByteArray)) :
      Option (List (UInt8 × ByteArray)) :=
    match fuel with
    | 0 => some acc.reverse
    | fuel + 1 =>
      if off ≥ b.size then some acc.reverse
      else
        let code := at! b off
        if code == Opt.end_ then some acc.reverse
        else if code == Opt.pad then go fuel (off + 1) acc
        else if off + 2 > b.size then none
        else
          let len := (at! b (off + 1)).toNat
          if off + 2 + len > b.size then none
          else go fuel (off + 2 + len) ((code, slice b (off + 2) len) :: acc)
  go b.size 0 []

/-- Parse a BOOTP/DHCP payload. -/
def parseMessage (b : ByteArray) : Option Message := do
  if b.size < 240 then none
  if !beq (slice b 236 4) magicCookie then none
  let options ← parseOptions (drop b 240)
  return { op := at! b 0, xid := getU32be b 4, yiaddr := getU32be b 16, siaddr := getU32be b 20,
           chaddr := slice b 28 16, options }

def Message.opt? (m : Message) (code : UInt8) : Option ByteArray :=
  (m.options.find? (·.1 == code)).map (·.2)

def Message.type? (m : Message) : Option UInt8 :=
  (m.opt? Opt.msgType).bind fun b => if b.size == 1 then some (at! b 0) else none

private def addr? (b : ByteArray) : Option Ipv4 :=
  if b.size ≥ 4 then some (getU32be b 0) else none

def Message.addrOpt? (m : Message) (code : UInt8) : Option Ipv4 :=
  (m.opt? code).bind addr?

/-- The network configuration obtained from an ACK. -/
structure Lease where
  address : Ipv4
  serverId : Ipv4
  subnetMask : Option Ipv4
  router : Option Ipv4
  dns : List Ipv4
  leaseSeconds : Option UInt32

def Message.lease? (m : Message) : Option Lease := do
  let serverId ← m.addrOpt? Opt.serverId
  let dns := match m.opt? Opt.dns with
    | some b => (List.range (b.size / 4)).map fun i => getU32be b (4 * i)
    | none => []
  return { address := m.yiaddr, serverId, subnetMask := m.addrOpt? Opt.subnetMask,
           router := m.addrOpt? Opt.router, dns, leaseSeconds := m.addrOpt? Opt.leaseTime }

/-- Parse an IPv4 datagram as a DHCP reply addressed to the client port. -/
def parseReply (packet : ByteArray) : Option Message := do
  let u ← parseIpv4Udp packet
  if u.dstPort != clientPort || u.srcPort != serverPort then none
  let m ← parseMessage u.payload
  if m.op != 2 then none
  return m

/-! ## Client state machine -/

inductive State where
  | selecting (xid : UInt32)
  | requesting (xid : UInt32) (offered : Lease)
  | bound (lease : Lease)

structure Client where
  mac : ByteArray
  state : State

/-- Begin: returns the client and the DISCOVER to broadcast. -/
def Client.start (mac : ByteArray) (xid : UInt32) : Client × ByteArray :=
  ({ mac, state := .selecting xid }, discover mac xid)

/-- Handle a received IPv4 datagram; returns the new client and an optional
datagram to transmit. Unrelated packets are ignored. -/
def Client.handle (c : Client) (packet : ByteArray) : Client × Option ByteArray :=
  match parseReply packet with
  | none => (c, none)
  | some m =>
    let forUs := beq (take m.chaddr 6) (take c.mac 6)
    match c.state with
    | .selecting xid =>
      if m.xid != xid || !forUs || m.type? != some MsgType.offer then (c, none) else
      match m.lease? with
      | none => (c, none)
      | some offer =>
        ({ c with state := .requesting xid offer },
         some (request c.mac xid offer.address offer.serverId))
    | .requesting xid offered =>
      if m.xid != xid || !forUs then (c, none)
      else if m.type? == some MsgType.nak then
        let xid' := xid + 1
        ({ c with state := .selecting xid' }, some (discover c.mac xid'))
      else if m.type? != some MsgType.ack then (c, none)
      else match m.lease? with
        | some lease =>
          if lease.serverId == offered.serverId then ({ c with state := .bound lease }, none)
          else (c, none)
        | none => (c, none)
    | .bound _ => (c, none)

def Client.lease? (c : Client) : Option Lease :=
  match c.state with
  | .bound l => some l
  | _ => none

end LeanOS.Wifi.Dhcp
