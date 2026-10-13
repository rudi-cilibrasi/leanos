import LeanOS.Net.Echo

/-!
# The ring-3 DHCP subject's client logic (issue #556)

The DHCP client of RFC 2131 for one Ethernet interface: DISCOVER, OFFER,
REQUEST, ACK and NAK, with retransmission. Until issue #556 the client ran
inside the BCM43224 driver's device program (`LeanOS.Wifi.DevDhcp`), so the
driver chose the address the network subject answered for. Here it is written
once, generic in a small hook interface, and has two readings, as
`LeanOS.Net.Echo` does:

* **Generated C.** With `τ := UInt64` the hooks are the `@[extern]` C
  primitives `dhcp_gen_value`, `dhcp_gen_rd8`, `dhcp_gen_wr8`, `dhcp_gen_ld`
  and `dhcp_gen_st` (`LeanOS.Net.DhcpClientC`), and `leanos_dhcp_step` is the
  compiled `step`: allocation-free `uint32_t`/`uint64_t` code whose only loops
  are the bounded zero fill, the IPv4 header checksum and the option scan, and
  which makes no Lean runtime call. The DHCP subject (`subjects/dhcp/`) links
  it and supplies the hooks over its own frame buffer and its own registers.
* **Model.** With `τ := Buf` the hooks read and write a `ByteArray` and an
  array of registers. The hosted vectors (`tests/NetDhcpVectors.lean`) check
  this reading against the reference client `LeanOS.Wifi.Dhcp.Client`, and
  the generated C against this reading.

The packets are exactly `LeanOS.Wifi.Dhcp`'s: `discover` and `request`
inside an Ethernet II header (broadcast destination, our hardware address,
ethertype 0x0800), and replies parsed with `Wifi.Dhcp.parseReply`'s checks
(IPv4 version, header length, header checksum, no fragment, UDP from port 67
to port 68, BOOTREPLY, the magic cookie, well-formed options).

## Inputs

`step t len` handles the buffer's first `len` bytes, one record of the frame
endpoint (`LeanOS.Net.FrameSource`'s layout, issue #556 variant):

* `len = 6`: the **link record**, the interface's hardware address. In
  phase `init` it starts the client: transaction id `xidOf mac`, phase
  `selecting`, and a DISCOVER.
* `len = 1`: a **tick**, which the driver yields when no frame arrived for a
  second. Every third tick without an answer retransmits: DISCOVER while
  selecting, REQUEST while requesting; the third unanswered REQUEST restarts
  from DISCOVER with the next transaction id (RFC 2131 4.4.1, 3.1).
* `len ≥ 14`: an Ethernet II frame, handled as `Wifi.Dhcp.Client.handle`
  handles the IPv4 datagram it carries: an OFFER for our transaction and
  hardware address with a server identifier → REQUEST; then an ACK from the
  same server → `bound` with the lease, or a NAK → DISCOVER with the next
  transaction id. Everything else is ignored.

The result value is the length of the frame `step` left in the buffer to
transmit (342 bytes), or 0 for none.

## Registers

The client's state lives in registers the subject keeps (`reg*`); the subject
reads `regPhase` and `regLease` to hand the lease on. Registers 8 and 9 are
scratch for the option scan.

Every buffer offset `step` reads lies below `len`: each read is behind a
check that the field lies inside the IPv4 total length, the UDP length or
the options, so the C reading over a 1536-byte buffer and the model over a
`len`-byte array agree.
-/
namespace LeanOS.Net.DhcpClient

-- The generated C runs in a ring-3 subject with no module initializer: keep
-- constants inline in the code.
set_option compiler.extract_closed false

open LeanOS.Net.Echo (byte word rd16 rd32 rd48 wr16 wr32 wrMac drop)

/-- The hooks `step` is written against: the frame buffer of `Echo.Hooks`,
and the client's registers. -/
class Hooks (τ : Type) extends LeanOS.Net.Echo.Hooks τ where
  /-- Read register `k` (the value is `val` of the result). -/
  ld : τ → UInt32 → τ
  /-- Write `v` to register `k`. -/
  st : τ → UInt32 → UInt64 → τ

open LeanOS.Net.Echo.Hooks
open Hooks

variable {τ : Type} [Hooks τ]

/-! ## Registers and phases -/

def regPhase : UInt32 := 0
def regXid : UInt32 := 1
def regMac : UInt32 := 2
def regOffered : UInt32 := 3
def regServer : UInt32 := 4
def regLease : UInt32 := 5
def regTicks : UInt32 := 6
def regTries : UInt32 := 7
/-- Option scan scratch: the first message-type option, the first server
identifier. -/
def regType : UInt32 := 8
def regSid : UInt32 := 9
/-- Registers the subject provides. -/
def registers : Nat := 10

def phaseInit : UInt64 := 0
def phaseSelecting : UInt64 := 1
def phaseRequesting : UInt64 := 2
def phaseBound : UInt64 := 3

/-- Bytes of a DISCOVER or REQUEST frame: Ethernet 14, IPv4 20, UDP 8, and
the 300-byte BOOTP minimum. -/
def frameBytes : UInt32 := 342
/-- Ticks without an answer before a retransmission. -/
def ticksPerRetransmit : UInt64 := 3
/-- REQUEST transmissions before the client restarts from DISCOVER. -/
def requestTries : UInt64 := 3

/-- The transaction id of the first DISCOVER: derived from the hardware
address (lab grade, like the driver's SNonce; RFC 2131 asks for a random
value). -/
@[inline] def xidOf (mac : UInt64) : UInt64 := (mac.toUInt32 ^^^ 0x4c454f53).toUInt64

/-! ## Bounded loops -/

theorem succ_toNat_lt {i n : UInt32} (h : i < n) :
    (n.toNat - (i + 1).toNat) < n.toNat - i.toNat := by
  have hi : i.toNat < n.toNat := h
  have := n.toNat_lt
  have : (i + 1).toNat = i.toNat + 1 := by
    rw [UInt32.toNat_add]; simp only [UInt32.toNat_one]; omega
  omega

/-- Zero buffer bytes `[i, n)`. -/
@[specialize] def zeroFrom (t : τ) (i n : UInt32) : τ :=
  if h : i < n then zeroFrom (wr t i 0) (i + 1) n else t
termination_by n.toNat - i.toNat
decreasing_by exact succ_toNat_lt h

/-- Add the big-endian 16-bit words `k .. n - 1` at `base + 2 k` to `acc`. -/
@[specialize] def sumFrom (t : τ) (base k n : UInt32) (acc : UInt32) : τ :=
  if _h : k < n then
    let t := rd16 t (base + 2 * k)
    sumFrom t base (k + 1) n (acc + word t)
  else withVal t acc.toUInt64
termination_by n.toNat - k.toNat
decreasing_by exact succ_toNat_lt _h

/-- Ones'-complement fold of a sum of at most 2^16 words. -/
@[inline] def fold (s : UInt32) : UInt32 :=
  let s := (s &&& (0xffff : UInt32)) + (s >>> (16 : UInt32))
  let s := (s &&& (0xffff : UInt32)) + (s >>> (16 : UInt32))
  (s &&& (0xffff : UInt32)) + (s >>> (16 : UInt32))

/-- Record the first occurrence of option `code` (53 or 54) whose body of
`len` bytes starts at `at_`: register `regType` gets `0x100 ||| type` for a
one-byte message type and `0x200` otherwise; register `regSid` gets
`2^32 ||| id` for a server identifier of at least four bytes and `2^33`
otherwise. A later occurrence changes nothing (`List.find?`). -/
@[inline] def noteOption (t : τ) (code at_ len : UInt32) : τ :=
  if code == 53 then
    let t := ld t regType
    if val t != 0 then t
    else if len == 1 then
      let t := rd t at_
      st t regType (0x100 ||| (byte t).toUInt64)
    else st t regType 0x200
  else if code == 54 then
    let t := ld t regSid
    if val t != 0 then t
    else if len ≥ 4 then
      let t := rd32 t at_
      st t regSid ((1 : UInt64) <<< 32 ||| (word t).toUInt64)
    else st t regSid ((2 : UInt64) <<< 32)
  else t

/-- `Wifi.Dhcp.parseOptions` over the options at buffer offset `base`,
`size` bytes, from option offset `off`; `k` counts iterations (each consumes
at least one byte, so `size` iterations reach the end). Delivers 1 when the
options are well formed up to END or their end, 0 when an option overruns. -/
@[specialize] def scanFrom (t : τ) (base size off k : UInt32) : τ :=
  if _h : k < size then
    if off ≥ size then withVal t 1 else
    let t := rd t (base + off)
    let code := byte t
    if code == 255 then withVal t 1
    else if code == 0 then scanFrom t base size (off + 1) (k + 1)
    else if off + 2 > size then withVal t 0
    else
      let t := rd t (base + off + 1)
      let len := byte t
      if off + 2 + len > size then withVal t 0
      else
        let t := noteOption t code (base + off + 2) len
        scanFrom t base size (off + 2 + len) (k + 1)
  else withVal t 1
termination_by size.toNat - k.toNat
decreasing_by all_goals exact succ_toNat_lt _h

/-! ## Building DISCOVER and REQUEST -/

/-- The IPv4 header checksum of both requests: total length 328,
identification 0, TTL 64, UDP, from 0.0.0.0 to 255.255.255.255. -/
def requestIpChecksum : UInt32 := 0x79a6

/-- The part DISCOVER and REQUEST share, up to and including the client
identifier option; message type `type`. -/
@[specialize] def buildCommon (t : τ) (mac xid : UInt64) (type : UInt32) : τ :=
  let t := zeroFrom t 0 frameBytes
  -- Ethernet II: broadcast, from us, IPv4
  let t := wrMac t 0 Echo.broadcast
  let t := wrMac t 6 mac
  let t := wr16 t 12 0x0800
  -- IPv4: 0x45, total 328, TTL 64, UDP, checksum, 0.0.0.0 → 255.255.255.255
  let t := wr t 14 0x45
  let t := wr16 t 16 328
  let t := wr t 22 64
  let t := wr t 23 17
  let t := wr16 t 24 requestIpChecksum
  let t := wr32 t 30 0xffffffff
  -- UDP 68 → 67, length 308, no checksum
  let t := wr16 t 34 68
  let t := wr16 t 36 67
  let t := wr16 t 38 308
  -- BOOTREQUEST, Ethernet, 6-byte address, xid, broadcast flag, chaddr
  let t := wr t 42 1
  let t := wr t 43 1
  let t := wr t 44 6
  let t := wr32 t 46 xid.toUInt32
  let t := wr16 t 52 0x8000
  let t := wrMac t 70 mac
  -- magic cookie
  let t := wr32 t 278 0x63825363
  -- message type, client identifier (type 1, hardware address)
  let t := wr t 282 53
  let t := wr t 283 1
  let t := wr t 284 type
  let t := wr t 285 61
  let t := wr t 286 7
  let t := wr t 287 1
  wrMac t 288 mac

/-- The parameter request list (subnet mask, router, DNS, lease time, server
identifier) at `at_`, then END. -/
@[inline] def paramList (t : τ) (at_ : UInt32) : τ :=
  let t := wr t at_ 55
  let t := wr t (at_ + 1) 5
  let t := wr t (at_ + 2) 1
  let t := wr t (at_ + 3) 3
  let t := wr t (at_ + 4) 6
  let t := wr t (at_ + 5) 51
  let t := wr t (at_ + 6) 54
  wr t (at_ + 7) 255

/-- `Wifi.Dhcp.discover mac xid` in an Ethernet frame. -/
@[specialize] def buildDiscover (t : τ) (mac xid : UInt64) : τ :=
  let t := buildCommon t mac xid 1
  let t := paramList t 294
  withVal t frameBytes.toUInt64

/-- `Wifi.Dhcp.request mac xid requested server` in an Ethernet frame. -/
@[specialize] def buildRequest (t : τ) (mac xid requested server : UInt64) : τ :=
  let t := buildCommon t mac xid 3
  let t := wr t 294 50
  let t := wr t 295 4
  let t := wr32 t 296 requested.toUInt32
  let t := wr t 300 54
  let t := wr t 301 4
  let t := wr32 t 302 server.toUInt32
  let t := paramList t 306
  withVal t frameBytes.toUInt64

/-- Enter `selecting` with transaction `xid` and transmit a DISCOVER. -/
@[specialize] def discoverWith (t : τ) (xid : UInt64) : τ :=
  let t := st t regXid xid
  let t := st t regPhase phaseSelecting
  let t := st t regTicks 0
  let t := st t regTries 0
  let t := ld t regMac
  buildDiscover t (val t) xid

/-- Transmit the REQUEST for the registers' offer. -/
@[specialize] def requestAgain (t : τ) : τ :=
  let t := ld t regMac
  let mac := val t
  let t := ld t regXid
  let xid := val t
  let t := ld t regOffered
  let offered := val t
  let t := ld t regServer
  buildRequest t mac xid offered (val t)

/-! ## Parsing a reply -/

/-- `Wifi.Dhcp.parseReply` over the Ethernet II frame of `len` bytes: it
delivers the BOOTP payload's buffer offset (at least 42) when the frame
carries a well-formed BOOTREPLY from port 67 to port 68, and 0 otherwise.
The first message-type option and the first server identifier are left in
`regType` and `regSid` (`noteOption`). -/
@[specialize] def parseReply (t : τ) (len : UInt32) : τ :=
  if len < 14 + 20 then drop t else
  let t := rd16 t 12
  if word t != 0x0800 then drop t else
  let psize := len - 14
  let t := rd t 14
  let vihl := byte t
  if vihl >>> 4 != 4 then drop t else
  let ihl := 4 * (vihl &&& 0x0f)
  let t := rd16 t 16
  let total := word t
  if ihl < 20 || total < ihl + 8 || total > psize then drop t else
  let t := sumFrom t 14 0 (ihl / 2) 0
  if fold (word t) != 0xffff then drop t else
  let t := rd t 23
  if byte t != 17 then drop t else
  let t := rd16 t 20
  if word t &&& 0x3fff != 0 then drop t else
  let udp := 14 + ihl
  let t := rd16 t (udp + 4)
  let udpLen := word t
  if udpLen < 8 || ihl + udpLen > total then drop t else
  let t := rd16 t (udp + 2)
  let dport := word t
  let t := rd16 t udp
  if dport != 68 || word t != 67 then drop t else
  let b := udp + 8
  let bsize := udpLen - 8
  if bsize < 240 then drop t else
  let t := rd32 t (b + 236)
  if word t != 0x63825363 then drop t else
  let t := st t regType 0
  let t := st t regSid 0
  let t := scanFrom t (b + 240) (bsize - 240) 0 0
  if val t == 0 then drop t else
  let t := rd t b
  if byte t != 2 then drop t else withVal t b.toUInt64

/-- An OFFER, ACK or NAK in the frame of `len` bytes, in phase `phase`
(`Wifi.Dhcp.Client.handle`). -/
@[specialize] def onFrame (t : τ) (len : UInt32) (phase : UInt64) : τ :=
  let t := parseReply t len
  let b := word t
  if b == 0 then drop t else
  let t := rd32 t (b + 4)
  let mxid := (word t).toUInt64
  let t := rd32 t (b + 16)
  let yiaddr := (word t).toUInt64
  let t := rd48 t (b + 28)
  let chaddr := val t
  let t := ld t regMac
  let forUs := chaddr == val t
  let t := ld t regXid
  let xid := val t
  let t := ld t regType
  let type := val t
  let t := ld t regSid
  let sid := val t
  let hasSid := sid >>> 32 == 1
  let server := sid &&& 0xffffffff
  if mxid != xid || !forUs then drop t
  else if phase == phaseSelecting then
    if type != 0x102 || !hasSid then drop t else
    let t := st t regOffered yiaddr
    let t := st t regServer server
    let t := st t regPhase phaseRequesting
    let t := st t regTicks 0
    let t := st t regTries 0
    requestAgain t
  else if type == 0x106 then discoverWith t ((xid + 1) &&& 0xffffffff)
  else if type != 0x105 || !hasSid then drop t
  else
    let t := ld t regServer
    if server != val t then drop t else
    let t := st t regLease yiaddr
    let t := st t regPhase phaseBound
    drop t

/-! ## The client -/

/-- A tick in phase `phase`: count it, and retransmit on every third. -/
@[inline] def onTick (t : τ) (phase : UInt64) : τ :=
  if phase != phaseSelecting && phase != phaseRequesting then drop t else
  let t := ld t regTicks
  let ticks := val t + 1
  if ticks < ticksPerRetransmit then drop (st t regTicks ticks) else
  let t := st t regTicks 0
  if phase == phaseSelecting then
    let t := ld t regXid
    discoverWith t (val t)
  else
    let t := ld t regTries
    let tries := val t + 1
    if tries < requestTries then requestAgain (st t regTries tries)
    else
      let t := ld t regXid
      discoverWith t ((val t + 1) &&& 0xffffffff)

/-- The link record: our hardware address; starts the client. -/
@[inline] def onLink (t : τ) : τ :=
  let t := rd48 t 0
  let mac := val t
  let t := st t regMac mac
  discoverWith t (xidOf mac)

/-- One record of the frame endpoint (see the module documentation):
delivers the length of the frame to transmit, 0 for none. -/
@[specialize] def step (t : τ) (len : UInt32) : τ :=
  let t := ld t regPhase
  let phase := val t
  if len == 6 then (if phase == phaseInit then onLink t else drop t)
  else if len == 1 then onTick t phase
  else if len < 14 then drop t
  else if phase == phaseSelecting || phase == phaseRequesting then onFrame t len phase
  else drop t

/-! ## The model reading -/

/-- A frame buffer, the client's registers and the last delivered value. -/
structure Buf where
  data : ByteArray
  regs : Array UInt64
  v : UInt64 := 0

instance instHooksBuf : Hooks Buf where
  val b := b.v
  withVal b x := { b with v := x }
  rd b off := { b with v := (b.data.get! off.toNat).toUInt64 }
  wr b off x := { b with data := b.data.set! off.toNat x.toUInt8, v := 0 }
  ld b k := { b with v := b.regs.getD k.toNat 0 }
  st b k x := { b with regs := b.regs.set! k.toNat x, v := 0 }

/-- The frame buffer's size in the subject. -/
def bufferBytes : Nat := 1536

/-- The model client: from registers `regs`, handle the record `f`; the new
registers and the frame to transmit, if any. -/
def stepRecord (regs : Array UInt64) (f : ByteArray) : Array UInt64 × Option ByteArray :=
  let data := f ++ ByteArray.mk (Array.replicate (bufferBytes - f.size) 0)
  let b := step (τ := Buf) { data, regs } f.size.toUInt32
  (b.regs, if b.v == 0 then none else some (b.data.extract 0 b.v.toNat))

/-- The registers of a client that has not started. -/
def initialRegs : Array UInt64 := Array.replicate registers 0

end LeanOS.Net.DhcpClient
