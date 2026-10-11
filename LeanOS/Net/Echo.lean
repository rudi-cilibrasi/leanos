/-!
# The ring-3 network subject's protocol logic (issue #450)

ARP reply (RFC 826), ICMP echo reply (RFC 792) and UDP echo on port 7
(RFC 862) for one IPv4 host, over Ethernet II frames. Until issue #450 this
logic lived inside the ring-0 BCM43224 device program
(`LeanOS.Wifi.Responder`); here it is written once, generic in a small hook
interface, and has two readings, as `LeanOS.Wifi.Exec.step` does:

* **Generated C.** With `τ := UInt64` the hooks are the `@[extern]` C
  primitives `net_gen_value`, `net_gen_rd8` and `net_gen_wr8`
  (`LeanOS.Net.EchoC`, kept apart so hosted executables that use the model
  need not link them), and `leanos_net_reply` is the compiled `reply`: allocation-free
  `uint32_t`/`uint64_t` straight-line code with no loop, no recursion and no
  Lean runtime call. The network subject (`subjects/net/`) links it and
  supplies the hooks over its own frame buffer.
* **Model.** With `τ := Buf` the hooks read and write a `ByteArray`, and
  `replyFrame` is the reference the frame-source device program
  (`LeanOS.Net.FrameSource`) and the hosted vectors check the C against.

Every hook that reads or changes the buffer takes the current token and
returns the next one; the value it reads is `Hooks.val` of the returned
token. Because each call consumes the token the previous call produced, the
compiler can neither reorder nor drop them (the discipline of
`LeanOS.Wifi.Exec`).

`reply t len mac ip` treats the buffer's first `len` bytes as a received
Ethernet II frame for the host with hardware address `mac` (48 bits, first
octet most significant) and IPv4 address `ip` (first octet most
significant). It rewrites the frame in place into the reply and delivers the
reply's length, or delivers 0 and leaves the frame as it was when there is
nothing to answer:

* ARP: a request (`htype` 1, `ptype` 0x0800, `hlen` 6, `plen` 4, `op` 1),
  broadcast or to `mac`, whose target protocol address is `ip` → an ARP
  reply to the requester (42 bytes).
* IPv4 to `mac` with a 20-byte header (`0x45`), destination `ip` and a
  total length `tl` with `28 ≤ tl ≤ len - 14`:
  * ICMP echo request (type 8) → echo reply: type 0, the checksum updated
    incrementally (RFC 1624: `+ 0x0800` in ones' complement), the
    addresses swapped (the header checksum is unchanged by a swap);
  * UDP to port 7, not a fragment → the datagram with addresses and ports
    swapped (both checksums are sums over the swapped fields, so neither
    changes).
  The reply is `14 + tl` bytes; Ethernet padding is not echoed.

Every buffer offset the code touches is below 42, and every one at or above
`len` is touched only after a check that `len` exceeds it, so the C reading
over a 1536-byte buffer and the model over a `len`-byte array agree.
-/
namespace LeanOS.Net.Echo

-- The generated C runs in a ring-3 subject with no module initializer: keep
-- constants inline in the code.
set_option compiler.extract_closed false

/-- Named primitives `reply` is written against. In C these are the
`net_gen_*` functions of `subjects/net/main.c`; the model reading is
`instHooksBuf`. -/
class Hooks (τ : Type) where
  /-- The value the last hook delivered. -/
  val : τ → UInt64
  /-- The same token delivering `x` (a computed value handed on). -/
  withVal : τ → UInt64 → τ
  /-- Read buffer byte `off`. -/
  rd : τ → UInt32 → τ
  /-- Write the low byte of `v` to buffer byte `off`. -/
  wr : τ → UInt32 → UInt32 → τ

open Hooks

variable {τ : Type} [Hooks τ]

/-- The last value as a byte. -/
@[inline] def byte (t : τ) : UInt32 := (val t).toUInt32 &&& 0xff

/-- The last value as a 32-bit word. -/
@[inline] def word (t : τ) : UInt32 := (val t).toUInt32

/-- Big-endian 16-bit read. -/
@[inline] def rd16 (t : τ) (off : UInt32) : τ :=
  let t := rd t off
  let hi := byte t
  let t := rd t (off + 1)
  withVal t ((hi <<< 8 ||| byte t).toUInt64)

/-- Big-endian 32-bit read. -/
@[inline] def rd32 (t : τ) (off : UInt32) : τ :=
  let t := rd16 t off
  let hi := word t
  let t := rd16 t (off + 2)
  withVal t ((hi <<< 16 ||| word t).toUInt64)

/-- Big-endian 48-bit read (a hardware address). -/
@[inline] def rd48 (t : τ) (off : UInt32) : τ :=
  let t := rd16 t off
  let hi := val t
  let t := rd32 t (off + 2)
  withVal t (hi <<< 32 ||| val t)

/-- Big-endian 16-bit write. -/
@[inline] def wr16 (t : τ) (off v : UInt32) : τ :=
  let t := wr t off (v >>> 8)
  wr t (off + 1) v

/-- Big-endian 32-bit write. -/
@[inline] def wr32 (t : τ) (off v : UInt32) : τ :=
  let t := wr16 t off (v >>> 16)
  wr16 t (off + 2) v

/-- Write a 48-bit hardware address. -/
@[inline] def wrMac (t : τ) (off : UInt32) (mac : UInt64) : τ :=
  let t := wr16 t off (mac >>> 32).toUInt32
  wr32 t (off + 2) mac.toUInt32

/-- Copy the 48-bit hardware address at `src` to `dst`. -/
@[inline] def mvMac (t : τ) (dst src : UInt32) : τ :=
  let t := rd48 t src
  wrMac t dst (val t)

/-- Copy the 32-bit word at `src` to `dst`. -/
@[inline] def mv32 (t : τ) (dst src : UInt32) : τ :=
  let t := rd32 t src
  wr32 t dst (word t)

/-- Deliver "no reply". -/
@[inline] def drop (t : τ) : τ := withVal t 0

/-- The broadcast hardware address. -/
def broadcast : UInt64 := 0xffffffffffff

/-- Ethernet: the reply goes back to the requester, from `mac`. -/
@[inline] def swapEth (t : τ) (mac : UInt64) : τ :=
  let t := mvMac t 0 6
  wrMac t 6 mac

/-- IPv4: swap source (26) and destination (30). -/
@[inline] def swapIp (t : τ) : τ :=
  let t := rd32 t 26
  let src := word t
  let t := rd32 t 30
  let dst := word t
  let t := wr32 t 26 dst
  wr32 t 30 src

/-- ARP request for `ip` → ARP reply (frame of at least 42 bytes). -/
@[specialize] def arp (t : τ) (len : UInt32) (mac : UInt64) (ip : UInt32) : τ :=
  if len < 42 then drop t else
  let t := rd48 t 0
  let dst := val t
  let t := rd16 t 14
  let htype := word t
  let t := rd16 t 16
  let ptype := word t
  let t := rd t 18
  let hlen := byte t
  let t := rd t 19
  let plen := byte t
  let t := rd16 t 20
  let op := word t
  let t := rd32 t 38
  let tpa := word t
  if (dst == broadcast || dst == mac) && htype == 1 && ptype == 0x0800 &&
      hlen == 6 && plen == 4 && op == 1 && tpa == ip then
    -- The target becomes the requester (sender hardware 22, protocol 28),
    -- before the sender fields are overwritten with ours.
    let t := mvMac t 0 6
    let t := mvMac t 32 22
    let t := mv32 t 38 28
    let t := wrMac t 6 mac
    let t := wr16 t 20 2
    let t := wrMac t 22 mac
    let t := wr32 t 28 ip
    withVal t 42
  else drop t

/-- ICMP echo request (type 8 at 34) → echo reply of `14 + tl` bytes. -/
@[specialize] def icmp (t : τ) (tl : UInt32) (mac : UInt64) : τ :=
  let t := rd t 34
  if byte t != 8 then drop t else
  let t := rd16 t 36
  let sum : UInt32 := word t + 0x0800
  let sum : UInt32 := (sum &&& (0xffff : UInt32)) + (sum >>> (16 : UInt32))
  let t := wr t 34 0
  let t := wr16 t 36 sum
  let t := swapIp t
  let t := swapEth t mac
  withVal t (14 + tl).toUInt64

/-- UDP to port 7 (destination port at 36), not a fragment → echo of
`14 + tl` bytes. -/
@[specialize] def udp (t : τ) (tl : UInt32) (mac : UInt64) : τ :=
  let t := rd16 t 20
  if (word t &&& (0x3fff : UInt32)) != 0 then drop t else
  let t := rd16 t 34
  let sport := word t
  let t := rd16 t 36
  if word t != 7 then drop t else
  let t := wr16 t 34 7
  let t := wr16 t 36 sport
  let t := swapIp t
  let t := swapEth t mac
  withVal t (14 + tl).toUInt64

/-- IPv4 to `mac` and `ip` (frame of at least 34 bytes). -/
@[specialize] def ipv4 (t : τ) (len : UInt32) (mac : UInt64) (ip : UInt32) : τ :=
  if len < 34 then drop t else
  let t := rd48 t 0
  let dst := val t
  let t := rd t 14
  let vihl := byte t
  let t := rd16 t 16
  let tl := word t
  let t := rd32 t 30
  let to := word t
  let t := rd t 23
  let proto := byte t
  if dst != mac || vihl != 0x45 || to != ip || tl < 28 || tl > len - 14 then drop t
  else if proto == 1 then icmp t tl mac
  else if proto == 17 then udp t tl mac
  else drop t

/-- The responder: deliver the reply's length (0: no reply) and leave the
reply in the buffer. -/
@[specialize] def reply (t : τ) (len : UInt32) (mac : UInt64) (ip : UInt32) : τ :=
  if len < 14 then drop t else
  let t := rd16 t 12
  let ty := word t
  if ty == 0x0806 then arp t len mac ip
  else if ty == 0x0800 then ipv4 t len mac ip
  else drop t

/-! ## The model reading -/

/-- A frame buffer and the last delivered value. -/
structure Buf where
  data : ByteArray
  v : UInt64 := 0

instance instHooksBuf : Hooks Buf where
  val b := b.v
  withVal b x := { b with v := x }
  rd b off := { b with v := (b.data.get! off.toNat).toUInt64 }
  wr b off x := { b with data := b.data.set! off.toNat x.toUInt8, v := 0 }

/-- The reference responder: the reply to frame `f`, if any. -/
def replyFrame (f : ByteArray) (mac : UInt64) (ip : UInt32) : Option ByteArray :=
  let b := reply (τ := Buf) { data := f } f.size.toUInt32 mac ip
  if b.v == 0 then none else some (b.data.extract 0 b.v.toNat)

end LeanOS.Net.Echo
