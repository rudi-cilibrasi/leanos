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
* `len = 1`: a **tick**, which the driver yields once a second of its clock
  has passed since the last tick. Ticks drive the retransmission schedule of
  RFC 2131 section 4.1, read on the one-second tick: the wait before the
  `n`-th retransmission (counting from 0) is `4 · 2^n` seconds, capped at 64
  (4, 8, 16, 32, 64, 64, …), randomized by ±1 second. The client has no
  random source, so the ±1 is derived deterministically from the transaction
  id and `n` (`retransmitDelay`). While selecting the client retransmits the
  DISCOVER for ever on this schedule; while requesting it retransmits the
  REQUEST, and the timeout of the third unanswered REQUEST restarts from
  DISCOVER with the next transaction id (RFC 2131 sections 3.1 and 4.4.1).
  See [The retransmission schedule](#the-retransmission-schedule-issue-573).
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
/-- Doublings of the retransmission wait: after 4 the wait stays at 64
ticks (RFC 2131 section 4.1, "up to a maximum of 64 seconds"). -/
def backoffSteps : UInt64 := 4
/-- REQUEST transmissions before the client restarts from DISCOVER. -/
def requestTries : UInt64 := 3

/-- The base wait, in ticks, before retransmission `n` (counting from 0) of
RFC 2131 section 4.1: 4, 8, 16, 32, then 64. -/
@[inline] def backoffBase (n : UInt64) : UInt64 :=
  if n < backoffSteps then (4 : UInt64) <<< n else 64

/-- The jitter of retransmission `n` of transaction `xid`, 0, 1 or 2: the
wait is the base wait minus one plus the jitter, so it lies within ±1 tick
of the base wait, as RFC 2131 section 4.1 asks of "a uniform random number
chosen from the range -1 to +1". The client has no random source; like its
transaction id (`xidOf`), the jitter is lab grade and deterministic, so
clients with different transaction ids still retransmit out of step. -/
@[inline] def jitter (xid n : UInt64) : UInt64 := (xid + n) % 3

/-- The ticks the client waits after a transmission before retransmission
`n` of transaction `xid` (`retransmitDelay_bounds`). -/
@[inline] def retransmitDelay (xid n : UInt64) : UInt64 := backoffBase n - 1 + jitter xid n

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

/-- Transmit the DISCOVER of transaction `xid`. -/
@[specialize] def discoverAgain (t : τ) (xid : UInt64) : τ :=
  let t := ld t regMac
  buildDiscover t (val t) xid

/-- Enter `selecting` with transaction `xid` and transmit a DISCOVER. -/
@[specialize] def discoverWith (t : τ) (xid : UInt64) : τ :=
  let t := st t regXid xid
  let t := st t regPhase phaseSelecting
  let t := st t regTicks 0
  let t := st t regTries 0
  discoverAgain t xid

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

/-- A tick in phase `phase`: count it, and retransmit once the ticks since
the last transmission reach the wait `retransmitDelay xid tries`
(`regTries` counts the retransmissions so far). -/
@[inline] def onTick (t : τ) (phase : UInt64) : τ :=
  if phase != phaseSelecting && phase != phaseRequesting then drop t else
  let t := ld t regTicks
  let ticks := val t + 1
  let t := ld t regTries
  let tries := val t
  let t := ld t regXid
  let xid := val t
  if ticks < retransmitDelay xid tries then drop (st t regTicks ticks) else
  let t := st t regTicks 0
  if phase == phaseSelecting then
    let t := st t regTries (if tries < backoffSteps then tries + 1 else tries)
    discoverAgain t xid
  else if tries + 1 < requestTries then requestAgain (st t regTries (tries + 1))
  else discoverWith t ((xid + 1) &&& 0xffffffff)

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

/-! ## The retransmission schedule (issue #573)

RFC 2131 section 4.1 asks a client that hears no answer to retransmit after
a randomized exponential backoff: 4 seconds ±1 before the first
retransmission, 8 ±1 before the next, doubling up to 64 ±1. The client
counts the driver's one-second ticks, so the schedule is read in ticks:

* `backoffBase_toNat`, `backoffBase_rfc`: the base wait before
  retransmission `n` is `4 · 2^min n 4` ticks: 4, 8, 16, 32, 64, 64, ….
* `retransmitDelay_bounds`, `retransmitDelay_range`: the wait lies within
  ±1 tick of the base wait, and between 3 and 65 ticks, so the client never
  retransmits on consecutive ticks.
* `step_tick_buf`, `stepRecord_tick`: the client's `step` on a tick record
  (the model reading, which the hosted vectors check the generated C
  against) moves the timer registers exactly as `Timer.tick` says,
  transmits a frame exactly when `Timer.tick` retransmits, and changes no
  other register.
* `tick_silent`, `run_silent`: before the wait is over a tick transmits
  nothing.
* `selecting_gap`: right after a DISCOVER, a client in `selecting` that
  hears nothing stays silent for `retransmitDelay xid tries - 1` ticks and
  retransmits the DISCOVER of the same transaction on the next, with the
  next, doubled, wait.
* `requesting_gap`: right after a REQUEST, a client in `requesting` that
  hears nothing stays silent for its wait and then retransmits the REQUEST,
  or, once three REQUESTs went unanswered, restarts from DISCOVER with the
  next transaction id (RFC 2131 section 4.4.1).
-/

theorem backoffBase_toNat (n : UInt64) :
    (backoffBase n).toNat = 4 * 2 ^ min n.toNat 4 := by
  unfold backoffBase backoffSteps
  by_cases h : n < 4
  · have hn : n.toNat < 4 := h
    simp only [h, ↓reduceIte]
    have : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by
      have : n.toNat = 0 ∨ n.toNat = 1 ∨ n.toNat = 2 ∨ n.toNat = 3 := by omega
      rcases this with h0 | h0 | h0 | h0
      · exact Or.inl (UInt64.toNat_inj.mp h0)
      · exact Or.inr (Or.inl (UInt64.toNat_inj.mp h0))
      · exact Or.inr (Or.inr (Or.inl (UInt64.toNat_inj.mp h0)))
      · exact Or.inr (Or.inr (Or.inr (UInt64.toNat_inj.mp h0)))
    rcases this with rfl | rfl | rfl | rfl <;> decide
  · have hn : ¬ n.toNat < 4 := h
    simp only [h, ↓reduceIte]
    rw [Nat.min_eq_right (by omega)]
    rfl

theorem jitter_lt (xid n : UInt64) : (jitter xid n).toNat < 3 := by
  unfold jitter
  rw [UInt64.toNat_mod]
  exact Nat.mod_lt _ (by decide)

theorem retransmitDelay_toNat (xid n : UInt64) :
    (retransmitDelay xid n).toNat = (backoffBase n).toNat - 1 + (jitter xid n).toNat := by
  have hb := backoffBase_toNat n
  have hj := jitter_lt xid n
  have : 4 ≤ (backoffBase n).toNat := by
    rw [hb]; have := Nat.one_le_two_pow (n := min n.toNat 4); omega
  have : (backoffBase n).toNat ≤ 64 := by
    rw [hb]
    have : 2 ^ min n.toNat 4 ≤ 2 ^ 4 := Nat.pow_le_pow_right (by decide) (Nat.min_le_right _ _)
    omega
  unfold retransmitDelay
  rw [UInt64.toNat_add, UInt64.toNat_sub_of_le]
  · simp only [UInt64.toNat_one]; omega
  · rw [UInt64.le_iff_toNat_le]; simp only [UInt64.toNat_one]; omega


/-! ### The model reading's registers -/

section BufRegs
open LeanOS.Net.Echo.Hooks Hooks

theorem buf_wr_regs (b : Buf) (o x : UInt32) : (wr b o x).regs = b.regs := rfl
theorem buf_withVal_regs (b : Buf) (x : UInt64) : (withVal b x).regs = b.regs := rfl
theorem buf_withVal_v (b : Buf) (x : UInt64) : val (withVal b x) = x := rfl
theorem buf_ld (b : Buf) (k : UInt32) : ld b k = { b with v := b.regs.getD k.toNat 0 } := rfl
theorem buf_st (b : Buf) (k : UInt32) (x : UInt64) :
    st b k x = { b with regs := b.regs.set! k.toNat x, v := 0 } := rfl

theorem zeroFrom_regs (b : Buf) (i n : UInt32) : (zeroFrom b i n).regs = b.regs := by
  fun_induction zeroFrom b i n with
  | case1 t i h ih => rw [ih]; rfl
  | case2 => rfl

theorem buildDiscover_buf (b : Buf) (mac xid : UInt64) :
    (buildDiscover b mac xid).regs = b.regs ∧ (buildDiscover b mac xid).v = 342 := by
  refine ⟨?_, rfl⟩
  simp only [buildDiscover, buildCommon, paramList, Echo.wrMac, Echo.wr32, Echo.wr16,
    buf_wr_regs, buf_withVal_regs, zeroFrom_regs]


theorem buildRequest_buf (b : Buf) (mac xid r s : UInt64) :
    (buildRequest b mac xid r s).regs = b.regs ∧ (buildRequest b mac xid r s).v = 342 := by
  refine ⟨?_, rfl⟩
  simp only [buildRequest, buildCommon, paramList, Echo.wrMac, Echo.wr32, Echo.wr16,
    buf_wr_regs, buf_withVal_regs, zeroFrom_regs]

theorem buf_val (b : Buf) : val b = b.v := rfl

theorem discoverAgain_regs (b : Buf) (xid : UInt64) : (discoverAgain b xid).regs = b.regs := by
  simp only [discoverAgain, buf_ld]; exact (buildDiscover_buf _ _ _).1
theorem discoverAgain_v (b : Buf) (xid : UInt64) : (discoverAgain b xid).v = 342 := by
  simp only [discoverAgain, buf_ld]; exact (buildDiscover_buf _ _ _).2
theorem requestAgain_regs (b : Buf) : (requestAgain b).regs = b.regs := by
  simp only [requestAgain, buf_ld]; exact (buildRequest_buf _ _ _ _ _).1
theorem requestAgain_v (b : Buf) : (requestAgain b).v = 342 := by
  simp only [requestAgain, buf_ld]; exact (buildRequest_buf _ _ _ _ _).2
theorem discoverWith_regs (b : Buf) (xid : UInt64) :
    (discoverWith b xid).regs =
      ((((b.regs.set! 1 xid).set! 0 phaseSelecting).set! 6 0).set! 7 0) := by
  simp only [discoverWith, buf_st, discoverAgain_regs]; rfl
theorem discoverWith_v (b : Buf) (xid : UInt64) : (discoverWith b xid).v = 342 := by
  simp only [discoverWith, discoverAgain_v]

theorem getD_set (a : Array UInt64) (i j : Nat) (x : UInt64) (hi : i < a.size) :
    (a.set! i x).getD j 0 = if i = j then x else a.getD j 0 := by
  simp only [Array.getD_eq_getD_getElem?, Array.set!_eq_setIfInBounds,
    Array.getElem?_setIfInBounds, hi, ↓reduceIte]
  split <;> rfl

theorem size_set (a : Array UInt64) (i : Nat) (x : UInt64) : (a.set! i x).size = a.size := by
  simp

end BufRegs

/-- The client's timer: its phase, its transaction, the ticks since its last
transmission and the retransmissions so far (registers 0, 1, 6, 7). -/
structure Timer where
  phase : UInt64
  xid : UInt64
  ticks : UInt64
  tries : UInt64
  deriving DecidableEq, Repr

/-- What a tick makes the client transmit. -/
inductive Sent where
  | none | discover | request
  deriving DecidableEq, Repr

/-- The timer in registers `r`. -/
def Timer.ofRegs (r : Array UInt64) : Timer :=
  ⟨r.getD 0 0, r.getD 1 0, r.getD 6 0, r.getD 7 0⟩

/-- The retransmissions counted after one more: the wait doubles up to
`backoffSteps` times. -/
def nextTries (n : UInt64) : UInt64 := if n < backoffSteps then n + 1 else n

/-- The retransmission schedule on a tick, read off `onTick`. -/
def Timer.tick (c : Timer) : Timer × Sent :=
  if c.phase != phaseSelecting && c.phase != phaseRequesting then (c, .none)
  else if c.ticks + 1 < retransmitDelay c.xid c.tries then ({ c with ticks := c.ticks + 1 }, .none)
  else if c.phase == phaseSelecting then
    ({ c with ticks := 0, tries := nextTries c.tries }, .discover)
  else if c.tries + 1 < requestTries then ({ c with ticks := 0, tries := c.tries + 1 }, .request)
  else ({ phase := phaseSelecting, xid := (c.xid + 1) &&& 0xffffffff, ticks := 0, tries := 0 },
      .discover)

/-- **The client's tick is the schedule.** On a tick record, the model
reading of `step` moves the timer registers exactly as `Timer.tick` says,
transmits a frame (342 bytes) exactly when `Timer.tick` says it retransmits,
and leaves every other register (the hardware address, the offer, its
server, the lease) unchanged. The hosted vectors check the generated C
against this reading, and the frames against `Wifi.Dhcp`. -/
theorem step_tick_buf (b : Buf) (hs : b.regs.size = registers) :
    Timer.ofRegs (step b 1).regs = (Timer.ofRegs b.regs).tick.1 ∧
    (step b 1).v = (if (Timer.ofRegs b.regs).tick.2 = .none then 0 else frameBytes.toUInt64) ∧
    ∀ k, k ≠ 0 → k ≠ 1 → k ≠ 6 → k ≠ 7 → (step b 1).regs.getD k 0 = b.regs.getD k 0 := by
  obtain ⟨data, regs, v⟩ := b
  simp only at hs
  simp only [step, onTick, buf_ld, buf_val, buf_st, Echo.drop, regPhase, regTicks, regTries,
    regXid, UInt32.reduceToNat]
  simp only [show ((1 : UInt32) == 6) = false from rfl, show ((1 : UInt32) == 1) = true from rfl,
    Bool.false_eq_true, ↓reduceIte]
  simp only [Timer.tick, Timer.ofRegs]
  by_cases a1 : (regs.getD 0 0 != phaseSelecting && regs.getD 0 0 != phaseRequesting) = true
  · simp only [a1, ↓reduceIte, buf_withVal_regs]
    exact ⟨trivial, rfl, fun _ _ _ _ _ => trivial⟩
  · simp only [a1, Bool.false_eq_true, ↓reduceIte]
    by_cases a2 : regs.getD 6 0 + 1 < retransmitDelay (regs.getD 1 0) (regs.getD 7 0)
    · simp only [a2, ↓reduceIte, buf_withVal_regs]
      refine ⟨?_, rfl, fun k _ _ h6 _ => ?_⟩
      · simp (disch := (simp only [size_set, hs, registers]; decide)) only [getD_set, Nat.reduceEqDiff, ↓reduceIte]
      · simp (disch := (simp only [size_set, hs, registers]; decide)) only [getD_set, Ne.symm h6, ↓reduceIte]
    · simp only [a2, ↓reduceIte]
      by_cases a3 : (regs.getD 0 0 == phaseSelecting) = true
      · simp only [a3, ↓reduceIte, discoverAgain_regs, discoverAgain_v]
        refine ⟨?_, rfl, fun k _ _ h6 h7 => ?_⟩
        · simp (disch := (simp only [size_set, hs, registers]; decide)) only [getD_set, Nat.reduceEqDiff, ↓reduceIte]
          rfl
        · simp (disch := (simp only [size_set, hs, registers]; decide)) only [getD_set, Ne.symm h6, Ne.symm h7, ↓reduceIte]
      · simp only [a3, Bool.false_eq_true, ↓reduceIte]
        by_cases a4 : regs.getD 7 0 + 1 < requestTries
        · simp only [a4, ↓reduceIte, requestAgain_regs, requestAgain_v]
          refine ⟨?_, rfl, fun k _ _ h6 h7 => ?_⟩
          · simp (disch := (simp only [size_set, hs, registers]; decide)) only [getD_set, Nat.reduceEqDiff, ↓reduceIte]
          · simp (disch := (simp only [size_set, hs, registers]; decide)) only [getD_set, Ne.symm h6, Ne.symm h7, ↓reduceIte]
        · simp only [a4, ↓reduceIte, discoverWith_regs, discoverWith_v]
          refine ⟨?_, rfl, fun k h0 h1 h6 h7 => ?_⟩
          · simp (disch := (simp only [size_set, hs, registers]; decide)) only [getD_set, Nat.reduceEqDiff, ↓reduceIte]
          · simp (disch := (simp only [size_set, hs, registers]; decide)) only [getD_set, Ne.symm h0, Ne.symm h1, Ne.symm h6, Ne.symm h7,
              ↓reduceIte]

theorem retransmitDelay_bounds (xid n : UInt64) :
    (backoffBase n).toNat - 1 ≤ (retransmitDelay xid n).toNat ∧
      (retransmitDelay xid n).toNat ≤ (backoffBase n).toNat + 1 := by
  rw [retransmitDelay_toNat]; have := jitter_lt xid n
  have := Nat.one_le_two_pow (n := min n.toNat 4)
  rw [backoffBase_toNat]; omega

theorem retransmitDelay_range (xid n : UInt64) :
    3 ≤ (retransmitDelay xid n).toNat ∧ (retransmitDelay xid n).toNat ≤ 65 := by
  rw [retransmitDelay_toNat, backoffBase_toNat]
  have := jitter_lt xid n
  have h1 := Nat.one_le_two_pow (n := min n.toNat 4)
  have h2 : 2 ^ min n.toNat 4 ≤ 2 ^ 4 := Nat.pow_le_pow_right (by decide) (Nat.min_le_right _ _)
  omega

/-- The base waits of RFC 2131 section 4.1: 4, 8, 16, 32, then 64 seconds. -/
theorem backoffBase_rfc :
    (List.range 7).map (fun n => (backoffBase n.toUInt64).toNat) = [4, 8, 16, 32, 64, 64, 64] := by
  decide

/-- A client waiting for an answer. -/
def Timer.Waiting (c : Timer) : Prop := c.phase = phaseSelecting ∨ c.phase = phaseRequesting

/-- `n` ticks: the timer after them, and what each made the client transmit. -/
def Timer.run : Nat → Timer → Timer × List Sent
  | 0, c => (c, [])
  | n + 1, c =>
    let r := c.tick
    let rest := Timer.run n r.1
    (rest.1, r.2 :: rest.2)

theorem tick_waiting_cond {c : Timer} (h : c.Waiting) :
    (c.phase != phaseSelecting && c.phase != phaseRequesting) = false := by
  rcases h with h | h <;> simp [h, phaseSelecting, phaseRequesting]

/-- A tick before the wait is over transmits nothing and counts. -/
theorem tick_silent {c : Timer} (h : c.Waiting)
    (hlt : c.ticks.toNat + 1 < (retransmitDelay c.xid c.tries).toNat) :
    c.tick = ({ c with ticks := c.ticks + 1 }, .none) := by
  have : c.ticks + 1 < retransmitDelay c.xid c.tries := by
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add, UInt64.toNat_one]
    have := (retransmitDelay_range c.xid c.tries).2
    rw [Nat.mod_eq_of_lt (by omega)]; exact hlt
  simp [Timer.tick, tick_waiting_cond h, this]

/-- While waiting, `n` ticks short of the wait transmit nothing. -/
theorem run_silent {c : Timer} (h : c.Waiting) :
    ∀ n, c.ticks.toNat + n < (retransmitDelay c.xid c.tries).toNat →
      Timer.run n c = ({ c with ticks := c.ticks + n.toUInt64 }, List.replicate n .none)
  | 0, _ => by simp [Timer.run]
  | n + 1, hlt => by
    have hd := (retransmitDelay_range c.xid c.tries).2
    rw [Timer.run, tick_silent h (by omega)]
    simp only
    have hw : ({ c with ticks := c.ticks + 1 } : Timer).Waiting := h
    have ht : (c.ticks + 1).toNat = c.ticks.toNat + 1 := by
      rw [UInt64.toNat_add, UInt64.toNat_one, Nat.mod_eq_of_lt (by omega)]
    rw [run_silent hw n (by simp only; omega)]
    simp only [List.replicate_succ, Prod.mk.injEq, and_true]
    congr 1
    rw [UInt64.add_assoc]
    congr 1
    apply UInt64.toNat_inj.mp
    simp [UInt64.toNat_add]
    omega

theorem run_add (m n : Nat) (c : Timer) :
    Timer.run (m + n) c =
      ((Timer.run n (Timer.run m c).1).1, (Timer.run m c).2 ++ (Timer.run n (Timer.run m c).1).2) := by
  induction m generalizing c with
  | zero => simp [Timer.run]
  | succ m ih =>
    rw [show m + 1 + n = (m + n) + 1 by omega, Timer.run, Timer.run, ih]
    simp

/-- The tick that ends the wait in `selecting` retransmits the DISCOVER of
the same transaction, and the next wait is one doubling longer (up to 64). -/
theorem tick_fires_selecting {c : Timer} (hp : c.phase = phaseSelecting)
    (he : c.ticks.toNat + 1 = (retransmitDelay c.xid c.tries).toNat) :
    c.tick = ({ c with ticks := 0, tries := nextTries c.tries }, .discover) := by
  have hd := (retransmitDelay_range c.xid c.tries).2
  have : ¬ c.ticks + 1 < retransmitDelay c.xid c.tries := by
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add, UInt64.toNat_one, Nat.mod_eq_of_lt (by omega)]
    omega
  simp [Timer.tick, this, hp, nextTries]

/-- The tick that ends the wait in `requesting` retransmits the REQUEST, or,
after the third, restarts from DISCOVER with the next transaction. -/
theorem tick_fires_requesting {c : Timer} (hp : c.phase = phaseRequesting)
    (he : c.ticks.toNat + 1 = (retransmitDelay c.xid c.tries).toNat) :
    c.tick = if c.tries + 1 < requestTries then
        ({ c with ticks := 0, tries := c.tries + 1 }, .request)
      else ({ phase := phaseSelecting, xid := (c.xid + 1) &&& 0xffffffff, ticks := 0, tries := 0 },
        .discover) := by
  have hd := (retransmitDelay_range c.xid c.tries).2
  have : ¬ c.ticks + 1 < retransmitDelay c.xid c.tries := by
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add, UInt64.toNat_one, Nat.mod_eq_of_lt (by omega)]
    omega
  simp [Timer.tick, this, hp, phaseSelecting, phaseRequesting]

/-- **The DISCOVER schedule.** Right after a DISCOVER (`ticks = 0`) with
`tries` retransmissions so far, a client in `selecting` that hears nothing
transmits nothing for `retransmitDelay xid tries - 1` ticks and retransmits
the DISCOVER of the same transaction on the next: its wait lies within ±1
tick of `4 · 2^min tries 4` (`retransmitDelay_bounds`, `backoffBase_toNat`). -/
theorem selecting_gap {c : Timer} (hp : c.phase = phaseSelecting) (h0 : c.ticks = 0) :
    Timer.run (retransmitDelay c.xid c.tries).toNat c =
      ({ c with tries := nextTries c.tries },
        List.replicate ((retransmitDelay c.xid c.tries).toNat - 1) .none ++ [.discover]) := by
  have hr := retransmitDelay_range c.xid c.tries
  obtain ⟨d, hd⟩ : ∃ d, (retransmitDelay c.xid c.tries).toNat = d + 1 := ⟨_, (Nat.succ_pred_eq_of_pos (by omega)).symm⟩
  rw [hd, run_add, run_silent (Or.inl hp) d (by rw [h0]; simp; omega)]
  simp only [Nat.add_sub_cancel, Timer.run]
  rw [tick_fires_selecting (by simpa using hp) (by
    simp only [h0, UInt64.zero_add]
    rw [UInt64.toNat_ofNat_of_lt' (by rw [show UInt64.size = 18446744073709551616 from rfl]; omega)]
    omega)]
  cases c; simp_all

/-- **The REQUEST schedule.** Right after a REQUEST (`ticks = 0`) with
`tries` retransmissions so far, a client in `requesting` that hears nothing
transmits nothing for `retransmitDelay xid tries - 1` ticks, then retransmits
the REQUEST, or, once three were unanswered, restarts from DISCOVER with the
next transaction id. -/
theorem requesting_gap {c : Timer} (hp : c.phase = phaseRequesting) (h0 : c.ticks = 0) :
    Timer.run (retransmitDelay c.xid c.tries).toNat c =
      if c.tries + 1 < requestTries then
        ({ c with tries := c.tries + 1 },
          List.replicate ((retransmitDelay c.xid c.tries).toNat - 1) .none ++ [.request])
      else ({ phase := phaseSelecting, xid := (c.xid + 1) &&& 0xffffffff, ticks := 0, tries := 0 },
          List.replicate ((retransmitDelay c.xid c.tries).toNat - 1) .none ++ [.discover]) := by
  have hr := retransmitDelay_range c.xid c.tries
  obtain ⟨d, hd⟩ : ∃ d, (retransmitDelay c.xid c.tries).toNat = d + 1 := ⟨_, (Nat.succ_pred_eq_of_pos (by omega)).symm⟩
  rw [hd, run_add, run_silent (Or.inr hp) d (by rw [h0]; simp; omega)]
  simp only [Nat.add_sub_cancel, Timer.run]
  rw [tick_fires_requesting (by simpa using hp) (by
    simp only [h0, UInt64.zero_add]
    rw [UInt64.toNat_ofNat_of_lt' (by rw [show UInt64.size = 18446744073709551616 from rfl]; omega)]
    omega)]
  cases c; simp_all
  split <;> simp

/-- `step_tick_buf` for the records the hosted vectors replay: a tick
record (one byte) moves the timer as `Timer.tick` says, draws a frame
exactly on a retransmission, and leaves the other registers alone. -/
theorem stepRecord_tick (regs : Array UInt64) (hs : regs.size = registers) (f : ByteArray)
    (hf : f.size = 1) :
    Timer.ofRegs (stepRecord regs f).1 = (Timer.ofRegs regs).tick.1 ∧
    ((stepRecord regs f).2.isSome = true ↔ (Timer.ofRegs regs).tick.2 ≠ .none) ∧
    ∀ k, k ≠ 0 → k ≠ 1 → k ≠ 6 → k ≠ 7 → (stepRecord regs f).1.getD k 0 = regs.getD k 0 := by
  dsimp only [stepRecord]
  have hl : f.size.toUInt32 = 1 := by rw [hf]; rfl
  rw [hl]
  generalize hb : ({ data := f ++ ByteArray.mk (Array.replicate (bufferBytes - f.size) 0), regs } :
    Buf) = b
  have hbr : b.regs = regs := by rw [← hb]
  obtain ⟨h1, h2, h3⟩ := step_tick_buf b (by rw [hbr]; exact hs)
  rw [hbr] at h1 h2 h3
  refine ⟨h1, ?_, h3⟩
  rw [h2]
  by_cases hn : (Timer.ofRegs regs).tick.2 = .none
  · simp [hn]
  · simp [hn, frameBytes]

end LeanOS.Net.DhcpClient
