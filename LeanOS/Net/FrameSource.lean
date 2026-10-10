import LeanOS.Wifi.Bytecode
import LeanOS.Net.Echo

/-!
# The frame endpoint's scratch layout and a deterministic frame source (issue #450)

A driver device program and the kernel exchange frames with the ring-3
network subject through a fixed layout in the program's executor scratch
(`LeanOS.NetworkSubject` models the endpoint):

* `rxAt`: the program leaves a received Ethernet II frame here and yields
  its length (14–1514). The first yield is instead the 10-byte host
  configuration record (`configLen`): the hardware address (6 bytes) and the
  IPv4 address (4 bytes) the network subject answers for. A length below 14
  is never a frame.
* `txAt`, `txLenAt`: before the program is resumed, the kernel leaves the
  network subject's reply here and its length in the 32-bit word at
  `txLenAt` (0: no reply). The program takes the reply and clears the word.

The BCM43224 serve program (`LeanOS.Wifi.Endpoint`) fills the layout from
the radio. `program` here fills it from a fixed list of synthesized frames
instead, so the network subject can be exercised end to end on q35 without
WiFi hardware: for every frame it checks the reply the network subject
returned, byte for byte, against the reference responder
`LeanOS.Net.Echo.replyFrame`, and prints one record per frame. It drives no
device: its declared target is the reserved identity `0xffffffff`, which no
PCI function reports, and its policy (`q35FrameSourcePolicy`) admits no
configuration access and no DMA.
-/
namespace LeanOS.Net.FrameSource

open LeanOS.Wifi.Bytecode

/-! ## The endpoint layout (executor scratch offsets) -/

def rxAt : UInt32 := 0x3E000
def txAt : UInt32 := 0x3E800
def txLenAt : UInt32 := 0x3F000
/-- Bytes of the host configuration record. -/
def configLen : UInt32 := 10
/-- Bytes reserved for each frame slot. -/
def slotBytes : UInt32 := 0x800

/-! Records the frame source prints (`print` tags). -/
namespace Tag
/-- The reply to frame `k` matched the reference: value `k <<< 16 ||| length`. -/
def replyMatched : UInt32 := 0x5101
/-- Frame `k` drew no reply, as the reference says: value `k`. -/
def noReplyMatched : UInt32 := 0x5102
end Tag

/-- Fail codes: the frame index is added. -/
def failLength : UInt32 := 0x51100
def failBytes : UInt32 := 0x51200

/-- The fixture's declared target: identity `0xffffffff` (no function). -/
def target : Target :=
  { bus := 0, dev := 0, fn := 0, id := 0xffffffff, windowBytes := 0x200 }

/-! ## Frame construction -/

def be16 (v : Nat) : List UInt8 := [(v / 256 % 256).toUInt8, (v % 256).toUInt8]

def macBytes (m : UInt64) : List UInt8 :=
  (List.range 6).map fun i => (m >>> (8 * (5 - i)).toUInt64).toUInt8

def ipBytes (a : UInt32) : List UInt8 :=
  (List.range 4).map fun i => (a >>> (8 * (3 - i)).toUInt32).toUInt8

/-- Ones'-complement sum of big-endian 16-bit words (odd tail padded). -/
def onesSum : List UInt8 → Nat → Nat
  | a :: b :: rest, acc => onesSum rest (acc + a.toNat * 256 + b.toNat)
  | [a], acc => acc + a.toNat * 256
  | [], acc => acc

def fold16 (s : Nat) : Nat :=
  let s := s % 65536 + s / 65536
  s % 65536 + s / 65536

/-- The Internet checksum of `l`. -/
def checksum (l : List UInt8) : Nat := 65535 - fold16 (onesSum l 0)

def ethernet (dst src : UInt64) (ty : Nat) (payload : List UInt8) : List UInt8 :=
  macBytes dst ++ macBytes src ++ be16 ty ++ payload

def ipv4 (proto : Nat) (src dst : UInt32) (id : Nat) (payload : List UInt8) : List UInt8 :=
  let hdr (sum : Nat) := [0x45, 0] ++ be16 (20 + payload.length) ++ be16 id ++
    [0x40, 0, 64, proto.toUInt8] ++ be16 sum ++ ipBytes src ++ ipBytes dst
  hdr (checksum (hdr 0)) ++ payload

def arpRequest (sha : UInt64) (spa tpa : UInt32) : List UInt8 :=
  ethernet Echo.broadcast sha 0x0806
    ([0, 1, 8, 0, 6, 4, 0, 1] ++ macBytes sha ++ ipBytes spa ++ macBytes 0 ++ ipBytes tpa ++
      List.replicate 18 0)

def icmpEcho (dst src : UInt64) (sip dip : UInt32) (id seq : Nat) (data : List UInt8) :
    List UInt8 :=
  let msg (sum : Nat) := [8, 0] ++ be16 sum ++ be16 id ++ be16 seq ++ data
  ethernet dst src 0x0800 (ipv4 1 sip dip 0x1001 (msg (checksum (msg 0))))

def udpDatagram (dst src : UInt64) (sip dip : UInt32) (sport dport : Nat) (data : List UInt8) :
    List UInt8 :=
  let len := 8 + data.length
  let seg (sum : Nat) := be16 sport ++ be16 dport ++ be16 len ++ be16 sum ++ data
  let pseudo := ipBytes sip ++ ipBytes dip ++ [0, 17] ++ be16 len
  let sum := checksum (pseudo ++ seg 0)
  ethernet dst src 0x0800 (ipv4 17 sip dip 0x2002 (seg (if sum == 0 then 65535 else sum)))

/-! ## The fixture's host and its peer -/

/-- The network subject's hardware address (locally administered) and IPv4
address 10.0.2.15. -/
def mac : UInt64 := 0x02004c45414e
def ip : UInt32 := 0x0a00020f
/-- The peer that sends the frames: 52:54:00:12:34:56 at 10.0.2.2. -/
def peerMac : UInt64 := 0x525400123456
def peerIp : UInt32 := 0x0a000202

def ascii (s : String) : List UInt8 := s.toUTF8.toList

/-- The synthesized frames, in order: an ARP request for the host (padded
to Ethernet's 60-byte minimum), an ICMP echo request, a UDP datagram to the
echo port, a UDP datagram to the discard port (no reply), an ARP request for
another address (no reply) and an ICMP echo request addressed to another
hardware address (no reply). -/
def frames : List ByteArray := List.map (fun l => ⟨l.toArray⟩) [
  arpRequest peerMac peerIp ip,
  icmpEcho mac peerMac peerIp ip 0x4c45 1 (ascii "leanos network subject"),
  udpDatagram mac peerMac peerIp ip 40000 7 (ascii "echo through ring 3"),
  udpDatagram mac peerMac peerIp ip 40001 9 (ascii "discarded"),
  arpRequest peerMac peerIp 0x0a000263,
  icmpEcho 0x02004c454141 peerMac peerIp ip 0x4c45 2 (ascii "not for us")]

/-- The reference replies. -/
def replies : List (Option ByteArray) := frames.map fun f => Echo.replyFrame f mac ip

/-- The host configuration record. -/
def configRecord : ByteArray := ⟨(macBytes mac ++ ipBytes ip).toArray⟩

/-! ## The program -/

def le32 (b : ByteArray) (i : Nat) : UInt32 :=
  b[i]!.toUInt32 ||| (b[i + 1]!.toUInt32 <<< 8) ||| (b[i + 2]!.toUInt32 <<< 16) |||
    (b[i + 3]!.toUInt32 <<< 24)

/-- Store `b` at scratch `at_` (r0 must be 0). -/
def storeAt (at_ : UInt32) (b : ByteArray) : ProgM Unit := do
  for k in [0:b.size / 4] do
    emit (.memStore 4 0 (at_ + (4 * k).toUInt32) (.imm (le32 b (4 * k))))
  for k in [4 * (b.size / 4):b.size] do
    emit (.memStore 1 0 (at_ + k.toUInt32) (.imm b[k]!.toUInt32))

/-- Jump to `bad` unless scratch `at_` holds `b` (r0 must be 0; uses r1). -/
def checkAt (at_ : UInt32) (b : ByteArray) (bad : Nat) : ProgM Unit := do
  for k in [0:b.size / 4] do
    emit (.memLoad 4 1 0 (at_ + (4 * k).toUInt32))
    emit (.branch .ne 1 (.imm (le32 b (4 * k))) bad)
  for k in [4 * (b.size / 4):b.size] do
    emit (.memLoad 1 1 0 (at_ + k.toUInt32))
    emit (.branch .ne 1 (.imm b[k]!.toUInt32) bad)

/-- Hand the frame in `rxAt` to the endpoint, then check the reply against
`expected` and clear the reply word. -/
def exchange (k : Nat) (len : UInt32) (expected : Option ByteArray) : ProgM Unit := do
  let badLen ← newLabel
  let badBytes ← newLabel
  let done ← newLabel
  emit (.yield (.imm len))
  li 0 0
  emit (.memLoad 4 2 0 txLenAt)
  match expected with
  | none =>
    emit (.branch .ne 2 (.imm 0) badLen)
    printImm Tag.noReplyMatched k.toUInt32
  | some r =>
    emit (.branch .ne 2 (.imm r.size.toUInt32) badLen)
    checkAt txAt r badBytes
    printImm Tag.replyMatched ((k.toUInt32 <<< 16) ||| r.size.toUInt32)
  emit (.memStore 4 0 txLenAt (.imm 0))
  emit (.jump done)
  place badLen
  fail (failLength + k.toUInt32)
  place badBytes
  fail (failBytes + k.toUInt32)
  place done

/-- The frame source: the configuration record, then every frame of `fs`
with its reference reply, then halt. -/
def programOf (t : Target) (fs : List ByteArray) (rs : List (Option ByteArray)) :
    ProgM Unit := do
  setTarget t
  li 0 0
  emit (.memStore 4 0 txLenAt (.imm 0))
  storeAt rxAt configRecord
  exchange 0 configLen none
  for (k, f, r) in (List.range fs.length).zip (fs.zip rs) do
    li 0 0
    storeAt rxAt f
    exchange (k + 1) f.size.toUInt32 r
  halt

/-- The q35 frame-source program (`net-q35-frames`). -/
def program : ProgM Unit := programOf target frames replies

/-- The same frames for the Qotom's BCM43224 (`net-bcm-frames`): a smoke test
of the ring-3 path on the lab machine that touches no device register and
needs no network key. Its target is the Broadcom function, so the lab binds
it as it binds the serve program, under `qotomBcm43224Policy`. -/
def bcmProgram : ProgM Unit := programOf bcm43224Target frames replies

end LeanOS.Net.FrameSource
