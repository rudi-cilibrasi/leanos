import LeanOS.Wifi.Connect

/-
Minimal IPv4 host responder for the associated station: answers ARP
requests for the leased address, and ICMP echo requests and UDP echo
datagrams (port 7) addressed to it, for a bounded time. Received frames are CCMP-decapsulated with the TK or GTK;
replies are built in scratch, CCMP-protected with the TK and sent through
the best-effort FIFO.

Reply construction:
* ARP (RFC 826): opcode 2, sender = our MAC/IP, target = the requester.
* ICMP echo reply (RFC 792): the request's IP datagram with source and
  destination swapped (the IPv4 header checksum is unchanged by a swap) and
  type 8 → 0; the ICMP checksum is updated incrementally (RFC 1624:
  HC' = HC + 0x0800 in ones'-complement arithmetic).
* UDP echo (RFC 862): the request's datagram with the IPv4 addresses and the
  UDP ports swapped. Both checksums are ones'-complement sums over the
  swapped fields, so neither changes.
-/
namespace LeanOS.Wifi.Responder

open LeanOS.Wifi.Bytecode LeanOS.Wifi.Bcm43224 LeanOS.Wifi.Connect

/-! Scratch (0x0C10–0x0C3F and 0x0C44; `plainBuf` 0x4000 holds the reply). -/
def seqAt : UInt32 := 0x0C10
def startAt : UInt32 := 0x0C14
def bodyAt : UInt32 := 0x0C18      -- decrypted body address
def lenAt : UInt32 := 0x0C1C       -- decrypted body length
def srcMacAt : UInt32 := 0x0C20    -- sender MAC of the request (6 bytes)
def arpCount : UInt32 := 0x0C28
def pingCount : UInt32 := 0x0C2C
def udpCount : UInt32 := 0x0C44
/-- Last accepted CCMP packet number per key: pairwise (TK) and group (GTK);
48-bit, low word then high half-word. -/
def lastPnTk : UInt32 := 0x0C30
def lastPnGtk : UInt32 := 0x0C38

namespace Tag
def arpReplied : UInt32 := 0x0F01
def pingReplied : UInt32 := 0x0F02
def summaryArp : UInt32 := 0x0F03
def summaryPing : UInt32 := 0x0F04
def listening : UInt32 := 0x0F05
def replay : UInt32 := 0x0F06
def udpReplied : UInt32 := 0x0F07
def summaryUdp : UInt32 := 0x0F08
end Tag

/-- Copy `r(n)` bytes from scratch `r(src)` to scratch `r(dst)`. Clobbers the
three registers and r0. -/
def copyR (dst src n : Reg) : ProgM Unit := do
  let top ← newLabel
  let done ← newLabel
  place top
  emit (.branch .eq n (.imm 0) done)
  emit (.memLoad 1 0 src 0)
  emit (.memStore 1 dst 0 (.reg 0))
  addi dst 1
  addi src 1
  emit (.alu .sub n (.imm 1))
  emit (.jump top)
  place done

/-- Store generation-time bytes at `r(base) + off`. -/
def storeBytes (base : Reg) (off : UInt32) (b : ByteArray) : ProgM Unit := do
  for h : k in [0:b.size] do
    emit (.memStore 1 base (off + k.toUInt32) (.imm b[k].toUInt32))

/-- Copy `n` bytes between fixed scratch addresses (uses r0, r1). -/
def copyFixed (dst src : UInt32) (n : Nat) : ProgM Unit := do
  li 1 0
  for k in [0:n] do
    emit (.memLoad 1 0 1 (src + k.toUInt32))
    emit (.memStore 1 1 (dst + k.toUInt32) (.reg 0))

/-- Write the 802.11 ToDS data header + LLC/SNAP for `ethertype` into
`plainBuf`: addr1 = BSSID, addr2 = us, addr3 = the requester, sequence from
`seqAt` (incremented). -/
def replyHeader (ethertype : UInt32) : ProgM Unit := do
  li 2 plainBuf
  storeBytes 2 0 (ByteArray.mk #[0x08, 0x01, 0, 0])
  copyFixed (plainBuf + 4) Mlme.bssidAt 6
  li 2 plainBuf
  storeBytes 2 10 (ByteArray.mk Mlme.ourMac.data)
  copyFixed (plainBuf + 16) srcMacAt 6
  li 1 0
  emit (.memLoad 4 3 1 seqAt)
  addi 3 1
  andi 3 0xFFF
  emit (.memStore 4 1 seqAt (.reg 3))
  shli 3 4
  emit (.memStore 2 1 (plainBuf + 22) (.reg 3))
  li 2 plainBuf
  storeBytes 2 24 (ByteArray.mk #[0xAA, 0xAA, 0x03, 0, 0, 0,
    (ethertype >>> 8).toUInt8, ethertype.toUInt8])

/-- Encrypt the `r(12)`-byte plaintext frame at `plainBuf` and transmit it. -/
def sendReply (C : DevCcmp.CcmpLib) (data : LeanOS.Wifi.Tx.TxConfig) : ProgM Unit := do
  DevCcmp.callEncap C (.imm plainBuf) (.reg 12) (.imm Mlme.txMpdu) (.imm Handshake.tkAt)
    (.imm txPnAt) (.imm 0)
  let ok ← newLabel
  emit (.branch .ne 0 (.imm 0) ok)
  fail Fail.encap
  place ok
  mov 12 0
  sendMpduR data 1

/-- CCMP replay check (IEEE 802.11-2016 12.5.3.4.4): after a successful
decapsulation (r3 = key id), accept the frame only if its packet number is
greater than the last one accepted for that key, then record it. A frame the
access point retransmitted because it missed our ACK carries the same PN and
is dropped, so it is answered only once. Uses r0–r6. -/
def replayCheck (skip : Nat) : ProgM Unit := do
  li 6 lastPnTk
  let tk ← newLabel
  emit (.branch .eq 3 (.imm 0) tk)
  li 6 lastPnGtk
  place tk
  li 0 0
  emit (.memLoad 4 1 0 DevCcmp.rxPnAt)          -- new low
  emit (.memLoad 2 2 0 (DevCcmp.rxPnAt + 4))    -- new high
  emit (.memLoad 4 4 6 0)                       -- last low
  emit (.memLoad 2 5 6 4)                       -- last high
  let newer ← newLabel
  let dup ← newLabel
  emit (.branch .ltu 5 (.reg 2) newer)          -- last high < new high
  emit (.branch .ne 5 (.reg 2) dup)             -- last high > new high
  emit (.branch .ltu 4 (.reg 1) newer)          -- same high, last low < new low
  place dup
  printImm Tag.replay 0
  emit (.jump skip)
  place newer
  emit (.memStore 4 6 0 (.reg 1))
  emit (.memStore 2 6 4 (.reg 2))

/-- Answer ARP and ICMP echo for `us` microseconds of TSF time. -/
def respond (C : DevCcmp.CcmpLib) (data : LeanOS.Wifi.Tx.TxConfig) (us : UInt32) :
    ProgM Unit := do
  li 1 0
  r32 2 0x180
  emit (.memStore 4 1 startAt (.reg 2))
  emit (.memStore 4 1 arpCount (.imm 0))
  emit (.memStore 4 1 pingCount (.imm 0))
  emit (.memStore 4 1 udpCount (.imm 0))
  emit (.memLoad 4 2 1 DevDhcp.yiaddrAt)
  print Tag.listening 2
  let top ← newLabel
  let skip ← newLabel
  let out ← newLabel
  place top
  r32 6 0x180
  li 1 0
  emit (.memLoad 4 7 1 startAt)
  emit (.alu .sub 6 (.reg 7))
  emit (.branch .geu 6 (.imm us) out)
  Mlme.rxFrame 100
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
  -- requester (FromDS: SA = addr3)
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
  li 0 0
  emit (.memLoad 4 1 0 bodyAt)                  -- replayCheck clobbers r1
  -- LLC/SNAP, then dispatch on ethertype
  emit (.memLoad 1 3 1 0); emit (.branch .ne 3 (.imm 0xAA) skip)
  emit (.memLoad 1 3 1 1); emit (.branch .ne 3 (.imm 0xAA) skip)
  emit (.memLoad 1 3 1 6)
  emit (.memLoad 1 4 1 7)
  shli 3 8
  emit (.alu .or 3 (.reg 4))
  let notArp ← newLabel
  emit (.branch .ne 3 (.imm 0x0806) notArp)
  arp C data skip
  emit (.jump top)
  place notArp
  emit (.branch .ne 3 (.imm 0x0800) skip)
  -- IPv4: dispatch on the protocol byte (IP header at body + 8)
  emit (.memLoad 1 3 1 (8 + 9))
  let notIcmp ← newLabel
  emit (.branch .ne 3 (.imm 1) notIcmp)
  icmp C data skip
  emit (.jump top)
  place notIcmp
  emit (.branch .ne 3 (.imm 17) skip)
  udp C data skip
  emit (.jump top)
  place skip
  emit (.jump top)
  place out
  li 1 0
  emit (.memLoad 4 2 1 arpCount); print Tag.summaryArp 2
  emit (.memLoad 4 2 1 pingCount); print Tag.summaryPing 2
  emit (.memLoad 4 2 1 udpCount); print Tag.summaryUdp 2
where
  /-- ARP request (body+8) for our address → reply. -/
  arp (C : DevCcmp.CcmpLib) (data : LeanOS.Wifi.Tx.TxConfig) (skip : Nat) : ProgM Unit := do
    li 0 0
    emit (.memLoad 4 1 0 bodyAt)
    addi 1 8                                         -- ARP packet
    -- htype 1, ptype 0x0800, hlen 6, plen 4, op 1
    let hdr : Array UInt32 := #[0, 1, 8, 0, 6, 4, 0, 1]
    for h : k in [0:hdr.size] do
      emit (.memLoad 1 3 1 k.toUInt32)
      emit (.branch .ne 3 (.imm hdr[k]) skip)
    -- target protocol address (24..27) must be ours
    li 0 0
    emit (.memLoad 4 4 0 DevDhcp.yiaddrAt)
    emit (.memLoad 4 3 1 24)
    emit (.branch .ne 3 (.reg 4) skip)
    replyHeader 0x0806
    -- reply body at plainBuf + 32
    li 2 (plainBuf + 32)
    storeBytes 2 0 (ByteArray.mk #[0, 1, 8, 0, 6, 4, 0, 2])
    storeBytes 2 8 (ByteArray.mk Mlme.ourMac.data)
    li 0 0
    emit (.memLoad 4 4 0 DevDhcp.yiaddrAt)
    emit (.memStore 4 2 14 (.reg 4))
    -- target = requester's sender hardware/protocol address (bytes 8..17)
    li 0 0
    emit (.memLoad 4 1 0 bodyAt)
    addi 1 (8 + 8)
    addi 2 18
    li 3 10
    copyR 2 1 3
    li 12 (32 + 28)
    sendReply C data
    li 1 0
    emit (.memLoad 4 2 1 arpCount); addi 2 1; emit (.memStore 4 1 arpCount (.reg 2))
    print Tag.arpReplied 2
  /-- IPv4 ICMP echo request to our address → echo reply. -/
  icmp (C : DevCcmp.CcmpLib) (data : LeanOS.Wifi.Tx.TxConfig) (skip : Nat) : ProgM Unit := do
    li 0 0
    emit (.memLoad 4 1 0 bodyAt)
    addi 1 8                                         -- IP header
    emit (.memLoad 1 3 1 0)
    emit (.branch .ne 3 (.imm 0x45) skip)            -- IPv4, 20-byte header
    emit (.memLoad 1 3 1 9)
    emit (.branch .ne 3 (.imm 1) skip)               -- protocol ICMP
    li 0 0
    emit (.memLoad 4 4 0 DevDhcp.yiaddrAt)
    emit (.memLoad 4 3 1 16)
    emit (.branch .ne 3 (.reg 4) skip)               -- destination = us
    emit (.memLoad 1 3 1 20)
    emit (.branch .ne 3 (.imm 8) skip)               -- echo request
    -- total length (big-endian), bounded by the decrypted body
    emit (.memLoad 1 5 1 2)
    emit (.memLoad 1 6 1 3)
    shli 5 8
    emit (.alu .or 5 (.reg 6))
    emit (.branch .ltu 5 (.imm 28) skip)
    li 0 0
    emit (.memLoad 4 6 0 lenAt)
    emit (.alu .sub 6 (.imm 8))
    emit (.branch .ltu 6 (.reg 5) skip)
    emit (.branch .geu 5 (.imm 1500) skip)
    li 0 0
    emit (.memStore 4 0 (lenAt + 0) (.reg 5))       -- now: IP total length
    replyHeader 0x0800
    -- copy the datagram to plainBuf + 32
    li 0 0
    emit (.memLoad 4 1 0 bodyAt)
    addi 1 8
    li 2 (plainBuf + 32)
    emit (.memLoad 4 3 0 lenAt)
    copyR 2 1 3
    -- swap source (12) and destination (16) addresses
    li 2 (plainBuf + 32)
    emit (.memLoad 4 3 2 12)
    emit (.memLoad 4 4 2 16)
    emit (.memStore 4 2 12 (.reg 4))
    emit (.memStore 4 2 16 (.reg 3))
    -- ICMP type 0; checksum += 0x0800 (ones' complement)
    emit (.memStore 1 2 20 (.imm 0))
    emit (.memLoad 1 3 2 22)
    emit (.memLoad 1 4 2 23)
    shli 3 8
    emit (.alu .or 3 (.reg 4))
    addi 3 0x0800
    mov 4 3
    shri 4 16
    andi 3 0xFFFF
    emit (.alu .add 3 (.reg 4))
    mov 4 3
    andi 4 0xFF
    emit (.memStore 1 2 23 (.reg 4))
    shri 3 8
    emit (.memStore 1 2 22 (.reg 3))
    li 0 0
    emit (.memLoad 4 12 0 lenAt)
    addi 12 32
    sendReply C data
    li 1 0
    emit (.memLoad 4 2 1 pingCount); addi 2 1; emit (.memStore 4 1 pingCount (.reg 2))
    print Tag.pingReplied 2
  /-- IPv4 UDP datagram to our address, port 7 → echo (RFC 862). -/
  udp (C : DevCcmp.CcmpLib) (data : LeanOS.Wifi.Tx.TxConfig) (skip : Nat) : ProgM Unit := do
    li 0 0
    emit (.memLoad 4 1 0 bodyAt)
    addi 1 8                                         -- IP header
    emit (.memLoad 1 3 1 0)
    emit (.branch .ne 3 (.imm 0x45) skip)            -- IPv4, 20-byte header
    emit (.memLoad 1 3 1 6)
    andi 3 0x3F
    emit (.branch .ne 3 (.imm 0) skip)               -- not a fragment (MF, offset)
    emit (.memLoad 1 3 1 7)
    emit (.branch .ne 3 (.imm 0) skip)
    li 0 0
    emit (.memLoad 4 4 0 DevDhcp.yiaddrAt)
    emit (.memLoad 4 3 1 16)
    emit (.branch .ne 3 (.reg 4) skip)               -- destination = us
    emit (.memLoad 1 3 1 22)
    emit (.branch .ne 3 (.imm 0) skip)               -- destination port 7
    emit (.memLoad 1 3 1 23)
    emit (.branch .ne 3 (.imm 7) skip)
    -- total length (big-endian), bounded by the decrypted body
    emit (.memLoad 1 5 1 2)
    emit (.memLoad 1 6 1 3)
    shli 5 8
    emit (.alu .or 5 (.reg 6))
    emit (.branch .ltu 5 (.imm 28) skip)
    li 0 0
    emit (.memLoad 4 6 0 lenAt)
    emit (.alu .sub 6 (.imm 8))
    emit (.branch .ltu 6 (.reg 5) skip)
    emit (.branch .geu 5 (.imm 1500) skip)
    li 0 0
    emit (.memStore 4 0 (lenAt + 0) (.reg 5))       -- now: IP total length
    replyHeader 0x0800
    li 0 0
    emit (.memLoad 4 1 0 bodyAt)
    addi 1 8
    li 2 (plainBuf + 32)
    emit (.memLoad 4 3 0 lenAt)
    copyR 2 1 3
    -- swap source/destination addresses (12, 16) and ports (20, 22)
    li 2 (plainBuf + 32)
    emit (.memLoad 4 3 2 12)
    emit (.memLoad 4 4 2 16)
    emit (.memStore 4 2 12 (.reg 4))
    emit (.memStore 4 2 16 (.reg 3))
    emit (.memLoad 2 3 2 20)
    emit (.memLoad 2 4 2 22)
    emit (.memStore 2 2 20 (.reg 4))
    emit (.memStore 2 2 22 (.reg 3))
    li 0 0
    emit (.memLoad 4 12 0 lenAt)
    addi 12 32
    sendReply C data
    li 1 0
    emit (.memLoad 4 2 1 udpCount); addi 2 1; emit (.memStore 4 1 udpCount (.reg 2))
    print Tag.udpReplied 2

end LeanOS.Wifi.Responder

namespace LeanOS.Wifi.Responder
open LeanOS.Wifi.Bytecode LeanOS.Wifi.NPhy

/-- Connect, lease an address, then answer ARP/ping for `us` microseconds. -/
def connectAndServe (fw : Bcm43224.Firmware) (cfg : PhyCfg) (bssid pmk : ByteArray)
    (us : UInt32) : ProgM Unit :=
  Connect.connectDhcpThen fw cfg bssid pmk fun _ C data => respond C data us

end LeanOS.Wifi.Responder
