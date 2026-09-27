import LeanOS.Wifi.Mlme
import LeanOS.Wifi.Dhcp

/-!
# DHCP client building blocks as device-program subroutines

* `dhcpDiscover` / `dhcpRequest` write a complete plaintext data MPDU to the
  AP (ToDS, A1 = BSSID from `Mlme.bssidAt`, A2 = our MAC, A3 = broadcast)
  whose body is LLC/SNAP + the IPv4/UDP DHCP datagram of
  `LeanOS.Wifi.Dhcp.discover` / `request`. The frames are generation-time
  templates (in the program blob) patched at run time with the BSSID, the
  transaction id (`xidAt`) and, for the request, the offered address and
  server id (`yiaddrAt`, `serverIdAt`, filled by the offer's `dhcpParse`).
  The patched fields are outside the IPv4 header, so its checksum stays
  valid; the UDP checksum is 0 (none), as in the reference.
* `dhcpParse` validates a decrypted LLC/SNAP body as an IPv4/UDP DHCP reply
  with the same checks as `Dhcp.parseReply` (IPv4 version, header length,
  total length, header checksum, protocol 17, no fragment, UDP length, ports
  67 → 68, BOOTP length ≥ 240, magic cookie, well-formed options, op = 2)
  plus xid and client hardware address, and extracts yiaddr and options
  53, 54, 3, 1, 51 (first occurrence of each, as `Dhcp.Message.opt?`).

## Calling convention

Arguments in `r1, r2`, result in `r0`; every routine clobbers `r0–r14`
(never `r15`); no nested calls.

## Scratch (`0xF900–0xF97F`)

Addresses and the lease time are stored as raw network-order bytes (as in
the packet). The public slots are written only when `dhcpParse` accepts a
message (`r0 ≠ 0`); it works in a staging copy at `+0x40`.
-/

namespace LeanOS.Wifi.DevDhcp

open LeanOS.Wifi.Bytecode LeanOS.Wifi.Bytes

def dhcpLo : UInt32 := 0xF900
def dhcpHi : UInt32 := 0xF980
/-- Transaction id, 4 bytes as sent (big-endian). -/
def xidAt : UInt32 := 0xF900
/-- DHCP message type (option 53), one byte. -/
def typeAt : UInt32 := 0xF904
def yiaddrAt : UInt32 := 0xF908
def serverIdAt : UInt32 := 0xF90C
def routerAt : UInt32 := 0xF910
def subnetAt : UInt32 := 0xF914
def leaseAt : UInt32 := 0xF918
/-- Bit mask of options present with a usable value: `serverIdBit`, … -/
def presentAt : UInt32 := 0xF91C
def stage : UInt32 := 0x40

def serverIdBit : UInt32 := 1
def routerBit : UInt32 := 2
def subnetBit : UInt32 := 4
def leaseBit : UInt32 := 8
def typeBit : UInt32 := 16

/-! ## Emission helpers -/

private def ld (w : Nat) (d b : Reg) (off : UInt32) : ProgM Unit := emit (.memLoad w d b off)
private def st (w : Nat) (b : Reg) (off : UInt32) (s : Reg) : ProgM Unit :=
  emit (.memStore w b off (.reg s))
private def sti (w : Nat) (b : Reg) (off v : UInt32) : ProgM Unit :=
  emit (.memStore w b off (.imm v))
private def addR (d s : Reg) : ProgM Unit := emit (.alu .add d (.reg s))
private def orR (d s : Reg) : ProgM Unit := emit (.alu .or d (.reg s))
private def subi (d : Reg) (v : UInt32) : ProgM Unit := emit (.alu .sub d (.imm v))
private def bri (c : Cond) (a : Reg) (v : UInt32) (l : Nat) : ProgM Unit :=
  emit (.branch c a (.imm v) l)
private def brr (c : Cond) (a b : Reg) (l : Nat) : ProgM Unit := emit (.branch c a (.reg b) l)
private def jmp (l : Nat) : ProgM Unit := emit (.jump l)
private def ret : ProgM Unit := emit .ret

private def le32At (b : ByteArray) (i : Nat) : UInt32 :=
  (at! b i).toUInt32 ||| ((at! b (i + 1)).toUInt32 <<< 8) ||| ((at! b (i + 2)).toUInt32 <<< 16) |||
    ((at! b (i + 3)).toUInt32 <<< 24)

/-! ## Frame templates -/

/-- Offset of the xid inside the MPDU: header 24, LLC/SNAP 8, IPv4 20, UDP 8, BOOTP 4. -/
def xidOff : Nat := 24 + 8 + 20 + 8 + 4

private def toAp (mac : ByteArray) (datagram : ByteArray) : ByteArray :=
  Ieee80211.dataToAp (zeros 6) mac Ieee80211.broadcastMac 0 Ieee80211.ethertypeIPv4 datagram

def discoverFrame (mac : ByteArray) : ByteArray := toAp mac (Dhcp.discover mac 0)

private def markReq : UInt32 := 0x5EC0FFEE
private def markSrv : UInt32 := 0x5EC1FFEE

private def findSub (b pat : ByteArray) : Nat := Id.run do
  for i in [0:b.size + 1 - pat.size] do
    if beq (b.extract i (i + pat.size)) pat then return i
  return 0

/-- The request template and the offsets of the requested-IP and server-id
option values inside it. -/
def requestFrame (mac : ByteArray) : ByteArray × Nat × Nat :=
  let f := toAp mac (Dhcp.request mac 0 markReq markSrv)
  let o1 := findSub f (u32be markReq)
  let o2 := findSub f (u32be markSrv)
  (overwrite (overwrite f o1 (zeros 4)) o2 (zeros 4), o1, o2)

structure DhcpLib where
  discover : Nat
  request : Nat
  parse : Nat
  discoverLen : Nat
  requestLen : Nat

/-- Copy `tmpl` (in the blob) to `r1`: whole words by a loop, the tail by
immediate stores. Uses r2–r4. -/
private def copyTemplate (name : String) (tmpl : ByteArray) : ProgM Unit := do
  let words := tmpl.size / 4
  let off ← addBlob name (tmpl.extract 0 (4 * words))
  let top ← newLabel
  mov 2 1; li 3 0
  place top
  emit (.blobLoad32 4 3 off); st 4 2 0 4; addi 2 4; addi 3 1
  bri .ltu 3 words.toUInt32 top
  for i in [4 * words:tmpl.size] do
    sti 1 1 i.toUInt32 (at! tmpl i).toUInt32

/-- BSSID into A1 and the xid (uses r0, r2). -/
private def patchCommon : ProgM Unit := do
  li 0 0
  ld 4 2 0 Mlme.bssidAt; st 4 1 4 2; ld 2 2 0 (Mlme.bssidAt + 4); st 2 1 8 2
  ld 4 2 0 xidAt; st 4 1 xidOff.toUInt32 2

/-- `dhcpDiscover(r1 = dst)`: write the DISCOVER MPDU; `r0 :=` its length. -/
private def discoverBody (mac : ByteArray) : ProgM Unit := do
  let f := discoverFrame mac
  copyTemplate "dhcp-discover" f
  patchCommon
  li 0 f.size.toUInt32; ret

/-- `dhcpRequest(r1 = dst)`: write the REQUEST MPDU for the offer held in
`yiaddrAt`/`serverIdAt`; `r0 :=` its length. -/
private def requestBody (mac : ByteArray) : ProgM Unit := do
  let (f, o1, o2) := requestFrame mac
  copyTemplate "dhcp-request" f
  patchCommon
  ld 4 2 0 yiaddrAt; st 4 1 o1.toUInt32 2
  ld 4 2 0 serverIdAt; st 4 1 o2.toUInt32 2
  li 0 f.size.toUInt32; ret

/-- `dhcpParse(r1 = body, r2 = len)`: parse the LLC/SNAP body of a
decrypted data frame. `r0 :=` 2 (OFFER), 5 (ACK) or 6 (NAK) when it is a
valid DHCP reply for our xid and MAC carrying that message type; the slots
are then updated. Otherwise `r0 := 0` and the slots are unchanged. -/
private def parseBody (mac : ByteArray) : ProgM Unit := do
  let bad ← newLabel
  let ck ← newLabel
  let ckd ← newLabel
  let fold ← newLabel
  let fd ← newLabel
  let walk ← newLabel
  let adv ← newLabel
  let walked ← newLabel
  let notPad ← newLabel
  li 0 0
  for k in [1:8] do sti 4 0 (xidAt + stage + (4 * k).toUInt32) 0
  li 11 0; li 12 0
  bri .ltu 2 28 bad
  ld 4 3 1 0; bri .ne 3 0x0003AAAA bad
  ld 4 3 1 4; bri .ne 3 0x00080000 bad
  addi 1 8; subi 2 8
  -- IPv4 header
  ld 1 3 1 0; mov 4 3; shri 4 4; bri .ne 4 4 bad
  andi 3 0x0f; shli 3 2; bri .ltu 3 20 bad                  -- r3 = ihl
  ld 1 4 1 2; shli 4 8; ld 1 5 1 3; orR 4 5                 -- r4 = total length
  mov 5 3; addi 5 8; brr .ltu 4 5 bad
  brr .ltu 2 4 bad
  li 5 0; mov 6 1; mov 7 3; shri 7 1
  place ck
  bri .eq 7 0 ckd
  ld 1 8 6 0; shli 8 8; ld 1 9 6 1; orR 8 9; addR 5 8; addi 6 2; subi 7 1; jmp ck
  place ckd
  place fold
  mov 8 5; shri 8 16; bri .eq 8 0 fd
  andi 5 0xffff; addR 5 8; jmp fold
  place fd
  bri .ne 5 0xffff bad
  ld 1 5 1 9; bri .ne 5 17 bad
  ld 1 5 1 6; shli 5 8; ld 1 6 1 7; orR 5 6; andi 5 0x3fff; bri .ne 5 0 bad
  -- UDP
  mov 6 1; addR 6 3
  ld 1 7 6 4; shli 7 8; ld 1 8 6 5; orR 7 8                 -- r7 = UDP length
  bri .ltu 7 8 bad
  mov 8 3; addR 8 7; brr .ltu 4 8 bad
  ld 2 5 6 0; bri .ne 5 0x4300 bad                          -- source port 67
  ld 2 5 6 2; bri .ne 5 0x4400 bad                          -- destination port 68
  mov 13 6; addi 13 8; mov 14 7; subi 14 8                  -- BOOTP message, length
  bri .ltu 14 240 bad
  ld 4 5 13 236; bri .ne 5 0x63538263 bad
  -- Options
  mov 5 13; addi 5 240; mov 6 13; addR 6 14
  place walk
  brr .geu 5 6 walked
  ld 1 7 5 0
  bri .eq 7 255 walked
  bri .ne 7 0 notPad
  addi 5 1; jmp walk
  place notPad
  mov 8 5; addi 8 2; brr .ltu 6 8 bad
  ld 1 8 5 1; mov 9 5; addi 9 2; addR 9 8; brr .ltu 6 9 bad
  -- r8 = option length, r9 = next option
  let optCase (code : UInt32) (bit : UInt32) (slot : UInt32) (typeOpt : Bool) : ProgM Unit := do
    let next ← newLabel
    bri .ne 7 code next
    mov 10 11; andi 10 bit; bri .ne 10 0 adv
    ori 11 bit
    if typeOpt then
      bri .ne 8 1 adv
      ld 1 10 5 2; st 1 0 (slot + stage) 10
    else
      bri .ltu 8 4 adv
      ld 4 10 5 2; st 4 0 (slot + stage) 10
    ori 12 bit
    jmp adv
    place next
  optCase 53 typeBit typeAt true
  optCase 54 serverIdBit serverIdAt false
  optCase 3 routerBit routerAt false
  optCase 1 subnetBit subnetAt false
  optCase 51 leaseBit leaseAt false
  place adv
  mov 5 9; jmp walk
  place walked
  ld 1 5 13 0; bri .ne 5 2 bad                              -- op = BOOTREPLY
  ld 4 5 13 4; ld 4 6 0 xidAt; brr .ne 5 6 bad
  ld 4 5 13 28; bri .ne 5 (le32At mac 0) bad
  ld 2 5 13 32; bri .ne 5 (le32At mac 4 &&& 0xffff) bad
  mov 5 12; andi 5 typeBit; bri .eq 5 0 bad
  ld 1 5 0 (typeAt + stage)
  let okType ← newLabel
  bri .eq 5 2 okType; bri .eq 5 5 okType; bri .eq 5 6 okType
  jmp bad
  place okType
  ld 4 6 13 16; st 4 0 (yiaddrAt + stage) 6
  st 4 0 (presentAt + stage) 12
  for k in [1:8] do
    ld 4 6 0 (xidAt + stage + (4 * k).toUInt32); st 4 0 (xidAt + (4 * k).toUInt32) 6
  mov 0 5; ret
  place bad
  li 0 0; ret

/-- Emit `jump over; <bodies>; over:` for station address `mac`. -/
def install (mac : ByteArray := ByteArray.mk Mlme.ourMac.data) : ProgM DhcpLib := do
  let over ← newLabel
  let d ← newLabel
  let r ← newLabel
  let p ← newLabel
  jmp over
  place d; discoverBody mac
  place r; requestBody mac
  place p; parseBody mac
  place over
  return { discover := d, request := r, parse := p, discoverLen := (discoverFrame mac).size,
           requestLen := (requestFrame mac).1.size }

/-- Write the DISCOVER MPDU at `dst`; `r0 :=` length. -/
def callDiscover (D : DhcpLib) (dst : Operand) : ProgM Unit := do
  emit (.alu .mov 1 dst); emit (.call D.discover)

/-- Write the REQUEST MPDU at `dst`; `r0 :=` length. -/
def callRequest (D : DhcpLib) (dst : Operand) : ProgM Unit := do
  emit (.alu .mov 1 dst); emit (.call D.request)

/-- Parse a decrypted LLC/SNAP body; `r0 :=` message type or 0. -/
def callParse (D : DhcpLib) (body len : Operand) : ProgM Unit := do
  emit (.alu .mov 1 body)
  match len with
  | .reg 2 => pure ()
  | l => emit (.alu .mov 2 l)
  emit (.call D.parse)

end LeanOS.Wifi.DevDhcp
