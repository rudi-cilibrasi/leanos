import LeanOS.Wifi.Mac
import LeanOS.Wifi.Ieee80211

/-
Station management (MLME) building blocks as device programs: frame
templates built at generation time with the verified `Ieee80211` library,
copied into scratch RAM and patched at run time; frames received by PIO into
a scratch buffer and matched against generation-time expectations.
-/
namespace LeanOS.Wifi.Mlme

open LeanOS.Wifi.Bytecode LeanOS.Wifi.Bcm43224 LeanOS.Wifi.Mac

/-! ## Scratch layout -/

/-- Received frame: 24-byte receive header, 6-byte PLCP, then the MPDU. -/
def rxBuf : UInt32 := 0x1000
def rxHdr : UInt32 := 30
def rxMpdu : UInt32 := rxBuf + rxHdr
/-- Transmit buffer: TX descriptor header followed by the MPDU. -/
def txBuf : UInt32 := 0x3000
/-- Chosen BSSID (6 bytes). -/
def bssidAt : UInt32 := 0x0F00

/-- Our station address (SROM IL0 MAC of the Qotom card). -/
def ourMac : ByteArray := ByteArray.mk #[0x10, 0x0d, 0x7f, 0xc9, 0x75, 0xf1]
def ssidQuail : ByteArray := "QUAIL".toUTF8

namespace Tag
def found : UInt32 := 0x0C00
def bssid01 : UInt32 := 0x0C01
def bssid25 : UInt32 := 0x0C02
def rxLen : UInt32 := 0x0C03
def waitTimeout : UInt32 := 0x0C04
def gotFrame : UInt32 := 0x0C05
end Tag

/-- Copy generation-time `bytes` into scratch at `dst` (uses r0–r2). -/
def putBytes (name : String) (dst : UInt32) (bytes : ByteArray) : ProgM Unit := do
  let padded := bytes ++ ByteArray.mk (Array.replicate ((4 - bytes.size % 4) % 4) 0)
  let off ← addBlob name padded
  let n := (padded.size / 4).toUInt32
  if n == 0 then return
  li 0 0
  li 2 dst
  let top ← newLabel
  place top
  emit (.blobLoad32 1 0 off)
  emit (.memStore 4 2 0 (.reg 1))
  addi 2 4
  addi 0 1
  emit (.branch .ltu 0 (.imm n) top)

/-- Receive one frame into `rxBuf`, waiting up to `tries` ms. On return
r5 = MPDU length in bytes as reported by the receive header (0 on
timeout). Uses r0–r5. -/
def rxFrame (tries : UInt32) : ProgM Unit := do
  li 5 0
  let got ← newLabel
  let out ← newLabel
  li 4 tries
  let wait ← newLabel
  place wait
  r32 0 rxPioCtl
  andi 0 1
  emit (.branch .ne 0 (.imm 0) got)
  delay 1000
  emit (.alu .sub 4 (.imm 1))
  emit (.branch .ne 4 (.imm 0) wait)
  emit (.jump out)
  place got
  w32 rxPioCtl 1
  poll32 rxPioCtl 2 2 100 10 0x7F02
  r32 2 rxPioData
  li 3 rxBuf
  emit (.memStore 4 3 0 (.reg 2))
  -- first header word: received length (PLCP + MPDU incl. FCS) in low half
  mov 5 2
  andi 5 0xFFFF
  mov 1 5
  addi 1 (24 + 3)
  shri 1 2
  emit (.alu .sub 1 (.imm 1))
  let small ← newLabel
  emit (.branch .ltu 1 (.imm 1024) small)
  li 1 1024
  place small
  li 3 (rxBuf + 4)
  emit (.fifoIn rxPioData 3 1)
  w32 rxPioCtl 2
  -- MPDU length = received length - 6 (PLCP)
  emit (.alu .sub 5 (.imm 6))
  place out

/-- Branch to `miss` unless scratch bytes at `at_` equal `bytes`. Uses r0. -/
def matchBytes (at_ : UInt32) (bytes : ByteArray) (miss : Nat) : ProgM Unit := do
  li 0 0
  for h : k in [0:bytes.size] do
    emit (.memLoad 1 0 0 (at_ + k.toUInt32))
    emit (.branch .ne 0 (.imm bytes[k].toUInt32) miss)
    li 0 0

/-- Branch to `miss` unless `n` scratch bytes at `a` equal those at `b`.
Uses r0, r1. -/
def matchScratch (a b : UInt32) (n : Nat) (miss : Nat) : ProgM Unit := do
  for k in [0:n] do
    li 0 0
    emit (.memLoad 1 1 0 (a + k.toUInt32))
    emit (.memLoad 1 0 0 (b + k.toUInt32))
    emit (.branch .ne 0 (.reg 1) miss)

/-- Wait (up to `frames` received frames) for a beacon carrying SSID
`ssid` as its first element, and latch its BSSID at `bssidAt`. Fails with
`code` if none is seen. -/
def findSsid (ssid : ByteArray) (frames tries code : UInt32) : ProgM Unit := do
  li 6 frames
  let top ← newLabel
  let next ← newLabel
  let found ← newLabel
  place top
  emit (.branch .eq 6 (.imm 0) next)   -- exhausted: fall through to fail
  emit (.alu .sub 6 (.imm 1))
  rxFrame tries
  let skip ← newLabel
  emit (.branch .eq 5 (.imm 0) skip)
  matchBytes rxMpdu (ByteArray.mk #[0x80]) skip
  -- SSID element right after the 24-byte header and 12 fixed bytes
  matchBytes (rxMpdu + 36) (ByteArray.mk #[0, ssid.size.toUInt8] ++ ssid) skip
  emit (.jump found)
  place skip
  emit (.jump top)
  place next
  fail code
  place found
  -- BSSID = addr3 (offset 16)
  li 0 0
  emit (.memLoad 4 1 0 (rxMpdu + 16)); emit (.memStore 4 0 bssidAt (.reg 1))
  emit (.memLoad 2 1 0 (rxMpdu + 20)); emit (.memStore 2 0 (bssidAt + 4) (.reg 1))
  emit (.memLoad 2 1 0 bssidAt); print Tag.bssid01 1
  emit (.memLoad 4 1 0 (bssidAt + 2)); print Tag.bssid25 1
  printImm Tag.found 0

/-- Wait for a management frame of `subtype` addressed to us (addr1) from
the latched BSSID (addr2). Up to `frames` frames; `fail code` otherwise.
On success r5 = MPDU length. -/
def waitMgmt (subtype : UInt8) (frames tries code : UInt32) (onFail : Option Nat := none) :
    ProgM Unit := do
  li 6 frames
  let top ← newLabel
  let done ← newLabel
  let give ← newLabel
  place top
  emit (.branch .eq 6 (.imm 0) give)
  emit (.alu .sub 6 (.imm 1))
  rxFrame tries
  let skip ← newLabel
  emit (.branch .eq 5 (.imm 0) skip)
  matchBytes rxMpdu (ByteArray.mk #[subtype <<< 4]) skip
  matchBytes (rxMpdu + 4) ourMac skip
  matchScratch (rxMpdu + 10) bssidAt 6 skip
  print Tag.gotFrame 5
  emit (.jump done)
  place skip
  emit (.jump top)
  place give
  printImm Tag.waitTimeout subtype.toUInt32
  failOr onFail code
  place done

end LeanOS.Wifi.Mlme

namespace LeanOS.Wifi.Mlme
open LeanOS.Wifi.Bytecode LeanOS.Wifi.Bcm43224 LeanOS.Wifi.Mac
open LeanOS.Wifi.Ieee80211 LeanOS.Wifi.Bytes

/-- MPDU template area inside the transmit buffer: the caller-supplied
sender prepends its descriptor in front of `txMpdu`. -/
def txMpdu : UInt32 := txBuf + 0x100

/-- Write the latched BSSID into scratch at `at_` (6 bytes). Uses r0, r1. -/
def putBssid (at_ : UInt32) : ProgM Unit := do
  li 0 0
  for k in [0:6] do
    emit (.memLoad 1 1 0 (bssidAt + k.toUInt32))
    emit (.memStore 1 0 (at_ + k.toUInt32) (.reg 1))

namespace Fail
def noQuail : UInt32 := 0x7C01
def noAuth : UInt32 := 0x7C02
def authRejected : UInt32 := 0x7C03
def noAssoc : UInt32 := 0x7C04
def assocRejected : UInt32 := 0x7C05
end Fail

namespace Tag
def authOk : UInt32 := 0x0C10
def assocOk : UInt32 := 0x0C11
def aid : UInt32 := 0x0C12
def sent : UInt32 := 0x0C13
end Tag

/-- Open-system authentication then association with the latched BSSID.
`send len` must transmit the `len`-byte MPDU at `txMpdu` (length given as
a generation-time constant) to the BSSID and may clobber r0–r9. -/
def authAssoc (send : Nat → ProgM Unit) (tries : UInt32) (onFail : Option Nat := none) :
    ProgM Unit := do
  -- Authentication request (algorithm 0, sequence 1).
  let zero : Mac := replicate 6 0
  let auth := authRequest (ByteArray.mk ourMac.data) zero 0
  putBytes "auth" txMpdu auth
  putBssid (txMpdu + 4)
  putBssid (txMpdu + 16)
  send auth.size
  printImm Tag.sent 0xB0
  waitMgmt MgmtSubtype.auth 200 tries Fail.noAuth onFail
  -- algorithm 0, transaction 2, status 0
  let bad ← newLabel
  let ok ← newLabel
  matchBytes (rxMpdu + 24) (ByteArray.mk #[0, 0, 2, 0, 0, 0]) bad
  emit (.jump ok)
  place bad
  li 0 0
  emit (.memLoad 2 1 0 (rxMpdu + 28)); print 0x0C1F 1
  failOr onFail Fail.authRejected
  place ok
  printImm Tag.authOk 0
  -- Association request with the WPA2-PSK-CCMP RSN element.
  let cap : UInt16 := Capability.ess ||| Capability.privacy ||| Capability.shortSlot
  let assoc := assocRequest (ByteArray.mk ourMac.data) zero ssidQuail cap 10 1
  putBytes "assoc" txMpdu assoc
  putBssid (txMpdu + 4)
  putBssid (txMpdu + 16)
  send assoc.size
  printImm Tag.sent 0x00
  waitMgmt MgmtSubtype.assocResp 200 tries Fail.noAssoc onFail
  let bad2 ← newLabel
  let ok2 ← newLabel
  matchBytes (rxMpdu + 26) (ByteArray.mk #[0, 0]) bad2
  emit (.jump ok2)
  place bad2
  li 0 0
  emit (.memLoad 2 1 0 (rxMpdu + 26)); print 0x0C1E 1
  failOr onFail Fail.assocRejected
  place ok2
  li 0 0
  emit (.memLoad 2 1 0 (rxMpdu + 28)); andi 1 0x3FFF; print Tag.aid 1
  printImm Tag.assocOk 0

end LeanOS.Wifi.Mlme

namespace LeanOS.Wifi.Mlme
open LeanOS.Wifi.Bytecode LeanOS.Wifi.Bcm43224 LeanOS.Wifi.Mac

namespace Fail
def noEapol : UInt32 := 0x7C06
def dropped : UInt32 := 0x7C07
end Fail

/-- Scratch word holding the `waitEapol` start time. -/
def eapolDeadlineAt : UInt32 := 0x0F10

namespace Tag
def eapol : UInt32 := 0x0C20
def fromBss : UInt32 := 0x0C21
end Tag

/-- Wait (at most `frames` µs) for an unprotected data frame from the latched BSSID to us carrying
LLC/SNAP ethertype 0x888E. Accepts plain (24-byte header) and QoS (26-byte)
data. On success r7 = scratch address of the EAPOL (802.1X) header and
r8 = its length in bytes (MPDU length minus header, SNAP and FCS). -/
def waitEapol (frames tries : UInt32) (onFail : Option Nat := none) : ProgM Unit := do
  -- `frames` bounds the wait in microseconds of MAC TSF time (register
  -- 0x180), so the bound is the same under every executor.
  let top ← newLabel
  let done ← newLabel
  let give ← newLabel
  li 0 0
  r32 6 0x180
  emit (.memStore 4 0 eapolDeadlineAt (.reg 6))
  place top
  r32 6 0x180
  li 0 0
  emit (.memLoad 4 9 0 eapolDeadlineAt)
  emit (.alu .sub 6 (.reg 9))
  emit (.branch .geu 6 (.imm frames) give)
  rxFrame tries
  let skip ← newLabel
  emit (.branch .eq 5 (.imm 0) skip)
  -- type data (fc0 & 0x0C == 0x08), not protected (fc1 & 0x40 == 0)
  -- diagnostics: any frame from the BSSID addressed to us (fc word, addr1)
  let notUs ← newLabel
  matchScratch (rxMpdu + 10) bssidAt 6 notUs
  matchBytes (rxMpdu + 4) ourMac notUs
  li 0 0
  emit (.memLoad 4 1 0 rxMpdu); print Tag.fromBss 1
  andi 1 0xFF
  let kill ← newLabel
  emit (.branch .eq 1 (.imm 0xA0) kill)
  emit (.branch .eq 1 (.imm 0xC0) kill)
  emit (.jump notUs)
  place kill
  failOr onFail Fail.dropped
  place notUs
  li 0 0
  emit (.memLoad 1 1 0 rxMpdu)
  mov 2 1
  andi 2 0x0C
  emit (.branch .ne 2 (.imm 0x08) skip)
  emit (.memLoad 1 2 0 (rxMpdu + 1))
  andi 2 0x40
  emit (.branch .ne 2 (.imm 0) skip)
  matchBytes (rxMpdu + 4) ourMac skip
  matchScratch (rxMpdu + 10) bssidAt 6 skip
  -- header length 24, or 26 for QoS data (subtype bit 0x80)
  li 7 (rxMpdu + 24)
  andi 1 0x80
  let plain ← newLabel
  emit (.branch .eq 1 (.imm 0) plain)
  li 7 (rxMpdu + 26)
  place plain
  -- LLC/SNAP AA AA 03 00 00 00 88 8E
  let snap : Array UInt32 := #[0xAA, 0xAA, 0x03, 0, 0, 0, 0x88, 0x8E]
  for h : k in [0:snap.size] do
    emit (.memLoad 1 0 7 k.toUInt32)
    emit (.branch .ne 0 (.imm snap[k]) skip)
  addi 7 8
  -- r8 = MPDU length - (r7 - rxMpdu) - 4 (FCS)
  mov 8 5
  emit (.alu .add 8 (.imm rxMpdu))
  emit (.alu .sub 8 (.reg 7))
  emit (.alu .sub 8 (.imm 4))
  print Tag.eapol 8
  emit (.jump done)
  place skip
  emit (.jump top)
  place give
  failOr onFail Fail.noEapol
  place done

end LeanOS.Wifi.Mlme
