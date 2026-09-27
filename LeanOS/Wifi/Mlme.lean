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
def waitMgmt (subtype : UInt8) (frames tries code : UInt32) : ProgM Unit := do
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
  fail code
  place done

end LeanOS.Wifi.Mlme
