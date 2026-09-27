import LeanOS.Wifi.Mlme
import LeanOS.Wifi.DevCrypto
import LeanOS.Wifi.Eapol

/-
WPA2-PSK 4-way handshake (supplicant side) as a device program.

Message construction mirrors `LeanOS.Wifi.Eapol.Supplicant` (the verified
reference): message 2 carries our RSN element and SNonce with key info
version 2 | pairwise | MIC; message 4 carries version 2 | pairwise | MIC |
secure; both echo the authenticator's replay counter. Frames are generated
from reference-library templates and patched at run time; MICs, the PTK and
the GTK unwrap use `LeanOS.Wifi.DevCrypto`.

The PMK is supplied at generation time (derived from the passphrase by the
host generator) and travels in the program's data blob; program images are
secrets and must not be committed.
-/
namespace LeanOS.Wifi.Handshake

open LeanOS.Wifi.Bytecode LeanOS.Wifi.Bcm43224 LeanOS.Wifi.Mac LeanOS.Wifi.Mlme
open LeanOS.Wifi.DevCrypto LeanOS.Wifi.Ieee80211 LeanOS.Wifi.Bytes

/-! ## Scratch layout (0x0800–0x0BFF) -/

def pmkAt : UInt32 := 0x800
def aaAt : UInt32 := 0x820
def spaAt : UInt32 := 0x828
def anonceAt : UInt32 := 0x840
def snonceAt : UInt32 := 0x860
def ptkAt : UInt32 := 0x880       -- KCK 0x880, KEK 0x890, TK 0x8A0
def kckAt : UInt32 := ptkAt
def kekAt : UInt32 := ptkAt + 16
def tkAt : UInt32 := ptkAt + 32
def replayAt : UInt32 := 0x8B0
def gtkAt : UInt32 := 0x8C0
def gtkIdAt : UInt32 := 0x8D0
def eapolPtrAt : UInt32 := 0x8E0
def eapolLenAt : UInt32 := 0x8E4
def versionAt : UInt32 := 0x8E8
def retryAt : UInt32 := 0x8EC
def plainAt : UInt32 := 0x900
def entropyAt : UInt32 := 0x980
def entropy2At : UInt32 := 0x9E0

namespace Fail
def notMsg1 : UInt32 := 0x7D01
def notMsg3 : UInt32 := 0x7D02
def anonce : UInt32 := 0x7D03
def mic : UInt32 := 0x7D04
def unwrap : UInt32 := 0x7D05
def noGtk : UInt32 := 0x7D06
end Fail

namespace Tag
def msg1 : UInt32 := 0x0D01
def msg2Sent : UInt32 := 0x0D02
def msg3 : UInt32 := 0x0D03
def msg4Sent : UInt32 := 0x0D04
def gtkId : UInt32 := 0x0D05
def complete : UInt32 := 0x0D06
def msg1Again : UInt32 := 0x0D07
end Tag

/-- Copy `n` bytes from scratch `r(src) + off` to scratch `dst` (uses r0, r1). -/
def copyFrom (src : Reg) (off : UInt32) (dst : UInt32) (n : Nat) : ProgM Unit := do
  if src == 0 then li 0 0
  for k in [0:n] do
    emit (.memLoad 1 1 src (off + k.toUInt32))
    li 0 0
    emit (.memStore 1 0 (dst + k.toUInt32) (.reg 1))

/-- Save r7/r8 (EAPOL pointer and length from `waitEapol`). -/
def saveEapol : ProgM Unit := do
  li 0 0
  emit (.memStore 4 0 eapolPtrAt (.reg 7))
  emit (.memStore 4 0 eapolLenAt (.reg 8))

def loadEapol : ProgM Unit := do
  li 0 0
  emit (.memLoad 4 7 0 eapolPtrAt)
  emit (.memLoad 4 8 0 eapolLenAt)

/-- 64 bytes of timing entropy (TSF low word samples separated by PHY
register reads), hashed twice with SHA-1 into the 32-byte SNonce. This is a
lab-grade nonce source; a production supplicant needs a vetted RNG. -/
def makeSNonce (L : Lib) : ProgM Unit := do
  for k in [0:16] do
    r32 1 0x180
    phyRead 2 0x01
    emit (.alu .xor 1 (.reg 2))
    emit (.alu .rotl 1 (.imm (k.toUInt32 * 7 % 32)))
    li 0 0
    emit (.memStore 4 0 (entropyAt + 4 * k.toUInt32) (.reg 1))
    delay 3
  callSha1 L (.imm entropyAt) (.imm 64) (.imm snonceAt)
  li 0 0
  emit (.memLoad 1 1 0 entropyAt)
  emit (.alu .xor 1 (.imm 0x5A))
  emit (.memStore 1 0 entropyAt (.reg 1))
  callSha1 L (.imm entropyAt) (.imm 64) (.imm entropy2At)
  copyFrom 0 entropy2At (snonceAt + 20) 12
where
  phyRead (dst : Reg) (addr : UInt32) : ProgM Unit := do
    w16 d11PhyCtl addr
    r16 dst d11PhyData

/-- Data-frame template (to the AP, LLC/SNAP 888E) around EAPOL `eapol`;
returns the MPDU and the offset of the EAPOL packet inside it. -/
def eapolFrame (eapol : ByteArray) : ByteArray × Nat :=
  let zero : Mac := replicate 6 0
  (dataToAp zero (ByteArray.mk ourMac.data) zero 0 ethertypeEapol eapol, 24 + 8)

/-- Build, patch, sign and send one EAPOL-Key message whose generation-time
encoding is `tmpl` (zero replay counter, nonce and MIC). When `withNonce`,
the SNonce is patched in. -/
def sendKeyMsg (L : Lib) (send : Nat → ProgM Unit) (name : String) (tmpl : ByteArray)
    (withNonce : Bool) : ProgM Unit := do
  let (mpdu, eoff) := eapolFrame tmpl
  let e := txMpdu + eoff.toUInt32
  putBytes name txMpdu mpdu
  putBssid (txMpdu + 4)
  putBssid (txMpdu + 16)
  -- protocol version echoed from the authenticator
  li 0 0
  emit (.memLoad 1 1 0 versionAt)
  emit (.memStore 1 0 e (.reg 1))
  copyFrom 0 replayAt (e + 9) 8
  if withNonce then copyFrom 0 snonceAt (e + 17) 32
  callMicCompute L (.imm kckAt) (.imm e) (.imm tmpl.size.toUInt32)
  send mpdu.size

/-- Run the 4-way handshake after association. -/
def fourWay (L : Lib) (pmk : ByteArray) (rsnIe : ByteArray) (send : Nat → ProgM Unit)
    (tries : UInt32) : ProgM Unit := do
  putBytes "pmk" pmkAt pmk
  copyFrom 0 bssidAt aaAt 6
  putBytes "spa" spaAt (ByteArray.mk ourMac.data)
  -- Message 1: pairwise | ack, no MIC. A retransmitted message 1 while
  -- waiting for message 3 re-enters here (bounded by `retryAt`).
  li 0 0
  emit (.memStore 4 0 retryAt (.imm 4))
  waitEapol 400 tries
  saveEapol
  let handle1 ← newLabel
  place handle1
  emit (.memLoad 1 1 7 6)                 -- key info low byte
  mov 2 1
  andi 2 0x88
  let bad1 ← newLabel
  let ok1 ← newLabel
  emit (.branch .ne 2 (.imm 0x88) bad1)
  emit (.memLoad 1 1 7 5)                 -- key info high byte: MIC bit 0x01
  andi 1 0x01
  emit (.branch .eq 1 (.imm 0) ok1)
  place bad1
  fail Fail.notMsg1
  place ok1
  printImm Tag.msg1 0
  loadEapol
  copyFrom 7 0 versionAt 1
  loadEapol
  copyFrom 7 17 anonceAt 32
  loadEapol
  copyFrom 7 9 replayAt 8
  makeSNonce L
  callPtk L (.imm pmkAt) (.imm aaAt) (.imm spaAt) (.imm anonceAt) (.imm snonceAt) (.imm ptkAt)
  let msg2 : Eapol.KeyFrame :=
    { protocolVersion := 2,
      keyInfo := Eapol.KeyInfo.versionHmacSha1Aes ||| Eapol.KeyInfo.pairwise ||| Eapol.KeyInfo.mic,
      keyLength := 0, replayCounter := 0, nonce := zeros 32, keyData := rsnIe }
  sendKeyMsg L send "msg2" msg2.encode true
  printImm Tag.msg2Sent 0
  -- Message 3: pairwise | ack | MIC | install (| secure), encrypted key data.
  waitEapol 400 tries
  saveEapol
  emit (.memLoad 1 1 7 5)
  andi 1 0x01
  let ok3 ← newLabel
  emit (.branch .ne 1 (.imm 0) ok3)
  -- no MIC: the authenticator retransmitted message 1
  li 0 0
  emit (.memLoad 4 1 0 retryAt)
  let giveUp ← newLabel
  emit (.branch .eq 1 (.imm 0) giveUp)
  emit (.alu .sub 1 (.imm 1))
  emit (.memStore 4 0 retryAt (.reg 1))
  printImm Tag.msg1Again 0
  loadEapol
  emit (.jump handle1)
  place giveUp
  fail Fail.notMsg3
  place ok3
  printImm Tag.msg3 0
  -- ANonce must match message 1.
  let badA ← newLabel
  let okA ← newLabel
  for k in [0:32] do
    loadEapol
    emit (.memLoad 1 1 7 (17 + k.toUInt32))
    li 0 0
    emit (.memLoad 1 0 0 (anonceAt + k.toUInt32))
    emit (.branch .ne 0 (.reg 1) badA)
  emit (.jump okA)
  place badA
  fail Fail.anonce
  place okA
  loadEapol
  callMicVerify L (.imm kckAt) (.reg 7) (.reg 8)
  let okM ← newLabel
  emit (.branch .eq 0 (.imm 1) okM)
  fail Fail.mic
  place okM
  loadEapol
  copyFrom 7 9 replayAt 8
  -- Key data: big-endian length at 97, data at 99; unwrap with KEK.
  loadEapol
  emit (.memLoad 1 3 7 97)
  emit (.memLoad 1 4 7 98)
  shli 3 8
  emit (.alu .or 3 (.reg 4))
  addi 7 99
  li 0 0
  emit (.memStore 4 0 (eapolPtrAt + 8) (.reg 3))  -- wrapped length
  callKeyUnwrap L (.imm kekAt) (.reg 7) (.reg 3) (.imm plainAt)
  let okU ← newLabel
  emit (.branch .eq 0 (.imm 1) okU)
  fail Fail.unwrap
  place okU
  -- Walk key data elements for the GTK KDE (dd len 00 0f ac 01 id rsvd gtk).
  li 7 plainAt
  li 0 0
  emit (.memLoad 4 9 0 (eapolPtrAt + 8))
  emit (.alu .sub 9 (.imm 8))
  emit (.alu .add 9 (.imm plainAt))      -- r9 = end of plaintext
  let walk ← newLabel
  let next ← newLabel
  let found ← newLabel
  let none_ ← newLabel
  place walk
  mov 2 7
  addi 2 2
  emit (.branch .geu 2 (.reg 9) none_)
  emit (.memLoad 1 1 7 0)                 -- type
  emit (.memLoad 1 2 7 1)                 -- length
  emit (.branch .ne 1 (.imm 0xdd) next)
  emit (.branch .ltu 2 (.imm 22) next)
  let sel : Array UInt32 := #[0x00, 0x0f, 0xac, 0x01]
  for h : k in [0:sel.size] do
    emit (.memLoad 1 3 7 (2 + k.toUInt32))
    emit (.branch .ne 3 (.imm sel[k]) next)
  emit (.jump found)
  place next
  addi 7 2
  emit (.alu .add 7 (.reg 2))
  emit (.jump walk)
  place none_
  fail Fail.noGtk
  place found
  emit (.memLoad 1 1 7 6)
  andi 1 3
  li 0 0
  emit (.memStore 1 0 gtkIdAt (.reg 1))
  print Tag.gtkId 1
  copyFrom 7 8 gtkAt 16
  -- Message 4.
  let msg4 : Eapol.KeyFrame :=
    { protocolVersion := 2,
      keyInfo := Eapol.KeyInfo.versionHmacSha1Aes ||| Eapol.KeyInfo.pairwise |||
        Eapol.KeyInfo.mic ||| Eapol.KeyInfo.secure,
      keyLength := 0, replayCounter := 0, nonce := zeros 32, keyData := ByteArray.empty }
  sendKeyMsg L send "msg4" msg4.encode false
  printImm Tag.msg4Sent 0
  printImm Tag.complete 0

end LeanOS.Wifi.Handshake
