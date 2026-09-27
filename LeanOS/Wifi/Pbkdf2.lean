import LeanOS.Wifi.Sha1

/-!
# PBKDF2-HMAC-SHA1 (RFC 8018 / RFC 2898) and the WPA2 passphrase-to-PMK mapping

`pmkOfPassphrase` implements IEEE 802.11-2016 J.4.1:
`PMK = PBKDF2(HMAC-SHA1, passphrase, ssid, 4096, 256 bits)`.
-/

namespace LeanOS.Wifi.Pbkdf2

open LeanOS.Wifi.Bytes LeanOS.Wifi.Sha1

/-- One output block `T_i = U_1 ⊕ … ⊕ U_c`. -/
private def block (hk : HmacKey) (salt : ByteArray) (iterations : Nat) (index : UInt32) :
    ByteArray := Id.run do
  let mut u := hk.mac (salt ++ u32be index)
  let mut t := u
  for _ in [1:iterations] do
    u := hk.mac u
    t := Bytes.xor t u
  return t

/-- PBKDF2-HMAC-SHA1 producing `dkLen` bytes. -/
def pbkdf2 (password salt : ByteArray) (iterations dkLen : Nat) : ByteArray := Id.run do
  let hk := HmacKey.ofKey password
  let blocks := (dkLen + 19) / 20
  let mut out := ByteArray.emptyWithCapacity (blocks * 20)
  for i in [1:blocks + 1] do
    out := out ++ block hk salt iterations i.toUInt32
  return out.extract 0 dkLen

/-- WPA2-PSK: 32-byte PMK from an ASCII passphrase (8..63 chars) and SSID. -/
def pmkOfPassphrase (passphrase ssid : ByteArray) : ByteArray :=
  pbkdf2 passphrase ssid 4096 32

end LeanOS.Wifi.Pbkdf2
