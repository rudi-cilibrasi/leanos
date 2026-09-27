import LeanOS.Wifi.Bytes

/-!
# SHA-1 and HMAC-SHA1 (FIPS 180-4, RFC 2104)

SHA-1 is only used here as the building block of HMAC-SHA1, which WPA2-PSK
needs for PBKDF2, the 802.11 PRF and the EAPOL-Key MIC (descriptor version 2).

The compression function works on `UInt32` words with an 80-entry message
schedule. `hashFrom` resumes from an intermediate state so HMAC can reuse
precomputed inner/outer pad states (important for PBKDF2's 4096 iterations).
-/

namespace LeanOS.Wifi.Sha1

open LeanOS.Wifi.Bytes

/-- Intermediate hash state `H0..H4`. -/
structure State where
  h0 : UInt32
  h1 : UInt32
  h2 : UInt32
  h3 : UInt32
  h4 : UInt32

def initState : State :=
  { h0 := 0x67452301, h1 := 0xEFCDAB89, h2 := 0x98BADCFE, h3 := 0x10325476, h4 := 0xC3D2E1F0 }

@[inline] private def rotl (x : UInt32) (n : UInt32) : UInt32 :=
  (x <<< n) ||| (x >>> (32 - n))

/-- Compress the 64-byte block of `block` starting at `off`. -/
def compress (s : State) (block : ByteArray) (off : Nat) : State := Id.run do
  let mut w : Array UInt32 := Array.emptyWithCapacity 80
  for i in [0:16] do
    w := w.push (getU32be block (off + 4 * i))
  for i in [16:80] do
    w := w.push (rotl (w[i - 3]! ^^^ w[i - 8]! ^^^ w[i - 14]! ^^^ w[i - 16]!) 1)
  let mut a := s.h0
  let mut b := s.h1
  let mut c := s.h2
  let mut d := s.h3
  let mut e := s.h4
  for i in [0:80] do
    let (f, k) :=
      if i < 20 then ((b &&& c) ||| ((~~~ b) &&& d), (0x5A827999 : UInt32))
      else if i < 40 then (b ^^^ c ^^^ d, (0x6ED9EBA1 : UInt32))
      else if i < 60 then ((b &&& c) ||| (b &&& d) ||| (c &&& d), (0x8F1BBCDC : UInt32))
      else (b ^^^ c ^^^ d, (0xCA62C1D6 : UInt32))
    let t := rotl a 5 + f + e + k + w[i]!
    e := d
    d := c
    c := rotl b 30
    b := a
    a := t
  return { h0 := s.h0 + a, h1 := s.h1 + b, h2 := s.h2 + c, h3 := s.h3 + d, h4 := s.h4 + e }

/-- Serialise a state as the 20-byte big-endian digest. -/
def State.digest (s : State) : ByteArray :=
  let out := ByteArray.emptyWithCapacity 20
  pushU32be (pushU32be (pushU32be (pushU32be (pushU32be out s.h0) s.h1) s.h2) s.h3) s.h4

/-- Hash `msg`, starting from state `s` that has already absorbed `prior`
bytes (`prior` must be a multiple of 64). Returns the 20-byte digest. -/
def hashFrom (s : State) (prior : Nat) (msg : ByteArray) : ByteArray := Id.run do
  let full := msg.size / 64
  let mut st := s
  for i in [0:full] do
    st := compress st msg (64 * i)
  -- Final block(s): remaining bytes, 0x80, zeros, 64-bit bit length.
  let rest := msg.extract (64 * full) msg.size
  let bitLen : UInt64 := ((prior + msg.size) * 8).toUInt64
  let padLen := if rest.size < 56 then 64 else 128
  let mut tail := rest.push 0x80
  while tail.size < padLen - 8 do
    tail := tail.push 0
  tail := tail ++ u64be bitLen
  st := compress st tail 0
  if padLen == 128 then
    st := compress st tail 64
  return st.digest

/-- SHA-1 digest (20 bytes). -/
def hash (msg : ByteArray) : ByteArray := hashFrom initState 0 msg

/-! ## HMAC-SHA1 -/

/-- Precomputed HMAC key: states after absorbing `K ⊕ ipad` and `K ⊕ opad`. -/
structure HmacKey where
  inner : State
  outer : State

def HmacKey.ofKey (key : ByteArray) : HmacKey :=
  let k := if key.size > 64 then hash key else key
  let k := k ++ zeros (64 - k.size)
  let ipad := ByteArray.mk (k.data.map (· ^^^ 0x36))
  let opad := ByteArray.mk (k.data.map (· ^^^ 0x5c))
  { inner := compress initState ipad 0, outer := compress initState opad 0 }

/-- HMAC with a precomputed key. -/
def HmacKey.mac (hk : HmacKey) (msg : ByteArray) : ByteArray :=
  hashFrom hk.outer 64 (hashFrom hk.inner 64 msg)

/-- HMAC-SHA1(key, msg), 20 bytes. -/
def hmac (key msg : ByteArray) : ByteArray :=
  (HmacKey.ofKey key).mac msg

end LeanOS.Wifi.Sha1
