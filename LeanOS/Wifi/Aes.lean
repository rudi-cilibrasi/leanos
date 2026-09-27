import LeanOS.Wifi.Bytes

/-!
# AES-128, AES key wrap (RFC 3394) and AES-CCM (RFC 3610) for CCMP

* AES-128 block encrypt/decrypt (FIPS-197). The S-box is derived from its
  algebraic definition (multiplicative inverse in GF(2^8) plus the affine map)
  rather than typed in, and checked by the FIPS-197 known-answer test.
* RFC 3394 key wrap/unwrap with the default IV `A6A6A6A6A6A6A6A6`, used by
  WPA2 to protect the GTK in EAPOL-Key message 3 (key descriptor version 2).
* CCM with `M = 8` (MIC bytes) and `L = 2` (length bytes), i.e. the 13-byte
  nonce form used by IEEE 802.11 CCMP.

This is a straightforward table-free byte implementation; it is not hardened
against timing side channels.
-/

namespace LeanOS.Wifi.Aes

open LeanOS.Wifi.Bytes

/-! ## GF(2^8) and the S-box -/

@[inline] def xtime (b : UInt8) : UInt8 :=
  (b <<< 1) ^^^ (if b &&& 0x80 != 0 then 0x1b else 0)

/-- Multiplication in GF(2^8) modulo `x^8 + x^4 + x^3 + x + 1`. -/
def gmul (a b : UInt8) : UInt8 := Id.run do
  let mut x := a
  let mut y := b
  let mut acc : UInt8 := 0
  for _ in [0:8] do
    if y &&& 1 != 0 then acc := acc ^^^ x
    x := xtime x
    y := y >>> 1
  return acc

private def ginv (a : UInt8) : UInt8 := Id.run do
  -- a^254 = a^-1 (and 0 ↦ 0)
  let mut r : UInt8 := 1
  for _ in [0:254] do
    r := gmul r a
  return r

@[inline] private def rotl8 (x : UInt8) (n : UInt8) : UInt8 := (x <<< n) ||| (x >>> (8 - n))

/-- The AES S-box, computed from its definition. -/
def sbox : ByteArray := Id.run do
  let mut out := ByteArray.emptyWithCapacity 256
  for i in [0:256] do
    let b := ginv i.toUInt8
    out := out.push (b ^^^ rotl8 b 1 ^^^ rotl8 b 2 ^^^ rotl8 b 3 ^^^ rotl8 b 4 ^^^ 0x63)
  return out

/-- The inverse S-box. -/
def invSbox : ByteArray := Id.run do
  let mut out := zeros 256
  for i in [0:256] do
    out := out.set! (at! sbox i).toNat i.toUInt8
  return out

/-! ## Key schedule and block cipher -/

/-- Expanded AES-128 key: 11 round keys, 176 bytes. -/
structure Key where
  roundKeys : ByteArray

private def rcon (i : Nat) : UInt8 := Id.run do
  let mut r : UInt8 := 1
  for _ in [1:i] do
    r := xtime r
  return r

/-- Expand a 16-byte key (shorter keys are zero-padded, longer ones truncated). -/
def expandKey (key : ByteArray) : Key := Id.run do
  let mut w := (key ++ zeros 16).extract 0 16
  for i in [4:44] do
    let p := 4 * (i - 1)
    let mut t0 := at! w p
    let mut t1 := at! w (p + 1)
    let mut t2 := at! w (p + 2)
    let mut t3 := at! w (p + 3)
    if i % 4 == 0 then
      let s0 := at! sbox t1.toNat
      let s1 := at! sbox t2.toNat
      let s2 := at! sbox t3.toNat
      let s3 := at! sbox t0.toNat
      t0 := s0 ^^^ rcon (i / 4)
      t1 := s1
      t2 := s2
      t3 := s3
    let q := 4 * (i - 4)
    w := w.push (at! w q ^^^ t0) |>.push (at! w (q + 1) ^^^ t1)
      |>.push (at! w (q + 2) ^^^ t2) |>.push (at! w (q + 3) ^^^ t3)
  return { roundKeys := w }

@[inline] private def gen16 (f : Nat → UInt8) : ByteArray := Id.run do
  let mut out := ByteArray.emptyWithCapacity 16
  for i in [0:16] do
    out := out.push (f i)
  return out

private def addRoundKey (k : Key) (round : Nat) (s : ByteArray) : ByteArray :=
  gen16 fun i => at! s i ^^^ at! k.roundKeys (16 * round + i)

private def subBytes (box : ByteArray) (s : ByteArray) : ByteArray :=
  gen16 fun i => at! box (at! s i).toNat

-- State byte index is `r + 4 * c` (column-major, matching the input order).
private def shiftRows (s : ByteArray) : ByteArray :=
  gen16 fun i => let r := i % 4; let c := i / 4; at! s (r + 4 * ((c + r) % 4))

private def invShiftRows (s : ByteArray) : ByteArray :=
  gen16 fun i => let r := i % 4; let c := i / 4; at! s (r + 4 * ((c + 4 - r) % 4))

private def mixColumns (s : ByteArray) : ByteArray :=
  gen16 fun i =>
    let r := i % 4
    let c := 4 * (i / 4)
    let a := fun j => at! s (c + (r + j) % 4)
    gmul 2 (a 0) ^^^ gmul 3 (a 1) ^^^ a 2 ^^^ a 3

private def invMixColumns (s : ByteArray) : ByteArray :=
  gen16 fun i =>
    let r := i % 4
    let c := 4 * (i / 4)
    let a := fun j => at! s (c + (r + j) % 4)
    gmul 14 (a 0) ^^^ gmul 11 (a 1) ^^^ gmul 13 (a 2) ^^^ gmul 9 (a 3)

/-- Encrypt one 16-byte block. -/
def encryptBlock (k : Key) (block : ByteArray) : ByteArray := Id.run do
  let mut s := addRoundKey k 0 block
  for round in [1:10] do
    s := addRoundKey k round (mixColumns (shiftRows (subBytes sbox s)))
  return addRoundKey k 10 (shiftRows (subBytes sbox s))

/-- Decrypt one 16-byte block. -/
def decryptBlock (k : Key) (block : ByteArray) : ByteArray := Id.run do
  let mut s := addRoundKey k 10 block
  for j in [0:9] do
    let round := 9 - j
    s := invMixColumns (addRoundKey k round (subBytes invSbox (invShiftRows s)))
  return addRoundKey k 0 (subBytes invSbox (invShiftRows s))

/-- Convenience: AES-128 encrypt with a raw 16-byte key. -/
def encrypt (key block : ByteArray) : ByteArray := encryptBlock (expandKey key) block

/-- Convenience: AES-128 decrypt with a raw 16-byte key. -/
def decrypt (key block : ByteArray) : ByteArray := decryptBlock (expandKey key) block

/-! ## RFC 3394 key wrap -/

def defaultIV : UInt64 := 0xA6A6A6A6A6A6A6A6

/-- Wrap `plain` (a multiple of 8 bytes, at least 16) under `kek`. -/
def keyWrap (kek plain : ByteArray) : Option ByteArray := Id.run do
  if plain.size % 8 != 0 || plain.size < 16 then return none
  let k := expandKey kek
  let n := plain.size / 8
  let mut a := defaultIV
  let mut r : Array ByteArray := (List.range n).toArray.map fun i => slice plain (8 * i) 8
  for j in [0:6] do
    for i in [0:n] do
      let b := encryptBlock k (u64be a ++ r[i]!)
      a := getU64be b 0 ^^^ (n * j + i + 1).toUInt64
      r := r.set! i (slice b 8 8)
  return some (r.foldl (· ++ ·) (u64be a))

/-- Unwrap `wrapped` under `kek`; `none` if malformed or the integrity check fails. -/
def keyUnwrap (kek wrapped : ByteArray) : Option ByteArray := Id.run do
  if wrapped.size % 8 != 0 || wrapped.size < 24 then return none
  let k := expandKey kek
  let n := wrapped.size / 8 - 1
  let mut a := getU64be wrapped 0
  let mut r : Array ByteArray := (List.range n).toArray.map fun i => slice wrapped (8 * (i + 1)) 8
  for jj in [0:6] do
    let j := 5 - jj
    for ii in [0:n] do
      let i := n - 1 - ii
      let b := decryptBlock k (u64be (a ^^^ (n * j + i + 1).toUInt64) ++ r[i]!)
      a := getU64be b 0
      r := r.set! i (slice b 8 8)
  if a != defaultIV then return none
  return some (r.foldl (· ++ ·) ByteArray.empty)

/-! ## AES-CCM, M = 8, L = 2 (13-byte nonce) -/

/-- CBC-MAC tag `T` (first 8 bytes) over nonce, AAD and message. -/
private def ccmMac (k : Key) (nonce aad msg : ByteArray) : ByteArray := Id.run do
  -- B0 flags: Adata (0x40) | ((M-2)/2) << 3 | (L-1) = 0x40 | 0x18 | 0x01
  let b0 := (ByteArray.mk #[0x59] ++ nonce ++ u16be msg.size.toUInt16)
  let mut x := encryptBlock k b0
  let a := u16be aad.size.toUInt16 ++ aad
  let a := a ++ zeros ((16 - a.size % 16) % 16)
  for i in [0:a.size / 16] do
    x := encryptBlock k (Bytes.xor x (slice a (16 * i) 16))
  let m := msg ++ zeros ((16 - msg.size % 16) % 16)
  for i in [0:m.size / 16] do
    x := encryptBlock k (Bytes.xor x (slice m (16 * i) 16))
  return x.extract 0 8

/-- Counter block `A_i` keystream. -/
@[inline] private def ctrBlock (k : Key) (nonce : ByteArray) (i : Nat) : ByteArray :=
  encryptBlock k (ByteArray.mk #[0x01] ++ nonce ++ u16be i.toUInt16)

/-- CTR-mode transform (encryption = decryption) starting at counter 1. -/
private def ccmCtr (k : Key) (nonce data : ByteArray) : ByteArray := Id.run do
  let mut out := ByteArray.emptyWithCapacity data.size
  let blocks := (data.size + 15) / 16
  for i in [0:blocks] do
    out := out ++ Bytes.xor (slice data (16 * i) 16) (ctrBlock k nonce (i + 1))
  return out

/-- CCM encrypt: returns ciphertext followed by the 8-byte encrypted MIC. -/
def ccmEncrypt (key nonce aad msg : ByteArray) : ByteArray :=
  let k := expandKey key
  let t := ccmMac k nonce aad msg
  ccmCtr k nonce msg ++ Bytes.xor t (ctrBlock k nonce 0)

/-- CCM decrypt of ciphertext‖MIC; `none` if the MIC does not verify. -/
def ccmDecrypt (key nonce aad ctMic : ByteArray) : Option ByteArray :=
  if ctMic.size < 8 then none else
  let k := expandKey key
  let ct := ctMic.extract 0 (ctMic.size - 8)
  let mic := ctMic.extract (ctMic.size - 8) ctMic.size
  let msg := ccmCtr k nonce ct
  let t := ccmMac k nonce aad msg
  if ctEq (Bytes.xor t (ctrBlock k nonce 0)) mic then some msg else none

end LeanOS.Wifi.Aes
