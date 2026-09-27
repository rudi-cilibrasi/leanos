/-!
# Byte helpers for the WiFi protocol layer

Small, pure helpers over `ByteArray`: endian-aware integer get/put, slicing,
XOR, constant construction and hex encode/decode (used mostly by tests).

Out-of-range reads return `0` (via `get!`-style defaults); callers that parse
untrusted input check lengths explicitly before reading.
-/

namespace LeanOS.Wifi.Bytes

/-- Byte at `i`, or `0` when out of range. -/
@[inline] def at! (b : ByteArray) (i : Nat) : UInt8 :=
  if h : i < b.size then b[i] else 0

/-- `n` copies of byte `v`. -/
def replicate (n : Nat) (v : UInt8) : ByteArray := Id.run do
  let mut out := ByteArray.emptyWithCapacity n
  for _ in [0:n] do
    out := out.push v
  return out

/-- `n` zero bytes. -/
def zeros (n : Nat) : ByteArray := replicate n 0

/-- The sub-array `[start, start + len)`, clamped to the array. -/
def slice (b : ByteArray) (start len : Nat) : ByteArray :=
  b.extract start (start + len)

/-- The suffix starting at `start`. -/
def drop (b : ByteArray) (start : Nat) : ByteArray :=
  b.extract start b.size

/-- The prefix of length `n`. -/
def take (b : ByteArray) (n : Nat) : ByteArray :=
  b.extract 0 n

/-- Byte-wise XOR; the result has the length of the shorter input. -/
def xor (a b : ByteArray) : ByteArray := Id.run do
  let n := min a.size b.size
  let mut out := ByteArray.emptyWithCapacity n
  for i in [0:n] do
    out := out.push (at! a i ^^^ at! b i)
  return out

/-- Concatenate a list of byte arrays. -/
def concat (parts : List ByteArray) : ByteArray :=
  parts.foldl (· ++ ·) ByteArray.empty

/-- Lexicographic comparison (shorter prefix is smaller). -/
def lt (a b : ByteArray) : Bool := Id.run do
  let n := min a.size b.size
  for i in [0:n] do
    let x := at! a i
    let y := at! b i
    if x < y then return true
    if x > y then return false
  return a.size < b.size

/-- Structural equality of contents. -/
def beq (a b : ByteArray) : Bool :=
  a.size == b.size && a.data == b.data

/-- Constant-time-style equality (no early exit on contents). -/
def ctEq (a b : ByteArray) : Bool := Id.run do
  if a.size != b.size then return false
  let mut acc : UInt8 := 0
  for i in [0:a.size] do
    acc := acc ||| (at! a i ^^^ at! b i)
  return acc == 0

/-! ## Endian helpers -/

@[inline] def getU16be (b : ByteArray) (i : Nat) : UInt16 :=
  ((at! b i).toUInt16 <<< 8) ||| (at! b (i + 1)).toUInt16

@[inline] def getU16le (b : ByteArray) (i : Nat) : UInt16 :=
  ((at! b (i + 1)).toUInt16 <<< 8) ||| (at! b i).toUInt16

@[inline] def getU32be (b : ByteArray) (i : Nat) : UInt32 :=
  ((at! b i).toUInt32 <<< 24) ||| ((at! b (i + 1)).toUInt32 <<< 16) |||
    ((at! b (i + 2)).toUInt32 <<< 8) ||| (at! b (i + 3)).toUInt32

@[inline] def getU32le (b : ByteArray) (i : Nat) : UInt32 :=
  ((at! b (i + 3)).toUInt32 <<< 24) ||| ((at! b (i + 2)).toUInt32 <<< 16) |||
    ((at! b (i + 1)).toUInt32 <<< 8) ||| (at! b i).toUInt32

def getU64be (b : ByteArray) (i : Nat) : UInt64 :=
  ((getU32be b i).toUInt64 <<< 32) ||| (getU32be b (i + 4)).toUInt64

def getU64le (b : ByteArray) (i : Nat) : UInt64 :=
  ((getU32le b (i + 4)).toUInt64 <<< 32) ||| (getU32le b i).toUInt64

def u16be (v : UInt16) : ByteArray :=
  ByteArray.mk #[(v >>> 8).toUInt8, v.toUInt8]

def u16le (v : UInt16) : ByteArray :=
  ByteArray.mk #[v.toUInt8, (v >>> 8).toUInt8]

def u32be (v : UInt32) : ByteArray :=
  ByteArray.mk #[(v >>> 24).toUInt8, (v >>> 16).toUInt8, (v >>> 8).toUInt8, v.toUInt8]

def u32le (v : UInt32) : ByteArray :=
  ByteArray.mk #[v.toUInt8, (v >>> 8).toUInt8, (v >>> 16).toUInt8, (v >>> 24).toUInt8]

def u64be (v : UInt64) : ByteArray :=
  u32be (v >>> 32).toUInt32 ++ u32be v.toUInt32

def u64le (v : UInt64) : ByteArray :=
  u32le v.toUInt32 ++ u32le (v >>> 32).toUInt32

/-- Append a big-endian `UInt32` (hot-path helper for SHA-1 output). -/
@[inline] def pushU32be (b : ByteArray) (v : UInt32) : ByteArray :=
  b.push (v >>> 24).toUInt8 |>.push (v >>> 16).toUInt8 |>.push (v >>> 8).toUInt8
    |>.push v.toUInt8

/-- Overwrite `src.size` bytes of `dst` starting at `off` (bytes past the end are dropped). -/
def overwrite (dst : ByteArray) (off : Nat) (src : ByteArray) : ByteArray := Id.run do
  let mut out := dst
  for i in [0:src.size] do
    if off + i < out.size then
      out := out.set! (off + i) (at! src i)
  return out

/-! ## Hex -/

private def hexDigit (n : UInt8) : Char :=
  if n < 10 then Char.ofNat (48 + n.toNat) else Char.ofNat (87 + n.toNat)

/-- Lower-case hex encoding without separators. -/
def toHex (b : ByteArray) : String := Id.run do
  let mut s := ""
  for i in [0:b.size] do
    let v := at! b i
    s := (s.push (hexDigit (v >>> 4))).push (hexDigit (v &&& 0x0f))
  return s

private def hexVal (c : Char) : Option UInt8 :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - 48).toUInt8
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 87).toUInt8
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 55).toUInt8
  else none

/-- Decode hex; spaces, `:` and `-` separators are ignored. `none` on bad input. -/
def ofHex? (s : String) : Option ByteArray := do
  let digits := s.toList.filter (fun c => c != ' ' && c != ':' && c != '-' && c != '\n')
  if digits.length % 2 != 0 then none
  let rec go : List Char → ByteArray → Option ByteArray
    | hi :: lo :: rest, acc => do
        let h ← hexVal hi
        let l ← hexVal lo
        go rest (acc.push ((h <<< 4) ||| l))
    | _, acc => some acc
  go digits ByteArray.empty

/-- Decode hex, returning the empty array on malformed input (test convenience). -/
def ofHex (s : String) : ByteArray := (ofHex? s).getD ByteArray.empty

end LeanOS.Wifi.Bytes
