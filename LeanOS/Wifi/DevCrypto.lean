import LeanOS.Wifi.Bytecode
import LeanOS.Wifi.Aes

/-!
# WPA2-PSK supplicant crypto as device-program subroutines

The in-kernel WiFi executor cannot run ordinary Lean code, so the
cryptography a WPA2-PSK supplicant needs at run time (the 4-way handshake)
is written here as bytecode subroutines over the executor's 64 KiB scratch
RAM. `tests/WifiDevCrypto.lean` runs every routine in the hosted simulator
(`LeanOS.Wifi.Sim`) and compares the results with the reference library
(`LeanOS.Wifi.Sha1`, `Aes`, `Eapol`).

## Using the library

`install` emits every routine body once (behind a jump, so it may be placed
anywhere in straight-line code) and returns a `Lib` of routine labels:

```
let L ← DevCrypto.install
DevCrypto.callPtk L (.imm pmk) (.imm aa) (.imm spa) (.imm anonce) (.imm snonce) (.imm out)
```

Alternatively `Lib.alloc` + `Lib.emitBodies` place the bodies explicitly
(e.g. after the program's final `halt`).

## Calling convention

* Arguments are passed in `r1, r2, …` (addresses and lengths in bytes);
  a result flag, when there is one, is returned in `r0`.
* `r15` is never read or written by any routine.
* Unless a routine lists a narrower set, it clobbers `r0–r14`. The narrower
  sets are part of the contract and are relied on internally:
  * leaf routines (`memcpy`, `memcmp`, `sha1Init`, `sha1Compress`,
    `aesInit`, `aesExpandKey`, `aesEncrypt`, `aesDecrypt`) touch only
    `r0–r9`;
  * `sha1Final`, `sha1` and `keyUnwrap` use `r0–r14`.
* The `callX` helpers load their operands into `r1, r2, …` in order, so a
  register operand must not name an argument register that an earlier
  operand of the same call has already overwritten.
* A call from the top level uses at most 4 return-stack entries, including
  the caller's own `call` (e.g. `ptk`, tail-jumping to `prf` → `hmac` →
  `sha1Final` → `sha1Compress`): well inside the executor's 16.
* Addresses are plain scratch byte offsets; no alignment is required.
  Input and output buffers must not overlap unless a routine says so.

## Reserved scratch region

`0xF000–0xF7FF` (`reservedLo`..`reservedHi`) holds tables, working buffers and
the routines' saved arguments; callers must not keep data there across
calls. Layout (see the constants below): S-box, inverse S-box, SHA-1 message
schedule / state / padding buffer, HMAC pad block and digests, AES states and
round keys, the PTK PRF input, and the variable slots. `0xF7FC` holds a flag
recording that the AES tables have been written (`aesExpandKey` writes them
on first use; scratch starts zeroed).

## Limits

* SHA-1 / HMAC message lengths: `(prior + len) * 8 < 2^32` (any length that
  fits in scratch).
* HMAC keys longer than 64 bytes are first hashed (RFC 2104).
* Key unwrap: wrapped length a multiple of 8 and at least 24; no upper bound
  other than scratch space.
-/

namespace LeanOS.Wifi.DevCrypto

open LeanOS.Wifi.Bytecode

/-! ## Scratch layout -/

def reservedLo : UInt32 := 0xF000
def reservedHi : UInt32 := 0xF800

def sboxAddr : UInt32 := 0xF000
def invSboxAddr : UInt32 := 0xF100
/-- SHA-1 message schedule `W[0..80)`, 320 bytes. -/
def shaW : UInt32 := 0xF200
/-- SHA-1 chaining state `H0..H4` (native little-endian words), 20 bytes. -/
def shaH : UInt32 := 0xF340
/-- SHA-1 final-block padding buffer, 128 bytes. -/
def shaBuf : UInt32 := 0xF360
/-- HMAC `K ⊕ ipad` / `K ⊕ opad` block, 64 bytes. -/
def hmacPad : UInt32 := 0xF3E0
/-- HMAC inner digest, 20 bytes. -/
def hmacInner : UInt32 := 0xF420
/-- Digest of an over-long HMAC key, 20 bytes. -/
def hmacKeyHash : UInt32 := 0xF440
/-- PRF block output, 20 bytes. -/
def prfOut : UInt32 := 0xF460
/-- Saved received MIC during `micVerify`, 16 bytes. -/
def micSave : UInt32 := 0xF480
/-- Computed HMAC for the MIC routines, 20 bytes. -/
def micCalc : UInt32 := 0xF490
/-- AES working states. -/
def aesA : UInt32 := 0xF4C0
def aesB : UInt32 := 0xF4D0
/-- Key-unwrap working block `A ‖ R[i]`, 16 bytes. -/
def unwrapBlk : UInt32 := 0xF4E0
/-- AES-128 round keys, 176 bytes. -/
def aesRk : UInt32 := 0xF500
/-- PTK PRF input `label ‖ 0 ‖ data ‖ counter`, 100 bytes. -/
def ptkMsg : UInt32 := 0xF5C0
/-- Saved-argument slots (32-bit each). -/
def vars : UInt32 := 0xF780
def tablesFlag : UInt32 := 0xF7FC
def tablesMagic : UInt32 := 0x584F4253 -- "SBOX"

private def var (k : Nat) : UInt32 := vars + (4 * k).toUInt32

/-! ## Emission helpers -/

private def ld (w : Nat) (d b : Reg) (off : UInt32) : ProgM Unit := emit (.memLoad w d b off)
private def st (w : Nat) (b : Reg) (off : UInt32) (s : Reg) : ProgM Unit :=
  emit (.memStore w b off (.reg s))
private def sti (w : Nat) (b : Reg) (off v : UInt32) : ProgM Unit :=
  emit (.memStore w b off (.imm v))
private def xorR (d s : Reg) : ProgM Unit := emit (.alu .xor d (.reg s))
private def addR (d s : Reg) : ProgM Unit := emit (.alu .add d (.reg s))
private def subR (d s : Reg) : ProgM Unit := emit (.alu .sub d (.reg s))
private def orR (d s : Reg) : ProgM Unit := emit (.alu .or d (.reg s))
private def andR (d s : Reg) : ProgM Unit := emit (.alu .and d (.reg s))
private def mulR (d s : Reg) : ProgM Unit := emit (.alu .mul d (.reg s))
private def xori (d : Reg) (v : UInt32) : ProgM Unit := emit (.alu .xor d (.imm v))
private def subi (d : Reg) (v : UInt32) : ProgM Unit := emit (.alu .sub d (.imm v))
private def muli (d : Reg) (v : UInt32) : ProgM Unit := emit (.alu .mul d (.imm v))
private def rotli (d : Reg) (v : UInt32) : ProgM Unit := emit (.alu .rotl d (.imm v))
private def bri (c : Cond) (a : Reg) (v : UInt32) (l : Nat) : ProgM Unit :=
  emit (.branch c a (.imm v) l)
private def brr (c : Cond) (a b : Reg) (l : Nat) : ProgM Unit := emit (.branch c a (.reg b) l)
private def jmp (l : Nat) : ProgM Unit := emit (.jump l)
private def callL (l : Nat) : ProgM Unit := emit (.call l)
private def ret : ProgM Unit := emit .ret

private def le32At (b : ByteArray) (i : Nat) : UInt32 :=
  let g (k : Nat) : UInt32 := (b.get! (i + k)).toUInt32
  g 0 ||| (g 1 <<< 8) ||| (g 2 <<< 16) ||| (g 3 <<< 24)

/-- Emit stores writing `bytes` to `r(base) + addr` (4-byte words, then a
byte tail). Straight-line; clobbers nothing. -/
def storeBytes (base : Reg) (addr : UInt32) (bytes : ByteArray) : ProgM Unit := do
  let words := bytes.size / 4
  for k in [0:words] do
    sti 4 base (addr + (4 * k).toUInt32) (le32At bytes (4 * k))
  for i in [4 * words:bytes.size] do
    sti 1 base (addr + i.toUInt32) (bytes.get! i).toUInt32

/-- Byte-swap `x` in place (big ↔ little endian); `t` is a temporary. -/
private def bswap (x t : Reg) : ProgM Unit := do
  mov t x; andi t 0x00FF00FF; rotli t 24
  andi x 0xFF00FF00; rotli x 8; orR x t

/-- Four packed GF(2^8) doublings of `y`; `t` is a temporary. -/
private def xtime4 (y t : Reg) : ProgM Unit := do
  mov t y; shri t 7; andi t 0x01010101; muli t 0x1b
  andi y 0x7f7f7f7f; shli y 1; xorR y t

/-! ## Routine labels -/

structure Lib where
  memcpy : Nat
  memcmp : Nat
  sha1Init : Nat
  sha1Compress : Nat
  sha1Final : Nat
  sha1 : Nat
  hmac : Nat
  prf : Nat
  ptk : Nat
  micCompute : Nat
  micVerify : Nat
  aesInit : Nat
  aesExpandKey : Nat
  aesEncrypt : Nat
  aesDecrypt : Nat
  keyUnwrap : Nat

def Lib.alloc : ProgM Lib := do
  return { memcpy := ← newLabel, memcmp := ← newLabel, sha1Init := ← newLabel,
           sha1Compress := ← newLabel, sha1Final := ← newLabel, sha1 := ← newLabel,
           hmac := ← newLabel, prf := ← newLabel, ptk := ← newLabel,
           micCompute := ← newLabel, micVerify := ← newLabel, aesInit := ← newLabel,
           aesExpandKey := ← newLabel, aesEncrypt := ← newLabel, aesDecrypt := ← newLabel,
           keyUnwrap := ← newLabel }

/-! ## Memory helpers -/

/-- `memcpy(r1 = src, r2 = dst, r3 = len)`: forward copy (words, then bytes).
Clobbers `r0–r3`. -/
private def memcpyBody : ProgM Unit := do
  let wtop ← newLabel
  let btop ← newLabel
  let done ← newLabel
  place wtop
  bri .ltu 3 4 btop
  ld 4 0 1 0; st 4 2 0 0; addi 1 4; addi 2 4; subi 3 4; jmp wtop
  place btop
  bri .eq 3 0 done
  ld 1 0 1 0; st 1 2 0 0; addi 1 1; addi 2 1; subi 3 1; jmp btop
  place done
  ret

/-- `memcmp(r1 = a, r2 = b, r3 = len)`: `r0 := 1` iff `a < b` as unsigned
byte strings (lexicographic), else `0`. Clobbers `r0–r5`. -/
private def memcmpBody : ProgM Unit := do
  let top ← newLabel
  let yes ← newLabel
  let no ← newLabel
  place top
  bri .eq 3 0 no
  ld 1 4 1 0; ld 1 5 2 0
  brr .ltu 4 5 yes
  brr .ltu 5 4 no
  addi 1 1; addi 2 1; subi 3 1; jmp top
  place yes; li 0 1; ret
  place no; li 0 0; ret

/-! ## SHA-1 (FIPS 180-4) -/

private def sha1Iv : List UInt32 := [0x67452301, 0xEFCDAB89, 0x98BADCFE, 0x10325476, 0xC3D2E1F0]

/-- `sha1Init()`: reset the chaining state. Clobbers `r0`. -/
private def sha1InitBody : ProgM Unit := do
  li 0 0
  for h in sha1Iv, k in [0:5] do
    sti 4 0 (shaH + (4 * k).toUInt32) h
  ret

/-- `sha1Compress(r1 = block)`: absorb the 64-byte block at `r1`.
Preserves `r1`; clobbers `r0`, `r2–r9`. Fully unrolled. -/
private def sha1CompressBody : ProgM Unit := do
  li 2 0
  let w (i : Nat) : UInt32 := shaW + (4 * i).toUInt32
  for i in [0:16] do
    ld 4 8 1 (4 * i).toUInt32; bswap 8 9; st 4 2 (w i) 8
  for i in [16:80] do
    ld 4 8 2 (w (i - 3)); ld 4 9 2 (w (i - 8)); xorR 8 9
    ld 4 9 2 (w (i - 14)); xorR 8 9; ld 4 9 2 (w (i - 16)); xorR 8 9
    rotli 8 1; st 4 2 (w i) 8
  for k in [0:5] do
    ld 4 (3 + k) 2 (shaH + (4 * k).toUInt32)
  -- Registers holding a, b, c, d, e; renamed instead of moved each round.
  let mut rs : Array Reg := #[3, 4, 5, 6, 7]
  for i in [0:80] do
    let a := rs[0]!
    let b := rs[1]!
    let c := rs[2]!
    let d := rs[3]!
    let e := rs[4]!
    let kconst : UInt32 :=
      if i < 20 then 0x5A827999 else if i < 40 then 0x6ED9EBA1
      else if i < 60 then 0x8F1BBCDC else 0xCA62C1D6
    if i < 20 then
      -- ch(b, c, d) = d ^ (b & (c ^ d))
      mov 8 c; xorR 8 d; andR 8 b; xorR 8 d
    else if i < 40 || i ≥ 60 then
      mov 8 b; xorR 8 c; xorR 8 d
    else
      -- maj(b, c, d) = (b & c) | (d & (b | c))
      mov 8 b; orR 8 c; andR 8 d; mov 9 b; andR 9 c; orR 8 9
    addR e 8
    mov 8 a; rotli 8 5; addR e 8
    ld 4 8 2 (w i); addR e 8
    addi e kconst
    rotli b 30
    rs := #[e, a, b, c, d]
  for k in [0:5] do
    ld 4 8 2 (shaH + (4 * k).toUInt32); addR 8 (3 + k); st 4 2 (shaH + (4 * k).toUInt32) 8
  ret


/-- `sha1Final(r1 = msg, r2 = len, r3 = dst, r4 = prior)`: absorb the
message, pad it as the tail of a stream that already absorbed `prior` bytes
(a multiple of 64) and write the 20-byte big-endian digest to `r3`.
`dst` may overlap `msg`. Clobbers `r0–r14`. -/
private def sha1FinalBody (L : Lib) : ProgM Unit := do
  let blk ← newLabel
  let tail ← newLabel
  let two ← newLabel
  let out ← newLabel
  mov 10 1; mov 11 2; mov 12 3
  mov 13 4; addR 13 2; shli 13 3 -- total length in bits
  place blk
  bri .ltu 11 64 tail
  mov 1 10; callL L.sha1Compress; addi 10 64; subi 11 64; jmp blk
  place tail
  li 14 0
  for k in [0:32] do sti 4 14 (shaBuf + (4 * k).toUInt32) 0
  mov 1 10; li 2 shaBuf; mov 3 11; callL L.memcpy
  mov 0 11; sti 1 0 shaBuf 0x80
  mov 0 13; bswap 0 1
  bri .geu 11 56 two
  st 4 14 (shaBuf + 60) 0; li 1 shaBuf; callL L.sha1Compress; jmp out
  place two
  st 4 14 (shaBuf + 124) 0
  li 1 shaBuf; callL L.sha1Compress
  li 1 (shaBuf + 64); callL L.sha1Compress
  place out
  for k in [0:5] do
    ld 4 0 14 (shaH + (4 * k).toUInt32); bswap 0 1; st 4 12 (4 * k).toUInt32 0
  ret

/-- `sha1(r1 = msg, r2 = len, r3 = dst)`: 20-byte digest. Clobbers `r0–r14`. -/
private def sha1Body (L : Lib) : ProgM Unit := do
  callL L.sha1Init
  li 4 0
  jmp L.sha1Final

/-! ## HMAC-SHA1 (RFC 2104) and the 802.11 PRF -/

/-- `hmac(r1 = key, r2 = keyLen, r3 = msg, r4 = msgLen, r5 = dst)`:
20-byte HMAC-SHA1. Keys longer than 64 bytes are hashed first. `dst` may
overlap `msg` or the key. Clobbers `r0–r14`; uses variable slots 0–2. -/
private def hmacBody (L : Lib) : ProgM Unit := do
  let short ← newLabel
  li 0 0; st 4 0 (var 0) 3; st 4 0 (var 1) 4; st 4 0 (var 2) 5
  bri .ltu 2 65 short
  li 3 hmacKeyHash; callL L.sha1
  li 1 hmacKeyHash; li 2 20
  place short
  li 0 0
  for k in [0:16] do sti 4 0 (hmacPad + (4 * k).toUInt32) 0
  mov 3 2; li 2 hmacPad; callL L.memcpy
  let xorPad (v : UInt32) : ProgM Unit := do
    li 0 0
    for k in [0:16] do
      ld 4 1 0 (hmacPad + (4 * k).toUInt32); xori 1 v; st 4 0 (hmacPad + (4 * k).toUInt32) 1
  xorPad 0x36363636
  callL L.sha1Init; li 1 hmacPad; callL L.sha1Compress
  li 0 0; ld 4 1 0 (var 0); ld 4 2 0 (var 1); li 3 hmacInner; li 4 64; callL L.sha1Final
  xorPad 0x6a6a6a6a -- ipad → opad (0x36 ^ 0x5c)
  callL L.sha1Init; li 1 hmacPad; callL L.sha1Compress
  li 1 hmacInner; li 2 20; li 0 0; ld 4 3 0 (var 2); li 4 64
  jmp L.sha1Final

/-- `prf(r1 = key, r2 = keyLen, r3 = prefix, r4 = prefixLen, r5 = dst,
r6 = outLen)`: IEEE 802.11 PRF, the concatenation of
`HMAC-SHA1(key, prefix ‖ i)` for `i = 0, 1, …` truncated to `outLen` bytes.
`prefix` is `label ‖ 0x00 ‖ data`; the byte at `prefix + prefixLen` must be
writable (it receives the counter `i`). Clobbers `r0–r14`; uses variable
slots 3–10. -/
private def prfBody (L : Lib) : ProgM Unit := do
  let loop ← newLabel
  let go ← newLabel
  let done ← newLabel
  li 0 0
  st 4 0 (var 3) 1; st 4 0 (var 4) 2; st 4 0 (var 5) 3; st 4 0 (var 6) 4
  st 4 0 (var 7) 5; st 4 0 (var 8) 6; sti 4 0 (var 9) 0; sti 4 0 (var 10) 0
  place loop
  li 0 0; ld 4 1 0 (var 10); ld 4 2 0 (var 8); brr .geu 1 2 done
  ld 4 1 0 (var 5); ld 4 2 0 (var 6); addR 1 2; ld 4 3 0 (var 9); st 1 1 0 3
  ld 4 1 0 (var 3); ld 4 2 0 (var 4); ld 4 3 0 (var 5); ld 4 4 0 (var 6); addi 4 1
  li 5 prfOut; callL L.hmac
  li 0 0; ld 4 4 0 (var 8); ld 4 5 0 (var 10); subR 4 5
  li 3 20; brr .geu 4 3 go; mov 3 4
  place go
  li 1 prfOut; ld 4 2 0 (var 7); addR 2 5
  addR 5 3; st 4 0 (var 10) 5
  callL L.memcpy
  li 0 0; ld 4 1 0 (var 9); addi 1 1; st 4 0 (var 9) 1
  jmp loop
  place done
  ret

def ptkLabel : ByteArray := "Pairwise key expansion".toUTF8.push 0

/-- `ptk(r1 = pmk, r2 = aa, r3 = spa, r4 = anonce, r5 = snonce, r6 = dst)`:
`PTK = PRF-384(PMK, "Pairwise key expansion", Min(AA,SPA) ‖ Max(AA,SPA) ‖
Min(ANonce,SNonce) ‖ Max(ANonce,SNonce))`, 48 bytes `KCK ‖ KEK ‖ TK` at
`dst`. PMK 32 bytes, MACs 6, nonces 32; the comparisons are done at run
time. Clobbers `r0–r14`; uses variable slot 11. -/
private def ptkBody (L : Lib) : ProgM Unit := do
  let k1 ← newLabel
  let k2 ← newLabel
  li 0 0; st 4 0 (var 11) 6
  mov 10 1; mov 11 2; mov 12 3; mov 13 4; mov 14 5
  storeBytes 0 ptkMsg ptkLabel
  let pre := ptkMsg + ptkLabel.size.toUInt32
  mov 1 11; mov 2 12; li 3 6; callL L.memcmp
  bri .ne 0 0 k1
  mov 0 11; mov 11 12; mov 12 0
  place k1
  mov 1 11; li 2 pre; li 3 6; callL L.memcpy
  mov 1 12; li 2 (pre + 6); li 3 6; callL L.memcpy
  mov 1 13; mov 2 14; li 3 32; callL L.memcmp
  bri .ne 0 0 k2
  mov 0 13; mov 13 14; mov 14 0
  place k2
  mov 1 13; li 2 (pre + 12); li 3 32; callL L.memcpy
  mov 1 14; li 2 (pre + 44); li 3 32; callL L.memcpy
  mov 1 10; li 2 32; li 3 ptkMsg; li 4 (pre + 76 - ptkMsg)
  li 0 0; ld 4 5 0 (var 11); li 6 48
  jmp L.prf

/-! ## EAPOL-Key MIC (key descriptor version 2: HMAC-SHA1-128) -/

/-- Offset of the 16-byte MIC field in an EAPOL packet (`Eapol.micOffset`). -/
def micOff : UInt32 := 81

/-- `micCompute(r1 = kck, r2 = frame, r3 = len)`: zero the MIC field of the
EAPOL packet at `r2` (`len` bytes, header included), compute
HMAC-SHA1-128(KCK[16], packet) and store it into the MIC field.
Clobbers `r0–r14`; uses variable slot 12. -/
private def micComputeBody (L : Lib) : ProgM Unit := do
  for k in [0:4] do sti 4 2 (micOff + (4 * k).toUInt32) 0
  li 0 0; st 4 0 (var 12) 2
  mov 4 3; mov 3 2; li 2 16; li 5 micCalc; callL L.hmac
  li 0 0; ld 4 1 0 (var 12)
  for k in [0:4] do
    ld 4 2 0 (micCalc + (4 * k).toUInt32); st 4 1 (micOff + (4 * k).toUInt32) 2
  ret

/-- `micVerify(r1 = kck, r2 = frame, r3 = avail)`: `r0 := 1` iff the MIC of
the received EAPOL packet at `r2` is valid, else `0`. The MAC covers
`4 + bodyLength` bytes (from the header); the packet is rejected when that
exceeds `avail` or does not reach past the MIC field. The frame is left
unchanged. The comparison has no early exit. Clobbers `r0–r14`; uses
variable slot 12. -/
private def micVerifyBody (L : Lib) : ProgM Unit := do
  let bad ← newLabel
  ld 1 4 2 2; shli 4 8; ld 1 5 2 3; orR 4 5; addi 4 4
  brr .ltu 3 4 bad
  bri .ltu 4 (micOff + 16) bad
  li 0 0; st 4 0 (var 12) 2
  for k in [0:4] do
    ld 4 5 2 (micOff + (4 * k).toUInt32); st 4 0 (micSave + (4 * k).toUInt32) 5
    sti 4 2 (micOff + (4 * k).toUInt32) 0
  mov 3 2; li 2 16; li 5 micCalc; callL L.hmac
  li 0 0; ld 4 1 0 (var 12); li 2 0
  for k in [0:4] do
    ld 4 3 0 (micSave + (4 * k).toUInt32); st 4 1 (micOff + (4 * k).toUInt32) 3
    ld 4 4 0 (micCalc + (4 * k).toUInt32); xorR 3 4; orR 2 3
  bri .ne 2 0 bad
  li 0 1; ret
  place bad
  li 0 0; ret

/-! ## AES-128 (FIPS-197) -/

/-- `aesInit()`: write the S-box and inverse S-box tables (taken from the
reference `Aes.sbox`, which is derived from the GF(2^8) definition) and set
the tables flag. Clobbers `r0`. -/
private def aesInitBody : ProgM Unit := do
  li 0 0
  storeBytes 0 sboxAddr Aes.sbox
  storeBytes 0 invSboxAddr Aes.invSbox
  sti 4 0 tablesFlag tablesMagic
  ret

private def rconOf (n : Nat) : UInt32 :=
  [0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 0x40, 0x80, 0x1b, 0x36].getD (n - 1) 0

/-- `aesExpandKey(r1 = key)`: expand the 16-byte key at `r1` into the
reserved round-key buffer (writing the S-box tables first if needed).
Preserves `r1`; clobbers `r0`, `r3`, `r4`, `r9`. -/
private def aesExpandKeyBody (L : Lib) : ProgM Unit := do
  let ok ← newLabel
  li 0 0; ld 4 9 0 tablesFlag; bri .eq 9 tablesMagic ok
  callL L.aesInit
  place ok
  li 0 0
  let rk (i : Nat) : UInt32 := aesRk + (4 * i).toUInt32
  for k in [0:4] do
    ld 4 3 1 (4 * k).toUInt32; st 4 0 (rk k) 3
  for i in [4:44] do
    if i % 4 == 0 then
      -- temp := SubWord(RotWord(w[i-1])) ^ Rcon (bytes in little-endian order)
      let p := rk (i - 1)
      ld 1 3 0 (p + 1); ld 1 3 3 sboxAddr
      ld 1 4 0 (p + 2); ld 1 4 4 sboxAddr; shli 4 8; orR 3 4
      ld 1 4 0 (p + 3); ld 1 4 4 sboxAddr; shli 4 16; orR 3 4
      ld 1 4 0 p; ld 1 4 4 sboxAddr; shli 4 24; orR 3 4
      xori 3 (rconOf (i / 4))
    -- otherwise r3 still holds w[i-1]
    ld 4 4 0 (rk (i - 4)); xorR 3 4; st 4 0 (rk i) 3
  ret

/-- SubBytes+ShiftRows (or the inverses) from `aesA` into `aesB`, byte-wise
through the table at `box`. Uses `r0 = 0`, clobbers `r3`. -/
private def subShift (box : UInt32) (inv : Bool) : ProgM Unit := do
  for c in [0:4] do
    for r in [0:4] do
      let sc := if inv then (c + 4 - r) % 4 else (c + r) % 4
      ld 1 3 0 (aesA + (r + 4 * sc).toUInt32); ld 1 3 3 box
      st 1 0 (aesB + (r + 4 * c).toUInt32) 3

/-- MixColumns of the column word in `r3` (byte `i` of the column in bits
`8i`) into `r5`; clobbers `r4`, `r6`. -/
private def mixCol : ProgM Unit := do
  mov 4 3; rotli 4 24          -- a_{i+1}
  mov 5 3; xorR 5 4; xtime4 5 6 -- 2(a_i ^ a_{i+1})
  xorR 5 4; rotli 4 24; xorR 5 4; rotli 4 24; xorR 5 4

/-- InvMixColumns of `r3` into `r5` as MixColumns after the
`[5 0 4 0]`-circulant pre-step; clobbers `r3`, `r4`, `r6`. -/
private def invMixCol : ProgM Unit := do
  mov 4 3; rotli 4 16; xorR 4 3; xtime4 4 6; xtime4 4 6; xorR 3 4
  mixCol

private def rkAt (round c : Nat) : UInt32 := aesRk + (16 * round + 4 * c).toUInt32

/-- `aesEncrypt(r1 = in, r2 = out)`: encrypt one 16-byte block with the
expanded key. `in` and `out` may be equal. Preserves `r1`, `r2`; clobbers
`r0`, `r3–r6`. -/
private def aesEncryptBody : ProgM Unit := do
  li 0 0
  for c in [0:4] do
    ld 4 3 1 (4 * c).toUInt32; ld 4 4 0 (rkAt 0 c); xorR 3 4; st 4 0 (aesA + (4 * c).toUInt32) 3
  for round in [1:10] do
    subShift sboxAddr false
    for c in [0:4] do
      ld 4 3 0 (aesB + (4 * c).toUInt32); mixCol
      ld 4 4 0 (rkAt round c); xorR 5 4; st 4 0 (aesA + (4 * c).toUInt32) 5
  subShift sboxAddr false
  for c in [0:4] do
    ld 4 3 0 (aesB + (4 * c).toUInt32); ld 4 4 0 (rkAt 10 c); xorR 3 4
    st 4 2 (4 * c).toUInt32 3
  ret

/-- `aesDecrypt(r1 = in, r2 = out)`: decrypt one 16-byte block with the
expanded key (inverse cipher). `in` and `out` may be equal. Preserves `r1`,
`r2`; clobbers `r0`, `r3–r6`. -/
private def aesDecryptBody : ProgM Unit := do
  li 0 0
  for c in [0:4] do
    ld 4 3 1 (4 * c).toUInt32; ld 4 4 0 (rkAt 10 c); xorR 3 4; st 4 0 (aesA + (4 * c).toUInt32) 3
  for j in [0:9] do
    let round := 9 - j
    subShift invSboxAddr true
    for c in [0:4] do
      ld 4 3 0 (aesB + (4 * c).toUInt32); ld 4 4 0 (rkAt round c); xorR 3 4
      invMixCol; st 4 0 (aesA + (4 * c).toUInt32) 5
  subShift invSboxAddr true
  for c in [0:4] do
    ld 4 3 0 (aesB + (4 * c).toUInt32); ld 4 4 0 (rkAt 0 c); xorR 3 4
    st 4 2 (4 * c).toUInt32 3
  ret

/-! ## AES key unwrap (RFC 3394) -/

/-- `keyUnwrap(r1 = kek, r2 = wrapped, r3 = len, r4 = dst)`: unwrap the
`len`-byte ciphertext (a multiple of 8, at least 24) under the 16-byte KEK
into `len - 8` bytes at `dst`. `r0 := 1` when the integrity check value is
`A6A6A6A6A6A6A6A6`; otherwise `r0 := 0` and `dst` is zeroed (or untouched
when `len` is malformed). `dst` must not overlap `wrapped`. Clobbers
`r0–r14`; replaces the expanded AES key. -/
private def keyUnwrapBody (L : Lib) : ProgM Unit := do
  let fail0 ← newLabel
  let jl ← newLabel
  let il ← newLabel
  let check ← newLabel
  let bad ← newLabel
  let zl ← newLabel
  mov 0 3; andi 0 7; bri .ne 0 0 fail0
  bri .ltu 3 24 fail0
  mov 10 4; mov 11 3; shri 11 3; subi 11 1 -- r10 = dst, r11 = n
  li 0 0
  ld 4 5 2 0; st 4 0 unwrapBlk 5; ld 4 5 2 4; st 4 0 (unwrapBlk + 4) 5
  mov 12 1
  mov 1 2; addi 1 8; mov 2 10; mov 3 11; shli 3 3; callL L.memcpy
  mov 1 12; callL L.aesExpandKey
  let rAddr : ProgM Unit := do mov 8 13; subi 8 1; shli 8 3; addR 8 10 -- r8 = &R[i]
  li 12 5 -- j
  place jl
  mov 13 11 -- i + 1, from n down to 1
  place il
  mov 14 11; mulR 14 12; addR 14 13 -- t = n*j + i + 1
  li 0 0; ld 4 5 0 (unwrapBlk + 4); mov 6 14; bswap 6 7; xorR 5 6; st 4 0 (unwrapBlk + 4) 5
  rAddr
  ld 4 5 8 0; st 4 0 (unwrapBlk + 8) 5; ld 4 5 8 4; st 4 0 (unwrapBlk + 12) 5
  li 1 unwrapBlk; li 2 unwrapBlk; callL L.aesDecrypt
  li 0 0; rAddr
  ld 4 5 0 (unwrapBlk + 8); st 4 8 0 5; ld 4 5 0 (unwrapBlk + 12); st 4 8 4 5
  subi 13 1; bri .ne 13 0 il
  bri .eq 12 0 check
  subi 12 1; jmp jl
  place check
  li 0 0
  ld 4 5 0 unwrapBlk; bri .ne 5 0xA6A6A6A6 bad
  ld 4 5 0 (unwrapBlk + 4); bri .ne 5 0xA6A6A6A6 bad
  li 0 1; ret
  place bad
  mov 13 11; shli 13 3; mov 8 10
  place zl
  bri .eq 13 0 fail0
  sti 1 8 0 0; addi 8 1; subi 13 1; jmp zl
  place fail0
  li 0 0; ret

/-! ## Placement and call helpers -/

/-- Place every routine body at its label. Control must not fall into the
emitted code (place it after a `halt`/`jump`, or use `install`). -/
def Lib.emitBodies (L : Lib) : ProgM Unit := do
  place L.memcpy; memcpyBody
  place L.memcmp; memcmpBody
  place L.sha1Init; sha1InitBody
  place L.sha1Compress; sha1CompressBody
  place L.sha1Final; sha1FinalBody L
  place L.sha1; sha1Body L
  place L.hmac; hmacBody L
  place L.prf; prfBody L
  place L.ptk; ptkBody L
  place L.micCompute; micComputeBody L
  place L.micVerify; micVerifyBody L
  place L.aesInit; aesInitBody
  place L.aesExpandKey; aesExpandKeyBody L
  place L.aesEncrypt; aesEncryptBody
  place L.aesDecrypt; aesDecryptBody
  place L.keyUnwrap; keyUnwrapBody L

/-- Emit `jump over; <all routine bodies>; over:` and return the labels. -/
def install : ProgM Lib := do
  let L ← Lib.alloc
  let over ← newLabel
  jmp over
  L.emitBodies
  place over
  return L

private def setArgs (args : List Operand) : ProgM Unit := do
  for a in args, r in [1:args.length + 1] do
    match a with
    | .reg s => if s != r then mov r s
    | .imm v => li r v

/-- SHA-1: `dst[20] := SHA1(msg[len])`. -/
def callSha1 (L : Lib) (msg len dst : Operand) : ProgM Unit := do
  setArgs [msg, len, dst]; callL L.sha1

/-- Reset the SHA-1 state (streaming use with `callSha1Compress`/`callSha1Final`). -/
def callSha1Init (L : Lib) : ProgM Unit := callL L.sha1Init

/-- Absorb one 64-byte block. -/
def callSha1Compress (L : Lib) (block : Operand) : ProgM Unit := do
  setArgs [block]; callL L.sha1Compress

/-- Finish a stream that already absorbed `prior` bytes (multiple of 64). -/
def callSha1Final (L : Lib) (msg len dst prior : Operand) : ProgM Unit := do
  setArgs [msg, len, dst, prior]; callL L.sha1Final

/-- `dst[20] := HMAC-SHA1(key[keyLen], msg[msgLen])`. -/
def callHmac (L : Lib) (key keyLen msg msgLen dst : Operand) : ProgM Unit := do
  setArgs [key, keyLen, msg, msgLen, dst]; callL L.hmac

/-- `dst[outLen] := PRF(key, prefix)`; the byte after the prefix is overwritten. -/
def callPrf (L : Lib) (key keyLen pfx pfxLen dst outLen : Operand) : ProgM Unit := do
  setArgs [key, keyLen, pfx, pfxLen, dst, outLen]; callL L.prf

/-- `dst[48] := KCK ‖ KEK ‖ TK` from PMK, AA, SPA, ANonce, SNonce. -/
def callPtk (L : Lib) (pmk aa spa anonce snonce dst : Operand) : ProgM Unit := do
  setArgs [pmk, aa, spa, anonce, snonce, dst]; callL L.ptk

/-- Write the EAPOL-Key MIC of `frame[len]` computed with `kck[16]`. -/
def callMicCompute (L : Lib) (kck frame len : Operand) : ProgM Unit := do
  setArgs [kck, frame, len]; callL L.micCompute

/-- `r0 := 1` iff the EAPOL-Key MIC of the received `frame` (`avail` bytes) is valid. -/
def callMicVerify (L : Lib) (kck frame avail : Operand) : ProgM Unit := do
  setArgs [kck, frame, avail]; callL L.micVerify

/-- Expand the 16-byte AES key at `key`. -/
def callAesExpandKey (L : Lib) (key : Operand) : ProgM Unit := do
  setArgs [key]; callL L.aesExpandKey

/-- Encrypt one block with the expanded key. -/
def callAesEncrypt (L : Lib) (inp out : Operand) : ProgM Unit := do
  setArgs [inp, out]; callL L.aesEncrypt

/-- Decrypt one block with the expanded key. -/
def callAesDecrypt (L : Lib) (inp out : Operand) : ProgM Unit := do
  setArgs [inp, out]; callL L.aesDecrypt

/-- RFC 3394 unwrap; `r0 := 1` on integrity success. -/
def callKeyUnwrap (L : Lib) (kek wrapped len dst : Operand) : ProgM Unit := do
  setArgs [kek, wrapped, len, dst]; callL L.keyUnwrap

end LeanOS.Wifi.DevCrypto
