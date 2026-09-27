import LeanOS.Wifi.DevCrypto

/-!
# CCMP (IEEE 802.11-2016 12.5.3) as device-program subroutines

Encapsulation and decapsulation of data MPDUs with CCMP (AES-128 CCM,
`M = 8`, `L = 2`) over scratch RAM, built on `LeanOS.Wifi.DevCrypto`'s AES.
The byte layout, AAD and nonce construction follow
`LeanOS.Wifi.Ieee80211.ccmpEncap` / `ccmpDecap` exactly (checked in the
simulator by `tests/WifiDevCcmp.lean`):

* header length from the frame control field: 24, `+6` with ToDS and FromDS
  (A4), `+2` for QoS data subtypes (QoS control);
* CCMP header `PN0 PN1 0 (0x20 | keyId << 6) PN2 PN3 PN4 PN5`;
* nonce `priority ‖ A2 ‖ PN5..PN0`, priority = QoS TID (0 without QoS);
* AAD: FC with subtype bits 4–6, Retry, PwrMgt and MoreData masked,
  Protected set and (QoS) Order masked; A1 A2 A3; sequence control with the
  sequence number masked; A4 if present; QoS control masked to the TID.

## Calling convention

As in `DevCrypto`: arguments in `r1, r2, …`, results in `r0` (and `r1–r3`
for `ccmpDecap`), `r15` untouched, every routine clobbers `r0–r14`, and the
expanded AES key is replaced. Call depth: a call from the top level uses at
most 3 return-stack entries.

## Scratch

`0xF800–0xF8BF` (`ccmpLo`..`ccmpHi`) holds the CTR block, the CBC-MAC
state, the key stream, the AAD, the tag, saved arguments and the received
PN; callers must not keep data there. `DevCrypto`'s `0xF000–0xF7FF` is also
used (AES tables and round keys).
-/

namespace LeanOS.Wifi.DevCcmp

open LeanOS.Wifi.Bytecode LeanOS.Wifi.DevCrypto

def ccmpLo : UInt32 := 0xF800
def ccmpHi : UInt32 := 0xF8C0
/-- Counter block `A_i = 0x01 ‖ nonce ‖ i` (also the template for `B_0`). -/
def ctrBlk : UInt32 := 0xF800
/-- CBC-MAC state `X`. -/
def macX : UInt32 := 0xF810
/-- Key-stream block `E(A_i)` (and `B_0`). -/
def keyStream : UInt32 := 0xF820
/-- `u16be(aadLen) ‖ AAD`, zero padded to 32 bytes. -/
def aadBuf : UInt32 := 0xF830
/-- The 8-byte MIC computed by the last operation. -/
def tagAt : UInt32 := 0xF850
private def vars : UInt32 := 0xF860
/-- PN of the last frame `ccmpDecap` accepted or rejected after parsing the
CCMP header: 6 bytes little-endian (`PN0` first), 2 zero bytes. -/
def rxPnAt : UInt32 := 0xF8A0
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
private def subi (d : Reg) (v : UInt32) : ProgM Unit := emit (.alu .sub d (.imm v))
private def bri (c : Cond) (a : Reg) (v : UInt32) (l : Nat) : ProgM Unit :=
  emit (.branch c a (.imm v) l)
private def brr (c : Cond) (a b : Reg) (l : Nat) : ProgM Unit := emit (.branch c a (.reg b) l)
private def jmp (l : Nat) : ProgM Unit := emit (.jump l)
private def callL (l : Nat) : ProgM Unit := emit (.call l)
private def ret : ProgM Unit := emit .ret
/-- `r(d) := var k` (uses `r0` as the zero base). -/
private def getv (d : Reg) (k : Nat) : ProgM Unit := do li 0 0; ld 4 d 0 (var k)

structure CcmpLib where
  setup : Nat
  crypt : Nat
  tag : Nat
  encap : Nat
  decap : Nat

/-- Header length from the frame control at `r(hdr)` into `r(out)`; uses
`r(t1)`, `r(t2)`. Branches to `bad` unless the frame is a data frame. -/
private def headerLen (hdr out t1 t2 : Reg) (bad : Nat) : ProgM Unit := do
  let a ← newLabel
  let b ← newLabel
  ld 1 t1 hdr 0; mov t2 t1; andi t2 0x0c; bri .ne t2 0x08 bad
  li out 24
  ld 1 t2 hdr 1; andi t2 3; bri .ne t2 3 a; addi out 6
  place a
  andi t1 0x80; bri .eq t1 0 b; addi out 2
  place b

/-- `setup(r1 = hdr, r2 = hdrLen, r3 = ccmpHdr, r4 = payloadLen)`: build
the counter block and AAD from the MAC header and CCMP header, and run the
CBC-MAC over `B_0` and the AAD (key already expanded). -/
private def setupBody (L : Lib) : ProgM Unit := do
  let noq ← newLabel
  let nq2 ← newLabel
  let no4 ← newLabel
  let no5 ← newLabel
  li 0 0
  for k in [0:4] do sti 4 0 (ctrBlk + (4 * k).toUInt32) 0
  for k in [0:8] do sti 4 0 (aadBuf + (4 * k).toUInt32) 0
  sti 1 0 ctrBlk 0x01
  ld 1 5 1 0; mov 6 5; andi 6 0x80 -- r5 = FC0, r6 = QoS flag
  mov 11 1; addR 11 2; subi 11 2 -- r11 = &QoS control (if QoS)
  li 7 0
  bri .eq 6 0 noq
  ld 1 7 11 0; andi 7 0x0f
  place noq
  st 1 0 (ctrBlk + 1) 7
  ld 4 8 1 10; st 4 0 (ctrBlk + 2) 8; ld 2 8 1 14; st 2 0 (ctrBlk + 6) 8
  for (d, s) in [(8, 7), (9, 6), (10, 5), (11, 4), (12, 1), (13, 0)] do
    ld 1 8 3 (s : Nat).toUInt32; st 1 0 (ctrBlk + (d : Nat).toUInt32) 8
  -- AAD
  mov 8 5; andi 8 0x8f; st 1 0 (aadBuf + 2) 8
  ld 1 8 1 1; andi 8 0xc7; ori 8 0x40
  bri .eq 6 0 nq2; andi 8 0x7f
  place nq2
  st 1 0 (aadBuf + 3) 8
  for k in [0:4] do
    ld 4 8 1 (4 + 4 * k).toUInt32; st 4 0 (aadBuf + (4 + 4 * k).toUInt32) 8
  ld 2 8 1 20; st 2 0 (aadBuf + 20) 8
  ld 1 8 1 22; andi 8 0x0f; st 1 0 (aadBuf + 22) 8
  li 9 (aadBuf + 24); li 10 22
  ld 1 8 1 1; andi 8 3; bri .ne 8 3 no4
  ld 4 8 1 24; st 4 9 0 8; ld 2 8 1 28; st 2 9 4 8; addi 9 6; addi 10 6
  place no4
  bri .eq 6 0 no5
  ld 1 8 11 0; andi 8 0x0f; st 1 9 0 8; addi 10 2
  place no5
  st 1 0 (aadBuf + 1) 10
  -- B_0 = 0x59 ‖ nonce ‖ u16be(payloadLen)
  for k in [0:4] do
    ld 4 8 0 (ctrBlk + (4 * k).toUInt32); st 4 0 (keyStream + (4 * k).toUInt32) 8
  sti 1 0 keyStream 0x59
  mov 8 4; shri 8 8; st 1 0 (keyStream + 14) 8; st 1 0 (keyStream + 15) 4
  li 1 keyStream; li 2 macX; callL L.aesEncrypt
  for half in [0:2] do
    li 0 0
    for k in [0:4] do
      ld 4 3 0 (macX + (4 * k).toUInt32); ld 4 4 0 (aadBuf + (16 * half + 4 * k).toUInt32)
      xorR 3 4; st 4 0 (macX + (4 * k).toUInt32) 3
    li 1 macX; li 2 macX; callL L.aesEncrypt
  ret

/-- `crypt(r1 = src, r2 = dst, r3 = len, r4 = mode)`: CTR transform from
counter 1 with the CBC-MAC run over the plaintext (`mode = 0`: the source is
plaintext; `mode = 1`: the destination is). `src = dst` is allowed. -/
private def cryptBody (L : Lib) : ProgM Unit := do
  let top ← newLabel
  let done ← newLabel
  let full ← newLabel
  let bl ← newLabel
  let be ← newLabel
  let useS ← newLabel
  mov 10 1; mov 11 2; mov 12 3; mov 13 4; li 14 1
  place top
  bri .eq 12 0 done
  li 0 0; st 1 0 (ctrBlk + 15) 14; mov 8 14; shri 8 8; st 1 0 (ctrBlk + 14) 8
  li 1 ctrBlk; li 2 keyStream; callL L.aesEncrypt
  li 9 16; brr .geu 12 9 full; mov 9 12
  place full
  li 7 0
  place bl
  brr .eq 7 9 be
  mov 8 10; addR 8 7; ld 1 3 8 0          -- s = src[j]
  ld 1 4 7 keyStream; mov 5 3; xorR 5 4    -- d = s ^ E(A_i)[j]
  mov 8 11; addR 8 7; st 1 8 0 5           -- dst[j] = d
  bri .eq 13 0 useS; mov 3 5
  place useS
  ld 1 4 7 macX; xorR 4 3; st 1 7 macX 4   -- X[j] ^= plaintext
  addi 7 1; jmp bl
  place be
  li 1 macX; li 2 macX; callL L.aesEncrypt
  addR 10 9; addR 11 9; subR 12 9; addi 14 1; jmp top
  place done
  ret

/-- `tag()`: `tagAt := (X ⊕ E(A_0))[0..8)`. -/
private def tagBody (L : Lib) : ProgM Unit := do
  li 0 0; sti 2 0 (ctrBlk + 14) 0
  li 1 ctrBlk; li 2 keyStream; callL L.aesEncrypt
  li 0 0
  for k in [0:2] do
    ld 4 3 0 (macX + (4 * k).toUInt32); ld 4 4 0 (keyStream + (4 * k).toUInt32); xorR 3 4
    st 4 0 (tagAt + (4 * k).toUInt32) 3
  ret

/-- `ccmpEncap(r1 = mpdu, r2 = len, r3 = out, r4 = tk, r5 = pn, r6 = keyId)`:
protect the plaintext data MPDU `mpdu[len]` (header ‖ body) into `out`:
header with Protected set, CCMP header, encrypted body, 8-byte MIC. The
48-bit PN at `pn` (6 bytes little-endian) is incremented first and the new
value is used. `r0 :=` output length (`len + 16`), or `0` (nothing written,
PN unchanged) if `mpdu` is not a data frame or is shorter than its header.
`out` must not overlap `mpdu`. -/
private def encapBody (L : Lib) (C : CcmpLib) : ProgM Unit := do
  let bad ← newLabel
  let nc ← newLabel
  li 0 0
  st 4 0 (var 0) 1; st 4 0 (var 1) 2; st 4 0 (var 2) 3; st 4 0 (var 3) 5; st 4 0 (var 4) 6
  headerLen 1 9 7 8 bad
  brr .ltu 2 9 bad
  st 4 0 (var 5) 9
  mov 1 4; callL L.aesExpandKey
  getv 5 3; ld 4 6 5 0; addi 6 1; st 4 5 0 6; bri .ne 6 0 nc
  ld 2 6 5 4; addi 6 1; st 2 5 4 6
  place nc
  getv 1 0; ld 4 2 0 (var 2); ld 4 3 0 (var 5); callL L.memcpy
  getv 2 2; ld 1 3 2 1; ori 3 0x40; st 1 2 1 3
  ld 4 9 0 (var 5); mov 8 2; addR 8 9      -- r8 = CCMP header
  ld 4 5 0 (var 3)
  ld 1 3 5 0; st 1 8 0 3; ld 1 3 5 1; st 1 8 1 3; sti 1 8 2 0
  ld 4 3 0 (var 4); andi 3 3; shli 3 6; ori 3 0x20; st 1 8 3 3
  ld 4 3 5 2; st 4 8 4 3
  mov 3 8; mov 1 2; mov 2 9; ld 4 4 0 (var 1); subR 4 9; callL C.setup
  getv 1 0; ld 4 9 0 (var 5); addR 1 9
  ld 4 2 0 (var 2); addR 2 9; addi 2 8
  ld 4 3 0 (var 1); subR 3 9; li 4 0; callL C.crypt
  callL C.tag
  getv 1 2; ld 4 2 0 (var 1); addR 1 2; addi 1 8
  ld 4 3 0 tagAt; st 4 1 0 3; ld 4 3 0 (tagAt + 4); st 4 1 4 3
  ld 4 0 0 (var 1); addi 0 16
  ret
  place bad
  li 0 0; ret

/-- `ccmpDecap(r1 = mpdu, r2 = len, r3 = tk, r4 = gtk, r5 = gtkKeyId)`:
verify and decrypt the protected data MPDU `mpdu[len]` (no FCS) in place.
Key id 0 in the CCMP header selects the pairwise key `tk`, key id
`gtkKeyId` (1–3) the group key `gtk`; any other key id is rejected. The PN
from the CCMP header is written to `rxPnAt` (replay checking is the
caller's job).

On success `r0 := 1`, `r1 :=` address of the plaintext body (at
`mpdu + hdrLen + 8`, starting with LLC/SNAP), `r2 :=` its length, `r3 :=`
the key id, and the header's Protected bit is cleared. On failure (not a
protected data frame, too short, no ExtIV, unknown key id, MIC mismatch)
`r0 = r1 = r2 := 0`; after a MIC mismatch the body is zeroed. -/
private def decapBody (L : Lib) (C : CcmpLib) : ProgM Unit := do
  let bad ← newLabel
  let key ← newLabel
  let zl ← newLabel
  let fail ← newLabel
  li 0 0
  st 4 0 (var 0) 1; st 4 0 (var 1) 2; st 4 0 (var 6) 3; st 4 0 (var 7) 4; st 4 0 (var 8) 5
  headerLen 1 9 7 8 fail
  ld 1 8 1 1; andi 8 0x40; bri .eq 8 0 fail
  mov 10 9; addi 10 16; brr .ltu 2 10 fail
  st 4 0 (var 5) 9
  mov 8 1; addR 8 9
  ld 1 10 8 3; mov 11 10; andi 11 0x20; bri .eq 11 0 fail
  shri 10 6; st 4 0 (var 4) 10
  ld 1 3 8 0; st 1 0 rxPnAt 3; ld 1 3 8 1; st 1 0 (rxPnAt + 1) 3
  ld 4 3 8 4; st 4 0 (rxPnAt + 2) 3; sti 2 0 (rxPnAt + 6) 0
  ld 4 1 0 (var 6); bri .eq 10 0 key
  ld 4 1 0 (var 7); ld 4 11 0 (var 8); brr .ne 10 11 fail
  place key
  callL L.aesExpandKey
  getv 1 0; ld 4 2 0 (var 5); mov 3 1; addR 3 2
  ld 4 4 0 (var 1); subR 4 2; subi 4 16; callL C.setup
  getv 1 0; ld 4 9 0 (var 5); addR 1 9; addi 1 8; mov 2 1
  ld 4 3 0 (var 1); subR 3 9; subi 3 16; li 4 1; callL C.crypt
  callL C.tag
  getv 1 0; ld 4 2 0 (var 1); addR 1 2; subi 1 8
  ld 4 3 1 0; ld 4 4 0 tagAt; xorR 3 4
  ld 4 5 1 4; ld 4 4 0 (tagAt + 4); xorR 5 4; orR 3 5
  bri .ne 3 0 bad
  ld 4 1 0 (var 0); ld 1 3 1 1; andi 3 0xbf; st 1 1 1 3
  ld 4 9 0 (var 5); ld 4 2 0 (var 1); subR 2 9; subi 2 16
  addR 1 9; addi 1 8
  ld 4 3 0 (var 4)
  li 0 1; ret
  place bad
  getv 8 0; ld 4 9 0 (var 5); addR 8 9; addi 8 8
  ld 4 13 0 (var 1); subR 13 9; subi 13 16
  place zl
  bri .eq 13 0 fail
  sti 1 8 0 0; addi 8 1; subi 13 1; jmp zl
  place fail
  li 0 0; li 1 0; li 2 0; ret

def CcmpLib.alloc : ProgM CcmpLib := do
  return { setup := ← newLabel, crypt := ← newLabel, tag := ← newLabel, encap := ← newLabel,
           decap := ← newLabel }

/-- Place the routine bodies (control must not fall into them). -/
def CcmpLib.emitBodies (C : CcmpLib) (L : Lib) : ProgM Unit := do
  place C.setup; setupBody L
  place C.crypt; cryptBody L
  place C.tag; tagBody L
  place C.encap; encapBody L C
  place C.decap; decapBody L C

/-- Emit `jump over; <bodies>; over:` and return the labels. -/
def install (L : Lib) : ProgM CcmpLib := do
  let C ← CcmpLib.alloc
  let over ← newLabel
  jmp over
  C.emitBodies L
  place over
  return C

private def setArgs (args : List Operand) : ProgM Unit := do
  for a in args, r in [1:args.length + 1] do
    match a with
    | .reg s => if s != r then mov r s
    | .imm v => li r v

/-- `r0 := ` protected length; see `encapBody`. -/
def callEncap (C : CcmpLib) (mpdu len out tk pn keyId : Operand) : ProgM Unit := do
  setArgs [mpdu, len, out, tk, pn, keyId]; callL C.encap

/-- `r0 := 1` and `r1, r2, r3 :=` plaintext body, length, key id on success. -/
def callDecap (C : CcmpLib) (mpdu len tk gtk gtkKeyId : Operand) : ProgM Unit := do
  setArgs [mpdu, len, tk, gtk, gtkKeyId]; callL C.decap

end LeanOS.Wifi.DevCcmp
