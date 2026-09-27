import LeanOS.Wifi.DevCrypto
import LeanOS.Wifi.Sim
import LeanOS.Wifi.Pbkdf2
import LeanOS.Wifi.Eapol
import LeanOS.Wifi.Ieee80211

/-! Device-program crypto (`LeanOS.Wifi.DevCrypto`) checked in the simulator.

Every case builds a small program: the library (`DevCrypto.install`), stores
that place the test inputs in scratch, the routine call, `halt`. The program
is run with `Sim.run` and the resulting scratch bytes / `r0` are compared
with the reference library (`Sha1`, `Aes`, `Eapol`), which itself passes the
published vectors (`leanos-wifi-vectors`). Each case also checks that

* execution ends in `halt` with an empty return stack,
* `r15` (set to a sentinel before the call) is untouched, and
* scratch outside the reserved region `0xF000–0xF7FF` holds exactly the
  inputs and the expected outputs (no stray writes).

The dynamic instruction count of each routine (steps of the full program
minus steps of the same program without the call) is reported per
operation. Prints PASS/FAIL per group and exits nonzero on failure. -/

open LeanOS.Wifi
open LeanOS.Wifi.Bytecode
open LeanOS.Wifi.DevCrypto
open LeanOS.Wifi.Bytes (ofHex toHex)

private def hx (s : String) : ByteArray := ofHex s
private def str (s : String) : ByteArray := s.toUTF8

/-! ## Deterministic pseudo-random inputs (64-bit LCG, Knuth MMIX constants) -/

structure Rng where
  s : UInt64

def Rng.next (r : Rng) : UInt8 × Rng :=
  let s := r.s * 6364136223846793005 + 1442695040888963407
  ((s >>> 56).toUInt8, ⟨s⟩)

def Rng.bytes (r : Rng) (n : Nat) : ByteArray × Rng := Id.run do
  let mut g := r
  let mut out := ByteArray.emptyWithCapacity n
  for _ in [0:n] do
    let (b, g') := g.next
    out := out.push b
    g := g'
  return (out, g)

/-- Uniform-ish in `[0, bound)` (bound ≤ 65536). -/
def Rng.below (r : Rng) (bound : Nat) : Nat × Rng :=
  let (a, r) := r.next
  let (b, r) := r.next
  ((a.toNat * 256 + b.toNat) % bound, r)

/-! ## Running a case -/

def sentinel : UInt32 := 0x5EA15EA1

structure Outcome where
  ok : Bool
  detail : String
  r0 : UInt32
  steps : Nat

private def setupStores (inputs : List (UInt32 × ByteArray)) : ProgM Unit := do
  li 0 0
  for (a, b) in inputs do storeBytes 0 a b
  li 15 sentinel

private def overlay (mem : ByteArray) (parts : List (UInt32 × ByteArray)) : ByteArray :=
  parts.foldl (fun m (a, b) => Bytes.overwrite m a.toNat b) mem

/-- Run `call` after storing `inputs`; `expect` lists the regions whose final
contents are known (inputs that change, outputs). -/
def runCase (inputs : List (UInt32 × ByteArray)) (call : Lib → ProgM Unit)
    (expect : List (UInt32 × ByteArray)) : Outcome := Id.run do
  let full := build do
    let L ← install
    setupStores inputs
    call L
    halt
  let base := build do
    let _ ← install
    setupStores inputs
    halt
  match full, base with
  | .error e, _ | _, .error e => return ⟨false, s!"build: {e}", 0, 0⟩
  | .ok p, .ok pb =>
    let (st, m) := Sim.run p Sim.Device.none ()
    let (_, mb) := Sim.run pb Sim.Device.none ()
    let steps := m.steps - mb.steps
    if st != .halt then return ⟨false, s!"status {repr st}", 0, steps⟩
    if !m.stack.isEmpty then return ⟨false, "stack not empty", 0, steps⟩
    if m.reg 15 != sentinel then return ⟨false, "r15 clobbered", 0, steps⟩
    let want := overlay (overlay (Bytes.zeros scratchBytes) inputs) expect
    let lo := reservedLo.toNat
    let hi := reservedHi.toNat
    let got := m.mem
    let outside (b : ByteArray) := b.extract 0 lo ++ b.extract hi scratchBytes
    if !Bytes.beq (outside got) (outside want) then
      let diffs := expect.filterMap fun (a, b) =>
        let g := got.extract a.toNat (a.toNat + b.size)
        if Bytes.beq g b then none else some s!"@{a}: got {toHex g} want {toHex b}"
      return ⟨false, s!"memory mismatch {diffs}", m.reg 0, steps⟩
    return ⟨true, "", m.reg 0, steps⟩

/-! ## Reporting -/

structure Group where
  name : String
  cases : Nat := 0
  failures : Array String := #[]

def Group.add (g : Group) (label : String) (o : Outcome) (extra : Bool := true)
    (extraDetail : String := "") : Group :=
  let g := { g with cases := g.cases + 1 }
  if o.ok && extra then g
  else { g with failures := g.failures.push s!"{label}: {o.detail} {extraDetail}" }

def report (g : Group) (fails : IO.Ref Nat) : IO Unit := do
  if g.failures.isEmpty then
    IO.println s!"PASS {g.name} ({g.cases} cases)"
  else
    fails.modify (· + 1)
    IO.println s!"FAIL {g.name} ({g.failures.size}/{g.cases} failed)"
    for f in g.failures.toList.take 5 do IO.println s!"  {f}"

/-! ## Scratch addresses used by the tests -/

def aKey : UInt32 := 0x0100
def aKey2 : UInt32 := 0x0200
def aOut : UInt32 := 0x0300
def aAa : UInt32 := 0x0400
def aSpa : UInt32 := 0x0410
def aAn : UInt32 := 0x0420
def aSn : UInt32 := 0x0440
def aMsg : UInt32 := 0x1000

/-! ## SHA-1 -/

def sha1Case (msg : ByteArray) : Outcome × Bool :=
  let o := runCase [(aMsg, msg)] (fun L => callSha1 L (.imm aMsg) (.imm msg.size.toUInt32) (.imm aOut))
    [(aOut, Sha1.hash msg)]
  (o, o.ok)

def sha1Group (rng : Rng) : Group × Rng := Id.run do
  let mut g : Group := { name := "sha1 (FIPS 180 vectors + 50 random, 0..1500 bytes)" }
  for (label, m) in [("abc", str "abc"), ("empty", ByteArray.empty),
      ("448-bit", str "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq")] do
    g := g.add label (sha1Case m).1
  -- Known answers of the vectors themselves (not only agreement with the reference).
  let kat := runCase [(aMsg, str "abc")] (fun L => callSha1 L (.imm aMsg) (.imm 3) (.imm aOut))
    [(aOut, hx "a9993e364706816aba3e25717850c26c9cd0d89d")]
  g := g.add "abc known answer" kat
  let mut r := rng
  let edge := [55, 56, 63, 64, 65, 119, 120, 127, 128, 1500]
  for i in [0:50] do
    let (n, r1) := if i < edge.length then (edge[i]!, r) else r.below 1501
    let (m, r2) := r1.bytes n
    r := r2
    g := g.add s!"random len {n}" (sha1Case m).1
  return (g, r)

/-! ## HMAC-SHA1 -/

def hmacCase (key msg : ByteArray) (want : Option ByteArray := none) : Outcome :=
  runCase [(aKey, key), (aMsg, msg)]
    (fun L => callHmac L (.imm aKey) (.imm key.size.toUInt32) (.imm aMsg) (.imm msg.size.toUInt32)
      (.imm aOut))
    [(aOut, want.getD (Sha1.hmac key msg))]

def hmacGroup (rng : Rng) : Group × Rng := Id.run do
  let mut g : Group := { name := "hmac-sha1 (RFC 2202 cases 1-7 + 50 random)" }
  let rfc2202 : List (ByteArray × ByteArray × String) := [
    (Bytes.replicate 20 0x0b, str "Hi There", "b617318655057264e28bc0b6fb378c8ef146be00"),
    (str "Jefe", str "what do ya want for nothing?", "effcdf6ae5eb2fa2d27416d5f184df9c259a7c79"),
    (Bytes.replicate 20 0xaa, Bytes.replicate 50 0xdd, "125d7342b9ac11cd91a39af48aa17b4f63f175d3"),
    (hx "0102030405060708090a0b0c0d0e0f10111213141516171819", Bytes.replicate 50 0xcd,
      "4c9007f4026250c6bc8414f9bf50c86c2d7235da"),
    (Bytes.replicate 20 0x0c, str "Test With Truncation", "4c1a03424b55e07fe7f27be1d58bb9324a9a5a04"),
    (Bytes.replicate 80 0xaa, str "Test Using Larger Than Block-Size Key - Hash Key First",
      "aa4ae5e15272d00e95705637ce8a3b55ed402112"),
    (Bytes.replicate 80 0xaa,
      str "Test Using Larger Than Block-Size Key and Larger Than One Block-Size Data",
      "e8e99d0f45237d786d6bbaa7965c7808bbff1a91")]
  let mut i := 1
  for (k, m, w) in rfc2202 do
    g := g.add s!"rfc2202 case {i}" (hmacCase k m (some (hx w)))
    i := i + 1
  let mut r := rng
  for j in [0:50] do
    let (kl, r1) := if j % 10 == 9 then (65 + j, r) else r.below 65
    let (ml, r2) := r1.below 1501
    let (k, r3) := r2.bytes kl
    let (m, r4) := r3.bytes ml
    r := r4
    g := g.add s!"random key {kl} msg {ml}" (hmacCase k m)
  return (g, r)

/-! ## PRF / PTK -/

def ptkCase (pmk aa spa an sn : ByteArray) (want : Option ByteArray := none) : Outcome :=
  let ref := Eapol.derivePtk pmk aa spa an sn
  runCase [(aKey, pmk), (aAa, aa), (aSpa, spa), (aAn, an), (aSn, sn)]
    (fun L => callPtk L (.imm aKey) (.imm aAa) (.imm aSpa) (.imm aAn) (.imm aSn) (.imm aOut))
    [(aOut, want.getD (ref.kck ++ ref.kek ++ ref.tk))]

def ptkGroup (rng : Rng) : Group × Rng := Id.run do
  let mut g : Group := { name := "ptk prf-384 (python-cross-checked vector + 50 random, both orders)" }
  let mut r := rng
  for j in [0:25] do
    let (pmk, r1) := r.bytes 32
    let (aa, r2) := r1.bytes 6
    let (spa0, r3) := r2.bytes 6
    let (an, r4) := r3.bytes 32
    let (sn0, r5) := r4.bytes 32
    r := r5
    -- Every fifth case shares long prefixes so the comparison runs deep.
    let spa := if j % 5 == 0 then aa.extract 0 5 ++ spa0.extract 5 6 else spa0
    let sn := if j % 5 == 0 then an.extract 0 31 ++ sn0.extract 31 32 else sn0
    let sn := if j == 10 then an else sn -- equal nonces
    g := g.add s!"random {j} (aa,spa)" (ptkCase pmk aa spa an sn)
    -- Same inputs with the roles swapped: exercises the other min/max branch.
    g := g.add s!"random {j} (spa,aa)" (ptkCase pmk spa aa sn an)
  return (g, r)

def prfGroup (rng : Rng) : Group × Rng := Id.run do
  let mut g : Group := { name := "prf generic (random label/data, output 1..80 bytes)" }
  let mut r := rng
  for j in [0:10] do
    let (key, r1) := r.bytes 32
    let (data, r2) := r1.bytes (20 + j * 7)
    let (n, r3) := r2.below 80
    r := r3
    let label := s!"Test label {j}"
    let pfx := label.toUTF8.push 0 ++ data
    let want := Eapol.prf key label data (n + 1)
    let o := runCase [(aKey, key), (aMsg, pfx)]
      (fun L => callPrf L (.imm aKey) (.imm 32) (.imm aMsg) (.imm pfx.size.toUInt32) (.imm aOut)
        (.imm (n + 1).toUInt32))
      -- the counter byte after the prefix is left at the last counter value
      [(aOut, want), (aMsg + pfx.size.toUInt32, ByteArray.mk #[((n + 1 + 19) / 20 - 1).toUInt8])]
    g := g.add s!"prf {j} len {n + 1}" o
  return (g, r)

/-! ## EAPOL-Key MIC -/

def aFrame : UInt32 := 0x2000

def micComputeCase (kck : ByteArray) (f : Eapol.KeyFrame) : Outcome :=
  let unsigned := { f with mic := Bytes.zeros 16 }.encode
  -- Garbage in the MIC field must be ignored (zeroed) by the routine.
  let dirty := Bytes.overwrite unsigned Eapol.micOffset (Bytes.replicate 16 0x5a)
  runCase [(aKey, kck), (aFrame, dirty)]
    (fun L => callMicCompute L (.imm aKey) (.imm aFrame) (.imm dirty.size.toUInt32))
    [(aFrame, (f.sign kck).encode)]

def micVerifyCase (kck frame : ByteArray) (avail : Nat) : Outcome × Bool :=
  let o := runCase [(aKey, kck), (aFrame, frame)]
    (fun L => callMicVerify L (.imm aKey) (.imm aFrame) (.imm avail.toUInt32)) []
  let want := Eapol.micValid kck (frame.extract 0 avail)
  (o, (o.r0 == 1) == want)

def micGroup (rng : Rng) : Group × Group × Rng := Id.run do
  let mut gc : Group := { name := "eapol mic compute (50 random msg2/msg3/msg4-shaped frames)" }
  let mut gv : Group := { name := "eapol mic verify (50 valid + 50 tampered + length checks)" }
  let mut r := rng
  for j in [0:50] do
    let (kck, r1) := r.bytes 16
    let (nonce, r2) := r1.bytes 32
    let (kdLen, r3) := r2.below 120
    let (kd, r4) := r3.bytes kdLen
    let (pos, r5) := r4.below (4 + 95 + kdLen)
    let (flip, r6) := r5.next
    r := r6
    let keyInfo : UInt16 := #[0x010a, 0x13ca, 0x030a][j % 3]!
    let f : Eapol.KeyFrame :=
      { protocolVersion := (1 + j % 2).toUInt8, keyInfo, keyLength := if j % 3 == 1 then 16 else 0,
        replayCounter := j.toUInt64 + 1, nonce, keyData := if j % 3 == 2 then .empty else kd }
    gc := gc.add s!"compute {j}" (micComputeCase kck f)
    let signed := (f.sign kck).encode
    let (o, agree) := micVerifyCase kck signed signed.size
    gv := gv.add s!"valid {j}" o (agree && o.r0 == 1) s!"r0={o.r0}"
    -- Trailing link-layer padding beyond the EAPOL length is ignored.
    let padded := signed ++ Bytes.replicate 3 0xee
    let (o, agree) := micVerifyCase kck padded padded.size
    gv := gv.add s!"valid+pad {j}" o (agree && o.r0 == 1) s!"r0={o.r0}"
    let tampered := Bytes.overwrite signed (pos % signed.size)
      (ByteArray.mk #[Bytes.at! signed (pos % signed.size) ^^^ (flip ||| 1)])
    let (o, agree) := micVerifyCase kck tampered tampered.size
    -- A flipped length byte can make the header length exceed the buffer:
    -- then both the device and our expectation reject it.
    gv := gv.add s!"tampered {j} @{pos % signed.size}" o (agree && o.r0 == 0) s!"r0={o.r0}"
  -- Truncated buffer: header length exceeds the available bytes.
  let f : Eapol.KeyFrame :=
    { protocolVersion := 1, keyInfo := 0x010a, keyLength := 0, replayCounter := 1,
      nonce := Bytes.zeros 32, keyData := Bytes.replicate 22 0x30 }
  let kck := Bytes.replicate 16 7
  let s := (f.sign kck).encode
  let (o, _) := micVerifyCase kck s (s.size - 1)
  gv := gv.add "truncated buffer rejected" o (o.r0 == 0) s!"r0={o.r0}"
  -- Header length shorter than the MIC field.
  let short := Bytes.overwrite s 2 (ByteArray.mk #[0, 90])
  let (o, _) := micVerifyCase kck short short.size
  gv := gv.add "short body rejected" o (o.r0 == 0) s!"r0={o.r0}"
  return (gc, gv, r)

/-! ## AES-128 -/

def aesCase (encrypt : Bool) (key block : ByteArray) (want : Option ByteArray := none) : Outcome :=
  let ref := if encrypt then Aes.encrypt key block else Aes.decrypt key block
  runCase [(aKey, key), (aMsg, block)]
    (fun L => do
      callAesExpandKey L (.imm aKey)
      if encrypt then callAesEncrypt L (.imm aMsg) (.imm aOut)
      else callAesDecrypt L (.imm aMsg) (.imm aOut))
    [(aOut, want.getD ref)]

def aesGroup (encrypt : Bool) (rng : Rng) : Group × Rng := Id.run do
  let dir := if encrypt then "encrypt" else "decrypt"
  let mut g : Group := { name := s!"aes-128 {dir} (FIPS-197 C.1 + 50 random)" }
  let k := hx "000102030405060708090a0b0c0d0e0f"
  let (i, o) := if encrypt then ("00112233445566778899aabbccddeeff", "69c4e0d86a7b0430d8cdb78070b4c55a")
    else ("69c4e0d86a7b0430d8cdb78070b4c55a", "00112233445566778899aabbccddeeff")
  g := g.add "fips197 C.1" (aesCase encrypt k (hx i) (some (hx o)))
  let mut r := rng
  for j in [0:50] do
    let (key, r1) := r.bytes 16
    let (blk, r2) := r1.bytes 16
    r := r2
    g := g.add s!"random {j}" (aesCase encrypt key blk)
  -- In-place operation (in = out).
  let (key, r1) := r.bytes 16
  let (blk, r2) := r1.bytes 16
  r := r2
  let ref := if encrypt then Aes.encrypt key blk else Aes.decrypt key blk
  let o := runCase [(aKey, key), (aMsg, blk)]
    (fun L => do
      callAesExpandKey L (.imm aKey)
      if encrypt then callAesEncrypt L (.imm aMsg) (.imm aMsg)
      else callAesDecrypt L (.imm aMsg) (.imm aMsg))
    [(aMsg, ref)]
  g := g.add "in place" o
  return (g, r)

/-! ## RFC 3394 key unwrap -/

def unwrapCase (kek wrapped : ByteArray) (plainLen : Nat) : Outcome × Bool :=
  let ref := Aes.keyUnwrap kek wrapped
  let o := runCase [(aKey, kek), (aMsg, wrapped)]
    (fun L => callKeyUnwrap L (.imm aKey) (.imm aMsg) (.imm wrapped.size.toUInt32) (.imm aOut))
    [(aOut, ref.getD (Bytes.zeros plainLen))]
  (o, (o.r0 == 1) == ref.isSome)

def unwrapGroup (rng : Rng) : Group × Rng := Id.run do
  let mut g : Group := { name := "aes key unwrap (RFC 3394 4.1 + 50 random + 50 corrupted)" }
  let k := hx "000102030405060708090a0b0c0d0e0f"
  let w := hx "1fa68b0a8112b447aef34bd8fb5a7b829d3e862371d2cfe5"
  let (o, agree) := unwrapCase k w 16
  let kat := o.ok && Bytes.beq (Aes.keyUnwrap k w |>.getD .empty) (hx "00112233445566778899aabbccddeeff")
  g := g.add "rfc3394 4.1" o (agree && o.r0 == 1 && kat)
  let bad := hx "1fa68b0a8112b447aef34bd8fb5a7b829d3e862371d2cfe4"
  let (o, agree) := unwrapCase k bad 16
  g := g.add "rfc3394 4.1 corrupted" o (agree && o.r0 == 0)
  let mut r := rng
  for j in [0:50] do
    let (kek, r1) := r.bytes 16
    let (n, r2) := r1.below 7
    let (plain, r3) := r2.bytes (8 * (n + 2)) -- 16..64 bytes
    let (pos, r4) := r3.below (8 * (n + 3))
    let (flip, r5) := r4.next
    r := r5
    let wrapped := (Aes.keyWrap kek plain).getD .empty
    let (o, agree) := unwrapCase kek wrapped plain.size
    g := g.add s!"random {j} ({plain.size} bytes)" o (agree && o.r0 == 1)
    let corrupt := Bytes.overwrite wrapped pos (ByteArray.mk #[Bytes.at! wrapped pos ^^^ (flip ||| 1)])
    let (o, agree) := unwrapCase kek corrupt plain.size
    g := g.add s!"corrupted {j} @{pos}" o (agree && o.r0 == 0)
  -- Malformed lengths: r0 = 0, destination untouched.
  for len in [16, 20, 25] do
    let o := runCase [(aKey, k), (aMsg, Bytes.replicate len 0xa6)]
      (fun L => callKeyUnwrap L (.imm aKey) (.imm aMsg) (.imm len.toUInt32) (.imm aOut)) []
    g := g.add s!"malformed length {len}" o (o.r0 == 0)
  return (g, r)

/-! ## 4-way handshake known answers (python-cross-checked in `leanos-wifi-vectors`) -/

def handshakeGroup : Group := Id.run do
  let mut g : Group := { name := "4-way handshake known answers (ptk, msg2 MIC, msg3 unwrap)" }
  let pmk := Pbkdf2.pmkOfPassphrase (str "ThisIsAPassword") (str "ThisIsASSID")
  let aa := hx "020000000001"
  let spa := hx "020000000002"
  let range8 (lo hi : Nat) := ByteArray.mk ((List.range (hi - lo)).toArray.map fun i => (lo + i).toUInt8)
  let anonce := range8 0x10 0x30
  let snonce := range8 0x40 0x60
  let ptkHex := "2679f4c73eaf26c76d20be254428596e28f8ec0936523fe76eaad91b88561b4f82a2e260af86287dd9cc287ff9fe7230"
  g := g.add "ptk" (ptkCase pmk aa spa anonce snonce (some (hx ptkHex)))
  let ptk := hx ptkHex
  let kck := ptk.extract 0 16
  let kek := ptk.extract 16 32
  let m2 := hx "0103007502010a00000000000000000001404142434445464748494a4b4c4d4e4f505152535455565758595a5b5c5d5e5f0000000000000000000000000000000000000000000000000000000000000000a221564c4fddfe48a1ec687154cd1e9b001630140100000fac040100000fac040100000fac020000"
  let unsigned := Bytes.overwrite m2 81 (Bytes.zeros 16)
  let o := runCase [(aKey, kck), (aFrame, unsigned)]
    (fun L => callMicCompute L (.imm aKey) (.imm aFrame) (.imm m2.size.toUInt32)) [(aFrame, m2)]
  g := g.add "msg2 mic compute" o
  let (o, _) := micVerifyCase kck m2 m2.size
  g := g.add "msg2 mic verify" o (o.r0 == 1)
  let wrapped := hx "ac45427ab64882c9d9d1d1d1a882ff208a01f059119e82ab7ce4bf12c8dba478d182ac1aecc21e903c4d090532bbe333d1c793b8612b3d24"
  let plain := hx "30140100000fac040100000fac040100000fac020000dd16000fac010100a0a1a2a3a4a5a6a7a8a9aaabacadaeafdd00"
  let o := runCase [(aKey, kek), (aMsg, wrapped)]
    (fun L => callKeyUnwrap L (.imm aKey) (.imm aMsg) (.imm wrapped.size.toUInt32) (.imm aOut))
    [(aOut, plain)]
  g := g.add "msg3 key data unwrap" o (o.r0 == 1)
  return g

/-! ## Step counts -/

def stepReport : IO Unit := do
  let row (label : String) (steps : Nat) (ok : Bool := true) : IO Unit :=
    let us := (steps * 20 + 500) / 1000
    IO.println s!"  {label}{"".pushn ' ' (44 - label.length)}{steps} steps  (~{us} us at 20 ns/step){if ok then "" else "  [FAILED]"}"
  let blk := Bytes.replicate 64 0x61
  let o := runCase [(aMsg, blk)] (fun L => do callSha1Init L; callSha1Compress L (.imm aMsg)) []
  row "sha1 one block (init + compress)" o.steps o.ok
  for n in [0, 55, 64, 100, 1500] do
    let o := (sha1Case (Bytes.replicate n 0x61)).1
    row s!"sha1 {n} bytes" o.steps o.ok
  let k32 := Bytes.replicate 32 1
  let o := hmacCase k32 (Bytes.replicate 100 2)
  row "hmac-sha1 32-byte key, 100-byte msg" o.steps o.ok
  let an := Bytes.replicate 32 3
  let sn := Bytes.replicate 32 4
  let o := ptkCase k32 (hx "020000000001") (hx "020000000002") an sn
  row "ptk derivation (prf-384)" o.steps o.ok
  let f : Eapol.KeyFrame :=
    { protocolVersion := 1, keyInfo := 0x010a, keyLength := 0, replayCounter := 1,
      nonce := sn, keyData := Ieee80211.wpa2PskCcmpRsnIe }
  let kck := Bytes.replicate 16 5
  let o := micComputeCase kck f
  row s!"mic compute (msg2, {f.encode.size} bytes)" o.steps o.ok
  let f3 : Eapol.KeyFrame := { f with keyInfo := 0x13ca, keyData := Bytes.replicate 56 6 }
  let s3 := (f3.sign kck).encode
  let o := (micVerifyCase kck s3 s3.size).1
  row s!"mic verify (msg3, {s3.size} bytes)" o.steps o.ok
  let key := Bytes.replicate 16 7
  let o := runCase [(aKey, key)] (fun L => callAesExpandKey L (.imm aKey)) []
  row "aes key expansion (first, writes tables)" o.steps o.ok
  let o2 := runCase [(aKey, key)]
    (fun L => do callAesExpandKey L (.imm aKey); callAesExpandKey L (.imm aKey)) []
  row "aes key expansion (tables present)" (o2.steps - o.steps) o2.ok
  let blocks (enc : Bool) (n : Nat) : Outcome :=
    runCase [(aKey, key), (aMsg, key)] (fun L => do
      callAesExpandKey L (.imm aKey)
      for _ in [0:n] do
        if enc then callAesEncrypt L (.imm aMsg) (.imm aOut)
        else callAesDecrypt L (.imm aMsg) (.imm aOut))
      [(aOut, if enc then Aes.encrypt key key else Aes.decrypt key key)]
  let (e1, e2) := (blocks true 1, blocks true 2)
  row "aes encrypt one block" (e2.steps - e1.steps) (e1.ok && e2.ok)
  let (d1, d2) := (blocks false 1, blocks false 2)
  row "aes decrypt one block" (d2.steps - d1.steps) (d1.ok && d2.ok)
  let w := (Aes.keyWrap key (Bytes.replicate 48 8)).getD .empty
  let o := (unwrapCase key w 48).1
  row "key unwrap 56 -> 48 bytes (msg3 key data)" o.steps o.ok

def main : IO UInt32 := do
  let fails ← IO.mkRef 0
  let r : Rng := ⟨0x0123456789ABCDEF⟩
  let (g, r) := sha1Group r
  report g fails
  let (g, r) := hmacGroup r
  report g fails
  let (g, r) := ptkGroup r
  report g fails
  let (g, r) := prfGroup r
  report g fails
  let (gc, gv, r) := micGroup r
  report gc fails
  report gv fails
  let (g, r) := aesGroup true r
  report g fails
  let (g, r) := aesGroup false r
  report g fails
  let (g, _) := unwrapGroup r
  report g fails
  report handshakeGroup fails
  IO.println "dynamic instruction counts (routine incl. argument setup, call and return):"
  stepReport
  match build (do let _ ← install; halt) with
  | .ok p => IO.println s!"library code size: {p.words.size - 2} instructions ({16 * (p.words.size - 2)} bytes), no blob"
  | .error e => IO.println s!"library build error: {e}"; fails.modify (· + 1)
  let n ← fails.get
  if n == 0 then
    IO.println "ALL PASS"
    return 0
  else
    IO.println s!"{n} GROUP(S) FAILED"
    return 1
