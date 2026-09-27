import LeanOS.Wifi.DevCcmp
import LeanOS.Wifi.DevDhcp
import LeanOS.Wifi.Sim

/-! Device-program CCMP (`LeanOS.Wifi.DevCcmp`) and DHCP (`DevDhcp`)
routines checked in the simulator against the reference library
(`Ieee80211.ccmpEncap`/`ccmpDecap`, `Dhcp.discover`/`request`/`parseReply`).

Each case stores its inputs with a straight-line prologue, calls the routine
and halts; it checks the status, the empty return stack, that `r15` is
untouched, the result registers, and that scratch outside the routines'
private regions holds exactly the inputs and expected outputs. Prints
PASS/FAIL per group and step counts; exits nonzero on failure. -/

open LeanOS.Wifi LeanOS.Wifi.Bytecode LeanOS.Wifi.DevCrypto
open LeanOS.Wifi.Bytes (ofHex toHex)

private def hx (s : String) : ByteArray := ofHex s

/-! ## Deterministic pseudo-random inputs -/

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

def Rng.below (r : Rng) (bound : Nat) : Nat × Rng :=
  let (a, r) := r.next
  let (b, r) := r.next
  ((a.toNat * 256 + b.toNat) % bound, r)

/-! ## Running a case -/

def sentinel : UInt32 := 0x5EA15EA1

structure Outcome where
  ok : Bool
  detail : String
  regs : Array UInt32
  mem : ByteArray
  steps : Nat

/-- Private scratch of the routines under test (not compared). -/
def privateRanges : List (Nat × Nat) :=
  [(DevCrypto.reservedLo.toNat, DevCcmp.ccmpHi.toNat),
   ((DevDhcp.xidAt + DevDhcp.stage).toNat, DevDhcp.dhcpHi.toNat)]

private def overlay (mem : ByteArray) (parts : List (UInt32 × ByteArray)) : ByteArray :=
  parts.foldl (fun m (a, b) => Bytes.overwrite m a.toNat b) mem

private def blank (b : ByteArray) : ByteArray :=
  privateRanges.foldl (fun m (lo, hi) => Bytes.overwrite m lo (Bytes.zeros (hi - lo))) b

structure Libs where
  L : Lib
  C : DevCcmp.CcmpLib
  D : DevDhcp.DhcpLib

def installAll : ProgM Libs := do
  let L ← DevCrypto.install
  let C ← DevCcmp.install L
  let D ← DevDhcp.install
  return { L, C, D }

def runCase (inputs : List (UInt32 × ByteArray)) (call : Libs → ProgM Unit)
    (expect : List (UInt32 × ByteArray)) : Outcome := Id.run do
  let setup : ProgM Unit := do
    li 0 0
    for (a, b) in inputs do storeBytes 0 a b
    li 15 sentinel
  let full := build do
    let ls ← installAll
    setup
    call ls
    halt
  let base := build do
    let _ ← installAll
    setup
    halt
  match full, base with
  | .error e, _ | _, .error e => return ⟨false, s!"build: {e}", #[], .empty, 0⟩
  | .ok p, .ok pb =>
    let (st, m) := Sim.run p Sim.Device.none ()
    let (_, mb) := Sim.run pb Sim.Device.none ()
    let steps := m.steps - mb.steps
    let fail (d : String) : Outcome := ⟨false, d, m.regs, m.mem, steps⟩
    if st != .halt then return fail s!"status {repr st}"
    if !m.stack.isEmpty then return fail "stack not empty"
    if m.reg 15 != sentinel then return fail "r15 clobbered"
    let want := overlay (overlay (Bytes.zeros scratchBytes) inputs) expect
    if !Bytes.beq (blank m.mem) (blank want) then
      let diffs := expect.filterMap fun (a, b) =>
        let g := m.mem.extract a.toNat (a.toNat + b.size)
        if Bytes.beq g b then none else some s!"@{a}: got {toHex g} want {toHex b}"
      return fail s!"memory mismatch {diffs}"
    return ⟨true, "", m.regs, m.mem, steps⟩

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

def reg (o : Outcome) (r : Nat) : UInt32 := o.regs.getD r 0

/-! ## Scratch addresses used by the tests -/

def aTk : UInt32 := 0x0100
def aGtk : UInt32 := 0x0110
def aPn : UInt32 := 0x0120
def aIn : UInt32 := 0x4000
def aOut : UInt32 := 0x5000

def pnBytes (pn : UInt64) : ByteArray := (Bytes.u64le pn).extract 0 6

/-! ## CCMP encapsulation -/

def encapCase (tk : ByteArray) (pn : UInt64) (keyId : Nat) (mpdu : ByteArray)
    (want : Option ByteArray := none) : Outcome × Bool :=
  let pn' := (pn + 1) &&& 0xFFFFFFFFFFFF
  let ref := want <|> Ieee80211.ccmpEncap tk pn' keyId.toUInt8 mpdu
  let o := runCase [(aTk, tk), (aPn, pnBytes pn), (aIn, mpdu)]
    (fun ls => DevCcmp.callEncap ls.C (.imm aIn) (.imm mpdu.size.toUInt32) (.imm aOut) (.imm aTk)
      (.imm aPn) (.imm keyId.toUInt32))
    (match ref with
     | some out => [(aOut, out), (aPn, pnBytes pn')]
     | none => [])
  let r0ok := match ref with
    | some out => reg o 0 == out.size.toUInt32
    | none => reg o 0 == 0
  (o, r0ok)

/-- A random data MPDU header: `fc1base` flags plus random Retry/PwrMgt/
MoreData/Order/Protected bits, QoS with probability 1/2 (random TID and
upper QoS bits), A4 when both DS bits are set. -/
def randomHeader (r : Rng) (fc1base : UInt8) (fourAddr : Bool) : ByteArray × Rng :=
  let (sub, r) := r.next
  let (fl, r) := r.next
  let (addrs, r) := r.bytes 24
  let qos := sub &&& 1 == 1
  let subtype : UInt8 := (if qos then (0x80 : UInt8) else 0) ||| ((sub >>> 1) &&& 0x30)
  let fc0 : UInt8 := subtype ||| 0x08
  let fc1 : UInt8 := fc1base ||| (if fourAddr then (0x03 : UInt8) else 0) ||| (fl &&& 0xf8)
  let base := ByteArray.mk #[fc0, fc1] ++ addrs.extract 0 22
  let base := if fourAddr then base ++ addrs.extract 18 24 else base
  let (qc, r) := r.bytes 2
  (if qos then base ++ qc else base, r)

def encapGroup (rng : Rng) : Group × Rng := Id.run do
  let mut g : Group := { name := "ccmp encap (J.6.4 + 50 random incl. QoS/A4/PN carry)" }
  -- IEEE 802.11-2016 J.6.4
  let tk := hx "c97c1f67ce371185514a8a19f2bdd52f"
  let hdr := hx "0848c32c0fd2e128a57c5030f1844408abaea5b8fcba8033"
  let plain := hx "f8ba1a55d02f85ae967bb62fb6cda8eb7e78a050"
  let want := hx "0848c32c0fd2e128a57c5030f1844408abaea5b8fcba80330ce70020769703b5f3d0a2fe9a3dbf2342a643e43246e80c3c04d0197845ce0b16f97623"
  let (o, r0ok) := encapCase tk (0xB5039776E70C - 1) 0 (hdr ++ plain) (some want)
  g := g.add "J.6.4" o r0ok
  let mut r := rng
  let lens := [0, 1, 15, 16, 17, 32, 1500]
  for j in [0:50] do
    let (tk, r1) := r.bytes 16
    let (pnb, r2) := r1.bytes 6
    let (hdr, r3) := randomHeader r2 0x01 (j % 7 == 3)
    let (n, r4) := if j < lens.length then (lens[j]!, r3) else r3.below 600
    let (body, r5) := r4.bytes n
    let (kid, r6) := r5.below 4
    r := r6
    let pn : UInt64 := if j % 10 == 5 then 0x1234FFFFFFFF else Bytes.getU64le (pnb ++ Bytes.zeros 2) 0
    let (o, r0ok) := encapCase tk pn kid (hdr ++ body)
    g := g.add s!"random {j} hdr {hdr.size} body {n}" o r0ok
  -- Not a data frame / shorter than its header: rejected, nothing written.
  let (o, r0ok) := encapCase tk 7 0 (hx "b0000000")
  g := g.add "management frame rejected" o r0ok
  let (o, r0ok) := encapCase tk 7 0 ((hdr ++ plain).extract 0 20)
  g := g.add "short frame rejected" o r0ok
  return (g, r)

/-! ## CCMP decapsulation -/

/-- Expected device behaviour for `mpdu`: the pre-checks the routine makes
before touching the body, and the reference result. -/
def decapExpect (tk gtk : ByteArray) (gtkId : Nat) (mpdu : ByteArray) :
    Bool × Option (ByteArray × Ieee80211.CcmpPlain) :=
  let fc := Ieee80211.FrameControl.decode mpdu
  let hl := Ieee80211.dataHeaderLen fc
  let pre := fc.ftype == Ieee80211.FrameType.data && fc.has Ieee80211.Flags.protectedFrame &&
    mpdu.size ≥ hl + 16
  match (if pre then Ieee80211.parseCcmpHeader (Bytes.slice mpdu hl 8) else none) with
  | none => (false, none)
  | some (_, kid) =>
    let key := if kid == 0 then some tk else if kid.toNat == gtkId then some gtk else none
    match key with
    | none => (false, none)
    | some k => (true, (Ieee80211.ccmpDecap k mpdu).map fun p => (k, p))

def decapCase (tk gtk : ByteArray) (gtkId : Nat) (mpdu : ByteArray) : Outcome × Bool :=
  let fc := Ieee80211.FrameControl.decode mpdu
  let hl := Ieee80211.dataHeaderLen fc
  let (pre, res) := decapExpect tk gtk gtkId mpdu
  let expect : List (UInt32 × ByteArray) :=
    match res with
    | some (_, p) =>
      -- header (Protected cleared), CCMP header kept, plaintext in place, MIC kept
      [(aIn, p.mpdu.extract 0 hl), (aIn + (hl + 8).toUInt32, p.mpdu.extract hl p.mpdu.size)]
    | none => if pre then [(aIn + (hl + 8).toUInt32, Bytes.zeros (mpdu.size - hl - 16))] else []
  let o := runCase [(aTk, tk), (aGtk, gtk), (aIn, mpdu)]
    (fun ls => DevCcmp.callDecap ls.C (.imm aIn) (.imm mpdu.size.toUInt32) (.imm aTk) (.imm aGtk)
      (.imm gtkId.toUInt32))
    expect
  let regsOk := match res with
    | some (_, p) =>
      let pnDev := o.mem.extract DevCcmp.rxPnAt.toNat (DevCcmp.rxPnAt.toNat + 8)
      reg o 0 == 1 && reg o 1 == aIn + (hl + 8).toUInt32 &&
        reg o 2 == (mpdu.size - hl - 16).toUInt32 && reg o 3 == p.keyId.toUInt32 &&
        Bytes.beq pnDev (Bytes.u64le p.pn)
    | none => reg o 0 == 0 && reg o 1 == 0 && reg o 2 == 0
  (o, regsOk)

def decapGroup (rng : Rng) : Group × Group × Rng := Id.run do
  let mut g : Group := { name := "ccmp decap (J.6.4 + 50 random FromDS, QoS, TK/GTK)" }
  let mut gt : Group := { name := "ccmp decap rejection (50 tampered + key id/flag/length cases)" }
  let tk := hx "c97c1f67ce371185514a8a19f2bdd52f"
  let j64 := hx "0848c32c0fd2e128a57c5030f1844408abaea5b8fcba80330ce70020769703b5f3d0a2fe9a3dbf2342a643e43246e80c3c04d0197845ce0b16f97623"
  let (o, ok) := decapCase tk (Bytes.zeros 16) 1 j64
  let plainOk := Bytes.beq (o.mem.extract (aIn.toNat + 32) (aIn.toNat + 52))
    (hx "f8ba1a55d02f85ae967bb62fb6cda8eb7e78a050")
  g := g.add "J.6.4" o (ok && plainOk && reg o 0 == 1)
  let mut r := rng
  let mut tamperAccepted := 0
  for j in [0:50] do
    let (tk, r1) := r.bytes 16
    let (gtk, r2) := r1.bytes 16
    let (pnb, r3) := r2.bytes 6
    let (hdr, r4) := randomHeader r3 0x02 (j % 9 == 4)
    let (n, r5) := if j < 3 then ([0, 16, 1500][j]!, r4) else r4.below 600
    let (body, r6) := r5.bytes n
    let (gid, r7) := r6.below 3
    let (pos, r8) := r7.below 10000
    let (flip, r9) := r8.next
    r := r9
    let gtkId := gid + 1
    let useGtk := j % 3 == 1
    let pn := Bytes.getU64le (pnb ++ Bytes.zeros 2) 0
    let key := if useGtk then gtk else tk
    let kid := if useGtk then gtkId else 0
    let mpdu := (Ieee80211.ccmpEncap key pn kid.toUInt8 (hdr ++ body)).getD .empty
    let (o, ok) := decapCase tk gtk gtkId mpdu
    g := g.add s!"random {j} hdr {hdr.size} body {n} kid {kid}" o (ok && reg o 0 == 1)
    let p := pos % mpdu.size
    let bad := Bytes.overwrite mpdu p (ByteArray.mk #[Bytes.at! mpdu p ^^^ (flip ||| 1)])
    let (o, ok) := decapCase tk gtk gtkId bad
    let want := (decapExpect tk gtk gtkId bad).2.isSome
    gt := gt.add s!"tampered {j} @{p} (accept={want})" o ok
    if want then tamperAccepted := tamperAccepted + 1
  -- Unknown key id, unprotected, missing ExtIV, too short.
  let tk := Bytes.replicate 16 1
  let gtk := Bytes.replicate 16 2
  let hdr := hx "08420000000000000000000000000000000000000000" ++ hx "3000"
  let f (kid : UInt8) := (Ieee80211.ccmpEncap (if kid == 0 then tk else gtk) 9 kid (hdr ++ Bytes.replicate 40 3)).getD .empty
  let qf := (Ieee80211.ccmpEncap tk 10 0
    (hx "88420000000000000000000000000000000000000000" ++ hx "30000500" ++ Bytes.replicate 40 3)).getD .empty
  let cases : List (String × ByteArray × Bool) := [
    ("key id 2 with gtk id 1", f 2, false), ("key id 1 with gtk id 1", f 1, true),
    ("unprotected", Bytes.overwrite (f 0) 1 (ByteArray.mk #[0x02]), false),
    ("no ExtIV", Bytes.overwrite (f 0) 27 (ByteArray.mk #[0x00]), false),
    ("too short", (f 0).extract 0 (24 + 15), false),
    ("header + 16 (empty body)", (Ieee80211.ccmpEncap tk 9 0 hdr).getD .empty, true),
    ("management frame", Bytes.overwrite (f 0) 0 (ByteArray.mk #[0xd0]), false),
    -- AAD masking: Retry / sequence number / QoS upper byte are not authenticated,
    -- the TID and the To/FromDS bits are.
    ("retry bit flipped (masked)", Bytes.overwrite (f 0) 1 (ByteArray.mk #[0x4a]), true),
    ("sequence number changed (masked)", Bytes.overwrite (f 0) 23 (ByteArray.mk #[0xab]), true),
    ("fragment number changed", Bytes.overwrite (f 0) 22 (ByteArray.mk #[0x31]), false),
    ("ToDS flipped", Bytes.overwrite (f 0) 1 (ByteArray.mk #[0x43]), false),
    ("QoS upper byte changed (masked)", Bytes.overwrite qf 25 (ByteArray.mk #[0x7f]), true),
    ("QoS TID changed", Bytes.overwrite qf 24 (ByteArray.mk #[0x06]), false),
    ("QoS control intact", qf, true)]
  for (label, frame, acc) in cases do
    let (o, ok) := decapCase tk gtk 1 frame
    gt := gt.add label o (ok && (reg o 0 == 1) == acc)
  -- Flips of AAD-masked header bits (Retry, PwrMgt, MoreData, sequence
  -- number, QoS upper bits) legitimately still verify.
  gt := { gt with name := gt.name ++ s!"; {tamperAccepted} tampered frames only touched masked bits and verified" }
  return (g, gt, r)

/-! ## DHCP frames -/

def ourMac : ByteArray := ByteArray.mk Mlme.ourMac.data

def u32 (v : UInt32) : ByteArray := Bytes.u32be v

def buildGroup (rng : Rng) : Group × Rng := Id.run do
  let mut g : Group := { name := "dhcp discover/request frames (25 random xid/bssid/offer each)" }
  let mut r := rng
  for j in [0:25] do
    let (bssid, r1) := r.bytes 6
    let (xidB, r2) := r1.bytes 4
    let (ipB, r3) := r2.bytes 4
    let (srvB, r4) := r3.bytes 4
    r := r4
    let xid := Bytes.getU32be xidB 0
    let frame (dg : ByteArray) :=
      Ieee80211.dataToAp bssid ourMac Ieee80211.broadcastMac 0 Ieee80211.ethertypeIPv4 dg
    let inputs := [(Mlme.bssidAt, bssid), (DevDhcp.xidAt, xidB)]
    let want := frame (Dhcp.discover ourMac xid)
    let o := runCase inputs (fun ls => DevDhcp.callDiscover ls.D (.imm aOut)) [(aOut, want)]
    g := g.add s!"discover {j}" o (reg o 0 == want.size.toUInt32)
    let want := frame (Dhcp.request ourMac xid (Bytes.getU32be ipB 0) (Bytes.getU32be srvB 0))
    let o := runCase (inputs ++ [(DevDhcp.yiaddrAt, ipB), (DevDhcp.serverIdAt, srvB)])
      (fun ls => DevDhcp.callRequest ls.D (.imm aOut)) [(aOut, want)]
    g := g.add s!"request {j}" o (reg o 0 == want.size.toUInt32)
  return (g, r)

/-! ## DHCP reply parsing -/

/-- A BOOTREPLY with the given options (raw bytes after the cookie). -/
def bootReply (op : UInt8) (xid : UInt32) (yiaddr : UInt32) (chaddr : ByteArray)
    (opts : ByteArray) : ByteArray :=
  Bytes.concat [ByteArray.mk #[op, 1, 6, 0], u32 xid, Bytes.zeros 4, Bytes.zeros 4, u32 yiaddr,
    u32 0xc0a80101, Bytes.zeros 4, Bytes.take (chaddr ++ Bytes.zeros 16) 16, Bytes.zeros 192,
    Dhcp.magicCookie, opts]

/-- IPv4/UDP around `payload` with optional IPv4 options (`ihlExtra` words). -/
def ipUdp (sport dport : UInt16) (payload : ByteArray) (ihlExtra : Nat := 0) (flags : UInt16 := 0) :
    ByteArray :=
  let ihl := 20 + 4 * ihlExtra
  let total := ihl + 8 + payload.size
  let hdr := Bytes.concat [ByteArray.mk #[(0x40 + ihl / 4).toUInt8, 0x10], Bytes.u16be total.toUInt16,
    Bytes.u16be 0x1234, Bytes.u16be flags, ByteArray.mk #[64, 17, 0, 0], u32 0xc0a80101, u32 0xffffffff,
    Bytes.replicate (4 * ihlExtra) 1]
  let hdr := Bytes.overwrite hdr 10 (Bytes.u16be (Dhcp.internetChecksum hdr))
  Bytes.concat [hdr, Bytes.u16be sport, Bytes.u16be dport, Bytes.u16be (8 + payload.size).toUInt16,
    Bytes.u16be 0, payload]

def snapIp : ByteArray := Ieee80211.llcSnap Ieee80211.ethertypeIPv4

def slotAddrs : List UInt32 :=
  [DevDhcp.typeAt, DevDhcp.yiaddrAt, DevDhcp.serverIdAt, DevDhcp.routerAt, DevDhcp.subnetAt,
   DevDhcp.leaseAt, DevDhcp.presentAt]

/-- Expected (r0, slot words) from the reference parser, or `none` when the
device must reject (slots unchanged). -/
def parseExpect (xid : UInt32) (body : ByteArray) : Option (UInt32 × ByteArray) := do
  if !Bytes.beq (body.extract 0 8) snapIp then none
  let m ← Dhcp.parseReply (body.extract 8 body.size)
  if m.xid != xid || !Bytes.beq (m.chaddr.extract 0 6) ourMac then none
  let t ← m.type?
  if t != 2 && t != 5 && t != 6 then none
  let addr (code : UInt8) (bit : UInt32) : UInt32 × ByteArray :=
    match m.addrOpt? code with
    | some a => (bit, u32 a)
    | none => (0, Bytes.zeros 4)
  let (b1, s) := addr Dhcp.Opt.serverId DevDhcp.serverIdBit
  let (b2, rt) := addr Dhcp.Opt.router DevDhcp.routerBit
  let (b3, sn) := addr Dhcp.Opt.subnetMask DevDhcp.subnetBit
  let (b4, ls) := addr Dhcp.Opt.leaseTime DevDhcp.leaseBit
  let present := b1 ||| b2 ||| b3 ||| b4 ||| DevDhcp.typeBit
  return (t.toUInt32, Bytes.concat [Bytes.u32le t.toUInt32, u32 m.yiaddr, s, rt, sn, ls,
    Bytes.u32le present])

def parseCase (xid : UInt32) (body : ByteArray) : Outcome × Bool :=
  let seeded := Bytes.replicate 28 0xcc
  let inputs := [(DevDhcp.xidAt, u32 xid), (DevDhcp.typeAt, seeded), (aIn, body)]
  let exp := parseExpect xid body
  let o := runCase inputs (fun ls => DevDhcp.callParse ls.D (.imm aIn) (.imm body.size.toUInt32))
    (match exp with
     | some (_, slots) => [(DevDhcp.typeAt, slots)]
     | none => [])
  (o, reg o 0 == (exp.map (·.1)).getD 0)

def opt (code : UInt8) (b : ByteArray) : ByteArray := Dhcp.opt code b

def parseGroup (rng : Rng) : Group × Rng := Id.run do
  let mut g : Group := { name := "dhcp parse (hand-built offers/acks/naks, 60 variants + rejections)" }
  let xid : UInt32 := 0x3903F326
  let mut r := rng
  for j in [0:60] do
    let (perm, r1) := r.bytes 8
    let (vals, r2) := r1.bytes 20
    let (npad, r3) := r2.below 4
    r := r3
    let t : UInt8 := #[2, 5, 6][j % 3]!
    let optsList : Array ByteArray := #[
      opt 54 (vals.extract 0 4), opt 3 (vals.extract 4 8), opt 1 (vals.extract 8 12),
      opt 51 (vals.extract 12 16), opt 6 (vals.extract 16 20 ++ vals.extract 0 4),
      opt 12 "host".toUTF8, opt 58 (vals.extract 4 8)]
    -- Random order: sort by the random key bytes; drop some options now and then.
    let keyed := (optsList.zipIdx.map fun (o, i) => (perm.get! i, o)).qsort (fun a b => a.1 < b.1)
    let kept : List ByteArray :=
      (keyed.toList.zipIdx.filter (fun (_, i) => j % 5 != 0 || i % 2 == 0)).map (·.1.2)
    let typeOpt := opt 53 (ByteArray.mk #[t])
    let pos := j % (kept.length + 1)
    let body := kept.take pos ++ [typeOpt] ++ kept.drop pos
    let pads := Bytes.zeros npad
    let opts := Bytes.concat (body.map (pads ++ ·)) ++ ByteArray.mk #[255] ++
      Bytes.zeros (j % 4)
    -- Variants: duplicates (first wins), short/long values, IPv4 options, link padding.
    let opts := match j % 6 with
      | 1 => opt 54 (hx "0a000001") ++ opts            -- duplicate: this one first
      | 2 => opt 3 (hx "0a01") ++ opts                  -- first router too short → none
      | 3 => opt 1 (hx "ffffff0000") ++ opts            -- longer than 4: first 4 used
      | _ => opts
    let ip := ipUdp 67 68 (bootReply 2 xid (Bytes.getU32be vals 0) ourMac opts) (j % 4 / 3)
    let body := snapIp ++ ip ++ Bytes.zeros (j % 3)
    let (o, ok) := parseCase xid body
    g := g.add s!"variant {j} type {t}" o (ok && (parseExpect xid body).isSome)
  -- Rejections (and the equivalent reference verdicts).
  let good := bootReply 2 xid 0xc0a80164 ourMac
    (opt 53 (ByteArray.mk #[2]) ++ opt 54 (hx "c0a80101") ++ ByteArray.mk #[255])
  let ip := ipUdp 67 68 good
  let flipAt (b : ByteArray) (i : Nat) := Bytes.overwrite b i (ByteArray.mk #[Bytes.at! b i ^^^ 0x01])
  let rej : List (String × ByteArray) := [
    ("good offer (control)", snapIp ++ ip),
    ("wrong xid", snapIp ++ ipUdp 67 68 (bootReply 2 (xid + 1) 1 ourMac (opt 53 (hx "02") ++ hx "ff"))),
    ("wrong chaddr", snapIp ++ ipUdp 67 68 (bootReply 2 xid 1 (Bytes.replicate 6 7) (opt 53 (hx "05") ++ hx "ff"))),
    ("op = 1", snapIp ++ ipUdp 67 68 (bootReply 1 xid 1 ourMac (opt 53 (hx "02") ++ hx "ff"))),
    ("bad ip checksum", snapIp ++ flipAt ip 10),
    ("bad cookie", snapIp ++ flipAt ip (28 + 236)),
    ("wrong dst port", snapIp ++ ipUdp 67 69 good),
    ("wrong src port", snapIp ++ ipUdp 68 68 good),
    ("fragment", snapIp ++ ipUdp 67 68 good 0 0x2000),
    ("truncated option", snapIp ++ ipUdp 67 68 (bootReply 2 xid 1 ourMac (opt 53 (hx "02") ++ hx "3608c0a8"))),
    ("no type option", snapIp ++ ipUdp 67 68 (bootReply 2 xid 1 ourMac (opt 54 (hx "c0a80101") ++ hx "ff"))),
    ("type length 2 first", snapIp ++ ipUdp 67 68 (bootReply 2 xid 1 ourMac (opt 53 (hx "0202") ++ opt 53 (hx "02") ++ hx "ff"))),
    ("type 3 (request)", snapIp ++ ipUdp 67 68 (bootReply 2 xid 1 ourMac (opt 53 (hx "03") ++ hx "ff"))),
    ("bootp < 240", snapIp ++ ipUdp 67 68 (good.extract 0 239)),
    ("options without END", snapIp ++ ipUdp 67 68 (bootReply 2 xid 1 ourMac (opt 53 (hx "05")))),
    ("not IPv4 ethertype", Ieee80211.llcSnap 0x86dd ++ ip),
    ("ip total > buffer", snapIp ++ ip.extract 0 (ip.size - 1)),
    ("too short", snapIp ++ ip.extract 0 10)]
  for (label, body) in rej do
    let (o, ok) := parseCase xid body
    g := g.add label o (ok && ((reg o 0 != 0) == (label == "good offer (control)" || label == "options without END"))) s!"r0={reg o 0} want={(parseExpect xid body).map (·.1)}"
  return (g, r)

/-! ## Step counts -/

def stepReport : IO Unit := do
  let row (label : String) (o : Outcome) : IO Unit :=
    let us := (o.steps * 20 + 500) / 1000
    IO.println s!"  {label}{"".pushn ' ' (44 - label.length)}{o.steps} steps  (~{us} us at 20 ns/step){if o.ok then "" else "  [FAILED]"}"
  let tk := Bytes.replicate 16 9
  let hdr := hx "0841" ++ Bytes.replicate 22 5
  let disc := Dhcp.discover ourMac 1
  let mpdu := hdr ++ snapIp ++ disc
  row s!"ccmp encap DHCPDISCOVER ({mpdu.size} bytes)" (encapCase tk 5 0 mpdu).1
  let big := hdr ++ Bytes.replicate 1500 7
  row "ccmp encap 1500-byte body" (encapCase tk 5 0 big).1
  let rxHdr := hx "8842" ++ Bytes.replicate 22 5 ++ hx "0500"
  let rx := (Ieee80211.ccmpEncap tk 9 0 (rxHdr ++ snapIp ++ disc)).getD .empty
  row s!"ccmp decap QoS {rx.size}-byte MPDU" (decapCase tk tk 1 rx).1
  let rxBig := (Ieee80211.ccmpEncap tk 9 0 (rxHdr ++ Bytes.replicate 1500 7)).getD .empty
  row "ccmp decap 1500-byte body" (decapCase tk tk 1 rxBig).1
  let bssid := Bytes.replicate 6 0x22
  let o := runCase [(Mlme.bssidAt, bssid)] (fun ls => DevDhcp.callDiscover ls.D (.imm aOut))
    [(aOut, Ieee80211.dataToAp bssid ourMac Ieee80211.broadcastMac 0 Ieee80211.ethertypeIPv4
      (Dhcp.discover ourMac 0))]
  row "dhcp discover frame build" o
  let xid : UInt32 := 0x01020304
  let offer := snapIp ++ ipUdp 67 68 (bootReply 2 xid 0xc0a80164 ourMac
    (opt 53 (hx "02") ++ opt 54 (hx "c0a80101") ++ opt 51 (hx "00000e10") ++ opt 1 (hx "ffffff00") ++
     opt 3 (hx "c0a80101") ++ opt 6 (hx "0808080801010101") ++ hx "ff"))
  row "dhcp parse offer" (parseCase xid offer).1

def main : IO UInt32 := do
  let fails ← IO.mkRef 0
  let r : Rng := ⟨0xC0FFEE0123456789⟩
  let (g, r) := encapGroup r
  report g fails
  let (g, gt, r) := decapGroup r
  report g fails
  report gt fails
  let (g, r) := buildGroup r
  report g fails
  let (g, _) := parseGroup r
  report g fails
  IO.println "dynamic instruction counts (routine incl. argument setup, call and return):"
  stepReport
  let n ← fails.get
  if n == 0 then
    IO.println "ALL PASS"
    return 0
  else
    IO.println s!"{n} GROUP(S) FAILED"
    return 1
