import LeanOS.Net.RekeySource
import LeanOS.Wifi.Sim

/-! Simulator test for group-key rotation on the frame-endpoint path
(issue #557; `LeanOS.GtkRekey`, `LeanOS.Wifi.Endpoint.handleFrame`).

1. **The q35 frame source** (`LeanOS.Net.RekeySource.program`, the
   `gtk-rekey` image's driver program) runs in the simulator with the
   network subject played by the reference responder
   `LeanOS.Net.Echo.replyFrame`. It must halt, having checked every
   frame's outcome, every transmitted MPDU and the key state after every
   frame against the model, and stay within the q35 kernel's step limit.
2. **Model against program, on random frame sequences**: a harness program
   runs the driver's receive path (`Endpoint.handleFrame`) and transmit path
   (`Endpoint.takeTx`) on frames the test injects, yielding every delivered
   frame and every transmitted MPDU. For each frame of 160 random sequences
   (key-id rollover 1↔2↔3, retransmitted, stale and forged group messages,
   key id 0, failed unwraps, packet numbers at, below and above every floor
   and across the 32-bit boundary) the program must do exactly what
   `GtkRekey.step` says: deliver exactly the frame's Ethernet II view, send
   exactly one group message 2 (decrypted with the TK, MIC valid, the
   replay counter echoed), or do nothing; and afterwards its key state must
   be the model's.

usage: leanos-wifi-rekeysim -/

open LeanOS LeanOS.Wifi LeanOS.Wifi.Bytecode LeanOS.Wifi.Bytes LeanOS.Net
open LeanOS.GtkRekey (State Frame Body Out GroupMsg1)
open LeanOS.Net.RekeySource (keyBytes kck kek hostMac macU64 frameEthernet mpdu le48)

/-- The q35 kernel's limit on the frame source's steps
(`NETWORK_STEP_LIMIT`). -/
def q35StepLimit : Nat := 4000000

/-! ## 1. The q35 frame source -/

/-- Run the frame source, answering every yielded frame with the reference
responder. Returns the final status, steps, yields and prints. -/
def runSource : Sim.Status × Nat × Nat × Array (UInt32 × UInt32) := Id.run do
  match build RekeySource.program with
  | .error _ => return (.error "build", 0, 0, #[])
  | .ok p =>
    let mut (st, m) := Sim.run p Sim.Device.none () 100000000
    let mut yields := 0
    while true do
      match st with
      | .yield len =>
        yields := yields + 1
        let f := m.mem.extract FrameSource.rxAt.toNat (FrameSource.rxAt.toNat + len.toNat)
        let reply := if yields == 1 then none else Echo.replyFrame f (macU64 hostMac) FrameSource.ip
        let mut mem := m.mem
        match reply with
        | some r =>
          for i in [0:r.size] do mem := mem.set! (FrameSource.txAt.toNat + i) r[i]!
          mem := Sim.memStore mem FrameSource.txLenAt.toNat 4 r.size.toUInt32
        | none => mem := Sim.memStore mem FrameSource.txLenAt.toNat 4 0
        (st, m) := Sim.resume p Sim.Device.none 100000000 { m with mem }
      | _ => break
    return (st, m.steps, yields, m.prints)

/-! ## 2. Model against program -/

def needFrame : UInt32 := 0xFFFF0000
def inLenAt : UInt32 := 0x3F020

/-- The driver's receive and transmit paths on injected frames. -/
def harness : ProgM Unit := do
  let L ← DevCrypto.install
  let C ← DevCcmp.install L
  -- a transmission yields 0x10000 + its length
  let radio : Responder.Radio := ⟨do mov 13 12; addi 13 0x10000; emit (.yield (.reg 13))⟩
  let top ← newLabel
  let delivered ← newLabel
  let done ← newLabel
  place top
  emit (.yield (.imm needFrame))
  li 0 0
  emit (.memLoad 4 5 0 inLenAt)
  emit (.branch .eq 5 (.imm 0) done)
  Endpoint.handleFrame L C radio delivered top
  place delivered
  Endpoint.takeTx C radio
  emit (.jump top)
  place done
  halt

def setBytes (mem : ByteArray) (at_ : Nat) (b : ByteArray) : ByteArray := Id.run do
  let mut mem := mem
  for i in [0:b.size] do mem := mem.set! (at_ + i) b[i]!
  return mem

def seed (s : State) (m : Sim.Machine Unit) : Sim.Machine Unit :=
  let mem := setBytes m.mem Handshake.kckAt.toNat kck
  let mem := setBytes mem Handshake.kekAt.toNat kek
  let mem := setBytes mem Handshake.tkAt.toNat (keyBytes s.tk)
  let mem := setBytes mem Handshake.gtkAt.toNat (keyBytes s.gtk)
  let mem := mem.set! Handshake.gtkIdAt.toNat s.gtkId.toUInt8
  let mem := setBytes mem Handshake.replayAt.toNat (u64be s.replay.toUInt64)
  let mem := setBytes mem Mlme.bssidAt.toNat RekeySource.bssid
  let mem := setBytes mem Responder.lastPnTk.toNat (le48 s.pnTk)
  let mem := setBytes mem Responder.lastPnGtk.toNat (le48 s.pnGtk)
  { m with mem }

/-- The driver's key state, read back from scratch. -/
def stateOf (mem : ByteArray) (s : State) : Bool :=
  let ext (a : UInt32) (n : Nat) := mem.extract a.toNat (a.toNat + n)
  mem[Handshake.gtkIdAt.toNat]! == s.gtkId.toUInt8 &&
  (ext Handshake.gtkAt 16).data == (keyBytes s.gtk).data &&
  (ext Handshake.tkAt 16).data == (keyBytes s.tk).data &&
  (ext Handshake.replayAt 8).data == (u64be s.replay.toUInt64).data &&
  (ext Responder.lastPnTk 6).data == (le48 s.pnTk).data &&
  (ext Responder.lastPnGtk 6).data == (le48 s.pnGtk).data

inductive Event where
  | deliver (eth : ByteArray)
  | tx (mpdu : ByteArray)

/-- Feed one frame (`none`: end) and collect what the program does until it
asks for the next one. -/
def feed (p : Program) (m : Sim.Machine Unit) (f : Option ByteArray) :
    Except String (Sim.Machine Unit × Array Event) := Id.run do
  let mut mem := m.mem
  match f with
  | some b =>
    mem := setBytes mem Mlme.rxMpdu.toNat b
    mem := Sim.memStore mem inLenAt.toNat 4 (b.size + 4).toUInt32
  | none => mem := Sim.memStore mem inLenAt.toNat 4 0
  let mut (st, m) := Sim.resume p Sim.Device.none (m.steps + 50000000) { m with mem }
  let mut events : Array Event := #[]
  for _ in [0:8] do
    match st with
    | .yield v =>
      if v == needFrame then return .ok (m, events)
      if v ≥ 0x10000 then
        let n := (v - 0x10000).toNat
        events := events.push (.tx (m.mem.extract Mlme.txMpdu.toNat (Mlme.txMpdu.toNat + n)))
        (st, m) := Sim.resume p Sim.Device.none (m.steps + 50000000) m
      else
        let eth := m.mem.extract FrameSource.rxAt.toNat (FrameSource.rxAt.toNat + v.toNat)
        events := events.push (.deliver eth)
        let replied := match Echo.replyFrame eth (macU64 hostMac) FrameSource.ip with
          | some r => Sim.memStore (setBytes m.mem FrameSource.txAt.toNat r)
              FrameSource.txLenAt.toNat 4 r.size.toUInt32
          | none => Sim.memStore m.mem FrameSource.txLenAt.toNat 4 0
        (st, m) := Sim.resume p Sim.Device.none (m.steps + 50000000) { m with mem := replied }
    | .halt => return if f.isNone then .ok (m, events) else .error "halted early"
    | other => return .error s!"status {repr other} at pc {m.pc}"
  return .error "too many events for one frame"

/-- A transmitted MPDU decrypted with the TK: group message 2 echoing `r`? -/
def isMsg2 (tk : ByteArray) (mp : ByteArray) (r : Nat) : Bool :=
  match Ieee80211.ccmpDecap tk mp with
  | none => false
  | some pl =>
    let body := pl.mpdu.extract 24 pl.mpdu.size
    pl.keyId == 0 && pl.mpdu[0]! == 0x08 && pl.mpdu[1]! == 0x01 &&
    (pl.mpdu.extract 4 10).data == RekeySource.bssid.data &&
    (pl.mpdu.extract 10 16).data == hostMac.data &&
    (body.extract 0 8).data == (Ieee80211.llcSnap Ieee80211.ethertypeEapol).data &&
    match Eapol.parseKeyFrame (body.extract 8 body.size) with
    | some k => k.keyInfo == (Eapol.KeyInfo.versionHmacSha1Aes ||| Eapol.KeyInfo.mic |||
        Eapol.KeyInfo.secure) && k.replayCounter == r.toUInt64 && k.keyData.size == 0 &&
        Eapol.micValid kck (body.extract 8 body.size)
    | none => false

/-- A transmitted MPDU decrypted with the TK: the ToDS frame carrying the
Ethernet II reply `r`? -/
def isReply (tk : ByteArray) (mp : ByteArray) (r : ByteArray) : Bool :=
  match Ieee80211.ccmpDecap tk mp with
  | none => false
  | some pl =>
    pl.mpdu[1]! == 0x01 && (pl.mpdu.extract 16 22).data == (r.extract 0 6).data &&
    (pl.mpdu.extract 24 32).data ==
      (ByteArray.mk #[0xAA, 0xAA, 0x03, 0, 0, 0] ++ r.extract 12 14).data &&
    (pl.mpdu.extract 32 pl.mpdu.size).data == (r.extract 14 r.size).data

/-- Does the program's behaviour on one frame match the model's outcome? -/
def agrees (tk : ByteArray) (f : Frame) (o : Out) (events : Array Event) : Bool :=
  match o, events.toList with
  | .drop _, [] => true
  | .msg2 r, [.tx mp] => isMsg2 tk mp r
  | .deliver _, .deliver eth :: rest =>
    eth.data == (frameEthernet f).data &&
    match Echo.replyFrame eth (macU64 hostMac) FrameSource.ip, rest with
    | none, [] => true
    | some r, [.tx mp] => isReply tk mp r
    | _, _ => false
  | _, _ => false

/-! ### Random sequences -/

structure Rng where
  s : Nat

def Rng.next (g : Rng) : Nat × Rng :=
  let s := (g.s * 6364136223846793005 + 1442695040888963407) % 18446744073709551616
  (s / 4294967296, ⟨s⟩)

def Rng.below (g : Rng) (n : Nat) : Nat × Rng := let (v, g) := g.next; (v % n, g)

/-- Packet numbers near `floor`: below, at, just above, far above, and
across the 32-bit boundary. -/
def pnNear (g : Rng) (floor : Nat) : Nat × Rng :=
  let (k, g) := g.below 8
  let (d, g) := g.below 4
  let pn := match k with
    | 0 => floor - d
    | 1 => floor
    | 2 | 3 | 4 => floor + 1 + d
    | 5 => floor + 1000 + d
    | 6 => 0xFFFFFFFF + d
    | _ => 0x100000000 + 0x10000 * d + 1
  (pn, g)

/-- One random frame for the driver in state `s`. -/
def randomFrame (s : State) (g : Rng) : Frame × Rng := Id.run do
  let mut g := g
  let (kind, g1) := g.below 10; g := g1
  if kind < 4 then
    -- a group message 1 under the TK
    let (pn, g1) := pnNear g s.pnTk; g := g1
    let (rk, g1) := g.below 5; g := g1
    let replay := match rk with | 0 => s.replay | 1 => s.replay - 1 | _ => s.replay + 1 + rk
    let (idk, g1) := g.below 9; g := g1
    let keyId := if idk == 0 then 0 else if idk ≤ 4 then (if s.gtkId == 1 then 2 else 1)
      else if idk ≤ 7 then (if s.gtkId == 3 then 1 else s.gtkId + 1) else s.gtkId
    let (key, g1) := g.below 5; g := g1
    let (bad, g1) := g.below 10; g := g1
    let (rsc, g1) := g.below 4; g := g1
    let rsc := match rsc with | 0 => 0 | 1 => 3 | 2 => 0xFFFFFFF0 | _ => 100
    let m : GroupMsg1 := { replay, keyId, gtk := 30 + key, rsc,
                           micOk := bad != 0, unwrapOk := bad != 1 }
    return ({ keyId := 0, key := s.tk, pn, body := .groupMsg1 m }, g)
  else
    -- a data frame: unicast under the TK, broadcast under the installed key,
    -- the other key ids, or stale material
    let (which, g1) := g.below 6; g := g1
    let (payload, g1) := g.below 4; g := g1
    let (keyId, key, floor) := match which with
      | 0 => (0, s.tk, s.pnTk)
      | 1 | 2 => (s.gtkId, s.gtk, s.pnGtk)
      | 3 => (s.gtkId, s.gtk + 1, s.pnGtk)
      | 4 => (if s.gtkId == 1 then 2 else 1, s.gtk, s.pnGtk)
      | _ => (3, 30 + payload, s.pnGtk)
    let (pn, g1) := pnNear g floor; g := g1
    return ({ keyId, key, pn, body := .data payload }, g)

def main : IO UInt32 := do
  let mut failures := 0
  let check (name : String) (ok : Bool) : IO Unit :=
    IO.println s!"{if ok then "PASS" else "FAIL"} {name}"
  -- 1. the q35 frame source
  let (st, steps, yields, prints) := runSource
  let count (t : UInt32) := (prints.filter (·.1 == t)).size
  let ok := st == .halt
  check s!"gtk-rekey frame source halts ({repr st}) after {steps} steps" ok
  if !ok then failures := failures + 1
  let ok := steps ≤ q35StepLimit
  check s!"within the q35 step limit ({steps} ≤ {q35StepLimit})" ok
  if !ok then failures := failures + 1
  let n := GtkRekey.scenario.length
  let ok := count RekeySource.Tag.stateMatched == n && yields == 5 &&
    count FrameSource.Tag.replyMatched == 4 && count FrameSource.Tag.noReplyMatched == 1 &&
    count RekeySource.Tag.notDelivered == n - 4 && count Responder.Tag.rekeyed == 2 &&
    count RekeySource.Tag.transmitMatched == 6
  check s!"every frame checked against the model ({count RekeySource.Tag.stateMatched}/{n}), 4 replies and 2 group message 2s matched" ok
  if !ok then failures := failures + 1
  -- 2. random sequences
  match build harness with
  | .error e => IO.eprintln e; return 1
  | .ok p =>
    let mut g : Rng := ⟨557⟩
    let mut frames := 0
    let mut outcomes : Array Nat := #[0, 0, 0]
    let mut rekeys := 0
    let mut mismatches := 0
    for seq in [0:160] do
      let s0 : State := { GtkRekey.start with pnTk := 0x10 * seq, pnGtk := seq }
      let (st, m) := Sim.run p Sim.Device.none () 50000000 (init := seed s0)
      if st != .yield needFrame then
        IO.println s!"FAIL harness start {repr st}"; return 1
      let mut m := m
      let mut s := s0
      for _ in [0:12] do
        let (f, g1) := randomFrame s g; g := g1
        let (s', o) := GtkRekey.step s f
        match feed p m (some (mpdu f)) with
        | .error e =>
          IO.println s!"FAIL sequence {seq}: {e}"; mismatches := mismatches + 1; break
        | .ok (m', events) =>
          frames := frames + 1
          match o with
          | .deliver _ => outcomes := outcomes.modify 0 (· + 1)
          | .msg2 _ => outcomes := outcomes.modify 1 (· + 1); rekeys := rekeys + 1
          | .drop _ => outcomes := outcomes.modify 2 (· + 1)
          if !(agrees (keyBytes s.tk) f o events) || !(stateOf m'.mem s') then
            IO.println s!"FAIL sequence {seq}: frame {repr f} model {repr o} events {events.size}"
            mismatches := mismatches + 1
          m := m'
          s := s'
    let ok := mismatches == 0 && rekeys ≥ 50 && outcomes[0]! ≥ 100 && outcomes[2]! ≥ 400
    check s!"{frames} random frames: program agrees with GtkRekey.step ({outcomes[0]!} delivered, {outcomes[1]!} rekeys, {outcomes[2]!} dropped)" ok
    if !ok then failures := failures + 1
  IO.println s!"{failures} failure(s)"
  return if failures == 0 then 0 else 1
