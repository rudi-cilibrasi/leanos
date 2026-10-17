import LeanOS.Net.Rtl8168
import LeanOS.DeviceProgramConfinement

/-!
# RTL8168 teardown (issue #577)

The `rtl8168-arp` program must hand the controller back the way re(4)'s
`re_stop` and `re_reset` do, on every exit after it enables the
transmit/receive engines (`LeanOS/Net/Rtl8168.lean`, `docs/net-rtl8168.md`).

These fixtures run the encoded program, under its declared policy, in the
reference simulator against a recording model of the controller whose link
is up but whose transmit DMA never completes (the transmit-stuck exit) or
whose link never comes up (the no-link exit) — the model cannot complete
descriptors, and the success path runs the same exit block. They check the
register writes of the teardown, the descriptors it leaves in scratch, Bus
Master, and the before/after register dumps; and statically, over the
encoded words, that no `fail` or `halt` lies between the engine enable and
the teardown's reset. Synthetic negatives show that the checks reject the
pre-#577 stop and an exit that skips the teardown.
-/

namespace LeanOS.NegativeFixtures.Rtl8168Teardown

open LeanOS.Wifi.Bytecode LeanOS.Wifi.Sim LeanOS.Net.Rtl8168 LeanOS.DeviceProgramConfinement

/-- What the model records: MMIO writes as (bits, offset, value) and
command-register updates as (offset, clear, set). -/
structure Log where
  writes : Array (Nat × UInt32 × UInt32) := #[]
  cfg : Array (UInt32 × UInt32 × UInt32) := #[]
  deriving Inhabited

/-- An 8168E-VL whose reset completes at once, whose transmit queue is empty,
whose RXCFG reads back the program's configuration, and whose link is up or
down. Everything else reads 0. -/
def model (link : Bool) : Device Log where
  read32 s off :=
    (if off == txcfg then hwrev8168eVl ||| txcfgQueueEmpty
     else if off == rxcfg then rxcfgConfig else 0, s)
  read16 s _ := (0, s)
  write32 s off v := { s with writes := s.writes.push (32, off, v) }
  write16 s off v := { s with writes := s.writes.push (16, off, v.toUInt32) }
  cfgRead32 s off := (if off == 0 then 0x816810ec else 0x00100007, s)
  cfgWrite32 s _ _ := s
  cfgUpdate32 s off c t := { s with cfg := s.cfg.push (off, c, t) }
  read8 s off := (if off == gmediastat then (if link then 0x8B else 0) else 0, s)
  write8 s off v := { s with writes := s.writes.push (8, off, v.toUInt32) }

/-- The generated image's program, with the policy the generator embeds. -/
def prog (body : ProgM Unit) : Program :=
  match build body with
  | .ok p => { p with policy := some qotomRtl8168Policy }
  | .error _ => { words := #[], blob := .empty, sections := #[] }

def arp : Program := prog program

/- The program, as the generator admits it. -/
#guard admissible arp qotomRtl8168Policy

/-- The writes after the last write of `v` to the command register. -/
def after (log : Log) (v : UInt32) : List (Nat × UInt32 × UInt32) :=
  let ws := log.writes.toList
  match (List.range ws.length).reverse.find? (fun i => ws[i]! == (8, command, v)) with
  | some i => ws.drop (i + 1)
  | none => []

/-- The command-register writes after the engines were enabled. -/
def commandWritesAfterEnable (log : Log) : List UInt32 :=
  (after log cmdTxRx).filterMap fun (w, off, v) => if w == 8 && off == command then some v else none

/-- re(4)'s stop and reset: the command register goes from TE|RE to the stop
request and then only to RST; never to 0 in between. -/
def faithfulStop (log : Log) : Bool :=
  commandWritesAfterEnable log == [cmdStopReq ||| cmdTxRx, cmdReset]

/-- The exact teardown writes, from the receive-filter write on: accept bits
off with the rest of RXCFG kept, stop request, interrupts masked and
acknowledged, reset, 9346CR locked, and nothing after it. -/
def teardownWrites : List (Nat × UInt32 × UInt32) :=
  [(32, rxcfg, rxcfgConfig &&& ~~~rxcfgAccept), (8, command, cmdStopReq ||| cmdTxRx),
   (16, imr, 0), (16, isr, 0xFFFF), (8, command, cmdReset), (8, eecmd, 0)]

def endsWithTeardown (log : Log) : Bool :=
  log.writes.toList.drop (log.writes.size - teardownWrites.length) == teardownWrites

/-- Scratch after the run: no descriptor is chip-owned or names a buffer. -/
def disarmed (mem : ByteArray) : Bool :=
  (List.range rxCount).all (fun k =>
    let d := rxRing.toNat + 16 * k
    le32 mem d &&& own == 0 && le32 mem (d + 8) == 0 && le32 mem (d + 12) == 0) &&
  le32 mem txRing.toNat &&& own == 0 && le32 mem (txRing.toNat + 8) == 0

/-- Bus Master is cleared last. -/
def busMasterOff (log : Log) : Bool := log.cfg.back? == some (0x04, 0xFFFF0004, 0x0002)

/-- Both dumps printed every register. -/
def dumped (prints : Array (UInt32 × UInt32)) : Bool :=
  dumpRegs.all fun (off, _) =>
    prints.any (·.1 == Tag.before ||| off) && prints.any (·.1 == Tag.after ||| off)

def outcome (link : Bool) : Status × Machine Log := LeanOS.Wifi.Sim.run arp (model link) {}

/- Link up, transmit never completes: the transmit-stuck exit tears down. -/
#guard (outcome true).1 == .fail Fail.txStuck
#guard faithfulStop (outcome true).2.dev
#guard endsWithTeardown (outcome true).2.dev
#guard disarmed (outcome true).2.mem
#guard busMasterOff (outcome true).2.dev
#guard dumped (outcome true).2.prints

/- Link down: the no-link exit tears down the same way. -/
#guard (outcome false).1 == .fail Fail.noLink
#guard faithfulStop (outcome false).2.dev
#guard endsWithTeardown (outcome false).2.dev
#guard disarmed (outcome false).2.mem
#guard busMasterOff (outcome false).2.dev

/-! ## Every exit after enable runs the teardown (static) -/

def isCommandWrite (w : Word4) (v : UInt32) : Bool :=
  w.op == (opcode (.write8 0 (.imm 0)) ||| immFlag) && w.a == command && w.b == v

/-- Every `halt` and `fail` word lies before the first engine enable or
after the last `RST` (the teardown's). -/
def exitsTearDown (ws : Array Word4) : Bool :=
  let idx := List.range ws.size
  match idx.find? (fun i => isCommandWrite ws[i]! cmdTxRx),
      idx.reverse.find? (fun i => isCommandWrite ws[i]! cmdReset) with
  | some e, some r =>
    e < r && idx.all fun i =>
      let op := ws[i]!.op &&& 0xFF
      !(op == 0 || op == 1) || i < e || r < i
  | _, _ => false

#guard exitsTearDown arp.words

/-! ## Negatives -/

private def words (is : List Instr) : Array Word4 :=
  (is.map fun i => (encode i).getD ⟨0, 0, 0, 0⟩).toArray

/- An exit between enable and teardown (the pre-#577 no-reply path). -/
#guard !exitsTearDown (words [.write8 command (.imm cmdTxRx), .fail Fail.noReply,
  .write8 command (.imm cmdReset), .halt])

/- No teardown reset at all. -/
#guard !exitsTearDown (words [.write8 command (.imm cmdTxRx), .halt])

/- The pre-#577 stop: RXCFG zeroed, stop request, then 0 to the command
register at once. -/
private def oldStop : Log :=
  { writes := #[(8, command, cmdTxRx), (32, rxcfg, 0), (8, command, cmdStopReq ||| cmdTxRx),
      (8, command, 0), (16, imr, 0), (16, isr, 0xFFFF)] }

#guard !faithfulStop oldStop
#guard !endsWithTeardown oldStop

/- A teardown that leaves the receive descriptor chip-owned is caught. -/
#guard !disarmed (memStore (ByteArray.mk (Array.replicate scratchBytes 0)) rxRing.toNat 4
  (own ||| eor ||| rxBufBytes))

end LeanOS.NegativeFixtures.Rtl8168Teardown
