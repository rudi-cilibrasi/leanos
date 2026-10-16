import LeanOS.Wifi.Endpoint
import LeanOS.Wifi.Sim

/-! Simulator test for the link-only endpoint's lease window and serve window
(issue #573, `LeanOS.Wifi.Endpoint.serveWith`).

The BCM43224 serve program runs in the simulator against a radio that
receives nothing: its TSF advances 1000 µs per poll of the receive FIFO
(the program's `delay 1000`) and 50 µs per read of the TSF itself. A harness
stands in for the kernel: it takes every record the program yields (the link
record, then a tick each TSF second) and, from a chosen TSF time on, stores
1 in the lease signal word (`FrameSource.leaseSignalAt`) before resuming the
program, as the kernel does at the DHCP subject's hand-off. The test
requires, for several lease times and windows:

* with a lease signal at time `T` within the lease window, the program
  records `Tag.leaseSignalled` once, with a value within a second of `T`,
  never `Tag.leaseWindowOver`, and halts between `serve` and `serve + 1 s`
  of TSF time after it saw the signal, however late `T` came in the lease
  window: a slow DHCP server does not consume the serve window;
* without a signal, it records `Tag.leaseWindowOver` with the lease window,
  never `Tag.leaseSignalled`, and halts within a second after the lease
  window ends;
* a signal after the lease window has no effect;
* the first record is the 6-byte link record, every other one a 1-byte
  tick, and the ticks come at least a second of TSF time apart.

usage: leanos-wifi-leasesim -/

open LeanOS.Wifi LeanOS.Wifi.Bytecode

structure Radio where
  tsf : UInt32 := 0
  deriving Inhabited

def device : Sim.Device Radio where
  read32 r off :=
    if off == 0x180 then (r.tsf, { r with tsf := r.tsf + 50 })
    else if off == Mac.rxPioCtl then (0, { r with tsf := r.tsf + 1000 })
    else (0, r)
  read16 r _ := (0, r)
  write32 r _ _ := r
  write16 r _ _ := r
  cfgRead32 r _ := (0, r)
  cfgWrite32 r _ _ := r

def prog (leaseUs serveUs : UInt32) : ProgM Unit := do
  let L ← DevCrypto.install
  let C ← DevCcmp.install L
  Endpoint.serveLink L C (Tx.TxConfig.ofPhy (NPhy.qotom 6) .ofdm6 Tx.txAcBeFifo) leaseUs serveUs
  halt

structure Outcome where
  status : Sim.Status
  /-- TSF time at the halt. -/
  endAt : UInt32
  /-- Every yielded record: its length and the TSF time it was yielded. -/
  records : Array (UInt32 × UInt32)
  /-- The TSF time the harness first set the lease signal, if it did. -/
  signalAt : Option UInt32
  prints : Array (UInt32 × UInt32)

/-- Run the program with lease window `leaseUs` and serve window `serveUs`;
the harness sets the lease signal before the first resumption at or after
TSF time `lease`. -/
def runCase (leaseUs serveUs : UInt32) (lease : Option UInt32) : IO Outcome := do
  match build (prog leaseUs serveUs) with
  | .error e => throw (IO.userError e)
  | .ok p =>
    let limit := 400000000
    let mut (st, m) := Sim.run p device {} limit
    let mut records : Array (UInt32 × UInt32) := #[]
    let mut signalAt : Option UInt32 := none
    while true do
      match st with
      | .yield v =>
        records := records.push (v, m.dev.tsf)
        if signalAt.isNone then
          if let some t := lease then
            if m.dev.tsf ≥ t then
              signalAt := some m.dev.tsf
              m := { m with mem := m.mem.set! LeanOS.Net.FrameSource.leaseSignalAt.toNat 1 }
        (st, m) := Sim.resume p device limit m
      | _ => break
    return { status := st, endAt := m.dev.tsf, records, signalAt, prints := m.prints }

def sec : UInt32 := 1000000

def main : IO UInt32 := do
  let mut failures := 0
  let check (name : String) (ok : Bool) : IO Unit :=
    IO.println s!"{if ok then "PASS" else "FAIL"} {name}"
  -- (lease window, serve window, lease signal time)
  let cases : List (UInt32 × UInt32 × Option UInt32) := [
    (30 * sec, 10 * sec, some (2 * sec)),
    (30 * sec, 10 * sec, some (25 * sec)),
    (8 * sec, 15 * sec, some (7 * sec)),
    (8 * sec, 10 * sec, none),
    (5 * sec, 10 * sec, some (9 * sec))]
  for (leaseUs, serveUs, lease) in cases do
    let o ← runCase leaseUs serveUs lease
    let name := s!"lease window {leaseUs / sec} s, serve window {serveUs / sec} s, lease {lease.map (· / sec)}"
    let signalled := o.prints.filter (·.1 == Endpoint.Tag.leaseSignalled)
    let over := o.prints.filter (·.1 == Endpoint.Tag.leaseWindowOver)
    let shape := o.records.size ≥ 2 && o.records[0]!.1 == 6 &&
      (o.records.extract 1 o.records.size).all (·.1 == 1)
    let ticks := (o.records.extract 1 o.records.size).map (·.2)
    let spaced := (List.range (ticks.size - 1)).all fun i => ticks[i + 1]! - ticks[i]! ≥ sec
    let mut ok := o.status == .halt && shape && spaced
    let inWindow : Bool := match o.signalAt with
      | some t => decide (t < leaseUs + sec)  -- seen on the program's next turn
      | none => false
    if inWindow then
      let t := o.signalAt.get!
      let seen := signalled.toList.map (·.2)
      ok := ok && over.isEmpty && seen.length == 1 &&
        (seen.head! ≥ t - 100000 && seen.head! ≤ t + sec)
      -- the serve window runs from the moment the program saw the signal
      let servedFrom := seen.head!
      ok := ok && o.endAt ≥ servedFrom + serveUs && o.endAt ≤ servedFrom + serveUs + sec
    else
      ok := ok && signalled.isEmpty && over.toList.map (·.2) == [leaseUs] &&
        o.endAt ≥ leaseUs && o.endAt ≤ leaseUs + sec
    check s!"{name}: halt at {o.endAt / 1000} ms after {o.records.size} records, signal {o.signalAt.map (· / 1000)} ms" ok
    if !ok then failures := failures + 1
  IO.println s!"{failures} failure(s)"
  return if failures == 0 then 0 else 1
