import LeanOS.DeviceProgramConfinement
import LeanOS.Storage.Ahci
import LeanOS.Storage.AhciRead
import LeanOS.Net.Rtl8168
import LeanOS.Usb.Keyboard
import LeanOS.Usb.Mouse
import LeanOS.Usb.MassStorage

/-!
# The Bus Master gate (issue #644)

An address sink bounds the values a program writes to a device's DMA root
register, not the value the register already holds. The executor therefore
refuses to set Bus Master (a `cfgUpdate32` of the command register with bit 2
in its set mask) until the program has written every declared sink's low
dword (a scratch bus address) and high dword (zero): `Policy.busMasterOk`
over `Sim.Machine.armed`. The kernel clears Bus Master at bind.

These fixtures run small programs in the simulator to show what the gate
refuses and admits, and check statically, over the encoded words, that every
DMA program writes both dwords of every sink of its policy before its first
Bus Master set. Each program's setup up to that point is straight-line code
(polling loops only repeat a read), so word order is run order there.
-/

namespace LeanOS.NegativeFixtures.BusMasterGate

open LeanOS.Wifi.Bytecode LeanOS.Wifi LeanOS.DeviceProgramConfinement

/-! ## The gate in the simulator -/

/-- Two sinks (0x20 and 0x30), DMA, Bus Master settable. -/
private def π2 : Policy :=
  { window := 0x1000, cfgRead := 0x3, cfgWrite := 0, cmdClear := 0xFFFF0004, cmdSet := 0x6,
    dma := true, addrSinks := [0x20, 0x30] }

/-- No sink: nothing to wait for. -/
private def π0 : Policy := { π2 with addrSinks := [] }

private def tgt : Target :=
  { bus := 1, dev := 0, fn := 0, id := 0x12345678, windowBytes := 0x1000 }

private def frag (π : Policy) (body : ProgM Unit) : Program :=
  match build (do body; halt) with
  | .ok p => { p with target := some tgt, policy := some π }
  | .error _ => { words := #[], blob := .empty, sections := #[] }

private def status (body : ProgM Unit) (π : Policy := π2) : Sim.Status :=
  (Sim.run (frag π body) Sim.Device.none () 1000).1

private def busMasterOn : ProgM Unit := emit (.cfgUpdate32 0x04 0xFFFF0000 0x0006)

/-- Both dwords of sink `s`: a scratch bus address, then zero. -/
private def arm (s : UInt32) : ProgM Unit := do
  emit (.physAddr 0 0x100)
  emit (.write32 s (.reg 0))
  w32 (s + 4) 0

/- Nothing written: refused. -/
#guard status busMasterOn == .error "policy"

/- One of the two sinks written: refused. -/
#guard status (do arm 0x20; busMasterOn) == .error "policy"

/- Both low dwords written, the high dwords left as the previous owner had
them: refused. -/
#guard status (do
  emit (.physAddr 0 0x100); emit (.write32 0x20 (.reg 0)); emit (.write32 0x30 (.reg 0))
  busMasterOn) == .error "policy"

/- Every dword of every sink written, in either order: admitted. -/
#guard status (do arm 0x20; arm 0x30; busMasterOn) == .halt
#guard status (do arm 0x30; arm 0x20; busMasterOn) == .halt

/- A register-indirect write (`write32At`) counts the same. -/
#guard status (do
  arm 0x20
  emit (.physAddr 0 0x100); li 1 0x30; emit (.write32At 1 0 (.reg 0)); w32 0x34 0
  busMasterOn) == .halt

/- Setting Memory Space and clearing Bus Master are never gated. -/
#guard status (emit (.cfgUpdate32 0x04 0xFFFF0004 0x0002)) == .halt

/- A policy without sinks has nothing to wait for. -/
#guard status busMasterOn (π := π0) == .halt

/-! ## Every DMA program writes its sinks before Bus Master -/

private def cmdUpdate (w : Word4) : Bool := w.op &&& 0xFF == 26 && w.a == 0x04

private def isWrite32 (w : Word4) (off : UInt32) : Bool := w.op &&& 0xFF == 6 && w.a == off

/-- Before the first word that sets Bus Master, a `write32` names both
dwords of each of `sinks`. -/
def sinksBeforeBusMaster (ws : Array Word4) (sinks : List UInt32) : Bool :=
  match (List.range ws.size).find? (fun i => cmdUpdate ws[i]! && ws[i]!.c &&& 0x4 != 0) with
  | none => false
  | some e =>
    let before := (List.range e).map (ws[·]!)
    sinks.all fun s => before.any (isWrite32 · s) && before.any (isWrite32 · (s + 4))

private def words (body : ProgM Unit) : Array Word4 :=
  match build body with
  | .ok p => p.words
  | .error _ => #[]

#guard sinksBeforeBusMaster (words LeanOS.Storage.Ahci.program) qotomAhciPolicy.addrSinks
#guard sinksBeforeBusMaster (words LeanOS.Storage.AhciRead.program) q35AhciPolicy.addrSinks
#guard sinksBeforeBusMaster (words LeanOS.Net.Rtl8168.program) qotomRtl8168Policy.addrSinks
#guard sinksBeforeBusMaster
  (words (@LeanOS.Usb.Keyboard.program LeanOS.Usb.Xhci.bayTrail 10 0 false false))
  qotomXhciPolicy.addrSinks
#guard sinksBeforeBusMaster
  (words (@LeanOS.Usb.Keyboard.program LeanOS.Usb.Xhci.qemu 10 0 true false))
  q35XhciPolicy.addrSinks
#guard sinksBeforeBusMaster
  (words (@LeanOS.Usb.Mouse.program LeanOS.Usb.Xhci.bayTrail 10)) qotomXhciPolicy.addrSinks
#guard sinksBeforeBusMaster
  (words (@LeanOS.Usb.Mouse.program LeanOS.Usb.Xhci.qemu 10)) q35XhciPolicy.addrSinks
#guard sinksBeforeBusMaster
  (words (@LeanOS.Usb.MassStorage.program LeanOS.Usb.Xhci.bayTrail)) qotomXhciPolicy.addrSinks
#guard sinksBeforeBusMaster
  (words (@LeanOS.Usb.MassStorage.program LeanOS.Usb.Xhci.qemu)) q35XhciPolicy.addrSinks

/- The check rejects the pre-#644 shapes: Bus Master first, and a missing
high dword. -/
#guard !sinksBeforeBusMaster (words (do busMasterOn; arm 0x20; arm 0x30)) π2.addrSinks
#guard !sinksBeforeBusMaster (words (do
  arm 0x20; emit (.physAddr 0 0x100); emit (.write32 0x30 (.reg 0)); busMasterOn)) π2.addrSinks

end LeanOS.NegativeFixtures.BusMasterGate
