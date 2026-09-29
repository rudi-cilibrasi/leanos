import LeanOS.DeviceProgramConfinement
import LeanOS.Usb.Xhci
import LeanOS.Storage.Ahci
import LeanOS.Net.Rtl8168

namespace LeanOS.NegativeFixtures.DeviceProgramConfinement

open LeanOS.Wifi.Bytecode LeanOS.Wifi LeanOS.DeviceProgramConfinement

/-- A one-instruction program for target `t`. -/
private def one (i : Instr) (t : Target := bcm43224Target) : Program :=
  { words := #[(encode i).getD ⟨0, 0, 0, 0⟩], blob := .empty, sections := #[], target := some t }

private def xhciTarget : Target :=
  { bus := 0, dev := 20, fn := 0, id := 0x0f358086, windowBytes := 0x10000 }

/-- `one i xhciTarget` declaring the xHCI policy, as the generator emits it. -/
private def oneX (i : Instr) : Program := { one i xhciTarget with policy := some qotomXhciPolicy }

/- A direct write to the command register cannot turn on bus mastering. -/
/--
error: Tactic `decide` proved that the proposition
  admissible (oneX (Instr.cfgWrite32 4 (Operand.imm 6))) qotomXhciPolicy = true
is false
-/
#guard_msgs in
example : admissible (oneX (.cfgWrite32 0x04 (.imm 0x6))) qotomXhciPolicy = true := by
  decide

/- A program cannot move its BAR. -/
/--
error: Tactic `decide` proved that the proposition
  admissible (oneX (Instr.cfgWrite32 16 (Operand.reg 0))) qotomXhciPolicy = true
is false
-/
#guard_msgs in
example : admissible (oneX (.cfgWrite32 0x10 (.reg 0))) qotomXhciPolicy = true := by
  decide

/- The WiFi policy never lets a program set Bus Master, even through the
checked read-modify-write. -/
/--
error: Tactic `decide` proved that the proposition
  admissible (one (Instr.cfgUpdate32 4 4294901760 6)) qotomBcm43224Policy = true
is false
-/
#guard_msgs in
example : admissible (one (.cfgUpdate32 0x04 0xFFFF0000 0x6)) qotomBcm43224Policy = true := by
  decide

/- Without a DMA policy a program cannot learn a bus address. -/
/--
error: Tactic `decide` proved that the proposition
  admissible (one (Instr.physAddr 0 0)) qotomBcm43224Policy = true
is false
-/
#guard_msgs in
example : admissible (one (.physAddr 0 0)) qotomBcm43224Policy = true := by
  decide

/- A direct MMIO access just past the 16 KiB WiFi window is rejected. -/
/--
error: Tactic `decide` proved that the proposition
  admissible (one (Instr.read32 0 16384)) qotomBcm43224Policy = true
is false
-/
#guard_msgs in
example : admissible (one (.read32 0 0x4000)) qotomBcm43224Policy = true := by
  decide

/- Offsets at or above 0x100 would alias through mechanism-1 configuration
access (`off & 0xfc`), so no policy admits them. -/
/--
error: Tactic `decide` proved that the proposition
  admissible (one (Instr.cfgRead32 0 260)) qotomBcm43224Policy = true
is false
-/
#guard_msgs in
example : admissible (one (.cfgRead32 0 0x104)) qotomBcm43224Policy = true := by
  decide

/- A program whose target window exceeds the policy window is rejected even
if it touches no device register. -/
/--
error: Tactic `decide` proved that the proposition
  admissible (one Instr.halt xhciTarget) qotomBcm43224Policy = true
is false
-/
#guard_msgs in
example : admissible (one .halt xhciTarget) qotomBcm43224Policy = true := by
  decide

private def barWriter : Policy :=
  { window := 0x4000, cfgRead := 0, cfgWrite := cfgBits [0x10], cmdClear := 0, cmdSet := 0, dma := false }

/- A policy that lets a program write BAR0 directly is not sane. -/
/--
error: Tactic `decide` proved that the proposition
  barWriter.sane = true
is false
-/
#guard_msgs in
example : barWriter.sane = true := by
  decide

private def masterWithoutDma : Policy :=
  { window := 0x4000, cfgRead := 0, cfgWrite := 0, cmdClear := 0, cmdSet := 0x6, dma := false }

/- A policy that sets Bus Master without admitting DMA is not sane. -/
/--
error: Tactic `decide` proved that the proposition
  masterWithoutDma.sane = true
is false
-/
#guard_msgs in
example : masterWithoutDma.sane = true := by
  decide

/- The admitted programs' own command-register updates do pass. -/
example : admissible (one (.cfgUpdate32 0x04 0xFFFF0004 0x2)) qotomBcm43224Policy = true := by
  decide
example : admissible (oneX (.cfgUpdate32 0x04 0xFFFF0000 0x6)) qotomXhciPolicy = true := by
  decide

/-! ## DMA address sinks (issue #448) -/

/-- The xHCI policy's sinks are exactly the driver's CRCR, DCBAAP, ERSTBA and
ERDP registers. -/
example : qotomXhciPolicy.addrSinks =
    [LeanOS.Usb.Xhci.crcrLo, LeanOS.Usb.Xhci.dcbaapLo, LeanOS.Usb.Xhci.erstbaLo,
      LeanOS.Usb.Xhci.erdpLo] := by
  decide

/-- The AHCI policy's sinks are exactly port 1's PxCLB and PxFB. -/
example : qotomAhciPolicy.addrSinks = [LeanOS.Storage.Ahci.pClb, LeanOS.Storage.Ahci.pFb] := by
  decide

/-- The RTL8168 policy's sinks are exactly the driver's DMA address registers. -/
example : qotomRtl8168Policy.addrSinks =
    [LeanOS.Net.Rtl8168.dtccr, LeanOS.Net.Rtl8168.tnpds, LeanOS.Net.Rtl8168.thpds,
      LeanOS.Net.Rtl8168.rdsar] := by
  decide

/- A byte write into a ring-base sink is refused like any partial sink write. -/
private def rtlByteSink : Program where
  words := #[(encode (.write8 0x20 (.imm 0))).getD ⟨0, 0, 0, 0⟩, (encode .halt).getD ⟨0, 0, 0, 0⟩]
  blob := .empty
  sections := #[]
  target := some LeanOS.Net.Rtl8168.target
  policy := some qotomRtl8168Policy

#guard (Sim.run rtlByteSink Sim.Device.none () 10).1 == .error "policy"

/-- An xHCI program declaring its policy. -/
private def xhciProg (is : List Instr) : Program :=
  { words := (is.map fun i => (encode i).getD ⟨0, 0, 0, 0⟩).toArray, blob := .empty,
    sections := #[], target := some xhciTarget, policy := some qotomXhciPolicy }

private def runStatus (p : Program) : Sim.Status := (Sim.run p Sim.Device.none () 100).1

/- A forged bus address (1 MiB, outside scratch) written to DCBAAP stops the
program with a policy violation before the write reaches the device. -/
#guard runStatus (xhciProg [.alu .mov 0 (.imm 0x00100000), .write32 0xB0 (.reg 0), .halt]) ==
  .error "policy"

/- The same through a register-indirect write. -/
#guard runStatus (xhciProg [.alu .mov 0 (.imm 0x00100000), .alu .mov 1 (.imm 0xB0),
  .write32At 1 0 (.reg 0), .halt]) == .error "policy"

/- One byte past the end of scratch is already outside. -/
#guard runStatus (xhciProg [.physAddr 0 0, .alu .add 0 (.imm (scratchBytes.toUInt32)),
  .write32 0x98 (.reg 0), .halt]) == .error "policy"

/- A nonzero high dword would move the address above 4 GiB. -/
#guard runStatus (xhciProg [.write32 0xB4 (.imm 1), .halt]) == .error "policy"

/- Partial writes and streams into a sink are refused. -/
#guard runStatus (xhciProg [.write16 0xB0 (.imm 0), .halt]) == .error "policy"
#guard runStatus (xhciProg [.alu .mov 0 (.imm 0), .alu .mov 1 (.imm 1), .fifoOut 0x2038 0 1, .halt]) ==
  .error "policy"

/- The driver's own pattern — the bus address of a scratch structure, then a
zero high dword — is accepted. -/
#guard runStatus (xhciProg [.physAddr 0 0x20000, .write32 0xB0 (.reg 0),
  .write32 0xB4 (.imm 0), .physAddr 0 0x20400, .alu .or 0 (.imm 1), .write32 0x98 (.reg 0),
  .halt]) == .halt

/- Because sink values are checked at run time, a program cannot be admitted
under a policy with sinks unless its image declares that policy. -/
/--
error: Tactic `decide` proved that the proposition
  admissible (one Instr.halt xhciTarget) qotomXhciPolicy = true
is false
-/
#guard_msgs in
example : admissible (one .halt xhciTarget) qotomXhciPolicy = true := by
  decide

end LeanOS.NegativeFixtures.DeviceProgramConfinement
