import LeanOS.DeviceProgramConfinement

namespace LeanOS.NegativeFixtures.DeviceProgramConfinement

open LeanOS.Wifi.Bytecode LeanOS.DeviceProgramConfinement

/-- A one-instruction program for target `t`. -/
private def one (i : Instr) (t : Target := bcm43224Target) : Program :=
  { words := #[(encode i).getD ⟨0, 0, 0, 0⟩], blob := .empty, sections := #[], target := some t }

private def xhciTarget : Target :=
  { bus := 0, dev := 20, fn := 0, id := 0x0f358086, windowBytes := 0x10000 }

/- A direct write to the command register cannot turn on bus mastering. -/
/--
error: Tactic `decide` proved that the proposition
  admissible (one (Instr.cfgWrite32 4 (Operand.imm 6)) xhciTarget) qotomXhciPolicy = true
is false
-/
#guard_msgs in
example : admissible (one (.cfgWrite32 0x04 (.imm 0x6)) xhciTarget) qotomXhciPolicy = true := by
  decide

/- A program cannot move its BAR. -/
/--
error: Tactic `decide` proved that the proposition
  admissible (one (Instr.cfgWrite32 16 (Operand.reg 0)) xhciTarget) qotomXhciPolicy = true
is false
-/
#guard_msgs in
example : admissible (one (.cfgWrite32 0x10 (.reg 0)) xhciTarget) qotomXhciPolicy = true := by
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
example : admissible (one (.cfgUpdate32 0x04 0xFFFF0000 0x2)) qotomBcm43224Policy = true := by
  decide
example : admissible (one (.cfgUpdate32 0x04 0xFFFF0000 0x6) xhciTarget) qotomXhciPolicy = true := by
  decide

end LeanOS.NegativeFixtures.DeviceProgramConfinement
