import LeanOS.DeviceProgramConfinement
import LeanOS.Usb.Xhci
import LeanOS.Storage.Ahci
import LeanOS.Storage.AhciRead
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
    [@LeanOS.Usb.Xhci.crcrLo LeanOS.Usb.Xhci.bayTrail, @LeanOS.Usb.Xhci.dcbaapLo LeanOS.Usb.Xhci.bayTrail,
      @LeanOS.Usb.Xhci.erstbaLo LeanOS.Usb.Xhci.bayTrail, @LeanOS.Usb.Xhci.erdpLo LeanOS.Usb.Xhci.bayTrail] := by
  decide

/-- The QEMU xHCI policy's sinks are the same registers in qemu-xhci's layout. -/
example : q35XhciPolicy.addrSinks =
    [@LeanOS.Usb.Xhci.crcrLo LeanOS.Usb.Xhci.qemu, @LeanOS.Usb.Xhci.dcbaapLo LeanOS.Usb.Xhci.qemu,
      @LeanOS.Usb.Xhci.erstbaLo LeanOS.Usb.Xhci.qemu, @LeanOS.Usb.Xhci.erdpLo LeanOS.Usb.Xhci.qemu] := by
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

/-! ## Descriptor pointers (issue #495) -/

/-- The xHCI policies' descriptor maps are exactly the driver's, per layout. -/
example : qotomXhciPolicy.descriptors =
    @LeanOS.Usb.Xhci.descriptorMap LeanOS.Usb.Xhci.bayTrail := by
  decide

example : q35XhciPolicy.descriptors =
    @LeanOS.Usb.Xhci.descriptorMap LeanOS.Usb.Xhci.qemu := by
  decide

section XhciFragments
open LeanOS.Usb.Xhci
attribute [local instance] LeanOS.Usb.Xhci.qemu

/-- A fragment written with the xHCI driver's own builders, generated for
qemu-xhci and declaring `q35XhciPolicy`, as the generator emits it. -/
private def xhciFrag (body : ProgM Unit) : Program :=
  match build (do body; halt) with
  | .ok p => { p with target := some target, policy := some q35XhciPolicy }
  | .error _ => { words := #[], blob := .empty, sections := #[] }

private def fragStatus (body : ProgM Unit) : Sim.Status :=
  (Sim.run (xhciFrag body) Sim.Device.none () 2000).1

private def addressDevice (ptr : Operand) : ProgM Unit := do
  ringInit commandRing
  enqueue commandRing ptr (.imm 0) (.imm 0) (.imm ((11 : UInt32) <<< 10))

/- The driver's Address Device command, its Input Context pointer from
`physAddr`, is accepted. -/
#guard fragStatus (do emit (.physAddr 6 inputCtx); addressDevice (.reg 6)) == .halt

/- The mutant: the same command with a forged Input Context pointer (1 MiB,
outside scratch) in the TRB parameter stops with a policy violation before the
TRB can be handed to the controller. -/
#guard fragStatus (addressDevice (.imm 0x00100000)) == .error "policy"

/- A forged data buffer in a Normal TRB on the interrupt ring, and a Data
Stage TRB whose high dword would move its buffer above 4 GiB. -/
#guard fragStatus (do
  ringInit (transferRing 5 intRing)
  enqueue (transferRing 5 intRing) (.imm 0x00100000) (.imm 0) (.imm 8)
    (.imm ((1 : UInt32) <<< 10))) == .error "policy"
#guard fragStatus (do
  ringInit (ep0Ring 0)
  emit (.physAddr 6 dataBuf)
  enqueue (ep0Ring 0) (.reg 6) (.imm 1) (.imm 18) (.imm ((3 : UInt32) <<< 10))) ==
  .error "policy"

/- A Setup Stage TRB carries its 8-byte setup packet inline: any value is
accepted there, and a Status Stage TRB with a zero parameter too. -/
#guard fragStatus (do
  ringInit (ep0Ring 0)
  enqueue (ep0Ring 0) (.imm 0x01000680) (.imm 0x00120000) (.imm 8)
    (.imm (((2 : UInt32) <<< 10) ||| 0x40))
  enqueue (ep0Ring 0) (.imm 0) (.imm 0) (.imm 0) (.imm ((4 : UInt32) <<< 10))) == .halt

/- Rewriting the parameter of a TRB already typed as a pointer TRB is checked
too: handing over a valid Data Stage TRB and then overwriting its buffer. -/
#guard fragStatus (do
  ringInit (ep0Ring 0)
  emit (.physAddr 6 dataBuf)
  enqueue (ep0Ring 0) (.reg 6) (.imm 0) (.imm 18) (.imm ((3 : UInt32) <<< 10))
  st 4 ep0RingBase (.imm 0x00100000)) == .error "policy"

/- Forged DCBAA, ERST and endpoint-context dequeue pointers; a byte store that
moves a valid pointer out of scratch; FIFO input into a ring. -/
#guard fragStatus (st 4 (dcbaa + 8) (.imm 0x00100000)) == .error "policy"
#guard fragStatus (st 4 erst (.imm 0x00100000)) == .error "policy"
#guard fragStatus (st 4 (ictx 2 2) (.imm 0x00100001)) == .error "policy"
#guard fragStatus (do storePhys64 dcbaa 0; st 1 (dcbaa + 2) (.imm 0x10)) == .error "policy"
#guard fragStatus (do li 1 cmdRing; li 2 4; emit (.fifoIn 0 1 2)) == .error "policy"

/- The driver's own descriptor stores — scratch pointers, flag bits in the
low byte (DCS) and zeros — are accepted. -/
#guard fragStatus (do
  storePhys64 dcbaa 0x100
  storePhys64 erst evRing
  st 4 (erst + 8) (.imm ringTrbs)
  emit (.physAddr 0 (ep0Ring 0).base); ori 0 1; st 4 (ictx 2 2) (.reg 0)
  st 4 (ictx 2 3) (.imm 0)
  clearInput) == .halt

end XhciFragments

/-! ## The q35 one-sector AHCI program (issue #496) -/

section AhciReadFragments
open LeanOS.Storage.AhciRead

/-- The q35 AHCI policy's sinks are PxCLB and PxFB of ports 0 and 1, and its
descriptor map is the read program's. -/
example : q35AhciPolicy.addrSinks = [pxClb 0, pxFb 0, pxClb dataPort, pxFb dataPort] := by
  decide

example : q35AhciPolicy.descriptors = descriptorMap := by
  decide

/-- The program's target window fits the policy window. -/
example : target.windowBytes = q35AhciPolicy.window := by
  decide

/-- A fragment declaring the q35 AHCI target and policy, as the generator
emits it. -/
private def ahciFrag (body : ProgM Unit) : Program :=
  match build (do body; halt) with
  | .ok p => { p with target := some target, policy := some q35AhciPolicy }
  | .error _ => { words := #[], blob := .empty, sections := #[] }

private def ahciStatus (body : ProgM Unit) : Sim.Status :=
  (Sim.run (ahciFrag body) Sim.Device.none () 2000).1

/- The program itself is admissible under the policy it declares. -/
#guard match build program with
  | .ok p => admissible { p with target := some target, policy := some q35AhciPolicy }
      q35AhciPolicy
  | .error _ => false

/- The program's own descriptor stores (command-table and data-buffer
pointers from `physAddr`, zero high dwords) are accepted. -/
#guard ahciStatus (do
  emit (.physAddr 0 cmdTable); st 4 (cmdList + 8) (.reg 0); st 4 (cmdList + 12) (.imm 0)
  emit (.physAddr 0 sector); st 4 prdt (.reg 0); st 4 (prdt + 4) (.imm 0)) == .halt

/- Mutants: a forged command-table base (1 MiB, outside scratch) in command
header 0 or in an unused header, a forged PRD data base, a nonzero high
dword, and a forged PRD past the first stop with a policy violation. -/
#guard ahciStatus (st 4 (cmdList + 8) (.imm 0x00100000)) == .error "policy"
#guard ahciStatus (st 4 (cmdList + 31 * 32 + 8) (.imm 0x00100000)) == .error "policy"
#guard ahciStatus (st 4 prdt (.imm 0x00100000)) == .error "policy"
#guard ahciStatus (st 4 (cmdList + 12) (.imm 1)) == .error "policy"
#guard ahciStatus (st 4 (prdt + 39 * 16) (.imm 0x00100000)) == .error "policy"

/- Port 0's and port 1's command-list and FIS bases take only scratch
addresses. -/
#guard ahciStatus (w32 (pxClb dataPort) 0x00100000) == .error "policy"
#guard ahciStatus (w32 (pxFb 0) 0x00100000) == .error "policy"

/-- `one i` for the q35 AHCI target, declaring its policy. -/
private def oneA (i : Instr) : Program := { one i target with policy := some q35AhciPolicy }

/- Ports outside the window (port 2 starts at 0x200) cannot be reached. -/
/--
error: Tactic `decide` proved that the proposition
  admissible (oneA (Instr.write32 (pxClb 2) (Operand.imm 0))) q35AhciPolicy = true
is false
-/
#guard_msgs in
example : admissible (oneA (.write32 (pxClb 2) (.imm 0))) q35AhciPolicy = true := by
  decide

end AhciReadFragments

/- A policy with a descriptor map admits a program only if its image declares
that policy, so the executor checks the map. -/
/--
error: Tactic `decide` proved that the proposition
  admissible (one Instr.halt xhciTarget)
      { window := 65536, cfgRead := 0, cfgWrite := 0, cmdClear := 0, cmdSet := 0, dma := true,
        descriptors := [{ trb := true, start := 1024, count := 64, stride := 16 }] } =
    true
is false
-/
#guard_msgs in
example : admissible (one .halt xhciTarget)
    { window := 0x10000, cfgRead := 0, cfgWrite := 0, cmdClear := 0, cmdSet := 0, dma := true,
      descriptors := [{ trb := true, start := 0x400, count := 64, stride := 16 }] } = true := by
  decide

end LeanOS.NegativeFixtures.DeviceProgramConfinement
