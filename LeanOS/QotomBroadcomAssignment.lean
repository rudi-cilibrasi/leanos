import LeanOS.QotomPCIFinalAdmission
import LeanOS.DeviceProgramConfinement

/-!
Reviewed assignment variant of the named Qotom PCI trust contract
`qotom-j1900-pci-trust-v1`. The variant is named
`qotom-j1900-pci-trust-v1-bcm43224-assign-v1` (ADR 0027). The initial
contract leaves the Broadcom BCM43224 at `02:00.0` in D3hot with Command
`0000`. This variant permits exactly one configuration store that returns it
to D0, and then permits assignment to the WiFi driver subject only when every
post-transition check matches.

The inputs are scalar observations made by the lab and the result of the
generated initial trust contract. The definitions below decide whether the
observations match; they do not prove that the observations are fresh, that
PCI configuration access is faithful, or that the device obeys its
Command register.

Hardware facts and their sources:

* D3 record (`qotom-broadcom-d3-v1`, status 0): Command `0006` before and
  `0000` after, PMCSR `4008` before and `400b` after. Every retained
  Broadcom D3 capture records these values.
* PMCSR is the word at configuration offset `0x44`: the PM capability is at
  `0x40` (captured capability list), PMCSR at capability + 4 (PCI PM 1.2).
* PMCSR `400b` is D3hot and `4008` is D0. Both keep PME disabled and the
  No_Soft_Reset bit (bit 3) set. The store changes only the PowerState field.
  With No_Soft_Reset set, a D3hot to D0 transition by a PowerState write
  keeps the configuration context (PCI PM 1.2), so the BARs survive.
* BAR0 `d0700004` (64-bit, non-prefetchable memory) and BAR1 `00000000`:
  the retained native inventory header of `02:00.0`.
* Device Control/Status `00190000`: the retained PCIe observation of the
  Broadcom in D0. Transactions Pending (Device Status bit 5) is clear.
-/
namespace LeanOS.QotomBroadcomAssignment

/-- PMCSR of the Broadcom in D3hot, PME disabled, No_Soft_Reset set. -/
def pmcsrD3hot : UInt64 := 0x400b
/-- PMCSR of the Broadcom in D0, PME disabled, No_Soft_Reset set. -/
def pmcsrD0 : UInt64 := 0x4008
/-- Configuration offset of PMCSR: PM capability `0x40` plus four. -/
def pmcsrOffset : UInt64 := 0x44
/-- Retained BAR0 of `02:00.0`: 64-bit non-prefetchable memory. -/
def bar0Expected : UInt64 := 0xd0700004
/-- Retained PCIe Device Control/Status dword of `02:00.0` in D0. -/
def deviceControlStatusExpected : UInt64 := 0x00190000
/-- Transactions Pending, Device Status bit 5, in the Control/Status dword. -/
def transactionsPendingBit : UInt64 := 0x00200000

/-- The earlier D3hot transition of this boot succeeded with its exact
record. -/
def d3Accepted (status commandBefore commandAfter pmcsrBefore pmcsrAfter : UInt64) :
    Bool :=
  status == 0 && commandBefore == 0x0006 && commandAfter == 0 &&
  pmcsrBefore == pmcsrD0 && pmcsrAfter == pmcsrD3hot

/-- The device is still as the D3 transition left it: Command `0000`,
PMCSR D3hot, BARs unchanged. -/
def preAccepted (command pmcsr bar0 bar1 : UInt64) : Bool :=
  command == 0 && pmcsr == pmcsrD3hot && bar0 == bar0Expected && bar1 == 0

/-- The single store of the variant: a 16-bit write of `4008` to PMCSR. -/
def writeExact (offset width value : UInt64) : Bool :=
  offset == pmcsrOffset && width == 2 && value == pmcsrD0

/-- The store is permitted only under the accepted initial trust contract,
after the exact D3 record, on the unchanged D3hot device. -/
def writePermitted (contract d3Status d3CommandBefore d3CommandAfter
      d3PmcsrBefore d3PmcsrAfter preCommand prePmcsr preBar0 preBar1
      offset width value : UInt64) : Bool :=
  contract == 1 &&
  d3Accepted d3Status d3CommandBefore d3CommandAfter d3PmcsrBefore d3PmcsrAfter &&
  preAccepted preCommand prePmcsr preBar0 preBar1 &&
  writeExact offset width value

@[export leanos_qotom_broadcom_assign_write]
def exportedWrite (contract d3Status d3CommandBefore d3CommandAfter
      d3PmcsrBefore d3PmcsrAfter preCommand prePmcsr preBar0 preBar1
      offset width value : UInt64) : UInt64 :=
  if writePermitted contract d3Status d3CommandBefore d3CommandAfter
      d3PmcsrBefore d3PmcsrAfter preCommand prePmcsr preBar0 preBar1
      offset width value then 1 else 0

/-- After the store and the 10 ms D3hot to D0 recovery time: still Command
`0000`, PMCSR D0, the same BARs, the retained Device Control/Status (so
Transactions Pending clear), and a quiet confirmation of two or more
samples, at most the bounded hundred, whose last Device Status is the
retained `0019`. -/
def postAccepted (command pmcsr bar0 bar1 deviceControlStatus
      quietPolls quietDeviceStatus : UInt64) : Bool :=
  command == 0 && pmcsr == pmcsrD0 && bar0 == bar0Expected && bar1 == 0 &&
  deviceControlStatus == deviceControlStatusExpected &&
  2 ≤ quietPolls && quietPolls ≤ 100 && quietDeviceStatus == 0x0019

/-- Assignment goes only to a program that targets exactly `02:00.0`
(`14e4:4353`), declares no DMA, writes no configuration dword outside the
profile's two backplane windows `0x80` and `0xAC` (bitmap `0x80100000000`, so
neither Command nor PMCSR nor a BAR), and can set no Command bit other than
Memory Space (`0x2`). The masks are the complements of those two values,
written as literals so the generated C has no lazily computed constant. -/
def policyAccepted (bus device function identity dma cfgWrite cmdSet : UInt64) :
    Bool :=
  bus == 2 && device == 0 && function == 0 && identity == 0x435314e4 &&
  dma == 0 && cfgWrite &&& 0xFFFFF7FEFFFFFFFF == 0 &&
  cmdSet &&& 0xFFFFFFFFFFFFFFFD == 0

/-- The complete variant: the permitted store was the one made, the
post-transition checks match, and the program policy is assignable. -/
def accepted (contract d3Status d3CommandBefore d3CommandAfter
      d3PmcsrBefore d3PmcsrAfter preCommand prePmcsr preBar0 preBar1
      offset width value postCommand postPmcsr postBar0 postBar1
      deviceControlStatus quietPolls quietDeviceStatus
      bus device function identity dma cfgWrite cmdSet : UInt64) : Bool :=
  writePermitted contract d3Status d3CommandBefore d3CommandAfter
      d3PmcsrBefore d3PmcsrAfter preCommand prePmcsr preBar0 preBar1
      offset width value &&
  postAccepted postCommand postPmcsr postBar0 postBar1 deviceControlStatus
      quietPolls quietDeviceStatus &&
  policyAccepted bus device function identity dma cfgWrite cmdSet

/-- The freestanding lab consumes every observation in one call before it
binds the program. One is the only accepted result. -/
@[export leanos_qotom_broadcom_assign_admission]
def exportedAdmission (contract d3Status d3CommandBefore d3CommandAfter
      d3PmcsrBefore d3PmcsrAfter preCommand prePmcsr preBar0 preBar1
      offset width value postCommand postPmcsr postBar0 postBar1
      deviceControlStatus quietPolls quietDeviceStatus
      bus device function identity dma cfgWrite cmdSet : UInt64) : UInt64 :=
  if accepted contract d3Status d3CommandBefore d3CommandAfter
      d3PmcsrBefore d3PmcsrAfter preCommand prePmcsr preBar0 preBar1
      offset width value postCommand postPmcsr postBar0 postBar1
      deviceControlStatus quietPolls quietDeviceStatus
      bus device function identity dma cfgWrite cmdSet then 1 else 0

theorem write_one_iff (contract d3Status d3CommandBefore d3CommandAfter
      d3PmcsrBefore d3PmcsrAfter preCommand prePmcsr preBar0 preBar1
      offset width value : UInt64) :
    exportedWrite contract d3Status d3CommandBefore d3CommandAfter
        d3PmcsrBefore d3PmcsrAfter preCommand prePmcsr preBar0 preBar1
        offset width value = 1 ↔
      contract = 1 ∧ d3Status = 0 ∧ d3CommandBefore = 0x0006 ∧ d3CommandAfter = 0 ∧
      d3PmcsrBefore = 0x4008 ∧ d3PmcsrAfter = 0x400b ∧
      preCommand = 0 ∧ prePmcsr = 0x400b ∧ preBar0 = 0xd0700004 ∧ preBar1 = 0 ∧
      offset = 0x44 ∧ width = 2 ∧ value = 0x4008 := by
  simp only [exportedWrite, writePermitted, d3Accepted, preAccepted, writeExact,
    pmcsrD0, pmcsrD3hot, pmcsrOffset, bar0Expected, Bool.and_eq_true, beq_iff_eq]
  split <;> simp_all

/-- Whatever else is supplied, the only store the variant ever permits is
the 16-bit PMCSR write of D0. -/
theorem write_exact (contract d3Status d3CommandBefore d3CommandAfter
      d3PmcsrBefore d3PmcsrAfter preCommand prePmcsr preBar0 preBar1
      offset width value : UInt64)
    (h : exportedWrite contract d3Status d3CommandBefore d3CommandAfter
      d3PmcsrBefore d3PmcsrAfter preCommand prePmcsr preBar0 preBar1
      offset width value = 1) :
    offset = 0x44 ∧ width = 2 ∧ value = 0x4008 := by
  have := (write_one_iff _ _ _ _ _ _ _ _ _ _ _ _ _).mp h
  exact ⟨this.2.2.2.2.2.2.2.2.2.2.1, this.2.2.2.2.2.2.2.2.2.2.2.1,
    this.2.2.2.2.2.2.2.2.2.2.2.2⟩

/-- The store needs the accepted initial trust contract. -/
theorem write_requires_contract (contract d3Status d3CommandBefore d3CommandAfter
      d3PmcsrBefore d3PmcsrAfter preCommand prePmcsr preBar0 preBar1
      offset width value : UInt64)
    (h : exportedWrite contract d3Status d3CommandBefore d3CommandAfter
      d3PmcsrBefore d3PmcsrAfter preCommand prePmcsr preBar0 preBar1
      offset width value = 1) : contract = 1 :=
  ((write_one_iff _ _ _ _ _ _ _ _ _ _ _ _ _).mp h).1

theorem admission_one_iff (contract d3Status d3CommandBefore d3CommandAfter
      d3PmcsrBefore d3PmcsrAfter preCommand prePmcsr preBar0 preBar1
      offset width value postCommand postPmcsr postBar0 postBar1
      deviceControlStatus quietPolls quietDeviceStatus
      bus device function identity dma cfgWrite cmdSet : UInt64) :
    exportedAdmission contract d3Status d3CommandBefore d3CommandAfter
        d3PmcsrBefore d3PmcsrAfter preCommand prePmcsr preBar0 preBar1
        offset width value postCommand postPmcsr postBar0 postBar1
        deviceControlStatus quietPolls quietDeviceStatus
        bus device function identity dma cfgWrite cmdSet = 1 ↔
      exportedWrite contract d3Status d3CommandBefore d3CommandAfter
        d3PmcsrBefore d3PmcsrAfter preCommand prePmcsr preBar0 preBar1
        offset width value = 1 ∧
      postAccepted postCommand postPmcsr postBar0 postBar1 deviceControlStatus
        quietPolls quietDeviceStatus = true ∧
      policyAccepted bus device function identity dma cfgWrite cmdSet = true := by
  unfold exportedAdmission exportedWrite accepted
  by_cases hw : writePermitted contract d3Status d3CommandBefore d3CommandAfter
      d3PmcsrBefore d3PmcsrAfter preCommand prePmcsr preBar0 preBar1
      offset width value = true <;>
    simp [hw, Bool.and_eq_true]

/-- An admitted assignment leaves the Broadcom in D0 with Command `0000`,
the retained BARs and Transactions Pending clear. -/
theorem admission_post_state (contract d3Status d3CommandBefore d3CommandAfter
      d3PmcsrBefore d3PmcsrAfter preCommand prePmcsr preBar0 preBar1
      offset width value postCommand postPmcsr postBar0 postBar1
      deviceControlStatus quietPolls quietDeviceStatus
      bus device function identity dma cfgWrite cmdSet : UInt64)
    (h : exportedAdmission contract d3Status d3CommandBefore d3CommandAfter
        d3PmcsrBefore d3PmcsrAfter preCommand prePmcsr preBar0 preBar1
        offset width value postCommand postPmcsr postBar0 postBar1
        deviceControlStatus quietPolls quietDeviceStatus
        bus device function identity dma cfgWrite cmdSet = 1) :
    postCommand = 0 ∧ postPmcsr = 0x4008 ∧ postBar0 = 0xd0700004 ∧ postBar1 = 0 ∧
      deviceControlStatus &&& transactionsPendingBit = 0 ∧ 2 ≤ quietPolls := by
  have hp := ((admission_one_iff _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).mp h).2.1
  simp only [postAccepted, pmcsrD0, bar0Expected, deviceControlStatusExpected,
    Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hp
  obtain ⟨⟨⟨⟨⟨⟨⟨hc, hm⟩, hb0⟩, hb1⟩, hd⟩, hq⟩, _⟩, _⟩ := hp
  subst hd
  exact ⟨hc, hm, hb0, hb1, by decide, hq⟩

/-- An admitted assignment needs the store permitted under the initial trust
contract. -/
theorem admission_requires_write (contract d3Status d3CommandBefore d3CommandAfter
      d3PmcsrBefore d3PmcsrAfter preCommand prePmcsr preBar0 preBar1
      offset width value postCommand postPmcsr postBar0 postBar1
      deviceControlStatus quietPolls quietDeviceStatus
      bus device function identity dma cfgWrite cmdSet : UInt64)
    (h : exportedAdmission contract d3Status d3CommandBefore d3CommandAfter
        d3PmcsrBefore d3PmcsrAfter preCommand prePmcsr preBar0 preBar1
        offset width value postCommand postPmcsr postBar0 postBar1
        deviceControlStatus quietPolls quietDeviceStatus
        bus device function identity dma cfgWrite cmdSet = 1) :
    exportedWrite contract d3Status d3CommandBefore d3CommandAfter
        d3PmcsrBefore d3PmcsrAfter preCommand prePmcsr preBar0 preBar1
        offset width value = 1 ∧ contract = 1 :=
  have hw := ((admission_one_iff _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).mp h).1
  ⟨hw, write_requires_contract _ _ _ _ _ _ _ _ _ _ _ _ _ hw⟩

/-- An admitted program can never make the Broadcom a bus master: it
declares no DMA, may set only Memory Space and may write neither Command
nor PMCSR as a configuration dword. -/
theorem admission_policy_no_bus_master (contract d3Status d3CommandBefore d3CommandAfter
      d3PmcsrBefore d3PmcsrAfter preCommand prePmcsr preBar0 preBar1
      offset width value postCommand postPmcsr postBar0 postBar1
      deviceControlStatus quietPolls quietDeviceStatus
      bus device function identity dma cfgWrite cmdSet : UInt64)
    (h : exportedAdmission contract d3Status d3CommandBefore d3CommandAfter
        d3PmcsrBefore d3PmcsrAfter preCommand prePmcsr preBar0 preBar1
        offset width value postCommand postPmcsr postBar0 postBar1
        deviceControlStatus quietPolls quietDeviceStatus
        bus device function identity dma cfgWrite cmdSet = 1) :
    bus = 2 ∧ device = 0 ∧ function = 0 ∧ identity = 0x435314e4 ∧ dma = 0 ∧
      cmdSet &&& 0x4 = 0 ∧ cfgWrite &&& 0x2 = 0 ∧ cfgWrite &&& 0x20000 = 0 := by
  have hp := ((admission_one_iff _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).mp h).2.2
  simp only [policyAccepted, Bool.and_eq_true, beq_iff_eq] at hp
  obtain ⟨⟨⟨⟨⟨⟨hb, hd⟩, hf⟩, hi⟩, hdma⟩, hw⟩, hs⟩ := hp
  refine ⟨hb, hd, hf, hi, hdma, ?_, ?_, ?_⟩
  · have : cmdSet &&& 0x4 = (cmdSet &&& 0xFFFFFFFFFFFFFFFD) &&& 0x4 := by
      rw [UInt64.and_assoc]; rfl
    rw [this, hs]; rfl
  · have : cfgWrite &&& 0x2 = (cfgWrite &&& 0xFFFFF7FEFFFFFFFF) &&& 0x2 := by
      rw [UInt64.and_assoc]; rfl
    rw [this, hw]; rfl
  · have : cfgWrite &&& 0x20000 = (cfgWrite &&& 0xFFFFF7FEFFFFFFFF) &&& 0x20000 := by
      rw [UInt64.and_assoc]; rfl
    rw [this, hw]; rfl

/-- The admitted Broadcom device-program profile itself is assignable. -/
theorem qotomBcm43224Policy_assignable :
    policyAccepted 2 0 0 0x435314e4 0
      DeviceProgramConfinement.qotomBcm43224Policy.cfgWrite
      DeviceProgramConfinement.qotomBcm43224Policy.cmdSet.toUInt64 = true := by
  decide

example : exportedWrite 1 0 6 0 0x4008 0x400b 0 0x400b 0xd0700004 0 0x44 2 0x4008 = 1 := by
  decide
example : exportedWrite 0 0 6 0 0x4008 0x400b 0 0x400b 0xd0700004 0 0x44 2 0x4008 = 0 := by
  decide
example : exportedWrite 1 0 6 0 0x4008 0x400b 0 0x400b 0xd0700004 0 0x44 4 0x4008 = 0 := by
  decide
example : exportedAdmission 1 0 6 0 0x4008 0x400b 0 0x400b 0xd0700004 0 0x44 2 0x4008
    0 0x4008 0xd0700004 0 0x00190000 2 0x19 2 0 0 0x435314e4 0 0x80100000000 2 = 1 := by
  decide
example : exportedAdmission 1 0 6 0 0x4008 0x400b 0 0x400b 0xd0700004 0 0x44 2 0x4008
    0 0x4008 0xd0700004 0 0x00390000 2 0x19 2 0 0 0x435314e4 0 0x80100000000 2 = 0 := by
  decide
example : exportedAdmission 1 0 6 0 0x4008 0x400b 0 0x400b 0xd0700004 0 0x44 2 0x4008
    0 0x4008 0xd0700004 0 0x00190000 2 0x19 2 0 0 0x435314e4 0 0x80100000000 6 = 0 := by
  decide

end LeanOS.QotomBroadcomAssignment
