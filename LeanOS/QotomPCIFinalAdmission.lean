/-!
Closed final-command and trust-assumption boundary for the named Qotom J1900
PCI profile. The command words are observations produced after the bounded
device-specific stages. The five assumption inputs are declarations of the
profile trust boundary, not hardware observations or inferred facts.
-/
namespace LeanOS.QotomPCIFinalAdmission

/-- Final PCI Command words in native inventory order. Host and LPC retain
fixed BME-looking bits even though their reviewed interfaces are not admitted
as ordinary DMA initiators. All controllable host-visible bus masters are off. -/
def commandsAccepted
    (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 : UInt64) : Bool :=
  c0 == 0x0007 && c1 == 0x0003 && c2 == 0x0003 && c3 == 0x0002 &&
  c4 == 0x0102 && c5 == 0x0002 && c6 == 0x0003 && c7 == 0x0003 &&
  c8 == 0x0003 && c9 == 0x0003 && c10 == 0x0402 && c11 == 0x0007 &&
  c12 == 0x0003 && c13 == 0x0003 && c14 == 0x0000 && c15 == 0x0003

/-- Admission is conditional on five named, mandatory trust assumptions for
this non-VT-d profile. Callers cannot omit or substitute one assumption. -/
def accepted
    (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 : UInt64)
    (fixedInfrastructureNonInitiating lpcNoDma postedWritesDrained
      txePrivateDmaQuiescent firmwareAndSmmNoninterference : UInt64) : Bool :=
  commandsAccepted c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 &&
  fixedInfrastructureNonInitiating == 1 && lpcNoDma == 1 &&
  postedWritesDrained == 1 && txePrivateDmaQuiescent == 1 &&
  firmwareAndSmmNoninterference == 1

/-- The freestanding image consumes the complete command vector and all named
assumptions in one call. One is the only accepted result. -/
@[export leanos_qotom_pci_final_admission]
def exported
    (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 : UInt64)
    (fixedInfrastructureNonInitiating lpcNoDma postedWritesDrained
      txePrivateDmaQuiescent firmwareAndSmmNoninterference : UInt64) : UInt64 :=
  if accepted c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15
      fixedInfrastructureNonInitiating lpcNoDma postedWritesDrained
      txePrivateDmaQuiescent firmwareAndSmmNoninterference then 1 else 0

theorem exported_one_iff
    (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 : UInt64)
    (fixedInfrastructureNonInitiating lpcNoDma postedWritesDrained
      txePrivateDmaQuiescent firmwareAndSmmNoninterference : UInt64) :
    exported c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15
      fixedInfrastructureNonInitiating lpcNoDma postedWritesDrained
      txePrivateDmaQuiescent firmwareAndSmmNoninterference = 1 ↔
    commandsAccepted c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 = true ∧
      fixedInfrastructureNonInitiating = 1 ∧ lpcNoDma = 1 ∧
      postedWritesDrained = 1 ∧ txePrivateDmaQuiescent = 1 ∧
      firmwareAndSmmNoninterference = 1 := by
  simp [exported, accepted, Bool.and_eq_true]

example : exported 7 3 3 2 0x102 2 3 3 3 3 0x402 7 3 3 0 3 1 1 1 1 1 = 1 := by decide
example : exported 7 3 3 2 0x102 2 3 3 3 3 0x402 7 3 3 0 3 1 1 1 0 1 = 0 := by decide

end LeanOS.QotomPCIFinalAdmission
