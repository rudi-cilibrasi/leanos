import LeanOS.J1900CpuProfile
import LeanOS.PrivilegeEntryControl
import LeanOS.J1900MsrReadback

namespace LeanOS.J1900EntryControl

open PrivilegeEntryControl

/-- Intel long-mode fast-entry behavior, selected only with the separate raw
J1900 capability snapshot. Vendor alone is not a platform identity. -/
def cpu : CpuContract :=
  { vendor := .intel, mode := .long64, syscallExposed := true,
    sysenterExposed := true }

/-- The normalized fast-entry/extended-state tuple for the measured CPU.
This is not the no-SMAP isolation contract and does not authorize CPL3. -/
def deniedControl : ControlState :=
  { acceptedControl with
    cpu := cpu
    extendedFeatures := { x87 := true, mmx := true, sse := true, sse2 := true,
                          xsave := false, avx := false } }

/-- Both the measured CPU words and the complete modeled control readback
must match. Boot-evidence fields describe adapter observations; the model
does not prove that CPUID or RDMSR actually executed. -/
def Normalized (snapshot : J1900CpuProfile.Snapshot) (control : ControlState) : Prop :=
  J1900CpuProfile.rejection snapshot = none ∧ control = deniedControl

def validate (snapshot : J1900CpuProfile.Snapshot) (control : ControlState) : Bool :=
  decide (J1900CpuProfile.rejection snapshot = none) && decide (control = deniedControl)

theorem validate_normalized_iff snapshot control :
    validate snapshot control = true ↔ Normalized snapshot control := by
  simp [validate, Normalized]

theorem normalized_disables_fast_entry snapshot control
    (h : Normalized snapshot control) :
    enabled control .syscall = false ∧ enabled control .sysenter = false := by
  rw [h.2]
  decide

theorem normalized_requires_completed_readback snapshot control
    (h : Normalized snapshot control) :
    control.boot.writesComplete = true ∧ control.boot.readbackMatches = true := by
  rw [h.2]
  decide

/-- Interpret the Intel EFER fields named by the generic entry-control model.
The raw validator additionally rejects reserved bits instead of masking them. -/
def interpretMsrs (s : J1900MsrReadback.Snapshot) : MsrState :=
  { eferLme := s.efer &&& 0x100 != 0
    eferLma := s.efer &&& 0x400 != 0
    eferNxe := s.efer &&& 0x800 != 0
    eferSce := s.efer &&& 1 != 0
    star := s.star, lstar := s.lstar, cstar := s.cstar, sfmask := s.sfmask
    sysenterCs := s.sysenterCs, sysenterEsp := s.sysenterEsp, sysenterEip := s.sysenterEip }

theorem raw_readback_requires_denied_msrs s
    (h : J1900MsrReadback.validate s = true) : interpretMsrs s = deniedMsrs := by
  have hs := (J1900MsrReadback.validate_denied_iff s).mp h
  rw [hs]
  rfl

end LeanOS.J1900EntryControl
