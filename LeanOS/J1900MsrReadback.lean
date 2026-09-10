namespace LeanOS.J1900MsrReadback

/-- Full-width observations in the same order as read_fast_entry_msrs. -/
structure Snapshot where
  efer : UInt64
  star : UInt64
  lstar : UInt64
  cstar : UInt64
  sfmask : UInt64
  sysenterCs : UInt64
  sysenterEsp : UInt64
  sysenterEip : UInt64
  deriving BEq, DecidableEq, Repr

/-- Intel long mode and NX active, SCE clear, all unused targets cleared.
Reserved EFER bits must be zero; this is not the AMD EFER projection. -/
def denied : Snapshot := ⟨0xd00, 0, 0, 0, 0, 0, 0, 0⟩

@[inline] def validate (s : Snapshot) : Bool :=
  s.efer == 0xd00 && s.star == 0 && s.lstar == 0 && s.cstar == 0 &&
  s.sfmask == 0 && s.sysenterCs == 0 && s.sysenterEsp == 0 && s.sysenterEip == 0

theorem validate_denied_iff s : validate s = true ↔ s = denied := by
  cases s
  simp [validate, denied, and_assoc]

/-- Check one complete readback. This function neither performs RDMSR nor
authorizes its execution; the CPU capability gate must precede those reads. -/
@[export leanos_j1900_msr_readback]
def checkRaw (efer star lstar cstar sfmask sysenterCs sysenterEsp sysenterEip : UInt64) : UInt64 :=
  if validate ⟨efer, star, lstar, cstar, sfmask, sysenterCs, sysenterEsp, sysenterEip⟩ then 1 else 0

end LeanOS.J1900MsrReadback
