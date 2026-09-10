namespace LeanOS.J1900CpuProfile

/-- Raw words from one executed CPUID leaf/subleaf pair. -/
structure Registers where
  eax : UInt32 := 0
  ebx : UInt32 := 0
  ecx : UInt32 := 0
  edx : UInt32 := 0
  deriving BEq, DecidableEq, Repr

/-- Version one has five slots: (0,0), (1,0), (7,0), (80000000,0),
(80000001,0). Presence bits record executed queries, not zero-filled defaults.
This is a capability snapshot, not evidence of the current execution mode. -/
structure Snapshot where
  version : UInt32 := 1
  present : UInt32
  basic : Registers
  features : Registers
  structured : Registers
  extended : Registers
  extendedFeatures : Registers
  deriving BEq, DecidableEq, Repr

inductive Rejection where
  | version | presence | basicRange | extendedRange | vendor | signature
  | requiredLegacy | requiredExtended | smep | unexpectedExtendedState | smap
  deriving BEq, DecidableEq, Repr

/-- A closed CPU capability projection. MSR authorization and the no-SMAP
isolation policy must be established separately before production CPL3. -/
structure Projection where
  version : UInt32
  signature : UInt32
  extendedFeatureMask : UInt32
  smep : Bool
  smap : Bool
  productionCpl3 : Bool
  deriving BEq, DecidableEq, Repr

def selected : Projection :=
  { version := 1, signature := 0x30678, extendedFeatureMask := 15,
    smep := true, smap := false, productionCpl3 := false }

/-- FPU, PSE, MSR, PAE, SEP, MMX, FXSR, SSE and SSE2. -/
@[inline] def legacyMask : UInt32 := 0x07800869

/-- SYSCALL, NX and long-mode support. -/
@[inline] def extendedMask : UInt32 := 0x20100800

@[inline] def rejection (s : Snapshot) : Option Rejection :=
  if s.version != 1 then some .version
  else if s.present != 31 then some .presence
  else if s.basic.eax < 7 then some .basicRange
  else if s.extended.eax < 0x80000001 then some .extendedRange
  else if s.basic.ebx != 0x756e6547 || s.basic.edx != 0x49656e69 ||
      s.basic.ecx != 0x6c65746e then some .vendor
  else if s.features.eax != 0x30678 then some .signature
  else if s.features.edx &&& legacyMask != legacyMask then some .requiredLegacy
  else if s.extendedFeatures.edx &&& extendedMask != extendedMask then some .requiredExtended
  else if s.structured.ebx &&& 0x80 == 0 then some .smep
  else if s.features.ecx &&& 0x1c000000 != 0 then some .unexpectedExtendedState
  else if s.structured.ebx &&& 0x100000 != 0 then some .smap
  else none

@[inline] def select (s : Snapshot) : Except Rejection Projection :=
  match rejection s with
  | some reason => .error reason
  | none => .ok selected

theorem selection_requires_all_checks s projection
    (h : select s = .ok projection) : rejection s = none := by
  cases hr : rejection s with
  | none => rfl
  | some reason => simp [select, hr] at h

theorem selection_does_not_authorize_cpl3 s projection
    (h : select s = .ok projection) : projection.productionCpl3 = false := by
  have hr := selection_requires_all_checks s projection h
  simp [select, hr] at h
  subst projection
  rfl

theorem selection_requires_measured_capabilities s projection
    (h : select s = .ok projection) :
    s.features.edx &&& legacyMask = legacyMask ∧
    s.extendedFeatures.edx &&& extendedMask = extendedMask ∧
    s.structured.ebx &&& 0x80 != 0 ∧
    s.features.ecx &&& 0x1c000000 = 0 ∧
    s.structured.ebx &&& 0x100000 = 0 := by
  have hr := selection_requires_all_checks s projection h
  have step (condition : Prop) [Decidable condition] (reason : Rejection) (rest : Option Rejection)
      (hn : (if condition then some reason else rest) = none) :
      ¬condition ∧ rest = none := by
    by_cases hc : condition <;> simp_all
  unfold rejection at hr
  have hv := step _ _ _ hr
  have hp := step _ _ _ hv.2
  have hb := step _ _ _ hp.2
  have he := step _ _ _ hb.2
  have hven := step _ _ _ he.2
  have hsig := step _ _ _ hven.2
  have hleg := step _ _ _ hsig.2
  have hext := step _ _ _ hleg.2
  have hsmep := step _ _ _ hext.2
  have hstate := step _ _ _ hsmep.2
  have hsmap := step _ _ _ hstate.2
  exact ⟨by simpa using hleg.1, by simpa using hext.1,
    by simpa using hsmep.1, by simpa using hstate.1, by simpa using hsmap.1⟩

/-- Stable scalar rejection words for the version-one CPU boundary. Zero is
not success: successful selection has its own distinct word. -/
@[inline] def rejectionWord : Rejection → UInt64
  | .version => 1
  | .presence => 2
  | .basicRange => 3
  | .extendedRange => 4
  | .vendor => 5
  | .signature => 6
  | .requiredLegacy => 7
  | .requiredExtended => 8
  | .smep => 9
  | .unexpectedExtendedState => 10
  | .smap => 11

/-- Version-one scalar boundary: version, presence, then EAX/EBX/ECX/EDX
for each of the five Snapshot slots in order. Every input must fit UInt32;
reject before narrowing, including otherwise unused CPUID words. Result 12
means a width violation; 1–11 are typed selection rejections; 0x10000 means
selection of `selected`, which still does not authorize production CPL3.
This entry point consumes a complete snapshot on each call and keeps no state. -/
@[export leanos_j1900_cpu_select]
def selectRaw
    (version present basic_eax basic_ebx : UInt64)
    (basic_ecx basic_edx features_eax features_ebx : UInt64)
    (features_ecx features_edx structured_eax structured_ebx : UInt64)
    (structured_ecx structured_edx extended_eax extended_ebx : UInt64)
    (extended_ecx extended_edx extendedFeatures_eax extendedFeatures_ebx : UInt64)
    (extendedFeatures_ecx extendedFeatures_edx : UInt64)
    : UInt64 :=
  if (version ||| present ||| basic_eax ||| basic_ebx |||
      basic_ecx ||| basic_edx ||| features_eax ||| features_ebx |||
      features_ecx ||| features_edx ||| structured_eax ||| structured_ebx |||
      structured_ecx ||| structured_edx ||| extended_eax ||| extended_ebx |||
      extended_ecx ||| extended_edx ||| extendedFeatures_eax ||| extendedFeatures_ebx |||
      extendedFeatures_ecx ||| extendedFeatures_edx) > 0xffffffff then 12
  else
    let snapshot : Snapshot :=
      { version := version.toUInt32, present := present.toUInt32
        basic := { eax := basic_eax.toUInt32, ebx := basic_ebx.toUInt32, ecx := basic_ecx.toUInt32, edx := basic_edx.toUInt32 }
        features := { eax := features_eax.toUInt32, ebx := features_ebx.toUInt32, ecx := features_ecx.toUInt32, edx := features_edx.toUInt32 }
        structured := { eax := structured_eax.toUInt32, ebx := structured_ebx.toUInt32, ecx := structured_ecx.toUInt32, edx := structured_edx.toUInt32 }
        extended := { eax := extended_eax.toUInt32, ebx := extended_ebx.toUInt32, ecx := extended_ecx.toUInt32, edx := extended_edx.toUInt32 }
        extendedFeatures := { eax := extendedFeatures_eax.toUInt32, ebx := extendedFeatures_ebx.toUInt32, ecx := extendedFeatures_ecx.toUInt32, edx := extendedFeatures_edx.toUInt32 }
      }
    match select snapshot with
    | .error reason => rejectionWord reason
    | .ok _ => 0x10000

end LeanOS.J1900CpuProfile
