import LeanOS.J1900CpuProfile
import LeanOS.J1900MsrReadback

/-!
# Qotom J1900 CPU/control production checkpoint

This allocation-free scalar gate composes the complete version-one CPUID
projection with the exact normalized fast-entry MSR readback.  Acceptance is
CPU/control authority for the named Qotom profile only.  It deliberately
publishes no CPL3 authority; the no-SMAP isolation and whole-platform gates
remain separate requirements.

Result words are ABI/status/error/profile/CPU-selection/MSR-readback/
fast-entry-policy/CPL3-authority.  CPU errors retain the existing stable 1--12
words; error 13 is an MSR mismatch.  Profile and policy word 1 identify the
version-one J1900/normalized-fast-entry contract.
-/
namespace LeanOS.J1900CpuControlPolicy

def acceptedCpu : UInt64 := 0x10000

@[inline] def query
    (version present basicEax basicEbx basicEcx basicEdx
     featuresEax featuresEbx featuresEcx featuresEdx
     structuredEax structuredEbx structuredEcx structuredEdx
     extendedEax extendedEbx extendedEcx extendedEdx
     extendedFeaturesEax extendedFeaturesEbx extendedFeaturesEcx
     extendedFeaturesEdx efer star lstar cstar sfmask sysenterCs sysenterEsp
     sysenterEip word : UInt64) : UInt64 :=
  let cpu := J1900CpuProfile.selectRaw
    version present basicEax basicEbx basicEcx basicEdx
    featuresEax featuresEbx featuresEcx featuresEdx
    structuredEax structuredEbx structuredEcx structuredEdx
    extendedEax extendedEbx extendedEcx extendedEdx
    extendedFeaturesEax extendedFeaturesEbx extendedFeaturesEcx
    extendedFeaturesEdx
  let msr := J1900MsrReadback.checkRaw
    efer star lstar cstar sfmask sysenterCs sysenterEsp sysenterEip
  let accepted := cpu == acceptedCpu && msr == 1
  let error := if cpu != acceptedCpu then cpu else if msr != 1 then 13 else 0
  if word == 0 then 1
  else if word == 1 then if accepted then 1 else 2
  else if word == 2 then error
  else if word == 3 && accepted then 1
  else if word == 4 && accepted then cpu
  else if word == 5 && accepted then msr
  else if word == 6 && accepted then 1
  else 0

theorem acceptance_iff
    (version present basicEax basicEbx basicEcx basicEdx
     featuresEax featuresEbx featuresEcx featuresEdx
     structuredEax structuredEbx structuredEcx structuredEdx
     extendedEax extendedEbx extendedEcx extendedEdx
     extendedFeaturesEax extendedFeaturesEbx extendedFeaturesEcx
     extendedFeaturesEdx efer star lstar cstar sfmask sysenterCs sysenterEsp
     sysenterEip : UInt64) :
    query version present basicEax basicEbx basicEcx basicEdx
      featuresEax featuresEbx featuresEcx featuresEdx
      structuredEax structuredEbx structuredEcx structuredEdx
      extendedEax extendedEbx extendedEcx extendedEdx
      extendedFeaturesEax extendedFeaturesEbx extendedFeaturesEcx
      extendedFeaturesEdx efer star lstar cstar sfmask sysenterCs sysenterEsp
      sysenterEip 1 = 1 ↔
    J1900CpuProfile.selectRaw
      version present basicEax basicEbx basicEcx basicEdx
      featuresEax featuresEbx featuresEcx featuresEdx
      structuredEax structuredEbx structuredEcx structuredEdx
      extendedEax extendedEbx extendedEcx extendedEdx
      extendedFeaturesEax extendedFeaturesEbx extendedFeaturesEcx
      extendedFeaturesEdx = acceptedCpu ∧
    J1900MsrReadback.checkRaw
      efer star lstar cstar sfmask sysenterCs sysenterEsp sysenterEip = 1 := by
  simp [query]
  repeat' (split <;> simp_all)

theorem query_never_authorizes_cpl3
    (version present basicEax basicEbx basicEcx basicEdx
     featuresEax featuresEbx featuresEcx featuresEdx
     structuredEax structuredEbx structuredEcx structuredEdx
     extendedEax extendedEbx extendedEcx extendedEdx
     extendedFeaturesEax extendedFeaturesEbx extendedFeaturesEcx
     extendedFeaturesEdx efer star lstar cstar sfmask sysenterCs sysenterEsp
     sysenterEip : UInt64) :
    query version present basicEax basicEbx basicEcx basicEdx
      featuresEax featuresEbx featuresEcx featuresEdx
      structuredEax structuredEbx structuredEcx structuredEdx
      extendedEax extendedEbx extendedEcx extendedEdx
      extendedFeaturesEax extendedFeaturesEbx extendedFeaturesEcx
      extendedFeaturesEdx efer star lstar cstar sfmask sysenterCs sysenterEsp
      sysenterEip 7 = 0 := by
  simp [query]

@[export leanos_j1900_cpu_control_policy_query]
def exportedQuery
    (version present basicEax basicEbx basicEcx basicEdx
     featuresEax featuresEbx featuresEcx featuresEdx
     structuredEax structuredEbx structuredEcx structuredEdx
     extendedEax extendedEbx extendedEcx extendedEdx
     extendedFeaturesEax extendedFeaturesEbx extendedFeaturesEcx
     extendedFeaturesEdx efer star lstar cstar sfmask sysenterCs sysenterEsp
     sysenterEip word : UInt64) : UInt64 :=
  query version present basicEax basicEbx basicEcx basicEdx
    featuresEax featuresEbx featuresEcx featuresEdx
    structuredEax structuredEbx structuredEcx structuredEdx
    extendedEax extendedEbx extendedEcx extendedEdx
    extendedFeaturesEax extendedFeaturesEbx extendedFeaturesEcx
    extendedFeaturesEdx efer star lstar cstar sfmask sysenterCs sysenterEsp
    sysenterEip word

end LeanOS.J1900CpuControlPolicy
