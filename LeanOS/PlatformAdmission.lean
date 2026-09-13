/-!
# Closed platform admission

This module binds complete, versioned platform observations to one of the two
reviewed boot profiles.  Component identities name the exact firmware-root,
memory-map, PCI, topology, isolation, scenario, and terminal contracts checked
by the boot adapters.  A caller cannot assemble an accepted profile from q35
and Qotom components because every field is compared with the one manifest
selected by the closed profile identifier.

The runtime model keeps the admitted witness immutable.  Its operation
vocabulary is closed for the bounded scenarios and includes the forbidden AP
start explicitly.  An AP-start attempt enters a typed absorbing halt without
publishing an AP start.
-/
namespace LeanOS.PlatformAdmission

inductive PlatformProfileId where
  | q35V1
  | qotomJ1900Clbtm210V2
  deriving DecidableEq, Repr

def PlatformProfileId.code : PlatformProfileId → UInt64
  | .q35V1 => 1
  | .qotomJ1900Clbtm210V2 => 2

def PlatformProfileId.version : PlatformProfileId → UInt64
  | .q35V1 => 1
  | .qotomJ1900Clbtm210V2 => 2

structure PlatformManifest where
  id : PlatformProfileId
  firmwareRootProfile : UInt64
  memoryMapProfile : UInt64
  pciProfile : UInt64
  uartBase : UInt64
  uartBaud : UInt64
  uartMode : UInt64
  bspProfile : UInt64
  executingBsp : UInt64
  advertisedProcessors : UInt64
  isolationProfile : UInt64
  vtdPolicy : UInt64
  assignedEduPolicy : UInt64
  scenarioProfile : UInt64
  terminalPolicy : UInt64
  debugExitConvenience : Bool
  deriving DecidableEq, Repr

/-- The existing q35 contract keeps its fixed component identities. -/
def q35Manifest : PlatformManifest := {
  id := .q35V1
  firmwareRootProfile := 0x351
  memoryMapProfile := 0x352
  pciProfile := 0x353
  uartBase := 0x3f8
  uartBaud := 38400
  uartMode := 1
  bspProfile := 0x354
  executingBsp := 0
  advertisedProcessors := 1
  isolationProfile := 0x355
  vtdPolicy := 1
  assignedEduPolicy := 1
  scenarioProfile := 10
  terminalPolicy := 1
  debugExitConvenience := true
}

/-- The admitted physical baseline is version two because the historical
version-one Qotom baseline is retained as a controlled rejection. -/
def qotomManifest : PlatformManifest := {
  id := .qotomJ1900Clbtm210V2
  firmwareRootProfile := 0x1901
  memoryMapProfile := 0x1902
  pciProfile := 0x1903
  uartBase := 0x3f8
  uartBaud := 38400
  uartMode := 1
  bspProfile := 0x1904
  executingBsp := 0
  advertisedProcessors := 4
  isolationProfile := 0x1905
  vtdPolicy := 0
  assignedEduPolicy := 0
  scenarioProfile := 10
  terminalPolicy := 1
  debugExitConvenience := false
}

def manifest : PlatformProfileId → PlatformManifest
  | .q35V1 => q35Manifest
  | .qotomJ1900Clbtm210V2 => qotomManifest

/-- Scalar observations passed only after the named component decoders have
checked their authoritative input.  The `Accepted` words prevent a component
identity alone from standing in for successful observation. -/
structure RawObservation where
  profileCode : UInt64
  profileVersion : UInt64
  firmwareRootProfile : UInt64
  firmwareRootAccepted : UInt64
  memoryMapProfile : UInt64
  memoryMapAccepted : UInt64
  pciProfile : UInt64
  pciAccepted : UInt64
  uartBase : UInt64
  uartBaud : UInt64
  uartMode : UInt64
  bspProfile : UInt64
  bspAccepted : UInt64
  executingBsp : UInt64
  advertisedProcessors : UInt64
  apStartIssued : UInt64
  isolationProfile : UInt64
  isolationAccepted : UInt64
  vtdPolicy : UInt64
  assignedEduPolicy : UInt64
  scenarioProfile : UInt64
  scenarioAccepted : UInt64
  terminalPolicy : UInt64
  deriving DecidableEq, Repr

inductive AdmissionError where
  | unknownProfile
  | wrongVersion
  | firmwareRoot
  | memoryMap
  | pci
  | uart
  | bsp
  | apStartForbidden
  | isolation
  | facilityPolicy
  | scenario
  | terminal
  deriving DecidableEq, Repr

def AdmissionError.code : AdmissionError → UInt64
  | .unknownProfile => 1
  | .wrongVersion => 2
  | .firmwareRoot => 3
  | .memoryMap => 4
  | .pci => 5
  | .uart => 6
  | .bsp => 7
  | .apStartForbidden => 8
  | .isolation => 9
  | .facilityPolicy => 10
  | .scenario => 11
  | .terminal => 12

inductive AdmissionResult where
  | rejected (reason : AdmissionError)
  | accepted (profile : PlatformProfileId)
  deriving DecidableEq, Repr

def decodeProfile (code version : UInt64) : Except AdmissionError PlatformProfileId :=
  if code == PlatformProfileId.code .q35V1 then
    if version == PlatformProfileId.version .q35V1 then .ok .q35V1
    else .error .wrongVersion
  else if code == PlatformProfileId.code .qotomJ1900Clbtm210V2 then
    if version == PlatformProfileId.version .qotomJ1900Clbtm210V2 then
      .ok .qotomJ1900Clbtm210V2
    else .error .wrongVersion
  else .error .unknownProfile

def completeMatch (expected : PlatformManifest) (raw : RawObservation) : Bool :=
  raw.profileCode == expected.id.code &&
  raw.profileVersion == expected.id.version &&
  raw.firmwareRootProfile == expected.firmwareRootProfile &&
  raw.firmwareRootAccepted == 1 &&
  raw.memoryMapProfile == expected.memoryMapProfile &&
  raw.memoryMapAccepted == 1 &&
  raw.pciProfile == expected.pciProfile && raw.pciAccepted == 1 &&
  raw.uartBase == expected.uartBase && raw.uartBaud == expected.uartBaud &&
  raw.uartMode == expected.uartMode &&
  raw.bspProfile == expected.bspProfile && raw.bspAccepted == 1 &&
  raw.executingBsp == expected.executingBsp &&
  raw.advertisedProcessors == expected.advertisedProcessors &&
  raw.apStartIssued == 0 &&
  raw.isolationProfile == expected.isolationProfile &&
  raw.isolationAccepted == 1 &&
  raw.vtdPolicy == expected.vtdPolicy &&
  raw.assignedEduPolicy == expected.assignedEduPolicy &&
  raw.scenarioProfile == expected.scenarioProfile &&
  raw.scenarioAccepted == 1 && raw.terminalPolicy == expected.terminalPolicy

def firstMismatch (expected : PlatformManifest) (raw : RawObservation) : AdmissionError :=
  if raw.firmwareRootProfile != expected.firmwareRootProfile ||
      raw.firmwareRootAccepted != 1 then .firmwareRoot
  else if raw.memoryMapProfile != expected.memoryMapProfile ||
      raw.memoryMapAccepted != 1 then .memoryMap
  else if raw.pciProfile != expected.pciProfile || raw.pciAccepted != 1 then .pci
  else if raw.uartBase != expected.uartBase || raw.uartBaud != expected.uartBaud ||
      raw.uartMode != expected.uartMode then .uart
  else if raw.bspProfile != expected.bspProfile || raw.bspAccepted != 1 ||
      raw.executingBsp != expected.executingBsp ||
      raw.advertisedProcessors != expected.advertisedProcessors then .bsp
  else if raw.apStartIssued != 0 then .apStartForbidden
  else if raw.isolationProfile != expected.isolationProfile ||
      raw.isolationAccepted != 1 then .isolation
  else if raw.vtdPolicy != expected.vtdPolicy ||
      raw.assignedEduPolicy != expected.assignedEduPolicy then .facilityPolicy
  else if raw.scenarioProfile != expected.scenarioProfile ||
      raw.scenarioAccepted != 1 then .scenario
  else .terminal

def admit (raw : RawObservation) : AdmissionResult :=
  match decodeProfile raw.profileCode raw.profileVersion with
  | .error reason => .rejected reason
  | .ok profile =>
      if completeMatch (manifest profile) raw then .accepted profile
      else .rejected (firstMismatch (manifest profile) raw)

def q35Observation : RawObservation := {
  profileCode := 1, profileVersion := 1
  firmwareRootProfile := 0x351, firmwareRootAccepted := 1
  memoryMapProfile := 0x352, memoryMapAccepted := 1
  pciProfile := 0x353, pciAccepted := 1
  uartBase := 0x3f8, uartBaud := 38400, uartMode := 1
  bspProfile := 0x354, bspAccepted := 1, executingBsp := 0
  advertisedProcessors := 1, apStartIssued := 0
  isolationProfile := 0x355, isolationAccepted := 1
  vtdPolicy := 1, assignedEduPolicy := 1
  scenarioProfile := 10, scenarioAccepted := 1, terminalPolicy := 1
}

def qotomObservation : RawObservation := {
  profileCode := 2, profileVersion := 2
  firmwareRootProfile := 0x1901, firmwareRootAccepted := 1
  memoryMapProfile := 0x1902, memoryMapAccepted := 1
  pciProfile := 0x1903, pciAccepted := 1
  uartBase := 0x3f8, uartBaud := 38400, uartMode := 1
  bspProfile := 0x1904, bspAccepted := 1, executingBsp := 0
  advertisedProcessors := 4, apStartIssued := 0
  isolationProfile := 0x1905, isolationAccepted := 1
  vtdPolicy := 0, assignedEduPolicy := 0
  scenarioProfile := 10, scenarioAccepted := 1, terminalPolicy := 1
}

theorem profile_ids_distinct :
    PlatformProfileId.code .q35V1 !=
      PlatformProfileId.code .qotomJ1900Clbtm210V2 := by decide

theorem accepted_identifies_complete_profile raw profile
    (h : admit raw = .accepted profile) :
    completeMatch (manifest profile) raw = true := by
  unfold admit at h
  cases hd : decodeProfile raw.profileCode raw.profileVersion with
  | error reason => simp [hd] at h
  | ok selected =>
      rw [hd] at h
      simp only at h
      by_cases hmatch : completeMatch (manifest selected) raw = true
      · rw [if_pos hmatch] at h
        injection h with hprofile
        subst profile
        exact hmatch
      · rw [if_neg hmatch] at h
        contradiction

theorem accepted_profile_unique raw first second
    (hfirst : admit raw = .accepted first)
    (hsecond : admit raw = .accepted second) : first = second := by
  rw [hfirst] at hsecond
  exact AdmissionResult.accepted.inj hsecond

/-- Replacing the q35 firmware component with the Qotom component is a typed
pre-CPL3 rejection; the other splice directions follow from complete match. -/
theorem cross_profile_firmware_splice_rejected :
    admit { q35Observation with firmwareRootProfile :=
      qotomManifest.firmwareRootProfile } = .rejected .firmwareRoot := by decide

inductive RuntimeOperation where
  | syscall
  | pageFault
  | contextSwitch
  | copyTransfer
  | pciObservation
  | serialWrite
  | terminal
  | startApplicationProcessor
  deriving DecidableEq, Repr

inductive HaltReason where
  | final
  | forbiddenApStart
  | platformMismatch
  deriving DecidableEq, Repr

structure RuntimeState where
  admitted : PlatformProfileId
  halted : Option HaltReason
  apStartIssued : Bool
  deriving DecidableEq, Repr

def initialRuntime (profile : PlatformProfileId) : RuntimeState :=
  { admitted := profile, halted := none, apStartIssued := false }

def runtimeGate (state : RuntimeState) (operation : RuntimeOperation) : RuntimeState :=
  match state.halted with
  | some _ => state
  | none =>
      match operation with
      | .startApplicationProcessor =>
          { state with halted := some .forbiddenApStart, apStartIssued := false }
      | .terminal => { state with halted := some .final }
      | _ => state

def runRuntime : RuntimeState → List RuntimeOperation → RuntimeState
  | state, [] => state
  | state, operation :: rest => runRuntime (runtimeGate state operation) rest

theorem runtime_preserves_profile state operation :
    (runtimeGate state operation).admitted = state.admitted := by
  cases h : state.halted <;> cases operation <;> simp [runtimeGate, h]

theorem runtime_never_publishes_ap_start state operation
    (h : state.apStartIssued = false) :
    (runtimeGate state operation).apStartIssued = false := by
  cases hs : state.halted <;> cases operation <;> simp [runtimeGate, hs, h]

theorem forbidden_ap_start_fail_stops profile :
    runtimeGate (initialRuntime profile) .startApplicationProcessor =
      { admitted := profile, halted := some .forbiddenApStart,
        apStartIssued := false } := by rfl

theorem halted_absorbing state reason operation
    (h : state.halted = some reason) : runtimeGate state operation = state := by
  simp [runtimeGate, h]

theorem run_preserves_profile state operations :
    (runRuntime state operations).admitted = state.admitted := by
  induction operations generalizing state with
  | nil => rfl
  | cons operation rest ih =>
      simp only [runRuntime]
      rw [ih, runtime_preserves_profile]

theorem run_never_publishes_ap_start state operations
    (h : state.apStartIssued = false) :
    (runRuntime state operations).apStartIssued = false := by
  induction operations generalizing state with
  | nil => exact h
  | cons operation rest ih =>
      simp only [runRuntime]
      exact ih _ (runtime_never_publishes_ap_start state operation h)

def queryResult (result : AdmissionResult) (word : UInt64) : UInt64 :=
  match result with
  | .rejected reason => if word == 2 then reason.code else 0
  | .accepted profile =>
      if word == 1 then 1
      else if word == 2 then 0
      else if word == 3 then profile.code
      else if word == 4 then 1
      else if word == 5 then (manifest profile).terminalPolicy
      else if word == 6 then if (manifest profile).debugExitConvenience then 1 else 0
      else if word == 7 then 0
      else 0

/-- Words are ABI, accepted, typed reason, selected profile, CPL3 authority,
semantic terminal policy, optional q35 debug-exit transport, and AP-start state. -/
def query (raw : RawObservation) (word : UInt64) : UInt64 :=
  if word == 0 then 1 else queryResult (admit raw) word

/-- Allocation-free scalar form of the same closed manifest checks.  The
freestanding adapter uses this form; the structure-valued admission above is
the proof-facing representation. -/
def scalarReason
    (profileCode profileVersion firmwareRootProfile firmwareRootAccepted
      memoryMapProfile memoryMapAccepted pciProfile pciAccepted uartBase uartBaud
      uartMode bspProfile bspAccepted executingBsp advertisedProcessors
      apStartIssued isolationProfile isolationAccepted vtdPolicy assignedEduPolicy
      scenarioProfile scenarioAccepted terminalPolicy : UInt64) : UInt64 :=
  if profileCode != 1 && profileCode != 2 then 1
  else
    let q35 := profileCode == 1
    if profileVersion != (if q35 then 1 else 2) then 2
    else if firmwareRootProfile != (if q35 then 0x351 else 0x1901) ||
        firmwareRootAccepted != 1 then 3
    else if memoryMapProfile != (if q35 then 0x352 else 0x1902) ||
        memoryMapAccepted != 1 then 4
    else if pciProfile != (if q35 then 0x353 else 0x1903) ||
        pciAccepted != 1 then 5
    else if uartBase != 0x3f8 || uartBaud != 38400 || uartMode != 1 then 6
    else if bspProfile != (if q35 then 0x354 else 0x1904) || bspAccepted != 1 ||
        executingBsp != 0 || advertisedProcessors != (if q35 then 1 else 4) then 7
    else if apStartIssued != 0 then 8
    else if isolationProfile != (if q35 then 0x355 else 0x1905) ||
        isolationAccepted != 1 then 9
    else if vtdPolicy != (if q35 then 1 else 0) ||
        assignedEduPolicy != (if q35 then 1 else 0) then 10
    else if scenarioProfile != 10 || scenarioAccepted != 1 then 11
    else if terminalPolicy != 1 then 12
    else 0

@[export leanos_platform_admission_query]
def exportedQuery
    (profileCode profileVersion firmwareRootProfile firmwareRootAccepted
      memoryMapProfile memoryMapAccepted pciProfile pciAccepted uartBase uartBaud
      uartMode bspProfile bspAccepted executingBsp advertisedProcessors
      apStartIssued isolationProfile isolationAccepted vtdPolicy assignedEduPolicy
      scenarioProfile scenarioAccepted terminalPolicy word : UInt64) : UInt64 :=
  let reason := scalarReason profileCode profileVersion firmwareRootProfile
    firmwareRootAccepted memoryMapProfile memoryMapAccepted pciProfile pciAccepted
    uartBase uartBaud uartMode bspProfile bspAccepted executingBsp
    advertisedProcessors apStartIssued isolationProfile isolationAccepted
    vtdPolicy assignedEduPolicy scenarioProfile scenarioAccepted terminalPolicy
  let accepted := reason == 0
  if word == 0 then 1
  else if word == 1 then if accepted then 1 else 0
  else if word == 2 then reason
  else if word == 3 then if accepted then profileCode else 0
  else if word == 4 then if accepted then 1 else 0
  else if word == 5 then if accepted then 1 else 0
  else if word == 6 then if accepted && profileCode == 1 then 1 else 0
  else 0

example : admit q35Observation = .accepted .q35V1 := by decide
example : admit qotomObservation = .accepted .qotomJ1900Clbtm210V2 := by decide
example : query qotomObservation 4 = 1 := by decide
example : query { qotomObservation with profileVersion := 1 } 2 = 2 := by decide
example : query { qotomObservation with pciAccepted := 0 } 2 = 5 := by decide
example : query { qotomObservation with uartBaud := 115200 } 2 = 6 := by decide
example : query { qotomObservation with executingBsp := 2 } 2 = 7 := by decide
example : query { qotomObservation with apStartIssued := 1 } 2 = 8 := by decide
example : exportedQuery 1 1 0x351 1 0x352 1 0x353 1 0x3f8 38400 1
    0x354 1 0 1 0 0x355 1 1 1 10 1 1 4 = 1 := by decide
example : exportedQuery 2 2 0x1901 1 0x1902 1 0x1903 0 0x3f8 38400 1
    0x1904 1 0 4 0 0x1905 1 0 0 10 1 1 2 = 5 := by decide

end LeanOS.PlatformAdmission
