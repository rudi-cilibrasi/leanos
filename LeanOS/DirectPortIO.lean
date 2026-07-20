/-!
# Finite direct-port-I/O authority

This model separates attacker-supplied port/value words from the trusted
kernel purpose used to authorize an operation.  The selected Phase 2 TSS
policy has IOPL zero and places the absent I/O bitmap immediately beyond the
descriptor limit.  User-origin requests therefore produce a modeled `#GP(0)`
without changing the complete device projection.  Kernel requests are
accepted only when their purpose, port, direction, and width exactly match the
finite reviewed manifest.

The model begins after a trusted adapter has constructed and read back the
control snapshot.  x86 privilege checks, TSS loading, instruction and exception
semantics, devices, generated code, assembly, and the final binary are not
proved here.
-/
namespace LeanOS.DirectPortIO

inductive Direction where
  | input | output
  deriving BEq, DecidableEq, Repr

inductive Width where
  | byte | word | dword
  deriving BEq, DecidableEq, Repr

inductive Purpose where
  | serial | pic | pit | debugExit
  deriving BEq, DecidableEq, Repr

inductive Origin where
  | user | kernel
  deriving BEq, DecidableEq, Repr

/-- The entry boundary, rather than operation words, selects current privilege. -/
def currentCpl : Origin → Nat
  | .user => 3
  | .kernel => 0

/-- Words available to an untrusted subject contain no origin or purpose. -/
structure PortOperation where
  port : Nat
  direction : Direction
  width : Width
  value : UInt64
  deriving DecidableEq, Repr

/-- A kernel purpose is supplied separately by trusted dispatch state. -/
structure KernelRequest where
  purpose : Purpose
  operation : PortOperation
  deriving DecidableEq, Repr

structure AuthorityKey where
  purpose : Purpose
  port : Nat
  direction : Direction
  width : Width
  deriving BEq, DecidableEq, Repr

def KernelRequest.key (request : KernelRequest) : AuthorityKey :=
  { purpose := request.purpose
    port := request.operation.port
    direction := request.operation.direction
    width := request.operation.width }

/-- Exact reviewed authority for the serial console, legacy PIC, PIT, and
isa-debug-exit operations used by the selected slice.  No port range is
implicitly widened. -/
def portManifest : List AuthorityKey :=
  [ ⟨.serial, 0x3f8, .output, .byte⟩
  , ⟨.serial, 0x3f9, .output, .byte⟩
  , ⟨.serial, 0x3fa, .output, .byte⟩
  , ⟨.serial, 0x3fb, .output, .byte⟩
  , ⟨.serial, 0x3fc, .output, .byte⟩
  , ⟨.serial, 0x3fd, .input, .byte⟩
  , ⟨.pic, 0x20, .output, .byte⟩
  , ⟨.pic, 0x21, .output, .byte⟩
  , ⟨.pic, 0xa0, .output, .byte⟩
  , ⟨.pic, 0xa1, .output, .byte⟩
  , ⟨.pit, 0x40, .output, .byte⟩
  , ⟨.pit, 0x43, .output, .byte⟩
  , ⟨.debugExit, 0xf4, .output, .byte⟩ ]

/-- Complete finite privilege-control projection consumed by this slice.
`ioBitmapPresent = false` records that the base is beyond the TSS limit rather
than naming any permissive bitmap bit. -/
structure Controls where
  ioPrivilegeLevel : Nat
  tssDescriptorLimit : Nat
  ioMapBase : Nat
  ioBitmapPresent : Bool
  kernelConfigured : Bool
  readbackMatches : Bool
  deriving BEq, DecidableEq, Repr

def selectedControls : Controls :=
  { ioPrivilegeLevel := 0
    tssDescriptorLimit := 103
    ioMapBase := 104
    ioBitmapPresent := false
    kernelConfigured := true
    readbackMatches := true }

def AcceptedControls (controls : Controls) : Prop := controls = selectedControls

/-- Finite privilege view: CPL at or below IOPL has ambient access; otherwise
this deny-all slice exposes no bitmap permission. -/
def privilegeAllows (controls : Controls) (origin : Origin) : Bool :=
  decide (currentCpl origin ≤ controls.ioPrivilegeLevel) || controls.ioBitmapPresent

theorem selected_controls_deny_user_cpl :
    privilegeAllows selectedControls .user = false := by decide

theorem selected_controls_allow_kernel_cpl :
    privilegeAllows selectedControls .kernel = true := by decide

/-- Abstract state of every device class named by this policy. -/
structure DeviceState where
  serial : UInt64
  pic : UInt64
  pit : UInt64
  debugExit : UInt64
  deriving DecidableEq, Repr

structure State where
  controls : Controls
  devices : DeviceState
  deriving DecidableEq, Repr

inductive RejectReason where
  | malformedPolicy | staleReadback | unauthorizedKernelOperation
  deriving DecidableEq, Repr

inductive Result where
  | userDeniedGP
  | kernelAccepted
  | rejected (reason : RejectReason)
  deriving DecidableEq, Repr

structure Outcome where
  state : State
  result : Result
  deriving DecidableEq, Repr

/-- Input operations observe but do not mutate this abstract projection.
Output operations affect only the device class selected by trusted purpose. -/
def applyKernel (devices : DeviceState) (request : KernelRequest) : DeviceState :=
  match request.operation.direction with
  | .input => devices
  | .output =>
      match request.purpose with
      | .serial => { devices with serial := request.operation.value }
      | .pic => { devices with pic := request.operation.value }
      | .pit => { devices with pit := request.operation.value }
      | .debugExit => { devices with debugExit := request.operation.value }

/-- User entry supplies only port operation words.  Origin and kernel purpose
are not fields that those words can select. -/
def executeUser (state : State) (liveControls : Controls)
    (_request : PortOperation) : Outcome :=
  if _hpolicy : state.controls ≠ selectedControls then
    { state, result := .rejected .malformedPolicy }
  else if _hlive : liveControls ≠ state.controls then
    { state, result := .rejected .staleReadback }
  else if privilegeAllows liveControls .user then
    { state, result := .rejected .malformedPolicy }
  else { state, result := .userDeniedGP }

/-- Trusted kernel entry additionally supplies a purpose.  Acceptance requires
the exact purpose/port/direction/width key in `portManifest`. -/
def executeKernel (state : State) (liveControls : Controls)
    (request : KernelRequest) : Outcome :=
  if _hpolicy : state.controls ≠ selectedControls then
    { state, result := .rejected .malformedPolicy }
  else if _hlive : liveControls ≠ state.controls then
    { state, result := .rejected .staleReadback }
  else if _hauthorized : portManifest.contains request.key then
    { state := { state with devices := applyKernel state.devices request }
      result := .kernelAccepted }
  else { state, result := .rejected .unauthorizedKernelOperation }

theorem executeUser_total state live request :
    ∃ outcome, executeUser state live request = outcome := ⟨_, rfl⟩

theorem executeKernel_total state live request :
    ∃ outcome, executeKernel state live request = outcome := ⟨_, rfl⟩

theorem executeUser_deterministic state live request first second
    (hfirst : executeUser state live request = first)
    (hsecond : executeUser state live request = second) : first = second := by
  rw [← hfirst, hsecond]

theorem executeKernel_deterministic state live request first second
    (hfirst : executeKernel state live request = first)
    (hsecond : executeKernel state live request = second) : first = second := by
  rw [← hfirst, hsecond]

/-- Every user-origin attempt preserves the identical complete device state,
including malformed-policy and stale-read-back rejection paths. -/
theorem user_request_preserves_device_state state live request :
    (executeUser state live request).state.devices = state.devices := by
  unfold executeUser
  split
  · rfl
  · split
    · rfl
    · split <;> rfl

theorem user_request_never_kernel_accepted state live request :
    (executeUser state live request).result ≠ .kernelAccepted := by
  unfold executeUser
  split
  · simp
  · split
    · simp
    · split <;> simp

theorem accepted_user_request_denied_gp state live request
    (hpolicy : AcceptedControls state.controls)
    (hlive : live = state.controls) :
    executeUser state live request = { state, result := .userDeniedGP } := by
  have hcontrols : state.controls = selectedControls := hpolicy
  simp [executeUser, hcontrols, hlive, selected_controls_deny_user_cpl]

/-- Any typed kernel acceptance exposes the exact manifest membership and
fresh control binding that authorized it. -/
theorem kernel_acceptance_confined state live request
    (haccepted : (executeKernel state live request).result = .kernelAccepted) :
    AcceptedControls state.controls ∧
      live = state.controls ∧
      portManifest.contains request.key = true ∧
      (executeKernel state live request).state.controls = state.controls ∧
      (executeKernel state live request).state.devices =
        applyKernel state.devices request := by
  unfold executeKernel at haccepted
  split at haccepted <;> try contradiction
  rename_i hpolicy
  split at haccepted <;> try contradiction
  rename_i hlive
  split at haccepted <;> try contradiction
  rename_i hauthorized
  cases haccepted
  have hp : state.controls = selectedControls := by simp_all
  have hl : live = state.controls := by simp_all
  simp [AcceptedControls, executeKernel, hp, hl, hauthorized]

/-- Every typed kernel rejection is atomic for the complete device state. -/
theorem kernel_rejection_preserves_device_state state live request reason
    (hrejected : (executeKernel state live request).result = .rejected reason) :
    (executeKernel state live request).state.devices = state.devices := by
  by_cases hpolicy : state.controls ≠ selectedControls
  · simp [executeKernel, hpolicy]
  · by_cases hlive : live ≠ state.controls
    · simp [executeKernel, hpolicy, hlive]
    · by_cases hauthorized : portManifest.contains request.key = true
      · simp [executeKernel, hpolicy, hlive, hauthorized] at hrejected
      · simp [executeKernel, hpolicy, hlive, hauthorized]

private def zeroDevices : DeviceState := ⟨0, 0, 0, 0⟩

private def witnessState : State := ⟨selectedControls, zeroDevices⟩

private def witnessOperation : PortOperation :=
  { port := 0x3f8, direction := .output, width := .byte, value := 65 }

private def witnessKernelRequest : KernelRequest :=
  { purpose := .serial, operation := witnessOperation }

/-- Non-vacuity: one reviewed kernel output is accepted and changes only its
device projection, while the same attacker-controlled port/value words are
denied with an identical device state on the user path. -/
theorem policy_nonvacuous :
    (executeKernel witnessState selectedControls witnessKernelRequest).result =
        .kernelAccepted ∧
      (executeKernel witnessState selectedControls witnessKernelRequest).state.devices =
        { zeroDevices with serial := 65 } ∧
      executeUser witnessState selectedControls witnessOperation =
        { state := witnessState, result := .userDeniedGP } := by
  native_decide

end LeanOS.DirectPortIO
