/-!
# Finite PCI DMA quarantine

This model begins after a complete PCI configuration-space observation.  It
does not prove enumeration completeness, PCI Command-register semantics,
QEMU/firmware behavior, or correspondence to a final binary.  Those facts are
the explicit `DeviceContract` assumption at the hardware boundary.
-/
namespace LeanOS.DMAQuarantine

def snapshotVersion : UInt64 := 1
def q35TopologyVersion : UInt64 := 0x0008_0002_0002
def maxFunctions : Nat := 16
def functionWords : Nat := 13
def snapshotWords : Nat := 2 + maxFunctions * functionWords

structure BDF where
  bus : UInt64
  device : UInt64
  function : UInt64
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

structure Identity where
  vendor : UInt64
  device : UInt64
  classCode : UInt64
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

inductive ReadStatus where
  | absent | present | unreadable
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

inductive Assignment where
  | unassigned | kernelOwner (owner : UInt64)
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

structure FunctionState where
  bdf : BDF
  identity : Identity
  status : ReadStatus
  command : UInt64
  assignment : Assignment
  bridge : Bool
  multifunction : Bool
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

structure ManifestEntry where
  bdf : BDF
  identity : Identity
  required : Bool
  dmaCapable : Bool
  bridge : Bool
  multifunction : Bool
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

structure Snapshot where
  version : UInt64
  topologyVersion : UInt64
  functions : List FunctionState
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

def bdfValid (bdf : BDF) : Bool :=
  bdf.bus < 256 && bdf.device < 32 && bdf.function < 8

def identityValid (identity : Identity) : Bool :=
  identity.vendor < 0x10000 && identity.device < 0x10000 &&
    identity.classCode < 0x1000000

def busMasterEnabled (function : FunctionState) : Bool :=
  function.command.toNat.testBit 2

def commandCanonical (command : UInt64) : Bool := command < 0x800

def assignmentTag : Assignment → UInt64
  | .unassigned => 0
  | .kernelOwner _ => 1

def assignmentOwner : Assignment → UInt64
  | .unassigned => 0
  | .kernelOwner owner => owner

def statusTag : ReadStatus → UInt64
  | .absent => 0
  | .present => 1
  | .unreadable => 2

/-- Thirteen 64-bit words per function.  Keeping the assignment tag and owner
in separate words avoids making `kernelOwner UInt64.max` collide with the
unassigned encoding through wrapping arithmetic. -/
def encodeFunction (function : FunctionState) : List UInt64 :=
  [1, function.bdf.bus, function.bdf.device, function.bdf.function,
   function.identity.vendor, function.identity.device, function.identity.classCode,
   statusTag function.status, function.command, assignmentTag function.assignment,
   assignmentOwner function.assignment,
   if function.bridge then 1 else 0, if function.multifunction then 1 else 0]

def emptySlot : List UInt64 := List.replicate functionWords 0

def encodeSlots : Nat → List FunctionState → List UInt64
  | 0, _ => []
  | slots + 1, [] => emptySlot ++ encodeSlots slots []
  | slots + 1, function :: rest => encodeFunction function ++ encodeSlots slots rest

/-- Canonical fixed-width state-corpus encoding: two version words followed by
exactly sixteen twelve-word function slots.  Oversized snapshots have no
encoding rather than being silently truncated. -/
def encodeSnapshot (snapshot : Snapshot) : Option (List UInt64) :=
  if snapshot.functions.length ≤ maxFunctions then
    some ([snapshot.version, snapshot.topologyVersion] ++
      encodeSlots maxFunctions snapshot.functions)
  else none

@[simp] theorem encodeFunction_length function : (encodeFunction function).length = functionWords :=
  by rfl

@[simp] theorem emptySlot_length : emptySlot.length = functionWords := by
  simp [emptySlot, functionWords]

theorem encodeSlots_length slots functions :
    (encodeSlots slots functions).length = slots * functionWords := by
  induction slots generalizing functions with
  | zero => simp [encodeSlots]
  | succ slots ih =>
      cases functions <;> simp [encodeSlots, ih, Nat.succ_mul, Nat.add_comm]

theorem accepted_encoding_fixed_width snapshot words
    (hencode : encodeSnapshot snapshot = some words) : words.length = snapshotWords := by
  simp only [encodeSnapshot] at hencode
  split at hencode <;> try contradiction
  injection hencode with hwords
  subst words
  simp [encodeSlots_length, snapshotWords, Nat.add_comm, Nat.add_left_comm]

private def bdf (bus device function : UInt64) : BDF := ⟨bus, device, function⟩
private def identity (vendor device classCode : UInt64) : Identity :=
  ⟨vendor, device, classCode⟩

/-- QEMU 8.2.2 q35 topology selected by the repository runners.  The network
slot is deliberately represented as optional-and-absent under `-nic none`.
All present entries are unassigned by the Phase 2 policy. -/
def q35Manifest : List ManifestEntry :=
  [⟨bdf 0 0 0, identity 0x8086 0x29c0 0x060000, true, false, false, false⟩,
   ⟨bdf 0 1 0, identity 0x1234 0x1111 0x030000, true, true, false, false⟩,
   ⟨bdf 0 3 0, identity 0x1af4 0x1000 0x020000, false, true, false, false⟩,
   ⟨bdf 0 31 0, identity 0x8086 0x2918 0x060100, true, false, true, true⟩,
   ⟨bdf 0 31 2, identity 0x8086 0x2922 0x010601, true, true, false, true⟩,
   ⟨bdf 0 31 3, identity 0x8086 0x2930 0x0c0500, true, true, false, true⟩]

def findFunction (snapshot : Snapshot) (target : BDF) : Option FunctionState :=
  snapshot.functions.find? (·.bdf == target)

def findManifest (target : BDF) : Option ManifestEntry :=
  q35Manifest.find? (·.bdf == target)

def exactlyOnce (target : BDF) (functions : List FunctionState) : Bool :=
  (functions.filter (·.bdf == target)).length == 1

def uniqueBDFs (functions : List FunctionState) : Bool :=
  functions.all fun function => exactlyOnce function.bdf functions

def canonicalOrder (functions : List FunctionState) : Bool :=
  functions.map (·.bdf) == q35Manifest.map (·.bdf)

def matchesManifest (entry : ManifestEntry) (function : FunctionState) : Bool :=
  function.bdf == entry.bdf && function.bridge == entry.bridge &&
    function.multifunction == entry.multifunction &&
    match function.status with
    | .present => function.identity == entry.identity
    | .absent => !entry.required && function.identity == identity 0 0 0 &&
        function.command == 0 && function.assignment == .unassigned
    | .unreadable => false

def accounted (snapshot : Snapshot) : Bool :=
  snapshot.functions.length == q35Manifest.length &&
    q35Manifest.all fun entry =>
      match findFunction snapshot entry.bdf with
      | some function => matchesManifest entry function
      | none => false

def canonical (snapshot : Snapshot) : Bool :=
  snapshot.functions.length ≤ maxFunctions && uniqueBDFs snapshot.functions &&
    canonicalOrder snapshot.functions &&
    snapshot.functions.all fun function =>
      bdfValid function.bdf && identityValid function.identity &&
        commandCanonical function.command && (findManifest function.bdf).isSome

def quarantine (snapshot : Snapshot) : Bool :=
  snapshot.functions.any (·.status == .present) &&
    snapshot.functions.all fun function =>
      match function.status with
      | .present => function.assignment == .unassigned && !busMasterEnabled function
      | .absent => true
      | .unreadable => false

inductive RejectReason where
  | staleSnapshotVersion | wrongTopology | tooManyFunctions | noncanonical
  | inventoryMismatch | unreadableFunction | assignmentForbidden | busMasterEnabled
  deriving BEq, DecidableEq, Repr

structure AcceptedSnapshot where
  snapshot : Snapshot
  versionAccepted : snapshot.version = snapshotVersion
  topologyAccepted : snapshot.topologyVersion = q35TopologyVersion
  canonicalAccepted : canonical snapshot = true
  accountedAccepted : accounted snapshot = true
  quarantineAccepted : quarantine snapshot = true

inductive ValidationResult where
  | accepted (snapshot : AcceptedSnapshot)
  | rejected (reason : RejectReason)

def ValidationResult.isAccepted : ValidationResult → Bool
  | .accepted _ => true
  | .rejected _ => false

def ValidationResult.reason : ValidationResult → Option RejectReason
  | .accepted _ => none
  | .rejected reason => some reason

def rejectReasonTag : RejectReason → UInt64
  | .staleSnapshotVersion => 1
  | .wrongTopology => 2
  | .tooManyFunctions => 3
  | .noncanonical => 4
  | .inventoryMismatch => 5
  | .unreadableFunction => 6
  | .assignmentForbidden => 7
  | .busMasterEnabled => 8

theorem rejectReasonTag_injective : Function.Injective rejectReasonTag := by
  intro first second hequal
  cases first <;> cases second <;> simp [rejectReasonTag] at hequal ⊢

/-- Canonical one-word validation-result encoding paired with `encodeSnapshot`
by the later stateful corpus.  Zero denotes acceptance; typed rejections use
stable nonzero tags. -/
def encodeValidationResult : ValidationResult → List UInt64
  | .accepted _ => [0]
  | .rejected reason => [rejectReasonTag reason]

@[simp] theorem encodeValidationResult_length result :
    (encodeValidationResult result).length = 1 := by
  cases result <;> rfl

def validate (snapshot : Snapshot) : ValidationResult :=
  if hversion : snapshot.version = snapshotVersion then
    if htopology : snapshot.topologyVersion = q35TopologyVersion then
      if _hbound : snapshot.functions.length ≤ maxFunctions then
        if _hunreadable : snapshot.functions.any (·.status == .unreadable) then
          .rejected .unreadableFunction
        else if hcanonical : canonical snapshot then
          if haccounted : accounted snapshot then
            if _hassignment : snapshot.functions.any fun function =>
                function.status == .present && function.assignment != .unassigned then
              .rejected .assignmentForbidden
            else if _hmaster : snapshot.functions.any fun function =>
                function.status == .present && busMasterEnabled function then
              .rejected .busMasterEnabled
            else if hquarantine : quarantine snapshot then
              .accepted
                { snapshot
                  versionAccepted := hversion
                  topologyAccepted := htopology
                  canonicalAccepted := hcanonical
                  accountedAccepted := haccounted
                  quarantineAccepted := hquarantine }
            else .rejected .noncanonical
          else .rejected .inventoryMismatch
        else .rejected .noncanonical
      else .rejected .tooManyFunctions
    else .rejected .wrongTopology
  else .rejected .staleSnapshotVersion

theorem validate_deterministic snapshot first second
    (hfirst : validate snapshot = first) (hsecond : validate snapshot = second) : first = second := by
  rw [hfirst] at hsecond
  exact hsecond

theorem accepted_nonempty (accepted : AcceptedSnapshot) :
    ∃ function ∈ accepted.snapshot.functions, function.status = .present := by
  have h := accepted.quarantineAccepted
  simp only [quarantine, Bool.and_eq_true] at h
  simp only [List.any_eq_true] at h
  obtain ⟨function, hmember, hpresent⟩ := h.1
  exact ⟨function, hmember, LawfulBEq.eq_of_beq hpresent⟩

theorem accepted_accounts_every_manifest_entry (accepted : AcceptedSnapshot)
    (entry : ManifestEntry) (hentry : entry ∈ q35Manifest) :
    ∃ function ∈ accepted.snapshot.functions,
      function.bdf = entry.bdf ∧ matchesManifest entry function = true := by
  have haccounted := accepted.accountedAccepted
  simp only [accounted, Bool.and_eq_true, List.all_eq_true] at haccounted
  have hfound := haccounted.2 entry hentry
  simp only [findFunction] at hfound
  cases hfind : accepted.snapshot.functions.find? (·.bdf == entry.bdf) with
  | none => simp [hfind] at hfound
  | some function =>
      have hmember := List.mem_of_find?_eq_some hfind
      have hbdf : function.bdf = entry.bdf := by
        have hp : (function.bdf == entry.bdf) = true :=
          @List.find?_some FunctionState (fun candidate => candidate.bdf == entry.bdf)
            function accepted.snapshot.functions hfind
        exact LawfulBEq.eq_of_beq hp
      exact ⟨function, hmember, hbdf, by simpa [hfind] using hfound⟩

/-- Every present function accepted from the hardware snapshot has a known
manifest BDF, and that BDF occurs exactly once in the accepted inventory. -/
theorem accepted_present_known_exactly_once (accepted : AcceptedSnapshot)
    (function : FunctionState) (hmember : function ∈ accepted.snapshot.functions)
    (_hpresent : function.status = .present) :
    (findManifest function.bdf).isSome = true ∧
      exactlyOnce function.bdf accepted.snapshot.functions = true := by
  have hcanonical := accepted.canonicalAccepted
  simp only [canonical, Bool.and_eq_true, List.all_eq_true] at hcanonical
  have hfunction := hcanonical.2 function hmember
  have hunique := hcanonical.1.1.2
  simp only [uniqueBDFs, List.all_eq_true] at hunique
  exact ⟨hfunction.2, hunique function hmember⟩

theorem accepted_unassigned_busMaster_disabled (accepted : AcceptedSnapshot)
    (function : FunctionState) (hmember : function ∈ accepted.snapshot.functions)
    (hpresent : function.status = .present) :
    function.assignment = .unassigned ∧ busMasterEnabled function = false := by
  have h := accepted.quarantineAccepted
  simp only [quarantine, Bool.and_eq_true, List.all_eq_true] at h
  have hall := h.2 function hmember
  simp [hpresent] at hall
  exact ⟨hall.1, hall.2⟩

/-! ## Device-control contract and complete memory preservation -/

structure MemoryProjection where
  physicalMemory : Nat → UInt8
  allocatorOwnership : Nat → Option Nat
  pageTableFrames : Nat → UInt8
  kernelOwnedFrames : Nat → UInt8
  kernelState : Nat → UInt64
  subjectVisible : Nat → Nat → UInt8

/-- Trusted hardware rule: any device-originated change by the named function
requires that function to be present with its observed PCI Command bus-master
bit enabled. Assignment is kernel policy, not a hardware precondition for DMA;
acceptance separately proves that every present function is unassigned. This
is an assumption about the modeled device, not a theorem about PCI/QEMU. -/
def DeviceContract (snapshot : Snapshot) (target : BDF)
    (before after : MemoryProjection) : Prop :=
  before ≠ after → ∃ function ∈ snapshot.functions,
    function.bdf = target ∧ function.status = .present ∧
      busMasterEnabled function = true

/-- An unowned function in an accepted, nonempty quarantine cannot change any
part of the complete modeled memory projection. -/
theorem unowned_device_preserves_complete_projection
    (accepted : AcceptedSnapshot) (target : BDF) (before after : MemoryProjection)
    (hcontract : DeviceContract accepted.snapshot target before after)
    (hknown : ∃ function ∈ accepted.snapshot.functions,
      function.bdf = target ∧ function.status = .present) :
    after.physicalMemory = before.physicalMemory ∧
      after.allocatorOwnership = before.allocatorOwnership ∧
      after.pageTableFrames = before.pageTableFrames ∧
      after.kernelOwnedFrames = before.kernelOwnedFrames ∧
      after.kernelState = before.kernelState ∧
      after.subjectVisible = before.subjectVisible := by
  obtain ⟨_known, _hknownMember, _hknownBdf, _hknownPresent⟩ := hknown
  have heq : before = after := by
    apply Classical.byContradiction
    intro hne
    obtain ⟨function, hmember, _hbdf, hpresent, hmaster⟩ := hcontract hne
    have hdisabled := accepted_unassigned_busMaster_disabled accepted function hmember hpresent
    simp [hdisabled.2] at hmaster
  cases heq
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## Runtime control continuity and typed fatal separation -/

inductive FatalReason where
  | controlSnapshotChanged | invalidControlSnapshot
  deriving BEq, DecidableEq, Repr

inductive RuntimeMode where
  | running | halted (reason : FatalReason)
  deriving BEq, DecidableEq, Repr

structure RuntimeState where
  accepted : AcceptedSnapshot
  observed : Snapshot
  memory : MemoryProjection
  mode : RuntimeMode

inductive PublicOperation where
  | ordinary
  | observeControl (snapshot : Snapshot)

inductive RuntimeResult where
  | continued | fatal (reason : FatalReason) | alreadyHalted (reason : FatalReason)
  deriving BEq, DecidableEq, Repr

structure RuntimeOutcome where
  state : RuntimeState
  result : RuntimeResult

def RuntimeInvariant (state : RuntimeState) : Prop :=
  state.mode = .running ∧ state.observed = state.accepted.snapshot

def runtimeGate (state : RuntimeState) (operation : PublicOperation) : RuntimeOutcome :=
  match state.mode with
  | .halted reason => ⟨state, .alreadyHalted reason⟩
  | .running =>
      match operation with
      | .ordinary => ⟨state, .continued⟩
      | .observeControl snapshot =>
          match validate snapshot with
          | .accepted _next =>
              if snapshot == state.accepted.snapshot then
                ⟨{ state with observed := snapshot }, .continued⟩
              else
                ⟨{ state with observed := snapshot, mode := .halted .controlSnapshotChanged },
                  .fatal .controlSnapshotChanged⟩
          | .rejected _ =>
              ⟨{ state with observed := snapshot, mode := .halted .invalidControlSnapshot },
                .fatal .invalidControlSnapshot⟩

theorem nonfatal_runtime_preserves_quarantine state operation outcome
    (hinvariant : RuntimeInvariant state)
    (hgate : runtimeGate state operation = outcome)
    (hcontinued : outcome.result = .continued) :
    RuntimeInvariant outcome.state ∧
      quarantine outcome.state.accepted.snapshot = true := by
  rcases hinvariant with ⟨hmode, hobserved⟩
  cases operation with
  | ordinary =>
      simp [runtimeGate, hmode] at hgate
      subst outcome
      exact ⟨⟨hmode, hobserved⟩, state.accepted.quarantineAccepted⟩
  | observeControl snapshot =>
      simp only [runtimeGate, hmode] at hgate
      cases hvalidation : validate snapshot with
      | rejected reason => simp [hvalidation] at hgate; subst outcome; contradiction
      | accepted next =>
          by_cases heq : snapshot == state.accepted.snapshot
          · simp [hvalidation, heq] at hgate
            subst outcome
            have hsnapshot : snapshot = state.accepted.snapshot := LawfulBEq.eq_of_beq heq
            exact ⟨⟨rfl, hsnapshot⟩, state.accepted.quarantineAccepted⟩
          · simp [hvalidation, heq] at hgate
            subst outcome
            contradiction

theorem changed_control_is_fatal state snapshot
    (hrunning : state.mode = .running)
    (hchanged : snapshot ≠ state.accepted.snapshot) :
    (runtimeGate state (.observeControl snapshot)).result ≠ .continued := by
  simp only [runtimeGate, hrunning]
  cases validate snapshot with
  | rejected reason => simp
  | accepted next =>
      have hbeq : (snapshot == state.accepted.snapshot) = false := by
        apply Bool.eq_false_iff.mpr
        intro heq
        exact hchanged (LawfulBEq.eq_of_beq heq)
      simp [hbeq]

theorem halted_absorbing state reason operation
    (hmode : state.mode = .halted reason) :
    runtimeGate state operation = ⟨state, .alreadyHalted reason⟩ := by
  simp [runtimeGate, hmode]

/-! ## Executable q35 vectors -/

def presentFunction (entry : ManifestEntry) (command : UInt64 := 0) : FunctionState :=
  ⟨entry.bdf, entry.identity, .present, command, .unassigned,
    entry.bridge, entry.multifunction⟩

def absentFunction (entry : ManifestEntry) : FunctionState :=
  ⟨entry.bdf, identity 0 0 0, .absent, 0, .unassigned,
    entry.bridge, entry.multifunction⟩

def q35Functions : List FunctionState :=
  q35Manifest.map fun entry => if entry.required then presentFunction entry else absentFunction entry

def q35Snapshot : Snapshot := ⟨snapshotVersion, q35TopologyVersion, q35Functions⟩

def q35OptionalNetworkPresentFunctions : List FunctionState :=
  q35Functions.set 2 (presentFunction q35Manifest[2]!)

def q35OptionalNetworkPresentSnapshot : Snapshot :=
  { q35Snapshot with functions := q35OptionalNetworkPresentFunctions }

def q35CommandBitFlipSnapshot : Snapshot :=
  { q35Snapshot with functions :=
      q35Functions.set 0 { q35Functions[0]! with command := 1 } }

def q35BusMasterBitFlipSnapshot : Snapshot :=
  { q35Snapshot with functions :=
      q35Functions.set 1 { q35Functions[1]! with command := 4 } }

def q35Accepted : AcceptedSnapshot where
  snapshot := q35Snapshot
  versionAccepted := by native_decide
  topologyAccepted := by native_decide
  canonicalAccepted := by native_decide
  accountedAccepted := by native_decide
  quarantineAccepted := by native_decide

def zeroMemoryProjection : MemoryProjection where
  physicalMemory := fun _ => 0
  allocatorOwnership := fun _ => none
  pageTableFrames := fun _ => 0
  kernelOwnedFrames := fun _ => 0
  kernelState := fun _ => 0
  subjectVisible := fun _ _ => 0

def q35Runtime : RuntimeState :=
  ⟨q35Accepted, q35Snapshot, zeroMemoryProjection, .running⟩

example : (validate q35Snapshot).isAccepted = true := by native_decide
example : encodeValidationResult (validate q35Snapshot) = [0] := by native_decide
example : encodeValidationResult (validate { q35Snapshot with version := 0 }) = [1] := by
  native_decide
example : q35Functions[2]!.status = .absent := by native_decide
example : (validate q35OptionalNetworkPresentSnapshot).isAccepted = true := by native_decide
example : (encodeSnapshot q35Snapshot).map List.length = some snapshotWords := by native_decide
example : encodeFunction
    { q35Functions.head! with assignment := .kernelOwner 0xffffffffffffffff } ≠
    encodeFunction { q35Functions.head! with assignment := .unassigned } := by
  native_decide
example : (validate { q35Snapshot with version := 0 }).reason = some .staleSnapshotVersion := by
  native_decide
example : (validate { q35Snapshot with topologyVersion := 0 }).reason = some .wrongTopology := by
  native_decide
example : (validate { q35Snapshot with functions := q35Functions ++ [q35Functions.head!] }).reason =
    some .noncanonical := by native_decide
example : (validate { q35Snapshot with functions := q35Functions.tail }).reason =
    some .noncanonical := by native_decide
example :
    let first := q35Functions.head!
    (validate { q35Snapshot with functions :=
      { first with identity := identity 0xffff 0xffff 0xffffff } :: q35Functions.tail }).reason =
      some .inventoryMismatch := by native_decide
example :
    let first := q35Functions.head!
    (validate { q35Snapshot with functions :=
      { first with identity := { first.identity with vendor := 0xffff } } ::
        q35Functions.tail }).reason = some .inventoryMismatch := by native_decide
example :
    let first := q35Functions.head!
    (validate { q35Snapshot with functions :=
      { first with identity := { first.identity with device := 0xffff } } ::
        q35Functions.tail }).reason = some .inventoryMismatch := by native_decide
example :
    let first := q35Functions.head!
    (validate { q35Snapshot with functions :=
      { first with identity := { first.identity with classCode := 0xffffff } } ::
        q35Functions.tail }).reason = some .inventoryMismatch := by native_decide
example :
    let first := q35Functions.head!
    (validate { q35Snapshot with functions :=
      { first with status := .unreadable } :: q35Functions.tail }).reason =
      some .unreadableFunction := by native_decide
example :
    let first := q35Functions.head!
    let unreadableAllOnes : FunctionState :=
      ⟨first.bdf, identity 0xffff 0xffff 0xffffff, .unreadable, 0xffffffffffffffff,
        first.assignment, first.bridge, first.multifunction⟩
    (validate { q35Snapshot with functions :=
      unreadableAllOnes :: q35Functions.tail }).reason =
      some .unreadableFunction := by native_decide
example :
    let bridge := q35Functions[3]!
    let modified : FunctionState := { bridge with bridge := false }
    (validate { q35Snapshot with functions :=
      (q35Functions.set 3 modified) }).reason = some .inventoryMismatch := by native_decide
example :
    let sata := q35Functions[4]!
    let modified : FunctionState := { sata with multifunction := false }
    (validate { q35Snapshot with functions :=
      (q35Functions.set 4 modified) }).reason = some .inventoryMismatch := by native_decide
example :
    let vga := q35Functions[1]!
    let modified : FunctionState := { vga with command := 4 }
    (validate { q35Snapshot with functions :=
      (q35Functions.set 1 modified) }).reason = some .busMasterEnabled := by native_decide
example :
    let network := q35OptionalNetworkPresentFunctions[2]!
    let modified : FunctionState := { network with command := 4 }
    (validate { q35OptionalNetworkPresentSnapshot with functions :=
      (q35OptionalNetworkPresentFunctions.set 2 modified) }).reason =
      some .busMasterEnabled := by native_decide
example :
    let sata := q35Functions[4]!
    let modified : FunctionState := { sata with command := 4 }
    (validate { q35Snapshot with functions :=
      (q35Functions.set 4 modified) }).reason = some .busMasterEnabled := by
  native_decide
example :
    let smbus := q35Functions[5]!
    let modified : FunctionState := { smbus with command := 4 }
    (validate { q35Snapshot with functions :=
      (q35Functions.set 5 modified) }).reason = some .busMasterEnabled := by native_decide
example :
    let sata := q35Functions[4]!
    let modified : FunctionState := { sata with command := 0x800 }
    (validate { q35Snapshot with functions :=
      (q35Functions.set 4 modified) }).reason = some .noncanonical := by
  native_decide
example :
    let sata := q35Functions[4]!
    let modified : FunctionState := { sata with assignment := .kernelOwner 1 }
    (validate { q35Snapshot with functions :=
      (q35Functions.set 4 modified) }).reason =
      some .assignmentForbidden := by native_decide

example : (validate q35CommandBitFlipSnapshot).isAccepted = true := by native_decide
example : (runtimeGate q35Runtime (.observeControl q35CommandBitFlipSnapshot)).result =
    .fatal .controlSnapshotChanged := by native_decide
example : (runtimeGate q35Runtime (.observeControl q35BusMasterBitFlipSnapshot)).result =
    .fatal .invalidControlSnapshot := by native_decide

end LeanOS.DMAQuarantine
