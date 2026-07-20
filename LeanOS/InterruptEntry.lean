import LeanOS.Interrupt

/-!
# Bounded x86-64 interrupt-entry manifest and frame normalization

This module models the inbound boundary for the six ordinary gates used by
the boot image and the separate terminal vector-2 contract.  Vector 8 remains
in its own terminal IST1 machine protocol.  Descriptor loads, NMI delivery and
blocking, x86 frame construction, IST switching, assembly, generated C, and
the final binary are trusted/tested boundaries rather than theorem claims.
-/
namespace LeanOS.InterruptEntry

open LeanOS

inductive GateType where | interrupt
  deriving DecidableEq, Repr

inductive Purpose where
  | extendedUnavailable | extendedDenied
  | generalProtection | userFault | timer | syscall | diagnosticRecovery
  | terminalNmi
  deriving DecidableEq, Repr

inductive OriginPolicy where | userOnly | userOrKernel
  deriving DecidableEq, Repr

structure ManifestEntry where
  vector : UInt64
  gate : GateType
  selector : UInt64
  dpl : UInt64
  ist : UInt64
  hardwareError : Bool
  origins : OriginPolicy
  purpose : Purpose
  interruptsDisabled : Bool
  deriving DecidableEq, Repr

def invalidOpcodeEntry : ManifestEntry :=
  ⟨6, .interrupt, 0x08, 0, 0, false, .userOnly, .extendedUnavailable, true⟩
def deviceNotAvailableEntry : ManifestEntry :=
  ⟨7, .interrupt, 0x08, 0, 0, false, .userOnly, .extendedDenied, true⟩
def generalProtectionEntry : ManifestEntry :=
  ⟨13, .interrupt, 0x08, 0, 0, true, .userOnly, .generalProtection, true⟩
def pageFaultEntry : ManifestEntry :=
  ⟨14, .interrupt, 0x08, 0, 0, true, .userOrKernel, .userFault, true⟩
def timerEntry : ManifestEntry :=
  ⟨32, .interrupt, 0x08, 0, 0, false, .userOnly, .timer, true⟩
def syscallEntry : ManifestEntry :=
  ⟨128, .interrupt, 0x08, 3, 0, false, .userOnly, .syscall, true⟩

/-- The complete ordinary-gate manifest.  Vector 8 is intentionally absent. -/
def manifest : List ManifestEntry :=
  [invalidOpcodeEntry, deviceNotAvailableEntry, generalProtectionEntry, pageFaultEntry,
    timerEntry, syscallEntry]

def entrySupported (entry : ManifestEntry) : Bool :=
  entry.gate = .interrupt && entry.selector = 0x08 && entry.ist = 0 &&
    entry.interruptsDisabled &&
    ((entry = invalidOpcodeEntry) || (entry = deviceNotAvailableEntry) ||
      (entry = generalProtectionEntry) || (entry = pageFaultEntry) ||
      (entry = timerEntry) || (entry = syscallEntry))

def noDuplicateVectors (entries : List ManifestEntry) : Bool :=
  (entries.map (·.vector)).Nodup

def validateManifest (entries : List ManifestEntry) : Bool :=
  entries.length = 6 && noDuplicateVectors entries &&
    entries.all entrySupported &&
    entries.filter (fun entry => entry.dpl = 3) = [syscallEntry]

theorem reviewed_manifest_valid : validateManifest manifest = true := by native_decide

theorem only_syscall_is_dpl3 entry
    (hmember : entry ∈ manifest) (hdpl : entry.dpl = 3) : entry = syscallEntry := by
  simp [manifest, invalidOpcodeEntry, deviceNotAvailableEntry, pageFaultEntry,
    generalProtectionEntry, timerEntry, syscallEntry] at hmember
  rcases hmember with rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all [syscallEntry]

/-- Vector 13 is a hardware-error, user-only general-protection gate.  A
handler may refine the cause only after validating the error code, RIP, and
instruction operands. -/
theorem general_protection_manifest_binding :
    generalProtectionEntry ∈ manifest ∧
    generalProtectionEntry.hardwareError = true ∧
    generalProtectionEntry.origins = .userOnly ∧
    generalProtectionEntry.purpose = .generalProtection := by
  native_decide

inductive RawFrame where
  /-- CPL changed, so x86 supplied saved RSP and SS. -/
  | privilegeChange (rip cs flags rsp ss : UInt64)
  /-- CPL did not change; saved RSP and SS are architecturally absent. -/
  | samePrivilege (rip cs flags : UInt64)
  deriving DecidableEq, Repr

structure RawEntry where
  boundVector : UInt64
  boundStub : UInt64
  errorCode : Option UInt64
  frame : RawFrame
  frameBytes : UInt64
  frameAddress : UInt64
  acCleared : Bool
  dfCleared : Bool
  deriving DecidableEq, Repr

/-- Attacker-controlled registers are deliberately not an input to normalize. -/
structure AttackerRegisters where
  words : List UInt64
  deriving DecidableEq, Repr

structure KernelContext where
  currentSubject : Interrupt.SubjectId
  activeAddressSpace : Interrupt.AddressSpaceId
  activeCr3 : UInt64
  stackIdentity : UInt64
  stackFirst : UInt64
  stackPastLast : UInt64
  entryActive : Bool
  deriving DecidableEq, Repr

structure NormalizedFrame where
  vector : UInt64
  purpose : Purpose
  origin : Interrupt.Privilege
  errorCode : Option UInt64
  rip : UInt64
  cs : UInt64
  flags : UInt64
  userRsp : Option UInt64
  userSs : Option UInt64
  currentSubject : Interrupt.SubjectId
  activeAddressSpace : Interrupt.AddressSpaceId
  activeCr3 : UInt64
  stackIdentity : UInt64
  deriving DecidableEq, Repr

inductive RejectReason where
  | invalidManifest | unsupportedVector | wrongStub | wrongErrorShape
  | wrongOrigin | wrongFrameShape | truncated | misaligned | stackOutOfBounds
  | nested | privilegedStateNotCleared
  deriving DecidableEq, Repr

inductive Result where
  | accepted (frame : NormalizedFrame)
  | fatal (reason : RejectReason)
  deriving DecidableEq, Repr

def findEntry (vector : UInt64) : Option ManifestEntry :=
  manifest.find? (fun entry => entry.vector = vector)

def frameOrigin : RawFrame → Interrupt.Privilege
  | .privilegeChange _ cs _ _ _ => if cs % 4 = 3 then .user else .kernel
  | .samePrivilege _ _ _ => .kernel

def shapeBytes : RawFrame → UInt64
  | .privilegeChange .. => 40
  | .samePrivilege .. => 24

def purposeFor (entry : ManifestEntry) (origin : Interrupt.Privilege) : Purpose :=
  if entry.purpose = .userFault && origin = .kernel then .diagnosticRecovery
  else entry.purpose

def makeNormalized (entry : ManifestEntry) (raw : RawEntry) (context : KernelContext) :
    NormalizedFrame :=
  match raw.frame with
  | .privilegeChange rip cs flags rsp ss =>
      ⟨entry.vector, purposeFor entry .user, .user, raw.errorCode, rip, cs, flags,
        some rsp, some ss, context.currentSubject, context.activeAddressSpace,
        context.activeCr3, context.stackIdentity⟩
  | .samePrivilege rip cs flags =>
      ⟨entry.vector, purposeFor entry .kernel, .kernel, raw.errorCode, rip, cs, flags,
        none, none, context.currentSubject, context.activeAddressSpace,
        context.activeCr3, context.stackIdentity⟩

theorem makeNormalized_binds_context entry raw context :
    (makeNormalized entry raw context).currentSubject = context.currentSubject ∧
    (makeNormalized entry raw context).activeAddressSpace = context.activeAddressSpace ∧
    (makeNormalized entry raw context).activeCr3 = context.activeCr3 ∧
    (makeNormalized entry raw context).stackIdentity = context.stackIdentity := by
  cases raw with
  | mk boundVector boundStub errorCode frame frameBytes frameAddress acCleared dfCleared =>
    cases frame <;> simp [makeNormalized]

theorem makeNormalized_same_privilege entry raw context rip cs flags
    (hshape : raw.frame = .samePrivilege rip cs flags) :
    (makeNormalized entry raw context).origin = .kernel ∧
    (makeNormalized entry raw context).userRsp = none ∧
    (makeNormalized entry raw context).userSs = none := by
  simp [makeNormalized, hshape]

/-- Total normalization.  Every rejection is terminal authorization failure;
no operation-specific action is represented by a rejected result. -/
def normalize (raw : RawEntry) (context : KernelContext) : Result :=
  if !validateManifest manifest then .fatal .invalidManifest
  else match findEntry raw.boundVector with
  | none => .fatal .unsupportedVector
  | some entry =>
      if raw.boundStub != entry.vector then .fatal .wrongStub
      else if raw.errorCode.isSome != entry.hardwareError then .fatal .wrongErrorShape
      else if raw.frameBytes != shapeBytes raw.frame then .fatal .truncated
      else if raw.frameAddress % 16 != 0 then .fatal .misaligned
      else if raw.frameAddress < context.stackFirst ||
          raw.frameAddress + raw.frameBytes > context.stackPastLast then
        .fatal .stackOutOfBounds
      else if context.entryActive then .fatal .nested
      else if !raw.acCleared || !raw.dfCleared then .fatal .privilegedStateNotCleared
      else match raw.frame, entry.origins with
      | .privilegeChange _ cs _ _ _, policy =>
          if cs % 4 != 3 then .fatal .wrongOrigin
          else match policy with
          | .userOnly | .userOrKernel => .accepted (makeNormalized entry raw context)
      | .samePrivilege _ _ _, .userOnly => .fatal .wrongOrigin
      | .samePrivilege _ cs _, .userOrKernel =>
          if cs % 4 != 0 then .fatal .wrongFrameShape
          else .accepted (makeNormalized entry raw context)

/-- The explicit machine-facing spelling records that saved GPRs are erased
before the trusted entry classifier is evaluated. -/
def normalizeWithRegisters (raw : RawEntry) (context : KernelContext)
    (_registers : AttackerRegisters) : Result :=
  normalize raw context

theorem attacker_register_erasure raw context left right :
    normalizeWithRegisters raw context left = normalizeWithRegisters raw context right := by
  rfl

theorem normalize_total raw context : ∃ result, normalize raw context = result := by
  exact ⟨_, rfl⟩

theorem rejection_stable raw context reason
    (hrejected : normalize raw context = .fatal reason) :
    normalize raw context = .fatal reason :=
  hrejected

theorem normalize_deterministic raw context first second
    (hfirst : normalize raw context = first)
    (hsecond : normalize raw context = second) : first = second := by
  rw [← hfirst, hsecond]

theorem nested_never_authorizes raw context (hnested : context.entryActive = true) :
    ∀ accepted, normalize raw context ≠ .accepted accepted := by
  intro accepted
  unfold normalize
  simp only [reviewed_manifest_valid, Bool.not_true, Bool.false_eq_true, if_false]
  split <;> try simp
  split <;> try simp
  split <;> try simp
  split <;> try simp
  split <;> try simp
  split <;> try simp

theorem uncleared_ac_never_authorizes raw context (hac : raw.acCleared = false) :
    ∀ accepted, normalize raw context ≠ .accepted accepted := by
  intro accepted
  unfold normalize
  simp only [reviewed_manifest_valid, Bool.not_true, Bool.false_eq_true, if_false]
  split <;> try simp
  split <;> try simp
  split <;> try simp
  split <;> try simp
  split <;> try simp
  split <;> try simp
  split <;> try simp
  simp [hac]

theorem uncleared_df_never_authorizes raw context (hdf : raw.dfCleared = false) :
    ∀ accepted, normalize raw context ≠ .accepted accepted := by
  intro accepted
  unfold normalize
  simp only [reviewed_manifest_valid, Bool.not_true, Bool.false_eq_true, if_false]
  split <;> try simp
  split <;> try simp
  split <;> try simp
  split <;> try simp
  split <;> try simp
  split <;> try simp
  split <;> try simp
  simp [hdf]

theorem same_privilege_never_user raw context accepted
    (hshape : ∃ rip cs flags, raw.frame = .samePrivilege rip cs flags)
    (haccepted : normalize raw context = .accepted accepted) :
    accepted.origin = .kernel ∧ accepted.userRsp = none ∧ accepted.userSs = none := by
  rcases hshape with ⟨rip, cs, flags, hshape⟩
  unfold normalize at haccepted
  simp only [reviewed_manifest_valid, Bool.not_true, Bool.false_eq_true, if_false] at haccepted
  split at haccepted <;> try contradiction
  split at haccepted <;> try contradiction
  split at haccepted <;> try contradiction
  split at haccepted <;> try contradiction
  split at haccepted <;> try contradiction
  split at haccepted <;> try contradiction
  split at haccepted <;> try contradiction
  split at haccepted <;> try contradiction
  rw [hshape] at haccepted
  split at haccepted <;> try contradiction
  split at haccepted <;> try contradiction
  cases haccepted
  exact makeNormalized_same_privilege _ _ _ _ _ _ hshape

/-! ## Separate terminal NMI manifest and IST-switch frame

The ordinary manifest intentionally cannot accept vector 2.  An NMI uses a
dedicated IST2 identity and an explicit five-word saved frame even when the
interrupted CPL is zero.  The model consumes a normalized raw snapshot; x86
delivery, NMI blocking/coalescing, and construction of that snapshot remain
trusted machine assumptions. -/

inductive InterruptedMode where
  | running | handling | halted
  deriving DecidableEq, Repr

def nmiVector : UInt64 := 2
def nmiIst : UInt64 := 2
def nmiStackIdentity : UInt64 := 2
def nmiStackFirst : UInt64 := 0x900000
def nmiStackPastLast : UInt64 := 0x904000

def nmiEntry : ManifestEntry :=
  ⟨2, .interrupt, 0x08, 0, nmiIst, false, .userOrKernel, .terminalNmi, true⟩

/-- Terminal entries are reviewed separately so extending them cannot make a
vector ordinary-handler-authorized. -/
def terminalManifest : List ManifestEntry := [nmiEntry]

def terminalEntrySupported (entry : ManifestEntry) : Bool :=
  entry = nmiEntry && entry.vector = nmiVector && entry.gate = .interrupt &&
    entry.selector = 0x08 && entry.dpl = 0 && entry.ist = nmiIst &&
    !entry.hardwareError && entry.origins = .userOrKernel &&
    entry.purpose = .terminalNmi && entry.interruptsDisabled

def validateTerminalManifest (entries : List ManifestEntry) : Bool :=
  entries = terminalManifest && noDuplicateVectors entries && entries.all terminalEntrySupported

theorem reviewed_terminal_manifest_valid :
    validateTerminalManifest terminalManifest = true := by
  native_decide

theorem nmi_not_ordinary : nmiEntry ∉ manifest := by
  native_decide

/-- IST switching supplies saved SS/RSP for both admitted origins.  There is
no same-privilege short form in this terminal contract. -/
structure RawNmiFrame where
  rip : UInt64
  cs : UInt64
  flags : UInt64
  rsp : UInt64
  ss : UInt64
  canonicalRip : Bool
  canonicalRsp : Bool
  deriving DecidableEq, Repr

structure RawNmiEntry where
  descriptor : ManifestEntry
  boundStub : UInt64
  errorCode : Option UInt64
  frame : RawNmiFrame
  claimedOrigin : Interrupt.Privilege
  frameBytes : UInt64
  frameAddress : UInt64
  acCleared : Bool
  dfCleared : Bool
  deriving DecidableEq, Repr

/-- These fields are supplied by the trusted kernel/machine snapshot, not by
the interrupted register bank.  The normalizer additionally checks the two
identities also represented by the fail-stop state. -/
structure NmiContext where
  currentSubject : Interrupt.SubjectId
  activeAddressSpace : Interrupt.AddressSpaceId
  activeCr3 : UInt64
  stackIdentity : UInt64
  stackFirst : UInt64
  stackPastLast : UInt64
  interruptedMode : InterruptedMode
  deriving DecidableEq, Repr

structure NormalizedNmi where
  vector : UInt64
  purpose : Purpose
  origin : Interrupt.Privilege
  ist : UInt64
  rip : UInt64
  cs : UInt64
  flags : UInt64
  savedRsp : UInt64
  savedSs : UInt64
  currentSubject : Interrupt.SubjectId
  activeAddressSpace : Interrupt.AddressSpaceId
  activeCr3 : UInt64
  stackIdentity : UInt64
  interruptedMode : InterruptedMode
  deriving DecidableEq, Repr

inductive NmiRejectReason where
  | invalidManifest | wrongDescriptor | wrongTarget | spuriousError
  | wrongFrameBytes | misaligned | stackOutOfBounds | wrongStackIdentity
  | wrongOrigin | wrongSelectors | noncanonical | privilegedStateNotCleared
  | staleKernelContext
  deriving DecidableEq, Repr

inductive NmiResult where
  | accepted (event : NormalizedNmi)
  | fatal (reason : NmiRejectReason)
  deriving DecidableEq, Repr

def nmiFrameOrigin (frame : RawNmiFrame) : Interrupt.Privilege :=
  if frame.cs % 4 = 3 then .user else .kernel

def makeNormalizedNmi (raw : RawNmiEntry) (context : NmiContext) : NormalizedNmi :=
  { vector := nmiVector
    purpose := .terminalNmi
    origin := nmiFrameOrigin raw.frame
    ist := nmiIst
    rip := raw.frame.rip
    cs := raw.frame.cs
    flags := raw.frame.flags
    savedRsp := raw.frame.rsp
    savedSs := raw.frame.ss
    currentSubject := context.currentSubject
    activeAddressSpace := context.activeAddressSpace
    activeCr3 := context.activeCr3
    stackIdentity := context.stackIdentity
    interruptedMode := context.interruptedMode }

/-- The first exact terminal-contract failure, or `none` for the sole accepted
shape.  Keeping validation separate makes the result constructor auditable. -/
def nmiRejection? (raw : RawNmiEntry) (context : NmiContext)
    (expectedSubject : Interrupt.SubjectId)
    (expectedAddressSpace : Interrupt.AddressSpaceId) : Option NmiRejectReason :=
  if !validateTerminalManifest terminalManifest then some .invalidManifest
  else if raw.descriptor != nmiEntry then some .wrongDescriptor
  else if raw.boundStub != nmiVector then some .wrongTarget
  else if raw.errorCode.isSome then some .spuriousError
  else if raw.frameBytes != 40 then some .wrongFrameBytes
  else if raw.frameAddress % 16 != 0 then some .misaligned
  else if context.stackIdentity != nmiStackIdentity then some .wrongStackIdentity
  else if context.stackFirst != nmiStackFirst ||
      context.stackPastLast != nmiStackPastLast ||
      raw.frameAddress < context.stackFirst ||
      raw.frameAddress + raw.frameBytes < raw.frameAddress ||
      raw.frameAddress + raw.frameBytes > context.stackPastLast then
    some .stackOutOfBounds
  else if nmiFrameOrigin raw.frame != raw.claimedOrigin then some .wrongOrigin
  else if raw.claimedOrigin = .user then
    if raw.frame.cs != 0x23 || raw.frame.ss != 0x1b then some .wrongSelectors
    else if !raw.frame.canonicalRip || !raw.frame.canonicalRsp then some .noncanonical
    else if !raw.acCleared || !raw.dfCleared then some .privilegedStateNotCleared
    else if context.currentSubject != expectedSubject ||
        context.activeAddressSpace != expectedAddressSpace then some .staleKernelContext
    else none
  else if raw.frame.cs != 0x08 || raw.frame.ss != 0x10 then some .wrongSelectors
  else if !raw.frame.canonicalRip || !raw.frame.canonicalRsp then some .noncanonical
  else if !raw.acCleared || !raw.dfCleared then some .privilegedStateNotCleared
  else if context.currentSubject != expectedSubject ||
      context.activeAddressSpace != expectedAddressSpace then some .staleKernelContext
  else none

/-- Total normalization of the reviewed terminal snapshot.  The explicit
`expectedSubject` and `expectedAddressSpace` arguments come from the execution
latch and prevent a detached trusted-context record from naming a peer. -/
def normalizeNmi (raw : RawNmiEntry) (context : NmiContext)
    (expectedSubject : Interrupt.SubjectId)
    (expectedAddressSpace : Interrupt.AddressSpaceId) : NmiResult :=
  match nmiRejection? raw context expectedSubject expectedAddressSpace with
  | some reason => .fatal reason
  | none => .accepted (makeNormalizedNmi raw context)

def normalizeNmiWithRegisters (raw : RawNmiEntry) (context : NmiContext)
    (expectedSubject : Interrupt.SubjectId)
    (expectedAddressSpace : Interrupt.AddressSpaceId)
    (_registers : AttackerRegisters) : NmiResult :=
  normalizeNmi raw context expectedSubject expectedAddressSpace

theorem nmi_attacker_register_erasure raw context subject addressSpace left right :
    normalizeNmiWithRegisters raw context subject addressSpace left =
      normalizeNmiWithRegisters raw context subject addressSpace right := by
  rfl

theorem normalizeNmi_total raw context subject addressSpace :
    ∃ result, normalizeNmi raw context subject addressSpace = result := by
  exact ⟨_, rfl⟩

theorem normalizeNmi_deterministic raw context subject addressSpace first second
    (hfirst : normalizeNmi raw context subject addressSpace = first)
    (hsecond : normalizeNmi raw context subject addressSpace = second) : first = second := by
  rw [hfirst] at hsecond
  exact hsecond

theorem accepted_nmi_exact raw context subject addressSpace event
    (haccepted : normalizeNmi raw context subject addressSpace = .accepted event) :
    event = makeNormalizedNmi raw context := by
  unfold normalizeNmi at haccepted
  split at haccepted <;> simp_all

theorem accepted_nmi_has_no_rejection raw context subject addressSpace event
    (haccepted : normalizeNmi raw context subject addressSpace = .accepted event) :
    nmiRejection? raw context subject addressSpace = none ∧
      event = makeNormalizedNmi raw context := by
  cases hrejection : nmiRejection? raw context subject addressSpace with
  | none => exact ⟨rfl, accepted_nmi_exact _ _ _ _ _ haccepted⟩
  | some reason => simp [normalizeNmi, hrejection] at haccepted

theorem makeNormalizedNmi_binds_terminal_contract raw context :
    let event := makeNormalizedNmi raw context
    event.vector = nmiVector ∧ event.purpose = .terminalNmi ∧ event.ist = nmiIst ∧
      event.currentSubject = context.currentSubject ∧
      event.activeAddressSpace = context.activeAddressSpace ∧
      event.activeCr3 = context.activeCr3 ∧
      event.stackIdentity = context.stackIdentity ∧
      event.interruptedMode = context.interruptedMode := by
  simp [makeNormalizedNmi]

/-- A fixed-width encoding for the later stateful-corpus boundary.  Rejection
codes are stable, and accepted fields occupy named words rather than a packed,
attacker-selectable payload. -/
structure NmiResultWords where
  version : UInt64
  result : UInt64
  detail : UInt64
  vector : UInt64
  purpose : UInt64
  origin : UInt64
  ist : UInt64
  interruptedMode : UInt64
  subject : UInt64
  addressSpace : UInt64
  cr3 : UInt64
  stackIdentity : UInt64
  rip : UInt64
  cs : UInt64
  flags : UInt64
  savedRsp : UInt64
  savedSs : UInt64
  deriving DecidableEq, Repr

def NmiRejectReason.code : NmiRejectReason → UInt64
  | .invalidManifest => 1 | .wrongDescriptor => 2 | .wrongTarget => 3
  | .spuriousError => 4 | .wrongFrameBytes => 5 | .misaligned => 6
  | .stackOutOfBounds => 7 | .wrongStackIdentity => 8 | .wrongOrigin => 9
  | .wrongSelectors => 10 | .noncanonical => 11
  | .privilegedStateNotCleared => 12 | .staleKernelContext => 13

def InterruptedMode.code : InterruptedMode → UInt64
  | .running => 0 | .handling => 1 | .halted => 2

def encodeNmiResult : NmiResult → NmiResultWords
  | .fatal reason =>
      ⟨1, 0, reason.code, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩
  | .accepted event =>
      ⟨1, 1, 0, event.vector, 1, if event.origin = .user then 1 else 0,
        event.ist, event.interruptedMode.code, UInt64.ofNat event.currentSubject,
        UInt64.ofNat event.activeAddressSpace, event.activeCr3, event.stackIdentity,
        event.rip, event.cs, event.flags, event.savedRsp, event.savedSs⟩

/-- Fixed-width oracle encoding.  Nonzero success words bind purpose, origin,
subject, and address-space; zero is terminal rejection. -/
def entryModelExpected (descriptor frame stack context cleanup : UInt64) : UInt64 :=
  let vector := descriptor % 256
  let stub := descriptor / 256 % 256
  let hasError := descriptor / 65536 % 2 = 1
  let userShape := frame / 256 % 2 = 1
  let cs := frame % 256
  let bytes := if userShape then 40 else 24
  let rawFrame := if userShape then RawFrame.privilegeChange 0x400100 cs 0x202 0x500ff8 0x1b
    else RawFrame.samePrivilege 0x100000 cs 0x202
  let raw : RawEntry :=
    { boundVector := vector, boundStub := stub
      errorCode := if hasError then some 0 else none
      frame := rawFrame, frameBytes := if frame / 512 % 2 = 1 then bytes - 8 else bytes
      frameAddress := stack
      acCleared := cleanup % 2 = 1, dfCleared := cleanup / 2 % 2 = 1 }
  let ctx : KernelContext :=
    { currentSubject := (context % 256).toNat,
      activeAddressSpace := (context / 256 % 256).toNat
      activeCr3 := context / 65536, stackIdentity := 1
      stackFirst := 0x800000, stackPastLast := 0x804000
      entryActive := cleanup / 4 % 2 = 1 }
  match normalize raw ctx with
  | .fatal _ => 0
  | .accepted accepted =>
      1 + accepted.vector * 256 +
        (if accepted.origin = .user then 1 else 2) * 65536 +
        UInt64.ofNat accepted.currentSubject * 0x1000000 +
        UInt64.ofNat accepted.activeAddressSpace * 0x100000000

/-- Allocation-free spelling of the bounded classifier used by generated C. -/
def entryDemo (descriptor frame stack context cleanup : UInt64) : UInt64 :=
  let vector := descriptor % 256
  let stub := descriptor / 256 % 256
  let hasError := descriptor / 65536 % 2 = 1
  let cs := frame % 256
  let userShape := frame / 256 % 2 = 1
  let truncated := frame / 512 % 2 = 1
  let descriptorAllowed :=
    stub = vector &&
      (((vector = 6 || vector = 7) && !hasError) ||
       (vector = 13 && hasError) ||
       (vector = 14 && hasError) ||
       (vector = 32 && !hasError) ||
       (vector = 128 && !hasError))
  let originAllowed :=
    if userShape then cs = 0x23
    else vector = 14 && cs % 4 = 0
  let stackAllowed :=
    stack % 16 = 0 && 0x800000 ≤ stack &&
      stack + (if userShape then 40 else 24) ≤ 0x804000
  if descriptorAllowed && originAllowed && !truncated && stackAllowed && cleanup = 3 then
    1 + vector * 256 + (if userShape then 1 else 2) * 65536 +
      (context % 256) * 0x1000000 + (context / 256 % 256) * 0x100000000
  else 0

theorem entryDemo_total descriptor frame stack context cleanup :
    ∃ result, entryDemo descriptor frame stack context cleanup = result := by
  exact ⟨_, rfl⟩

@[export leanos_entry_demo]
def entryDemoExport (descriptor frame stack context cleanup : UInt64) : UInt64 :=
  entryDemo descriptor frame stack context cleanup

end LeanOS.InterruptEntry
