import LeanOS.Interrupt
import LeanOS.X86PageTable

/-!
# Bounded x86-64 interrupt-entry manifest and frame normalization

This module models the inbound boundary for the eight ordinary gates used by
the boot image and the separate terminal vector-2 contract.  Vector 8 remains
in its own terminal IST1 machine protocol.  Descriptor loads, NMI delivery and
blocking, x86 frame construction, IST switching, assembly, generated C, and
the final binary are trusted/tested boundaries rather than theorem claims.
The vector, error-word, and saved-RIP restart-class conventions for the
contained synchronous fault vectors follow the AMD64 Architecture
Programmer's Manual Volume 2 exception tables; x86 delivery itself stays a
trusted machine assumption, never a theorem conclusion.
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

/-- Vector 0 (#DE) is a hardware-originated fault gate.  Its DPL stays 0 so a
CPL3 `int $0` cannot software-select the containment path; only the
architectural divide error reaches this gate. -/
def divideErrorEntry : ManifestEntry :=
  ⟨0, .interrupt, 0x08, 0, 0, false, .userOnly, .userFault, true⟩
/-- Vector 3 (#BP) is deliberately CPL3 software-callable: `int3` requires
gate DPL 3.  The reviewed descriptor stays an interrupt gate (IF masked on
entry) rather than a trap gate; any other DPL/type combination is rejected by
`validateManifest`. -/
def breakpointEntry : ManifestEntry :=
  ⟨3, .interrupt, 0x08, 3, 0, false, .userOnly, .userFault, true⟩
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
  [divideErrorEntry, breakpointEntry, invalidOpcodeEntry, deviceNotAvailableEntry,
    generalProtectionEntry, pageFaultEntry, timerEntry, syscallEntry]

def entrySupported (entry : ManifestEntry) : Bool :=
  entry.gate = .interrupt && entry.selector = 0x08 && entry.ist = 0 &&
    entry.interruptsDisabled &&
    ((entry = divideErrorEntry) || (entry = breakpointEntry) ||
      (entry = invalidOpcodeEntry) || (entry = deviceNotAvailableEntry) ||
      (entry = generalProtectionEntry) || (entry = pageFaultEntry) ||
      (entry = timerEntry) || (entry = syscallEntry))

def noDuplicateVectors (entries : List ManifestEntry) : Bool :=
  (entries.map (·.vector)).Nodup

def validateManifest (entries : List ManifestEntry) : Bool :=
  entries.length = 8 && noDuplicateVectors entries &&
    entries.all entrySupported &&
    entries.filter (fun entry => entry.dpl = 3) = [breakpointEntry, syscallEntry]

theorem reviewed_manifest_valid : validateManifest manifest = true := by native_decide

/-- The complete software-callable (DPL3) descriptor inventory: the deliberate
`int3` breakpoint gate and the `int 0x80` syscall gate, nothing else. -/
theorem only_breakpoint_and_syscall_are_dpl3 entry
    (hmember : entry ∈ manifest) (hdpl : entry.dpl = 3) :
    entry = breakpointEntry ∨ entry = syscallEntry := by
  simp [manifest, divideErrorEntry, breakpointEntry, invalidOpcodeEntry,
    deviceNotAvailableEntry, pageFaultEntry, generalProtectionEntry, timerEntry,
    syscallEntry] at hmember
  rcases hmember with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp_all [breakpointEntry, syscallEntry]

/-- Vector 0 must never become a CPL3 software-callable `INT n` gate. -/
theorem divide_error_not_software_callable :
    divideErrorEntry ∈ manifest ∧ divideErrorEntry.dpl = 0 ∧
      divideErrorEntry.gate = .interrupt ∧
      divideErrorEntry.hardwareError = false ∧
      divideErrorEntry.origins = .userOnly ∧
      divideErrorEntry.purpose = .userFault := by
  native_decide

/-- Vector 3's reviewed descriptor policy is explicit: DPL3 software-callable,
interrupt (not trap) gate type, no architectural error word, user-only origin,
and the shared containment purpose. -/
theorem breakpoint_manifest_binding :
    breakpointEntry ∈ manifest ∧ breakpointEntry.dpl = 3 ∧
      breakpointEntry.gate = .interrupt ∧
      breakpointEntry.interruptsDisabled = true ∧
      breakpointEntry.hardwareError = false ∧
      breakpointEntry.origins = .userOnly ∧
      breakpointEntry.purpose = .userFault := by
  native_decide

/-- Any single-field DPL/type deviation from the reviewed vector-3 descriptor
is rejected: substituting a DPL0 breakpoint gate (or any unreviewed vector-3
entry) cannot revalidate the manifest. -/
theorem breakpoint_descriptor_deviation_rejected :
    validateManifest (manifest.map (fun entry =>
      if entry.vector = 3 then { entry with dpl := 0 } else entry)) = false := by
  native_decide

/-- Vector 13 is a hardware-error, user-only general-protection gate.  A
handler may refine the cause only after validating the error code, RIP, and
instruction operands. -/
theorem general_protection_manifest_binding :
    generalProtectionEntry ∈ manifest ∧
    generalProtectionEntry.hardwareError = true ∧
    generalProtectionEntry.origins = .userOnly ∧
    generalProtectionEntry.purpose = .generalProtection := by
  native_decide

/-! ## Typed contained-fault reason and saved-RIP restart classes

The contained synchronous CPL3 fault classes are a finite reviewed vocabulary
keyed by the manifest-bound vector, never by attacker registers, user-stack
words, syscall arguments, or the saved RIP value.  The AMD64 manual fixes the
per-vector error-word convention and whether the saved RIP names the faulting
instruction (#DE, #PF) or the following instruction boundary (#BP trap). -/

inductive ContainedReason where
  | pageFault | divideError | breakpoint
  deriving DecidableEq, Repr

def ContainedReason.vector : ContainedReason → UInt64
  | .pageFault => 14 | .divideError => 0 | .breakpoint => 3

/-- Only the page fault pushes an architectural error word; #DE and #BP push
none, and the normalizer rejects a spurious synthesized word. -/
def ContainedReason.hasErrorWord : ContainedReason → Bool
  | .pageFault => true | .divideError => false | .breakpoint => false

/-- Stable fixed-width code for the bounded corpus boundary.  The legacy
page-fault class stays zero so version-one expected words are unchanged. -/
def ContainedReason.code : ContainedReason → UInt64
  | .pageFault => 0 | .divideError => 1 | .breakpoint => 2

/-- What the normalized saved RIP names.  This is a machine assumption about
the raw snapshot; no modeled transition rewrites RIP to authorize recovery. -/
inductive RestartClass where
  | faultingInstruction | followingBoundary
  deriving DecidableEq, Repr

def RestartClass.other : RestartClass → RestartClass
  | .faultingInstruction => .followingBoundary
  | .followingBoundary => .faultingInstruction

def ContainedReason.restartClass : ContainedReason → RestartClass
  | .pageFault => .faultingInstruction
  | .divideError => .faultingInstruction
  | .breakpoint => .followingBoundary

/-- The manifest-bound reason decoder.  Exactly vectors 0, 3, and 14 name a
contained class; every other vector has no containment reason. -/
def containedReason? (vector : UInt64) : Option ContainedReason :=
  if vector = 0 then some .divideError
  else if vector = 3 then some .breakpoint
  else if vector = 14 then some .pageFault
  else none

/-- Reviewed AMD64 saved-RIP table for every ordinary vector: traps and
interrupts (#BP, timer, `int 0x80`) save the following boundary; faults save
the faulting instruction. -/
def restartClassFor (vector : UInt64) : RestartClass :=
  if vector = 3 || vector = 32 || vector = 128 then .followingBoundary
  else .faultingInstruction

theorem containedReason_vector_agreement reason vector
    (hdecoded : containedReason? vector = some reason) : reason.vector = vector := by
  grind [containedReason?, ContainedReason.vector]

theorem containedReason_roundtrip reason :
    containedReason? reason.vector = some reason := by
  cases reason <;> native_decide

/-- The reviewed restart-class table agrees with the typed per-reason class. -/
theorem contained_restart_class_agreement (reason : ContainedReason) :
    restartClassFor reason.vector = reason.restartClass := by
  cases reason <;> native_decide

/-- Every contained class resolves in the manifest to an entry with the exact
reviewed error convention and the shared containment purpose. -/
theorem contained_manifest_error_shape (reason : ContainedReason) :
    ∃ entry, manifest.find? (fun entry => entry.vector = reason.vector) = some entry ∧
      entry.vector = reason.vector ∧
      entry.hardwareError = reason.hasErrorWord ∧
      entry.purpose = .userFault := by
  cases reason
  · exact ⟨pageFaultEntry, by native_decide, rfl, rfl, rfl⟩
  · exact ⟨divideErrorEntry, by native_decide, rfl, rfl, rfl⟩
  · exact ⟨breakpointEntry, by native_decide, rfl, rfl, rfl⟩

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
  /-- Stub-supplied evidence naming what the saved RIP points at.  The
  normalizer rejects a claim that disagrees with the reviewed per-vector
  AMD64 table; no transition rewrites RIP to change restart semantics. -/
  restartClass : RestartClass
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
  | wrongRestartClass
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
  | mk boundVector boundStub errorCode restartClass frame frameBytes frameAddress
      acCleared dfCleared =>
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
      else if raw.restartClass != restartClassFor entry.vector then .fatal .wrongRestartClass
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
  split at haccepted <;> try contradiction
  rw [hshape] at haccepted
  split at haccepted <;> try contradiction
  split at haccepted <;> try contradiction
  cases haccepted
  exact makeNormalized_same_privilege _ _ _ _ _ _ hshape

/-- An accepted record's vector, error shape, and restart-class evidence are
bound by the manifest entry selected from the kernel-bound vector, never by
attacker payload words. -/
theorem accepted_binds_manifest_shape raw context accepted
    (haccepted : normalize raw context = .accepted accepted) :
    ∃ entry, findEntry raw.boundVector = some entry ∧
      accepted.vector = entry.vector ∧
      accepted.errorCode.isSome = entry.hardwareError ∧
      raw.restartClass = restartClassFor entry.vector := by
  unfold normalize at haccepted
  simp only [reviewed_manifest_valid, Bool.not_true, Bool.false_eq_true,
    if_false] at haccepted
  split at haccepted <;> try contradiction
  rename_i entry hentry
  refine ⟨entry, hentry, ?_⟩
  split at haccepted <;> try contradiction
  split at haccepted <;> try contradiction
  split at haccepted <;> try contradiction
  split at haccepted <;> try contradiction
  split at haccepted <;> try contradiction
  split at haccepted <;> try contradiction
  split at haccepted <;> try contradiction
  split at haccepted <;> try contradiction
  split at haccepted <;> try contradiction
  all_goals try split at haccepted <;> try contradiction
  all_goals try split at haccepted <;> try contradiction
  all_goals injection haccepted with haccepted
  all_goals subst haccepted
  all_goals simp_all [makeNormalized]

/-- Every accepted generic normalization retains the kernel-owned authority
context, independent of the selected frame shape. -/
theorem normalize_accepted_binds_context raw context accepted
    (haccepted : normalize raw context = .accepted accepted) :
    raw.errorCode = accepted.errorCode ∧
      accepted.currentSubject = context.currentSubject ∧
      accepted.activeAddressSpace = context.activeAddressSpace ∧
      accepted.activeCr3 = context.activeCr3 := by
  unfold normalize at haccepted
  simp only [reviewed_manifest_valid, Bool.not_true, Bool.false_eq_true,
    if_false] at haccepted
  split at haccepted <;> try contradiction
  rename_i entry hentry
  split at haccepted <;> try contradiction
  split at haccepted <;> try contradiction
  split at haccepted <;> try contradiction
  split at haccepted <;> try contradiction
  split at haccepted <;> try contradiction
  split at haccepted <;> try contradiction
  split at haccepted <;> try contradiction
  split at haccepted <;> try contradiction
  all_goals try split at haccepted <;> try contradiction
  all_goals try split at haccepted <;> try contradiction
  all_goals generalize horigin : entry.origins = origin at haccepted
  all_goals cases origin <;> simp_all [makeNormalized]
  all_goals subst accepted
  all_goals simp

/-- No-error-code normalization and restart-class agreement for the typed
contained classes, packaged so issue-#104 composition never unfolds
`normalize`: the accepted error shape and the raw saved-RIP evidence both
equal the reviewed per-reason convention. -/
theorem accepted_contained_error_shape raw context accepted reason
    (haccepted : normalize raw context = .accepted accepted)
    (hreason : containedReason? accepted.vector = some reason) :
    accepted.errorCode.isSome = reason.hasErrorWord ∧
      raw.restartClass = reason.restartClass := by
  obtain ⟨entry, hentry, hvector, herror, hrestart⟩ :=
    accepted_binds_manifest_shape raw context accepted haccepted
  have hpredicate := List.find?_some hentry
  have hbound : entry.vector = raw.boundVector := by
    simpa using hpredicate
  have hreasonVector : reason.vector = accepted.vector :=
    containedReason_vector_agreement reason accepted.vector hreason
  obtain ⟨reviewed, hreviewed, hreviewedVector, hreviewedError, _⟩ :=
    contained_manifest_error_shape reason
  have hsame : reviewed = entry := by
    have : findEntry reason.vector = some entry := by
      rw [hreasonVector, hvector, hbound]
      exact hentry
    have hfind : manifest.find? (fun entry => entry.vector = reason.vector) =
        some entry := this
    rw [hreviewed] at hfind
    exact Option.some.inj hfind
  constructor
  · rw [herror, ← hsame, hreviewedError]
  · rw [hrestart, ← hvector, ← hreasonVector]
    exact contained_restart_class_agreement reason

/-! ## Canonical page-fault provenance

The generic entry record above deliberately stops at the architectural error
word.  This page-fault-specific layer attaches the CR2 sample and a
kernel-owned paging-control snapshot only after the vector-14 entry has passed
the ordinary manifest/frame normalizer.  The supported architectural profile
is the AMD64 `P`, `W/R`, `U/S`, `RSVD`, and `I/D` error-word layout.  `RSVD=1`
is retained as a distinct rejection, and every bit at position five or above
(including PK, shadow-stack, and SGX indications) is unsupported by this
bounded profile and rejected rather than truncated.

x86 delivery, the temporal relationship between the pushed error word and
CR2, assembly sampling, and control-register read-back remain trusted machine
assumptions. -/

structure PagingControls where
  writeProtect : Bool
  nxEnable : Bool
  smep : Bool
  smap : Bool
  deriving DecidableEq, Repr

structure PageFaultContext where
  entry : KernelContext
  controls : PagingControls
  deriving DecidableEq, Repr

structure DecodedPageFaultError where
  protection : Bool
  write : Bool
  user : Bool
  instructionFetch : Bool
  deriving DecidableEq, Repr

def DecodedPageFaultError.accessKind (error : DecodedPageFaultError) :
    X86PageTable.AccessKind :=
  if error.instructionFetch then .execute else if error.write then .write else .read

inductive PageFaultErrorReject where
  | reservedBitViolation | unsupportedBits
  deriving DecidableEq, Repr

/-- Total exact decoder for the selected five-bit AMD64 profile. -/
def decodePageFaultError (word : UInt64) :
    Except PageFaultErrorReject DecodedPageFaultError :=
  if word / 32 != 0 then .error .unsupportedBits
  else if word / 8 % 2 = 1 then .error .reservedBitViolation
  else .ok
    { protection := word % 2 = 1
      write := word / 2 % 2 = 1
      user := word / 4 % 2 = 1
      instructionFetch := word / 16 % 2 = 1 }

theorem decodePageFaultError_total word :
    ∃ result, decodePageFaultError word = result := ⟨_, rfl⟩

theorem decodePageFaultError_deterministic word first second
    (hfirst : decodePageFaultError word = first)
    (hsecond : decodePageFaultError word = second) : first = second := by
  rw [← hfirst, hsecond]

theorem reserved_error_bit_rejected (word : UInt64)
    (hsupported : word / 32 = 0) (hreserved : word / 8 % 2 = 1) :
    decodePageFaultError word = .error .reservedBitViolation := by
  simp [decodePageFaultError, hsupported, hreserved]

theorem unsupported_error_bits_rejected (word : UInt64) (hhigh : word / 32 ≠ 0) :
    decodePageFaultError word = .error .unsupportedBits := by
  simp [decodePageFaultError, hhigh]

structure RawPageFault where
  entry : RawEntry
  /-- Trusted assembly samples CR2 for this accepted vector-14 entry. -/
  faultAddress : UInt64
  /-- Saved GPRs and diagnostics are retained only as non-authoritative data. -/
  savedGprs : AttackerRegisters
  diagnosticWords : List UInt64
  deriving DecidableEq, Repr

structure NormalizedPageFault where
  entry : NormalizedFrame
  error : DecodedPageFaultError
  accessKind : X86PageTable.AccessKind
  faultAddress : UInt64
  faultPage : UInt64
  controls : PagingControls
  deriving DecidableEq, Repr

inductive PageFaultRejectReason where
  | entry (reason : RejectReason)
  | wrongVector | missingError | reservedBitViolation | unsupportedErrorBits
  | privilegeMismatch | noncanonicalAddress
  deriving DecidableEq, Repr

inductive PageFaultResult where
  | accepted (snapshot : NormalizedPageFault)
  | fatal (reason : PageFaultRejectReason)
  deriving DecidableEq, Repr

def canonicalLinearAddress (address : UInt64) : Bool :=
  address < 0x0000800000000000 || address ≥ 0xffff800000000000

def makeNormalizedPageFault (frame : NormalizedFrame) (word : UInt64)
    (decoded : DecodedPageFaultError) (raw : RawPageFault)
    (context : PageFaultContext) : NormalizedPageFault :=
  { entry := { frame with errorCode := some word }
    error := decoded
    accessKind := decoded.accessKind
    faultAddress := raw.faultAddress
    faultPage := raw.faultAddress / 4096
    controls := context.controls }

/-- The page-fault payload can authorize nothing until the generic vector-14
entry is accepted.  Privilege is checked twice: saved-CS origin must agree
with the architectural U/S error bit. -/
def normalizePageFault (raw : RawPageFault) (context : PageFaultContext) :
    PageFaultResult :=
  match normalize raw.entry context.entry with
  | .fatal reason => .fatal (.entry reason)
  | .accepted frame =>
      if frame.vector != 14 then .fatal .wrongVector
      else match frame.errorCode with
      | none => .fatal .missingError
      | some word =>
          match decodePageFaultError word with
          | .error .reservedBitViolation => .fatal .reservedBitViolation
          | .error .unsupportedBits => .fatal .unsupportedErrorBits
          | .ok decoded =>
              let originUser := frame.origin = .user
              if originUser != decoded.user then .fatal .privilegeMismatch
              else if !canonicalLinearAddress raw.faultAddress then
                .fatal .noncanonicalAddress
              else .accepted (makeNormalizedPageFault frame word decoded raw context)

theorem normalizePageFault_total raw context :
    ∃ result, normalizePageFault raw context = result := ⟨_, rfl⟩

theorem normalizePageFault_deterministic raw context first second
    (hfirst : normalizePageFault raw context = first)
    (hsecond : normalizePageFault raw context = second) : first = second := by
  rw [← hfirst, hsecond]

/-- GPRs and diagnostic payload are erased from every authorization field. -/
theorem pageFault_saved_gpr_confinement (raw : RawPageFault)
    (context : PageFaultContext) left right :
    normalizePageFault { raw with savedGprs := left } context =
      normalizePageFault { raw with savedGprs := right } context := by
  rfl

theorem pageFault_diagnostic_confinement (raw : RawPageFault)
    (context : PageFaultContext) left right :
    normalizePageFault { raw with diagnosticWords := left } context =
      normalizePageFault { raw with diagnosticWords := right } context := by
  rfl

/-- Exact CR2 page binding and authoritative context binding at construction. -/
theorem makeNormalizedPageFault_exact_binding frame word decoded raw context :
    let snapshot := makeNormalizedPageFault frame word decoded raw context
    snapshot.entry.vector = frame.vector ∧
      snapshot.entry.errorCode = some word ∧
      snapshot.error = decoded ∧
      snapshot.accessKind = decoded.accessKind ∧
      snapshot.faultAddress = raw.faultAddress ∧
      snapshot.faultPage = raw.faultAddress / 4096 ∧
      snapshot.entry.currentSubject = frame.currentSubject ∧
      snapshot.entry.activeAddressSpace = frame.activeAddressSpace ∧
      snapshot.entry.activeCr3 = frame.activeCr3 ∧
      snapshot.controls = context.controls := by
  simp [makeNormalizedPageFault]

/-- Acceptance, rather than direct constructor use, establishes the complete
page-fault provenance contract. -/
theorem normalizePageFault_accepted_binding raw context snapshot
    (haccepted : normalizePageFault raw context = .accepted snapshot) :
    snapshot.entry.vector = 14 ∧
      ∃ word,
        raw.entry.errorCode = some word ∧
        snapshot.entry.errorCode = some word ∧
        decodePageFaultError word = .ok snapshot.error ∧
        snapshot.accessKind = snapshot.error.accessKind ∧
        snapshot.faultAddress = raw.faultAddress ∧
        snapshot.faultPage = raw.faultAddress / 4096 ∧
        canonicalLinearAddress raw.faultAddress = true ∧
        decide (snapshot.entry.origin = .user) = snapshot.error.user ∧
        snapshot.entry.currentSubject = context.entry.currentSubject ∧
        snapshot.entry.activeAddressSpace = context.entry.activeAddressSpace ∧
        snapshot.entry.activeCr3 = context.entry.activeCr3 ∧
        snapshot.controls = context.controls := by
  unfold normalizePageFault at haccepted
  split at haccepted <;> try contradiction
  rename_i frame hframe
  have hcontext :=
    normalize_accepted_binds_context raw.entry context.entry frame hframe
  split at haccepted <;> try contradiction
  split at haccepted <;> try contradiction
  split at haccepted <;> try contradiction
  dsimp only at haccepted
  split at haccepted <;> try contradiction
  split at haccepted <;> try contradiction
  all_goals injection haccepted with hsnapshot
  all_goals subst snapshot
  all_goals simp_all [makeNormalizedPageFault]

/-- Fixed-width version-one canonical record.  All fields are words; derived
fields are repeated deliberately so the decoder can reject relabeling. -/
structure CanonicalPageFault where
  vector : UInt64
  errorWord : UInt64
  faultAddress : UInt64
  faultPage : UInt64
  accessCode : UInt64
  protectionCode : UInt64
  privilegeCode : UInt64
  currentSubject : UInt64
  activeAddressSpace : UInt64
  activeCr3 : UInt64
  controlsCode : UInt64
  rip : UInt64
  cs : UInt64
  flags : UInt64
  userRsp : UInt64
  userSs : UInt64
  stackIdentity : UInt64
  reserved : UInt64
  deriving DecidableEq, Repr

def pageFaultAccessCode : X86PageTable.AccessKind → UInt64
  | .read => 0 | .write => 1 | .execute => 2

def pagingControlsCode (controls : PagingControls) : UInt64 :=
  (if controls.writeProtect then 1 else 0) +
    (if controls.nxEnable then 2 else 0) +
    (if controls.smep then 4 else 0) +
    (if controls.smap then 8 else 0)

/-- Decode the four reviewed paging-control bits from their canonical word. -/
def pagingControlsOfCode (code : UInt64) : PagingControls :=
  { writeProtect := code % 2 = 1
    nxEnable := code / 2 % 2 = 1
    smep := code / 4 % 2 = 1
    smap := code / 8 % 2 = 1 }

/-- The canonical codec is the serialized image of the normalized snapshot,
not a second independently authoritative record format. -/
def canonicalPageFaultRecord (snapshot : NormalizedPageFault) : CanonicalPageFault :=
  { vector := snapshot.entry.vector
    errorWord := snapshot.entry.errorCode.getD 0
    faultAddress := snapshot.faultAddress
    faultPage := snapshot.faultPage
    accessCode := pageFaultAccessCode snapshot.accessKind
    protectionCode := if snapshot.error.protection then 1 else 0
    privilegeCode := if snapshot.error.user then 1 else 0
    currentSubject := UInt64.ofNat snapshot.entry.currentSubject
    activeAddressSpace := UInt64.ofNat snapshot.entry.activeAddressSpace
    activeCr3 := snapshot.entry.activeCr3
    controlsCode := pagingControlsCode snapshot.controls
    rip := snapshot.entry.rip
    cs := snapshot.entry.cs
    flags := snapshot.entry.flags
    userRsp := snapshot.entry.userRsp.getD 0
    userSs := snapshot.entry.userSs.getD 0
    stackIdentity := snapshot.entry.stackIdentity
    reserved := 0 }

def validCanonicalPageFault (record : CanonicalPageFault) : Bool :=
  record.vector = 14 && canonicalLinearAddress record.faultAddress &&
    canonicalLinearAddress record.rip &&
    record.faultPage = record.faultAddress / 4096 &&
    record.reserved = 0 && record.controlsCode < 16 &&
    pagingControlsCode (pagingControlsOfCode record.controlsCode) =
      record.controlsCode &&
    record.flags / 2 % 2 = 1 && record.currentSubject != 0 &&
    record.activeAddressSpace != 0 && record.activeCr3 != 0 &&
    record.stackIdentity != 0 &&
    match decodePageFaultError record.errorWord with
    | .error _ => false
    | .ok decoded =>
        record.accessCode = pageFaultAccessCode decoded.accessKind &&
          record.protectionCode = (if decoded.protection then 1 else 0) &&
          record.privilegeCode = (if decoded.user then 1 else 0) &&
          (if decoded.user then
            record.cs = 0x23 && canonicalLinearAddress record.userRsp &&
              record.userRsp != 0 && record.userSs = 0x1b
            else record.cs = 0x08 && record.userRsp = 0 && record.userSs = 0)

def pageFaultCodecVersion : UInt64 := 1
def pageFaultCodecWidth : Nat := 19

/-- Version, followed by the 18 canonical fields in declaration order. -/
def encodeCanonicalPageFault (record : CanonicalPageFault) : List UInt64 :=
  [pageFaultCodecVersion, record.vector, record.errorWord, record.faultAddress,
    record.faultPage, record.accessCode, record.protectionCode,
    record.privilegeCode, record.currentSubject, record.activeAddressSpace,
    record.activeCr3, record.controlsCode, record.rip, record.cs, record.flags,
    record.userRsp, record.userSs, record.stackIdentity, record.reserved]

def parseCanonicalPageFault : List UInt64 → Option (UInt64 × CanonicalPageFault)
  | [version, vector, errorWord, faultAddress, faultPage, accessCode,
      protectionCode, privilegeCode, currentSubject, activeAddressSpace,
      activeCr3, controlsCode, rip, cs, flags, userRsp, userSs, stackIdentity,
      reserved] =>
      some (version,
        { vector, errorWord, faultAddress, faultPage, accessCode, protectionCode,
          privilegeCode, currentSubject, activeAddressSpace, activeCr3,
          controlsCode, rip, cs, flags, userRsp, userSs, stackIdentity, reserved })
  | _ => none

def decodeCanonicalPageFault (words : List UInt64) : Option CanonicalPageFault :=
  match parseCanonicalPageFault words with
  | none => none
  | some (version, record) =>
      if version != pageFaultCodecVersion then none
      else if !validCanonicalPageFault record then none
      else some record

theorem encodeCanonicalPageFault_width record :
    (encodeCanonicalPageFault record).length = pageFaultCodecWidth := by
  rfl

theorem decode_encode_canonical_page_fault record
    (hvalid : validCanonicalPageFault record = true) :
    decodeCanonicalPageFault (encodeCanonicalPageFault record) = some record := by
  simp [decodeCanonicalPageFault, parseCanonicalPageFault,
    encodeCanonicalPageFault, pageFaultCodecVersion, hvalid]

theorem canonical_page_fault_encoding_injective left right
    (h : encodeCanonicalPageFault left = encodeCanonicalPageFault right) :
    left = right := by
  simp [encodeCanonicalPageFault] at h
  cases left
  cases right
  simp_all

theorem canonical_exact_bit_binding record
    (hvalid : validCanonicalPageFault record = true) :
    ∃ decoded, decodePageFaultError record.errorWord = .ok decoded ∧
      record.accessCode = pageFaultAccessCode decoded.accessKind ∧
      record.protectionCode = (if decoded.protection then 1 else 0) ∧
      record.privilegeCode = (if decoded.user then 1 else 0) ∧
      record.faultPage = record.faultAddress / 4096 := by
  unfold validCanonicalPageFault at hvalid
  split at hvalid <;> simp_all

private def canonicalPageFaultRaw (record : CanonicalPageFault) : RawPageFault :=
  let frame :=
    if record.privilegeCode = 1 then
      .privilegeChange record.rip record.cs record.flags record.userRsp record.userSs
    else .samePrivilege record.rip record.cs record.flags
  { entry :=
      { boundVector := 14
        boundStub := 14
        errorCode := some record.errorWord
        restartClass := restartClassFor 14
        frame
        frameBytes := shapeBytes frame
        frameAddress := 0x800000
        acCleared := true
        dfCleared := true }
    faultAddress := record.faultAddress
    savedGprs := ⟨[]⟩
    diagnosticWords := [] }

private def canonicalPageFaultContext (record : CanonicalPageFault) : PageFaultContext :=
  { entry :=
      { currentSubject := record.currentSubject.toNat
        activeAddressSpace := record.activeAddressSpace.toNat
        activeCr3 := record.activeCr3
        stackIdentity := record.stackIdentity
        stackFirst := 0x800000
        stackPastLast := 0x804000
        entryActive := false }
    controls := pagingControlsOfCode record.controlsCode }

private def canonicalPageFaultSnapshot (record : CanonicalPageFault)
    (decoded : DecodedPageFaultError) : NormalizedPageFault :=
  { entry :=
      { vector := 14
        purpose := if decoded.user then .userFault else .diagnosticRecovery
        origin := if decoded.user then .user else .kernel
        errorCode := some record.errorWord
        rip := record.rip
        cs := record.cs
        flags := record.flags
        userRsp := if decoded.user then some record.userRsp else none
        userSs := if decoded.user then some record.userSs else none
        currentSubject := record.currentSubject.toNat
        activeAddressSpace := record.activeAddressSpace.toNat
        activeCr3 := record.activeCr3
        stackIdentity := record.stackIdentity }
    error := decoded
    accessKind := decoded.accessKind
    faultAddress := record.faultAddress
    faultPage := record.faultAddress / 4096
    controls := pagingControlsOfCode record.controlsCode }

private theorem find_page_fault_entry : findEntry 14 = some pageFaultEntry := by
  native_decide

/-- Every record admitted by the codec has a concrete accepted vector-14
normalizer preimage, and serializing that snapshot yields the same record. -/
theorem valid_canonical_page_fault_has_normalized_preimage record
    (hvalid : validCanonicalPageFault record = true) :
    ∃ snapshot,
      normalizePageFault (canonicalPageFaultRaw record)
          (canonicalPageFaultContext record) = .accepted snapshot ∧
        canonicalPageFaultRecord snapshot = record := by
  unfold validCanonicalPageFault at hvalid
  split at hvalid
  · simp_all
  · rename_i decoded hdecoded
    refine ⟨canonicalPageFaultSnapshot record decoded, ?_, ?_⟩
    · cases decoded with
      | mk protection write user instructionFetch =>
        cases user <;> cases record <;>
        simp_all [canonicalPageFaultRaw, canonicalPageFaultContext,
          canonicalPageFaultSnapshot, normalizePageFault, normalize,
          find_page_fault_entry, reviewed_manifest_valid, pageFaultEntry,
          makeNormalized, makeNormalizedPageFault, shapeBytes, purposeFor]
    · cases decoded with
      | mk protection write user instructionFetch =>
        cases user <;> cases record <;>
        simp_all [canonicalPageFaultSnapshot, canonicalPageFaultRecord,
          pagingControlsCode, pageFaultAccessCode,
          DecodedPageFaultError.accessKind]

theorem decoded_canonical_page_fault_has_normalized_preimage words record
    (hdecoded : decodeCanonicalPageFault words = some record) :
    ∃ snapshot,
      normalizePageFault (canonicalPageFaultRaw record)
          (canonicalPageFaultContext record) = .accepted snapshot ∧
        canonicalPageFaultRecord snapshot = record := by
  have hvalid : validCanonicalPageFault record = true := by
    unfold decodeCanonicalPageFault at hdecoded
    split at hdecoded <;> try contradiction
    split at hdecoded <;> try contradiction
    split at hdecoded <;> try contradiction
    injection hdecoded with hrecord
    subst record
    simp_all
  exact valid_canonical_page_fault_has_normalized_preimage record hvalid

def canonicalPageFaultExample : CanonicalPageFault :=
  { vector := 14
    errorWord := 4
    faultAddress := 0x400123
    faultPage := 0x400
    accessCode := 0
    protectionCode := 0
    privilegeCode := 1
    currentSubject := 1
    activeAddressSpace := 1
    activeCr3 := 0x1000
    controlsCode := 15
    rip := 0x400100
    cs := 0x23
    flags := 0x202
    userRsp := 0x500ff8
    userSs := 0x1b
    stackIdentity := 1
    reserved := 0 }

def canonicalPageFaultExampleContext : PageFaultContext :=
  { entry :=
      { currentSubject := 1
        activeAddressSpace := 1
        activeCr3 := 0x1000
        stackIdentity := 1
        stackFirst := 0x800000
        stackPastLast := 0x804000
        entryActive := false }
    controls :=
      { writeProtect := true
        nxEnable := true
        smep := true
        smap := true } }

theorem canonical_page_fault_codec_nonvacuous :
    validCanonicalPageFault canonicalPageFaultExample = true ∧
      decodeCanonicalPageFault (encodeCanonicalPageFault canonicalPageFaultExample) =
        some canonicalPageFaultExample := by
  native_decide

/-- The action boundary consumes the codec result only after reconstructing
the architectural snapshot under an independently supplied kernel context.
Serialized authority and paging-control words are therefore claims to check,
not inputs from which trusted context may be reconstructed.  Subject and
address-space identities must also fit one canonical codec word before any
fixed-width comparison is permitted. -/
structure CanonicalPageFaultAction (State : Type) where
  authorized : Option CanonicalPageFault
  state : State

/-- Exactly the `Nat` authority identities that can be compared to one
canonical codec word without truncation.  Zero remains rejected by the codec;
the all-ones word remains available, preserving the existing codec domain. -/
def AuthorityIdentityRepresentable (identity : Nat) : Prop :=
  identity < 2 ^ 64

instance (identity : Nat) : Decidable (AuthorityIdentityRepresentable identity) := by
  unfold AuthorityIdentityRepresentable
  infer_instance

def authorizeCanonicalPageFault (words : List UInt64)
    (trustedContext : PageFaultContext) (state : State) :
    CanonicalPageFaultAction State :=
  if AuthorityIdentityRepresentable trustedContext.entry.currentSubject ∧
      AuthorityIdentityRepresentable trustedContext.entry.activeAddressSpace then
    match decodeCanonicalPageFault words with
    | none => ⟨none, state⟩
    | some record =>
        match normalizePageFault (canonicalPageFaultRaw record) trustedContext with
        | .fatal _ => ⟨none, state⟩
        | .accepted snapshot =>
            if canonicalPageFaultRecord snapshot = record then
              ⟨some record, state⟩
            else
              ⟨none, state⟩
  else
    ⟨none, state⟩

theorem rejected_canonical_authorizes_nothing (State : Type) words
    (trustedContext : PageFaultContext) (state : State)
    (hrejected : decodeCanonicalPageFault words = none) :
    (authorizeCanonicalPageFault words trustedContext state).authorized = none ∧
      (authorizeCanonicalPageFault words trustedContext state).state = state := by
  simp [authorizeCanonicalPageFault, hrejected]

/-- Successful authorization certifies that both kernel-owned authority
identities fit the canonical codec word domain.  This premise prevents
`UInt64.ofNat` from becoming a truncating comparison. -/
theorem authorized_canonical_trusted_identities_representable
    (State : Type) words (trustedContext : PageFaultContext) (state : State) record
    (hauthorized :
      (authorizeCanonicalPageFault words trustedContext state).authorized =
        some record) :
    AuthorityIdentityRepresentable trustedContext.entry.currentSubject ∧
      AuthorityIdentityRepresentable trustedContext.entry.activeAddressSpace := by
  unfold authorizeCanonicalPageFault at hauthorized
  by_cases hrepresentable :
      AuthorityIdentityRepresentable trustedContext.entry.currentSubject ∧
        AuthorityIdentityRepresentable trustedContext.entry.activeAddressSpace
  · exact hrepresentable
  · simp [hrepresentable] at hauthorized

/-- Authorization supplies an accepted normalizer witness under the caller's
independent trusted context, not the context claimed by the encoded record. -/
theorem authorized_canonical_has_trusted_normalized_preimage
    (State : Type) words (trustedContext : PageFaultContext) (state : State) record
    (hauthorized :
      (authorizeCanonicalPageFault words trustedContext state).authorized =
        some record) :
    ∃ snapshot,
      normalizePageFault (canonicalPageFaultRaw record) trustedContext =
          .accepted snapshot ∧
        canonicalPageFaultRecord snapshot = record := by
  unfold authorizeCanonicalPageFault at hauthorized
  split at hauthorized
  · generalize hdecode : decodeCanonicalPageFault words = decoded at hauthorized
    cases decoded with
    | none => contradiction
    | some decodedRecord =>
        generalize haccepted :
          normalizePageFault (canonicalPageFaultRaw decodedRecord) trustedContext =
            result at hauthorized
        cases result with
        | fatal reason =>
            simp [haccepted] at hauthorized
        | accepted snapshot =>
            by_cases hrecord : canonicalPageFaultRecord snapshot = decodedRecord
            · simp [haccepted, hrecord] at hauthorized
              subst record
              exact ⟨snapshot, haccepted, hrecord⟩
            · simp [haccepted, hrecord] at hauthorized
  · simp_all

/-- Every authorized authority/control field equals the independently supplied
kernel context.  The representability certificate makes the subject and
address-space equalities exact in `Nat`, not merely equal after conversion to
a fixed-width word.  No serialized field is promoted to authority by itself. -/
theorem authorized_canonical_binds_trusted_context
    (State : Type) words (trustedContext : PageFaultContext) (state : State) record
    (hauthorized :
      (authorizeCanonicalPageFault words trustedContext state).authorized =
        some record) :
    AuthorityIdentityRepresentable trustedContext.entry.currentSubject ∧
      AuthorityIdentityRepresentable trustedContext.entry.activeAddressSpace ∧
      record.currentSubject.toNat = trustedContext.entry.currentSubject ∧
      record.activeAddressSpace.toNat =
        trustedContext.entry.activeAddressSpace ∧
      record.currentSubject = UInt64.ofNat trustedContext.entry.currentSubject ∧
      record.activeAddressSpace =
        UInt64.ofNat trustedContext.entry.activeAddressSpace ∧
      record.activeCr3 = trustedContext.entry.activeCr3 ∧
      record.controlsCode = pagingControlsCode trustedContext.controls := by
  obtain ⟨hsubjectRepresentable, hspaceRepresentable⟩ :=
    authorized_canonical_trusted_identities_representable
      State words trustedContext state record hauthorized
  obtain ⟨snapshot, haccepted, hrecord⟩ :=
    authorized_canonical_has_trusted_normalized_preimage
      State words trustedContext state record hauthorized
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hsubject, hspace, hcr3, hcontrols⟩ :=
    normalizePageFault_accepted_binding _ _ _ haccepted
  have hsubjectExact :
      (UInt64.ofNat trustedContext.entry.currentSubject).toNat =
        trustedContext.entry.currentSubject := by
    rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt hsubjectRepresentable]
  have hspaceExact :
      (UInt64.ofNat trustedContext.entry.activeAddressSpace).toNat =
        trustedContext.entry.activeAddressSpace := by
    rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt hspaceRepresentable]
  rw [← hrecord]
  simp [canonicalPageFaultRecord, hsubject, hspace, hcr3, hcontrols,
    hsubjectRepresentable, hspaceRepresentable, hsubjectExact, hspaceExact]

/-- Decoding and context comparison are pure authorization checks; neither an
accepted nor a rejected serialized record mutates containment state. -/
theorem canonical_page_fault_authorization_preserves_state
    (State : Type) words (trustedContext : PageFaultContext) (state : State) :
    (authorizeCanonicalPageFault words trustedContext state).state = state := by
  unfold authorizeCanonicalPageFault
  split <;> try rfl
  split <;> try rfl
  split <;> try rfl
  split <;> rfl

/-- Rejection at either the codec or trusted-context boundary cannot authorize
containment and cannot mutate the supplied state. -/
theorem unauthorized_canonical_cannot_mutate
    (State : Type) words (trustedContext : PageFaultContext) (state : State)
    (hunauthorized :
      (authorizeCanonicalPageFault words trustedContext state).authorized = none) :
    (authorizeCanonicalPageFault words trustedContext state).authorized = none ∧
      (authorizeCanonicalPageFault words trustedContext state).state = state := by
  constructor
  · exact hunauthorized
  · exact canonical_page_fault_authorization_preserves_state
      State words trustedContext state

theorem canonical_page_fault_authorization_nonvacuous :
    (authorizeCanonicalPageFault
      (encodeCanonicalPageFault canonicalPageFaultExample)
      canonicalPageFaultExampleContext ()).authorized =
        some canonicalPageFaultExample := by
  native_decide

/-- Each authority/control mutation is still codec-valid, but none is
authorized against the independently supplied example context. -/
theorem canonical_page_fault_forged_authority_rejected :
    let authorize := fun record =>
      (authorizeCanonicalPageFault (encodeCanonicalPageFault record)
        canonicalPageFaultExampleContext ()).authorized
    authorize { canonicalPageFaultExample with currentSubject := 2 } = none ∧
      authorize { canonicalPageFaultExample with activeAddressSpace := 2 } = none ∧
      authorize { canonicalPageFaultExample with activeCr3 := 0x2000 } = none ∧
      authorize { canonicalPageFaultExample with controlsCode := 14 } = none ∧
      authorize { canonicalPageFaultExample with controlsCode := 13 } = none ∧
      authorize { canonicalPageFaultExample with controlsCode := 11 } = none ∧
      authorize { canonicalPageFaultExample with controlsCode := 7 } = none := by
  native_decide

/-- Trusted authority identities outside the canonical word domain fail
closed instead of aliasing an encoded in-range identity modulo `2^64`. -/
theorem canonical_page_fault_unrepresentable_trusted_authority_rejected :
    let authorize := fun context =>
      (authorizeCanonicalPageFault
        (encodeCanonicalPageFault canonicalPageFaultExample) context ()).authorized
    authorize
        { canonicalPageFaultExampleContext with
          entry :=
            { canonicalPageFaultExampleContext.entry with
              currentSubject := 2 ^ 64 + 1 } } = none ∧
      authorize
        { canonicalPageFaultExampleContext with
          entry :=
            { canonicalPageFaultExampleContext.entry with
              activeAddressSpace := 2 ^ 64 + 1 } } = none := by
  native_decide

/-- The new bound preserves the complete prior `UInt64` codec domain,
including the all-ones subject and address-space identity word. -/
theorem canonical_page_fault_max_word_authority_preserved :
    let record :=
      { canonicalPageFaultExample with
        currentSubject := UInt64.ofNat (2 ^ 64 - 1)
        activeAddressSpace := UInt64.ofNat (2 ^ 64 - 1) }
    let context :=
      { canonicalPageFaultExampleContext with
        entry :=
          { canonicalPageFaultExampleContext.entry with
            currentSubject := 2 ^ 64 - 1
            activeAddressSpace := 2 ^ 64 - 1 } }
    (authorizeCanonicalPageFault
      (encodeCanonicalPageFault record) context ()).authorized = some record := by
  native_decide

def PageFaultRejectReason.code : PageFaultRejectReason → UInt64
  | .entry _ => 1
  | .wrongVector => 2 | .missingError => 3
  | .reservedBitViolation => 4 | .unsupportedErrorBits => 5
  | .privilegeMismatch => 6 | .noncanonicalAddress => 7

/-- Lower-half executable witness combining the architectural result with the
exact compact authority-context word and all four paging-control bits. -/
def pageFaultAuthorityMix (context controlsCode : UInt64) : UInt64 :=
  (context * 0x9e3779b185ebca87 +
    controlsCode * 0x100000001b3) % 0x8000000000000000

def pageFaultAcceptedWitness (faultPage : UInt64)
    (accessCode : UInt64) (protection user : Bool)
    (context controlsCode : UInt64) : UInt64 :=
  (faultPage * 32 + accessCode * 4 +
    (if protection then 2 else 0) + (if user then 1 else 0) +
    pageFaultAuthorityMix context controlsCode) % 0x8000000000000000

def compactPageFaultResult : PageFaultResult → UInt64
  | .fatal reason => 0x8000000000000000 + reason.code
  | .accepted snapshot =>
      let context := UInt64.ofNat snapshot.entry.currentSubject +
        UInt64.ofNat snapshot.entry.activeAddressSpace * 256 +
        snapshot.entry.activeCr3 * 65536
      pageFaultAcceptedWitness snapshot.faultPage
        (pageFaultAccessCode snapshot.accessKind)
        snapshot.error.protection snapshot.error.user context
        (pagingControlsCode snapshot.controls)

private def pageFaultDemoRaw (error address mode controls : UInt64) : RawPageFault :=
  let userShape := mode != 1
  let vector := if mode = 2 then 13 else 14
  let stub := if mode = 3 then 13 else vector
  let frame : RawFrame :=
    if userShape then .privilegeChange 0x400100 0x23 0x202 0x500ff8 0x1b
    else .samePrivilege 0x100000 0x08 0x202
  { entry :=
      { boundVector := vector
        boundStub := stub
        errorCode := if mode = 4 then none else some error
        restartClass := restartClassFor vector
        frame
        frameBytes := if mode = 5 then shapeBytes frame - 8 else shapeBytes frame
        frameAddress := 0x800000
        acCleared := controls % 2 = 1
        dfCleared := controls / 2 % 2 = 1 }
    faultAddress := address
    savedGprs := ⟨[0xdead, 0xbeef]⟩
    diagnosticWords := [address, error] }

private def pageFaultDemoContext (context controls : UInt64) : PageFaultContext :=
  { entry :=
      { currentSubject := (context % 256).toNat
        activeAddressSpace := (context / 256 % 256).toNat
        activeCr3 := context / 65536
        stackIdentity := 1
        stackFirst := 0x800000
        stackPastLast := 0x804000
        entryActive := controls / 4 % 2 = 1 }
    controls :=
      { writeProtect := controls / 8 % 2 = 1
        nxEnable := controls / 16 % 2 = 1
        smep := controls / 32 % 2 = 1
        smap := controls / 64 % 2 = 1 } }

/-- Five-word generated adapter for executable provenance vectors.  `mode`
selects only controlled entry-shape negatives; access kind always comes from
the architectural error word, and the fault page always comes from CR2. -/
def pageFaultModelExpected (error address mode context controls : UInt64) : UInt64 :=
  compactPageFaultResult
    (normalizePageFault (pageFaultDemoRaw error address mode controls)
      (pageFaultDemoContext context controls))

/-- Allocation-free spelling used by generated C.  The ordered rejection
codes mirror `normalizePageFault`; its accepted witness includes the exact
authority context and paging controls.  Finite pointwise agreement with the
rich model is checked by `Oracle.page_fault_adapter_agrees_with_model`. -/
def pageFaultDemo (error address mode context controls : UInt64) : UInt64 :=
  let acCleared := controls % 2 = 1
  let dfCleared := controls / 2 % 2 = 1
  let nested := controls / 4 % 2 = 1
  let originUser := mode != 1
  let errorUser := error / 4 % 2 = 1
  let accessCode := if error / 16 % 2 = 1 then 2
    else if error / 2 % 2 = 1 then 1 else 0
  if !acCleared || !dfCleared || nested || mode = 3 || mode = 4 || mode = 5 then
    0x8000000000000001
  else if mode = 2 then 0x8000000000000002
  else if error / 32 != 0 then 0x8000000000000005
  else if error / 8 % 2 = 1 then 0x8000000000000004
  else if originUser != errorUser then 0x8000000000000006
  else if !canonicalLinearAddress address then 0x8000000000000007
  else pageFaultAcceptedWitness (address / 4096) accessCode
    (error % 2 = 1) errorUser context (controls / 8 % 16)

theorem pageFaultDemo_total error address mode context controls :
    ∃ result, pageFaultDemo error address mode context controls = result := ⟨_, rfl⟩

@[export leanos_page_fault_demo]
def pageFaultDemoExport (error address mode context controls : UInt64) : UInt64 :=
  pageFaultDemo error address mode context controls

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
/-- Canonical coordinates in the normalized model snapshot.  These are not
linker virtual addresses; the machine policy separately validates its live
`__nmi_ist_stack_start`/`end` symbols before constructing a snapshot. -/
def nmiAbstractStackFirst : UInt64 := 0x900000
def nmiAbstractStackPastLast : UInt64 := 0x904000

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
  | staleKernelContext | invalidBoundsEncoding | invalidModeEncoding
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
  else if raw.frameAddress % 16 != 8 then some .misaligned
  else if context.stackIdentity != nmiStackIdentity then some .wrongStackIdentity
  else if context.stackFirst != nmiAbstractStackFirst ||
      context.stackPastLast != nmiAbstractStackPastLast ||
      raw.frameAddress < context.stackFirst ||
      raw.frameAddress + raw.frameBytes < raw.frameAddress ||
      raw.frameAddress + raw.frameBytes != context.stackPastLast then
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
  | .invalidBoundsEncoding => 14 | .invalidModeEncoding => 15

/-- Rejections selectable through the fixed-width generated boundary.  The
compile-time-only `invalidManifest` constructor is excluded deliberately and
is exercised by a separate negative proof fixture. -/
def NmiRejectReason.runtimeInventory : List NmiRejectReason :=
  [.wrongDescriptor, .wrongTarget, .spuriousError, .wrongFrameBytes,
    .misaligned, .wrongStackIdentity, .stackOutOfBounds, .wrongOrigin,
    .wrongSelectors, .noncanonical, .privilegedStateNotCleared,
    .staleKernelContext, .invalidBoundsEncoding, .invalidModeEncoding]

theorem nmi_runtime_rejection_inventory_codes :
    NmiRejectReason.runtimeInventory.map NmiRejectReason.code =
      [2, 3, 4, 5, 6, 8, 7, 9, 10, 11, 12, 13, 14, 15] := by
  native_decide

/-- Named executable-trace inventory required by the terminal policy.  These
classes are discharged by the concrete witnesses plus the generic atomicity
and absorption theorems in `SecurityClaims`/`FailStop`; keeping the inventory
as data makes accidental trace removal visible to a negative fixture. -/
inductive NmiTraceClass where
  | cpl3Running | cpl0Running | syscallHandling | pageFaultHandling
  | timerHandling | copyOverrideArmed | repeatedNmi | afterDoubleFault
  | operationSuffix | returnSuffix
  deriving DecidableEq, Repr

def nmiTraceInventory : List NmiTraceClass :=
  [.cpl3Running, .cpl0Running, .syscallHandling, .pageFaultHandling,
    .timerHandling, .copyOverrideArmed, .repeatedNmi, .afterDoubleFault,
    .operationSuffix, .returnSuffix]

theorem nmi_trace_inventory_exact :
    nmiTraceInventory =
      [.cpl3Running, .cpl0Running, .syscallHandling, .pageFaultHandling,
        .timerHandling, .copyOverrideArmed, .repeatedNmi, .afterDoubleFault,
        .operationSuffix, .returnSuffix] := by
  rfl

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

/-! The canonical scalar corpus below is deliberately a projection of the
17-word result, not a replacement for it.  Its high-bit fatal tag preserves
the exact rejection code while the accepted word binds the origin,
interrupted mode, subject, and address-space fields. -/

private def compactNmiResult : NmiResult → UInt64
  | .fatal reason => 0x8000000000000000 + reason.code
  | .accepted event =>
      1 + (if event.origin = .user then 1 else 0) * 0x100 +
        event.interruptedMode.code * 0x10000 +
        UInt64.ofNat event.currentSubject * 0x1000000 +
        UInt64.ofNat event.activeAddressSpace * 0x100000000

private def nmiDescriptorOf (code : UInt64) : ManifestEntry :=
  if code = 0 then nmiEntry else { nmiEntry with vector := 3 }

private def nmiInterruptedModeOf (code : UInt64) : InterruptedMode :=
  if code = 0 then .running else if code = 1 then .handling else .halted

private def nmiContextStackFirst (boundsCode : UInt64) : UInt64 :=
  if boundsCode = 1 then nmiAbstractStackFirst + 16 else nmiAbstractStackFirst

private def nmiContextStackPastLast (boundsCode : UInt64) : UInt64 :=
  if boundsCode = 2 then nmiAbstractStackPastLast - 16 else nmiAbstractStackPastLast

/-- Rich-model expectation for the bounded generated-C NMI classifier.  The
five scalar words encode a descriptor selector, the five-word frame metadata,
the IST2 frame address, trusted context identities, and validation controls.
The raw RIP/RSP/flags/CR3 payload is fixed because the corpus tests the entry
contract rather than attacker-selected register serialization. -/
def nmiModelExpected (descriptor frame stack context control : UInt64) : UInt64 :=
  let cs := frame % 256
  let ss := frame / 256 % 256
  let raw : RawNmiEntry :=
    { descriptor := nmiDescriptorOf descriptor
      boundStub := control % 256
      errorCode := if control / 256 % 2 = 1 then some 0 else none
      frame :=
        { rip := 0x400100, cs, flags := 0x202, rsp := 0x500ff8, ss
          canonicalRip := frame / 65536 % 2 = 1
          canonicalRsp := frame / 131072 % 2 = 1 }
      claimedOrigin := if frame / 262144 % 2 = 1 then .user else .kernel
      frameBytes := control / 512 % 256
      frameAddress := stack
      acCleared := control / 131072 % 2 = 1
      dfCleared := control / 262144 % 2 = 1 }
  let boundsCode := context / 0x1000000 % 4
  let modeCode := context / 0x4000000 % 4
  let ctx : NmiContext :=
    { currentSubject := (context % 256).toNat
      activeAddressSpace := (context / 256 % 256).toNat
      activeCr3 := 0x1000
      stackIdentity := context / 65536 % 256
      stackFirst := nmiContextStackFirst boundsCode
      stackPastLast := nmiContextStackPastLast boundsCode
      interruptedMode := nmiInterruptedModeOf modeCode }
  if boundsCode = 3 then compactNmiResult (.fatal .invalidBoundsEncoding)
  else if modeCode = 3 then compactNmiResult (.fatal .invalidModeEncoding)
  else compactNmiResult (normalizeNmi raw ctx
    (control / 0x80000 % 256).toNat (control / 0x8000000 % 256).toNat)

/-- Allocation-free spelling of the bounded NMI classifier used by generated
C.  It mirrors the ordered rich normalizer and returns the compact corpus word
defined above; it does not model x86 delivery or install an IST2 handler. -/
def nmiDemo (descriptor frame stack context control : UInt64) : UInt64 :=
  let cs := frame % 256
  let ss := frame / 256 % 256
  let canonicalRip := frame / 65536 % 2 = 1
  let canonicalRsp := frame / 131072 % 2 = 1
  let claimedUser := frame / 262144 % 2 = 1
  let frameUser := cs % 4 = 3
  let stub := control % 256
  let hasError := control / 256 % 2 = 1
  let frameBytes := control / 512 % 256
  let acCleared := control / 131072 % 2 = 1
  let dfCleared := control / 262144 % 2 = 1
  let subject := context % 256
  let addressSpace := context / 256 % 256
  let stackIdentity := context / 65536 % 256
  let boundsCode := context / 0x1000000 % 4
  let stackFirst := nmiContextStackFirst boundsCode
  let stackPastLast := nmiContextStackPastLast boundsCode
  let modeCode := context / 0x4000000 % 4
  let mode := if modeCode = 0 then 0 else if modeCode = 1 then 1 else 2
  let expectedSubject := control / 0x80000 % 256
  let expectedAddressSpace := control / 0x8000000 % 256
  if boundsCode = 3 then 0x800000000000000e
  else if modeCode = 3 then 0x800000000000000f
  else if descriptor != 0 then 0x8000000000000002
  else if stub != nmiVector then
    0x8000000000000003
  else if hasError then 0x8000000000000004
  else if frameBytes != 40 then
    0x8000000000000005
  else if stack % 16 != 8 then 0x8000000000000006
  else if stackIdentity != nmiStackIdentity then
    0x8000000000000008
  else if stackFirst != nmiAbstractStackFirst ||
      stackPastLast != nmiAbstractStackPastLast ||
      stack < stackFirst || stack + frameBytes < stack || stack + frameBytes != stackPastLast then
    0x8000000000000007
  else if frameUser != claimedUser then
    0x8000000000000009
  else if (claimedUser && (cs != 0x23 || ss != 0x1b)) ||
      (!claimedUser && (cs != 0x08 || ss != 0x10)) then 0x800000000000000a
  else if !canonicalRip || !canonicalRsp then
    0x800000000000000b
  else if !acCleared || !dfCleared then
    0x800000000000000c
  else if subject != expectedSubject || addressSpace != expectedAddressSpace then
    0x800000000000000d
  else
    1 + (if claimedUser then 1 else 0) * 0x100 + mode * 0x10000 +
      subject * 0x1000000 + addressSpace * 0x100000000

theorem nmiDemo_total descriptor frame stack context control :
    ∃ result, nmiDemo descriptor frame stack context control = result := by
  exact ⟨_, rfl⟩

@[export leanos_nmi_demo]
def nmiDemoExport (descriptor frame stack context control : UInt64) : UInt64 :=
  nmiDemo descriptor frame stack context control

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
      restartClass := if frame / 1024 % 2 = 1 then (restartClassFor vector).other
        else restartClassFor vector
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
  let restartFlipped := frame / 1024 % 2 = 1
  let descriptorAllowed :=
    stub = vector &&
      ((vector = 0 && !hasError) ||
       (vector = 3 && !hasError) ||
       ((vector = 6 || vector = 7) && !hasError) ||
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
  if descriptorAllowed && originAllowed && !truncated && !restartFlipped && stackAllowed &&
      cleanup = 3 then
    1 + vector * 256 + (if userShape then 1 else 2) * 65536 +
      (context % 256) * 0x1000000 + (context / 256 % 256) * 0x100000000
  else 0

theorem entryDemo_total descriptor frame stack context cleanup :
    ∃ result, entryDemo descriptor frame stack context cleanup = result := by
  exact ⟨_, rfl⟩

@[export leanos_entry_demo]
def entryDemoExport (descriptor frame stack context cleanup : UInt64) : UInt64 :=
  entryDemo descriptor frame stack context cleanup

/-! ## Boot-interrupt phase scalar adapter

Allocation-free spelling of the finite boot-interrupt phase classifier defined
by `LeanOS.BootInterruptPhase`.  The five words encode the current phase, one
publication or event operation, its detail word, the prior terminal-latch
selector, and an opaque business token that must round-trip unchanged.  The
corpus proves pointwise agreement with `bootPhaseModelExpected`; this adapter
does not model descriptor loads, x86 delivery, or the final binary. -/

def bootPhaseDemo (phase operation detail latchWord business : UInt64) : UInt64 :=
  if phase > 4 then 0x8000000000000021
  else if operation = 0 || operation > 4 then 0x8000000000000022
  else if latchWord > 1 then 0x8000000000000023
  else
    let businessWord := business % 256 * 0x10000
    if latchWord = 1 then 3 + businessWord
    else
      let latched := fun (recordPhase vector errorBit userBit reason : UInt64) =>
        2 + recordPhase * 0x100 + businessWord + vector % 256 * 0x1000000 +
          errorBit * 0x100000000 + userBit * 0x200000000 + reason * 0x400000000
      if operation = 1 then
        if phase = 0 then 1 + 0x100 + businessWord
        else latched phase 0 0 0 3
      else if operation = 2 then
        if phase = 1 then 1 + 2 * 0x100 + businessWord
        else latched phase 0 0 0 4
      else if operation = 3 then
        if phase = 2 then
          if detail % 2 = 1 && detail / 2 % 2 = 1 && detail / 4 % 2 = 1 then
            1 + 3 * 0x100 + businessWord
          else latched 2 0 0 0 6
        else latched phase 0 0 0 5
      else
        let vector := detail % 256
        let errorBit := detail / 256 % 2
        let userBit := detail / 512 % 2
        if phase = 3 then 4 + businessWord + vector * 0x1000000
        else if phase = 0 then latched 0 vector errorBit userBit 1
        else latched phase vector errorBit userBit 0

theorem bootPhaseDemo_total phase operation detail latchWord business :
    ∃ result, bootPhaseDemo phase operation detail latchWord business = result := by
  exact ⟨_, rfl⟩

@[export leanos_boot_phase_demo]
def bootPhaseDemoExport (phase operation detail latchWord business : UInt64) : UInt64 :=
  bootPhaseDemo phase operation detail latchWord business

end LeanOS.InterruptEntry
