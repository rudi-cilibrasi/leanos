import LeanOS.IOMMU

/-!
# Deterministic VT-d boot plan

Bounded, executable plan for the pinned q35 `intel-iommu` unit: the exact
root/context tables installed before translation enable, derived from the
accepted static device-domain model.  This proves facts about accepted plan
values and their agreement with `IOMMU.validateCore`-accepted states.  DMAR
firmware bytes, PCIe requester identifiers, VT-d MMIO and table-walk
semantics, QEMU's remapping implementation, generated C, boot assembly, and
the final binary remain trusted integration boundaries, not theorems.
-/
namespace LeanOS.VTdBootPlan

set_option maxRecDepth 8000

open LeanOS
open LeanOS.X86PageTable (pageBytes physicalFrameLimit)

/-! ## Pinned unit configuration

The register values are the reviewed QEMU 8.2.2 `intel-iommu` configuration
(`intremap=off,pt=off,caching-mode=off,device-iotlb=off,aw-bits=39,
dma-translation=on,snoop-control=off`).  Passthrough, caching mode, and device
IOTLB support are visibly absent from the pinned capability words, so option
drift is observable in hardware state rather than only in the command line. -/

def planVersion : UInt64 := 1
/-- QEMU q35 `intel-iommu` register block base (`Q35_HOST_BRIDGE_IOMMU_ADDR`). -/
def mmioBase : Nat := 0xFED9_0000
def mmioFrame : Nat := mmioBase / pageBytes
/-- VT-d architecture version 1.0. -/
def expectedVersionRegister : UInt64 := 0x10
/-- CAP: CM clear (bit 7), SAGAW three-level only (bits 12:8 = 0b00010),
MGAW 39, register-based invalidation fault recording at 0x220. -/
def expectedCapabilityRegister : UInt64 := 0x00d2008c22260206
/-- ECAP: queued invalidation supported, IOTLB registers at 0x0F0,
pass-through (bit 6) and device-IOTLB (bit 2) clear. -/
def expectedExtendedCapabilityRegister : UInt64 := 0x0f02
/-- Global status after fail-closed activation: exactly TES (bit 31) and
RTPS (bit 30); queued invalidation and interrupt remapping stay disabled. -/
def enabledGlobalStatus : UInt64 := 0xC000_0000
def rootEntryCount : Nat := 256
def contextEntryCount : Nat := 256
/-- Context-entry AW encoding for the 39-bit three-level subset. -/
def addressWidthEncoding : Nat := 1
def domainLimit : Nat := 2 ^ 16

theorem physicalFrameLimit_value : physicalFrameLimit = 1099511627776 := by native_decide
theorem domainLimit_value : domainLimit = 65536 := by native_decide

/-! ## Canonical entry codec

Each table entry occupies two 64-bit words.  The supported subset keeps every
architecturally reserved bit zero, so acceptance is exactly the image of the
encoder: every decoded word pair is re-encodable to the same words. -/

structure RootEntry where
  present : Bool
  contextTableFrame : Nat
  deriving BEq, DecidableEq, Repr

structure ContextEntry where
  present : Bool
  domain : Nat
  addressWidth : Nat
  secondLevelFrame : Nat
  deriving BEq, DecidableEq, Repr

def absentRootEntry : RootEntry := { present := false, contextTableFrame := 0 }
def absentContextEntry : ContextEntry :=
  { present := false, domain := 0, addressWidth := 0, secondLevelFrame := 0 }

def RootEntryEncodable (entry : RootEntry) : Prop :=
  if entry.present then
    0 < entry.contextTableFrame ∧ entry.contextTableFrame < physicalFrameLimit
  else entry = absentRootEntry

instance (entry : RootEntry) : Decidable (RootEntryEncodable entry) := by
  unfold RootEntryEncodable
  infer_instance

def ContextEntryEncodable (entry : ContextEntry) : Prop :=
  if entry.present then
    0 < entry.secondLevelFrame ∧ entry.secondLevelFrame < physicalFrameLimit ∧
      entry.addressWidth = addressWidthEncoding ∧ entry.domain < domainLimit
  else entry = absentContextEntry

instance (entry : ContextEntry) : Decidable (ContextEntryEncodable entry) := by
  unfold ContextEntryEncodable
  infer_instance

/-- Low word: present bit plus the 4 KiB-aligned context-table pointer.  The
high word of a root entry is architecturally reserved and stays zero. -/
def rootEntryLow (entry : RootEntry) : Nat :=
  if entry.present then entry.contextTableFrame * pageBytes + 1 else 0

/-- Low word: present bit, translation type 00 (untranslated requests use the
second-level tables), and the aligned second-level pointer. -/
def contextEntryLow (entry : ContextEntry) : Nat :=
  if entry.present then entry.secondLevelFrame * pageBytes + 1 else 0

/-- High word: domain identifier (bits 8+) and address width (bits 2:0). -/
def contextEntryHigh (entry : ContextEntry) : Nat :=
  if entry.present then entry.domain * 256 + entry.addressWidth else 0

inductive EntryError where
  | upperWord | reservedBits | nullPointer | frameOutOfRange
  | wrongAddressWidth | domainOutOfRange
  deriving BEq, DecidableEq, Repr

/-- Total root-entry decoder; every rejected word pair names a reason. -/
def decodeRootEntry (low high : Nat) : Except EntryError RootEntry :=
  if high ≠ 0 then .error .upperWord
  else if low = 0 then .ok absentRootEntry
  else if low % pageBytes ≠ 1 then .error .reservedBits
  else if low / pageBytes = 0 then .error .nullPointer
  else if physicalFrameLimit ≤ low / pageBytes then .error .frameOutOfRange
  else .ok { present := true, contextTableFrame := low / pageBytes }

/-- Total context-entry decoder for the pinned three-level subset. -/
def decodeContextEntry (low high : Nat) : Except EntryError ContextEntry :=
  if low = 0 then
    if high ≠ 0 then .error .upperWord else .ok absentContextEntry
  else if low % pageBytes ≠ 1 then .error .reservedBits
  else if low / pageBytes = 0 then .error .nullPointer
  else if physicalFrameLimit ≤ low / pageBytes then .error .frameOutOfRange
  else if high % 256 ≠ addressWidthEncoding then .error .wrongAddressWidth
  else if domainLimit ≤ high / 256 then .error .domainOutOfRange
  else .ok { present := true, domain := high / 256, addressWidth := high % 256,
             secondLevelFrame := low / pageBytes }

/-- Encoding a bounded root entry and decoding its words is exact. -/
theorem decode_encode_root (entry : RootEntry) (h : RootEntryEncodable entry) :
    decodeRootEntry (rootEntryLow entry) 0 = .ok entry := by
  have hpage : pageBytes = 4096 := rfl
  obtain ⟨present, frame⟩ := entry
  unfold RootEntryEncodable at h
  split at h
  next hpresent =>
    have hpt : present = true := hpresent
    subst hpt
    obtain ⟨hpos, hlimit⟩ := h
    have hpos' : 0 < frame := hpos
    have hlimit' : frame < physicalFrameLimit := hlimit
    have hlow : rootEntryLow ⟨true, frame⟩ = frame * 4096 + 1 := by simp [rootEntryLow, hpage]
    have hmod : (frame * 4096 + 1) % 4096 = 1 := by omega
    have hdiv : (frame * 4096 + 1) / 4096 = frame := by omega
    simp only [decodeRootEntry, hlow, hpage, hmod, hdiv]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega)]
  next hpresent =>
    have hpf : present = false := by
      cases present with
      | true => exact absurd rfl hpresent
      | false => rfl
    subst hpf
    simp only [absentRootEntry, RootEntry.mk.injEq] at h
    obtain ⟨_, hframe⟩ := h
    subst hframe
    simp [rootEntryLow, decodeRootEntry, absentRootEntry]

/-- Every accepted root-entry word pair is the canonical encoding of the
decoded entry, so acceptance is exactly the image of the encoder. -/
theorem encode_decode_root (low high : Nat) (entry : RootEntry)
    (h : decodeRootEntry low high = .ok entry) :
    RootEntryEncodable entry ∧ rootEntryLow entry = low ∧ high = 0 := by
  have hpage : pageBytes = 4096 := rfl
  simp only [decodeRootEntry, hpage] at h
  split at h
  · contradiction
  next hhigh =>
    split at h
    next hzero =>
      injection h with hentry
      subst hentry
      refine ⟨by simp [RootEntryEncodable, absentRootEntry], ?_, by omega⟩
      have h0 : rootEntryLow absentRootEntry = 0 := rfl
      rw [h0]; omega
    next hzero =>
      split at h
      · contradiction
      next hmod =>
        split at h
        · contradiction
        next hdivzero =>
          split at h
          · contradiction
          next hlimit =>
            injection h with hentry
            subst hentry
            refine ⟨?_, ?_, by omega⟩
            · show 0 < low / 4096 ∧ low / 4096 < physicalFrameLimit
              exact ⟨by omega, by omega⟩
            · show low / 4096 * 4096 + 1 = low
              omega

/-- One accepted root-entry word cannot encode two entries. -/
theorem root_entry_encoding_injective (first second : RootEntry)
    (hfirst : RootEntryEncodable first) (hsecond : RootEntryEncodable second)
    (h : rootEntryLow first = rootEntryLow second) : first = second := by
  have dfirst := decode_encode_root first hfirst
  have dsecond := decode_encode_root second hsecond
  rw [h] at dfirst
  rw [dfirst] at dsecond
  exact Except.ok.inj dsecond

/-- Encoding a bounded context entry and decoding its words is exact. -/
theorem decode_encode_context (entry : ContextEntry) (h : ContextEntryEncodable entry) :
    decodeContextEntry (contextEntryLow entry) (contextEntryHigh entry) = .ok entry := by
  have hpage : pageBytes = 4096 := rfl
  have hwidthValue : addressWidthEncoding = 1 := rfl
  obtain ⟨present, domain, width, frame⟩ := entry
  unfold ContextEntryEncodable at h
  split at h
  next hpresent =>
    have hpt : present = true := hpresent
    subst hpt
    obtain ⟨hpos, hlimit, hwidth, hdomain⟩ := h
    dsimp only at hpos hlimit hwidth hdomain
    subst hwidth
    rw [physicalFrameLimit_value] at hlimit
    rw [domainLimit_value] at hdomain
    have hlow : contextEntryLow ⟨true, domain, addressWidthEncoding, frame⟩ =
        frame * 4096 + 1 := by simp [contextEntryLow, hpage]
    have hhigh : contextEntryHigh ⟨true, domain, addressWidthEncoding, frame⟩ =
        domain * 256 + 1 := by simp [contextEntryHigh, hwidthValue]
    rw [hlow, hhigh]
    simp only [decodeContextEntry, hpage, hwidthValue, physicalFrameLimit_value,
      domainLimit_value]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega), if_neg (by omega)]
    refine congrArg Except.ok ?_
    congr 1 <;> omega
  next hpresent =>
    have hpf : present = false := by
      cases present with
      | true => exact absurd rfl hpresent
      | false => rfl
    subst hpf
    simp only [absentContextEntry, ContextEntry.mk.injEq, true_and] at h
    obtain ⟨hdomain, hwidth, hframe⟩ := h
    subst hdomain; subst hwidth; subst hframe
    simp [contextEntryLow, contextEntryHigh, decodeContextEntry, absentContextEntry]

/-- Every accepted context-entry word pair is the canonical encoding of the
decoded entry. -/
theorem encode_decode_context (low high : Nat) (entry : ContextEntry)
    (h : decodeContextEntry low high = .ok entry) :
    ContextEntryEncodable entry ∧ contextEntryLow entry = low ∧
      contextEntryHigh entry = high := by
  have hpage : pageBytes = 4096 := rfl
  have hwidthValue : addressWidthEncoding = 1 := rfl
  simp only [decodeContextEntry, hpage, hwidthValue] at h
  split at h
  next hzero =>
    split at h
    · contradiction
    next hhigh =>
      injection h with hentry
      subst hentry
      have hhigh' : high = 0 := by simpa using hhigh
      refine ⟨by simp [ContextEntryEncodable, absentContextEntry], ?_, ?_⟩
      · simp [contextEntryLow, absentContextEntry, hzero]
      · simp [contextEntryHigh, absentContextEntry, hhigh']
  next hzero =>
    split at h
    · contradiction
    next hmod =>
      split at h
      · contradiction
      next hdivzero =>
        split at h
        · contradiction
        next hlimit =>
          split at h
          · contradiction
          next hwidth =>
            split at h
            · contradiction
            next hdomain =>
              injection h with hentry
              subst hentry
              refine ⟨?_, ?_, ?_⟩
              · show 0 < low / 4096 ∧ low / 4096 < physicalFrameLimit ∧
                    high % 256 = addressWidthEncoding ∧ high / 256 < domainLimit
                exact ⟨by omega, by omega, by omega, by omega⟩
              · show low / 4096 * 4096 + 1 = low
                omega
              · show high / 256 * 256 + high % 256 = high
                omega

/-- One accepted context-entry word pair cannot encode two entries. -/
theorem context_entry_encoding_injective (first second : ContextEntry)
    (hfirst : ContextEntryEncodable first) (hsecond : ContextEntryEncodable second)
    (hlow : contextEntryLow first = contextEntryLow second)
    (hhigh : contextEntryHigh first = contextEntryHigh second) : first = second := by
  have dfirst := decode_encode_context first hfirst
  have dsecond := decode_encode_context second hsecond
  rw [hlow, hhigh] at dfirst
  rw [dfirst] at dsecond
  exact Except.ok.inj dsecond

/-! ## Plan compilation

`compile` is the only constructor.  The v1 subset installs the deny-all boot
tables: one present root entry for bus 0 selecting the reserved context table,
and 256 absent context entries, exactly the projection of an accepted static
device-domain state with no live assignments.  Assigned-device projections are
deliberately rejected until the assigned-EDU issue reviews them. -/

structure Input where
  /-- Accepted static device-domain state (`IOMMU.validateCore` carried). -/
  state : IOMMU.State
  rootTableFrame : Nat
  contextTableFrame : Nat
  /-- CPU page-table constructor frames accepted by the boot page-table plan,
  supplied by the same generator run over the same linked layout. -/
  cpuTableFrames : List Nat
  /-- The remapping-table reservation is accepted only as part of the
  validated boot-memory manifest overlay, exactly like CPU page tables. -/
  reservationResult : Option BootReservation.Result

inductive Error where
  | missingValidatedReservation | unreservedTableFrame | duplicateTableFrame
  | tableAliasesCpuTables | frameOutOfRange | assignmentsNotSupported
  | mappingsNotSupported
  deriving BEq, DecidableEq, Repr

def reservedFrame (input : Input) (frame : Nat) : Bool :=
  match input.reservationResult with
  | none => false
  | some reserved => BootReservation.reservedBy reserved.intervals frame

/-- Exactly one present root entry: bus 0 selects the reserved context table. -/
def canonicalRootEntries (contextTableFrame : Nat) : List RootEntry :=
  (List.range rootEntryCount).map fun bus =>
    if bus == 0 then { present := true, contextTableFrame } else absentRootEntry

/-- The deny-all boot projection: every requester decodes to an absent entry. -/
def canonicalContextEntries : List ContextEntry :=
  List.replicate contextEntryCount absentContextEntry

structure Plan where
  private mk ::
  private rootTable : Nat
  private contextTable : Nat
  private roots : List RootEntry
  private contexts : List ContextEntry
  private modelAssignments : List IOMMU.Assignment
  private modelMappings : List IOMMU.Mapping
  private denyAllAssignments : modelAssignments = []
  private denyAllMappings : modelMappings = []
  private rootsCanonical : roots = canonicalRootEntries contextTable
  private contextsCanonical : contexts = canonicalContextEntries
  private tablesDistinct : rootTable ≠ contextTable
  private tablesBounded : 0 < rootTable ∧ rootTable < physicalFrameLimit ∧
    0 < contextTable ∧ contextTable < physicalFrameLimit
  private reservationChecked : Bool
  private reservationEvidence : reservationChecked = true
  private cpuDisjoint : Bool
  private cpuDisjointEvidence : cpuDisjoint = true

def Plan.rootFrame (plan : Plan) : Nat := plan.rootTable
def Plan.contextFrame (plan : Plan) : Nat := plan.contextTable

/-- Total compiler/checker for the deliberately finite supported subset. -/
def compile (input : Input) : Except Error Plan :=
  if input.reservationResult.isNone then .error .missingValidatedReservation
  else match hassign : input.state.core.assignments with
  | _ :: _ => .error .assignmentsNotSupported
  | [] => match hmap : input.state.core.mappings with
    | _ :: _ => .error .mappingsNotSupported
    | [] =>
      if hdup : input.rootTableFrame = input.contextTableFrame then
        .error .duplicateTableFrame
      else if hcpu : input.cpuTableFrames.contains input.rootTableFrame ||
          input.cpuTableFrames.contains input.contextTableFrame then
        .error .tableAliasesCpuTables
      else if hbound : 0 < input.rootTableFrame ∧
          input.rootTableFrame < physicalFrameLimit ∧
          0 < input.contextTableFrame ∧ input.contextTableFrame < physicalFrameLimit then
        if hreserved : reservedFrame input input.rootTableFrame &&
            reservedFrame input input.contextTableFrame then
          .ok ⟨input.rootTableFrame, input.contextTableFrame,
            canonicalRootEntries input.contextTableFrame, canonicalContextEntries,
            input.state.core.assignments, input.state.core.mappings,
            hassign, hmap, rfl, rfl, hdup, hbound,
            reservedFrame input input.rootTableFrame &&
              reservedFrame input input.contextTableFrame, hreserved,
            !(input.cpuTableFrames.contains input.rootTableFrame ||
              input.cpuTableFrames.contains input.contextTableFrame),
            by simpa using hcpu⟩
        else .error .unreservedTableFrame
      else .error .frameOutOfRange

theorem compile_deterministic input first second
    (hfirst : compile input = first) (hsecond : compile input = second) : first = second := by
  rw [hfirst] at hsecond
  exact hsecond

/-! ## Agreement with the accepted static domain projection -/

/-- Accepted plans carry the deny-all model projection: the accepted static
state authorizes no assignment, so no context entry may be present. -/
theorem accepted_context_entries_absent input plan (_h : compile input = .ok plan) :
    plan.contexts = List.replicate contextEntryCount absentContextEntry :=
  plan.contextsCanonical

/-- Each requester decodes through exactly one context slot: the table has
exactly `contextEntryCount` entries, indexed by device/function number. -/
theorem accepted_requesters_bound_once input plan (_h : compile input = .ok plan) :
    plan.contexts.length = contextEntryCount := by
  rw [plan.contextsCanonical]
  simp [canonicalContextEntries]

/-- No physical frame is reachable through an accepted deny-all plan: there
are no present context entries, hence no second-level tables at all. -/
theorem accepted_maps_no_frame input plan (_h : compile input = .ok plan) :
    (plan.contexts.filter (·.present)).map (·.secondLevelFrame) = [] := by
  rw [plan.contextsCanonical]
  simp [canonicalContextEntries, absentContextEntry]

/-- Bus 0 selects exactly the reserved context table; every other root entry
is absent. -/
theorem accepted_root_shape input plan (_h : compile input = .ok plan) :
    plan.roots = canonicalRootEntries plan.contextFrame :=
  plan.rootsCanonical

theorem accepted_tables_distinct input plan (_h : compile input = .ok plan) :
    plan.rootFrame ≠ plan.contextFrame := plan.tablesDistinct

theorem accepted_reservation_checked input plan (_h : compile input = .ok plan) :
    plan.reservationChecked = true := plan.reservationEvidence

theorem accepted_cpu_tables_disjoint input plan (_h : compile input = .ok plan) :
    plan.cpuDisjoint = true := plan.cpuDisjointEvidence

/-- Acceptance requires the model state itself to be deny-all. -/
theorem accepted_state_deny_all input plan (h : compile input = .ok plan) :
    input.state.core.assignments = [] ∧ input.state.core.mappings = [] := by
  unfold compile at h
  split at h
  · contradiction
  · split at h
    · contradiction
    next hassign =>
      split at h
      · contradiction
      next hmap => exact ⟨hassign, hmap⟩

/-- The accepted plan agrees with the model's authority lookup: no source and
generation resolves to a live assignment in the accepted state. -/
theorem accepted_agrees_with_domain_projection input plan (h : compile input = .ok plan)
    (source : IOMMU.SourceId) (generation : IOMMU.Generation) :
    IOMMU.findAssignmentBySource input.state.core source generation = none := by
  have hdeny := (accepted_state_deny_all input plan h).1
  simp [IOMMU.findAssignmentBySource, hdeny]

/-! ## Word-level table projection

The generator emits these words; the guest constructs the in-memory tables
from them and re-compares after activation.  The interleaved low/high order is
exactly the 128-bit little-endian entry layout VT-d hardware walks. -/

def rootTableWords (plan : Plan) : List Nat :=
  plan.roots.flatMap fun entry => [rootEntryLow entry, 0]

def contextTableWords (plan : Plan) : List Nat :=
  plan.contexts.flatMap fun entry => [contextEntryLow entry, contextEntryHigh entry]

theorem pair_words_length {α : Type} (entries : List α) (low high : α → Nat) :
    (entries.flatMap fun entry => [low entry, high entry]).length = 2 * entries.length := by
  induction entries with
  | nil => rfl
  | cons head tail ih =>
      simp [List.flatMap_cons, ih]
      omega

theorem accepted_root_words_length input plan (_h : compile input = .ok plan) :
    (rootTableWords plan).length = 2 * rootEntryCount := by
  rw [rootTableWords, pair_words_length, plan.rootsCanonical]
  simp [canonicalRootEntries]

theorem accepted_context_words_length input plan (_h : compile input = .ok plan) :
    (contextTableWords plan).length = 2 * contextEntryCount := by
  rw [contextTableWords, pair_words_length, plan.contextsCanonical]
  simp [canonicalContextEntries]

/-! ## Bounded live-unit comparison boundary

A guest decoder reads the unit registers and re-reads the constructed table
memory into this shape.  The register read, pointer chase, and memory ordering
are integration evidence, not Lean theorems. -/

structure DecodedUnit where
  versionRegister : UInt64
  capabilityRegister : UInt64
  extendedCapabilityRegister : UInt64
  globalStatus : UInt64
  faultStatus : UInt64
  rootTableAddress : UInt64
  rootWords : List UInt64
  contextWords : List UInt64
  deriving BEq, DecidableEq, Repr

inductive ReportError where
  | wrongVersion | wrongCapability | wrongExtendedCapability | translationDisabled
  | faultRecorded | wrongRootPointer | wrongRootWords | wrongContextWords
  deriving BEq, DecidableEq, Repr

def validateDecodedUnit (plan : Plan) (unit : DecodedUnit) : Except ReportError Unit := do
  if unit.versionRegister ≠ expectedVersionRegister then throw .wrongVersion
  if unit.capabilityRegister ≠ expectedCapabilityRegister then throw .wrongCapability
  if unit.extendedCapabilityRegister ≠ expectedExtendedCapabilityRegister then
    throw .wrongExtendedCapability
  if unit.globalStatus ≠ enabledGlobalStatus then throw .translationDisabled
  if unit.faultStatus ≠ 0 then throw .faultRecorded
  if unit.rootTableAddress.toNat ≠ plan.rootFrame * pageBytes then throw .wrongRootPointer
  if unit.rootWords.map (·.toNat) ≠ rootTableWords plan then throw .wrongRootWords
  if unit.contextWords.map (·.toNat) ≠ contextTableWords plan then throw .wrongContextWords
  pure ()

theorem decoded_validation_deterministic plan unit first second
    (hfirst : validateDecodedUnit plan unit = first)
    (hsecond : validateDecodedUnit plan unit = second) : first = second := by
  rw [hfirst] at hsecond
  exact hsecond

/-! ## Fail-closed activation order

The guest journals each activation step; the canonical order is validated by
the generated boundary below.  Reordered, omitted, or repeated steps produce a
non-canonical journal word. -/

inductive Step where
  | capabilitiesValidated | tablesScrubbed | tablesConstructed | rootPublished
  | contextCacheInvalidated | iotlbInvalidated | translationEnabled | statusVerified
  deriving BEq, DecidableEq, Repr

def stepTag : Step → Nat
  | .capabilitiesValidated => 1
  | .tablesScrubbed => 2
  | .tablesConstructed => 3
  | .rootPublished => 4
  | .contextCacheInvalidated => 5
  | .iotlbInvalidated => 6
  | .translationEnabled => 7
  | .statusVerified => 8

theorem stepTag_injective : Function.Injective stepTag := by
  intro first second hequal
  cases first <;> cases second <;> simp [stepTag] at hequal ⊢

def canonicalJournal : List Step :=
  [.capabilitiesValidated, .tablesScrubbed, .tablesConstructed, .rootPublished,
   .contextCacheInvalidated, .iotlbInvalidated, .translationEnabled, .statusVerified]

/-- Little-endian 4-bit step tags: the first executed step is the lowest
nibble, so the complete canonical journal is one exact 32-bit constant. -/
def encodeJournal (steps : List Step) : Nat :=
  steps.foldr (fun step accumulated => accumulated * 16 + stepTag step) 0

def canonicalJournalWord : Nat := encodeJournal canonicalJournal

example : canonicalJournalWord = 0x87654321 := by native_decide

/-! ## Generated activation boundary -/

/-- The canonical journal as the scalar the generated boundary compares
against; `canonicalJournalUInt64_toNat` binds it to the encoded journal so the
freestanding comparison never depends on a module-initialized `Nat` global. -/
def canonicalJournalUInt64 : UInt64 := 0x87654321

theorem canonicalJournalUInt64_toNat :
    canonicalJournalUInt64.toNat = canonicalJournalWord := by native_decide

/-- Typed rejection tags for the generated scalar boundary.  Zero denotes
acceptance; each nonzero tag names the first failed check.  `topology` is
checked against the current pinned platform revision, which is shared with the
DMA snapshot topology; construction revision 1 pinned the `intel-iommu` unit
in the shared q35 builder.  Every comparison is scalar `UInt64` work so the
generated C stays safe in the freestanding image, where no Lean module
initializer runs. -/
def validateActivation (version topology unitVersion capability extendedCapability
    globalStatus faultStatus rootTableAddress expectedRootTableAddress
    journal : UInt64) : UInt64 :=
  if version ≠ planVersion then 1
  else if topology ≠ DMAQuarantine.q35TopologyVersion then 2
  else if unitVersion ≠ expectedVersionRegister then 3
  else if capability ≠ expectedCapabilityRegister then 4
  else if extendedCapability ≠ expectedExtendedCapabilityRegister then 5
  else if globalStatus ≠ enabledGlobalStatus then 6
  else if faultStatus ≠ 0 then 7
  else if expectedRootTableAddress = 0 ∨
      expectedRootTableAddress % 4096 ≠ 0 ∨
      rootTableAddress ≠ expectedRootTableAddress then 8
  else if journal ≠ canonicalJournalUInt64 then 9
  else 0

theorem validateActivation_alignment_matches_pageBytes
    (address : UInt64) :
    (address % 4096 = 0) ↔ (address.toNat % pageBytes = 0) := by
  constructor
  · intro h
    have := congrArg UInt64.toNat h
    simpa [UInt64.toNat_mod, pageBytes] using this
  · intro h
    apply UInt64.toNat_inj.mp
    simpa [UInt64.toNat_mod, pageBytes] using h

@[export leanos_validate_vtd_activation]
def validateActivationExport (version topology unitVersion capability extendedCapability
    globalStatus faultStatus rootTableAddress expectedRootTableAddress
    journal : UInt64) : UInt64 :=
  validateActivation version topology unitVersion capability extendedCapability
    globalStatus faultStatus rootTableAddress expectedRootTableAddress journal

/-! ## Assigned-EDU authority/control boundary

The assigned image must not reconstruct device authority from C literals.  This
allocation-free scalar boundary accepts only the complete reviewed projection:
the assigned construction revision, assignment/domain identity, platform
requester, linker-owned table/buffer layout, and both directionally restricted
mappings.  The exported code intentionally compares only `UInt64` values so it
does not require a Lean module initializer in the freestanding image. -/

def assignedProjectionVersion : UInt64 := 1
def assignedEDUTopologyVersion : UInt64 := 0x0001000800020003

/-- The one reviewed assignment and its directionally restricted mappings.
This state is shared by table generation and the exported transfer-admission
boundary so neither path reconstructs authority from caller-supplied words. -/
def assignedEDUState : IOMMU.State :=
  let readGranted := IOMMU.gate IOMMU.assignedState (.grant IOMMU.readOnlyGrant)
  (IOMMU.gate readGranted.state (.grant IOMMU.writeOnlyGrant)).state

def validateAssignedEDUProjection
    (version topology device source assignmentGeneration domain domainGeneration
      owner requester secondLevelRootFrame secondLevelDirectoryFrame
      secondLevelTableFrame readBufferFrame writeBufferFrame readIova readLength
      readFrame readFrameGeneration readFrameOffset readPermission writeIova
      writeLength writeFrame writeFrameGeneration writeFrameOffset writePermission :
      UInt64) : UInt64 :=
  if version != assignedProjectionVersion then 1
  else if topology != assignedEDUTopologyVersion then 2
  else if device != 0 || source != 0 || assignmentGeneration != 1 ||
      domain != 0 || domainGeneration != 1 || owner != 0 || requester != 16 then 3
  else if secondLevelRootFrame = 0 ||
      secondLevelDirectoryFrame != secondLevelRootFrame + 1 ||
      secondLevelTableFrame != secondLevelDirectoryFrame + 1 ||
      readBufferFrame != secondLevelTableFrame + 2 ||
      writeBufferFrame != readBufferFrame + 1 then 4
  else if readIova != 0 || readLength != 16 || readFrame != 0 ||
      readFrameGeneration != 1 || readFrameOffset != 0 || readPermission != 1 then 5
  else if writeIova != 16 || writeLength != 16 || writeFrame != readFrame ||
      writeFrameGeneration != readFrameGeneration || writeFrameOffset != 16 ||
      writePermission != 2 then 6
  else 0

@[export leanos_validate_assigned_edu_projection]
def validateAssignedEDUProjectionExport
    (version topology device source assignmentGeneration domain domainGeneration
      owner requester secondLevelRootFrame secondLevelDirectoryFrame
      secondLevelTableFrame readBufferFrame writeBufferFrame readIova readLength
      readFrame readFrameGeneration readFrameOffset readPermission writeIova
      writeLength writeFrame writeFrameGeneration writeFrameOffset writePermission :
      UInt64) : UInt64 :=
  validateAssignedEDUProjection version topology device source assignmentGeneration
    domain domainGeneration owner requester secondLevelRootFrame
    secondLevelDirectoryFrame secondLevelTableFrame readBufferFrame writeBufferFrame
    readIova readLength readFrame readFrameGeneration readFrameOffset readPermission
    writeIova writeLength writeFrame writeFrameGeneration writeFrameOffset writePermission

/-- Stable scalar result for the assigned image's reviewed transfer requests.
Direction 1 is a device read from guest memory; direction 2 is a device write.
The request contains no domain, owner, mapping, or physical-frame authority. -/
def validateAssignedEDUTransfer
    (version source assignmentGeneration iova length direction : UInt64) : UInt64 :=
  if version != assignedProjectionVersion then 1
  else
    let request : IOMMU.TransferRequest :=
      ⟨source.toNat, assignmentGeneration.toNat, iova.toNat, length.toNat⟩
    if direction == 1 then
      match IOMMU.translate assignedEDUState request .read with
      | .ok _ => 0
      | .error .staleAssignment => 3
      | .error .invalidRange => 4
      | .error .permissionDenied => 5
      | .error .staleFrame => 6
      | .error _ => 7
    else if direction == 2 then
      match IOMMU.translate assignedEDUState request .write with
      | .ok _ => 0
      | .error .staleAssignment => 3
      | .error .invalidRange => 4
      | .error .permissionDenied => 5
      | .error .staleFrame => 6
      | .error _ => 7
    else 2

/-- Allocation-free implementation of the assigned-EDU transfer boundary.
The branch structure is the scalar projection of `IOMMU.translate` over
`assignedEDUState`: source 0 at generation 1 owns a read-only `[0, 16)`
mapping and a write-only `[16, 32)` mapping.  Keeping the exported wrapper on
fixed-width words prevents the freestanding image from acquiring Lean runtime
or imported model dependencies; the model-facing definition above remains the
independent specification used by the executable checks below. -/
def validateAssignedEDUTransferScalar
    (version source assignmentGeneration iova length direction : UInt64) : UInt64 :=
  if version != assignedProjectionVersion then 1
  else if direction != 1 && direction != 2 then 2
  else if source ≥ 8 || length = 0 || iova > 4096 || length > 4096 - iova then 4
  else if source != 0 || assignmentGeneration != 1 then 3
  else if iova ≤ 16 && length ≤ 16 - iova then
    if direction == 1 then 0 else 5
  else if 16 ≤ iova && iova ≤ 32 && length ≤ 32 - iova then
    if direction == 2 then 0 else 5
  else 4

@[export leanos_validate_assigned_edu_transfer]
def validateAssignedEDUTransferExport
    (version source assignmentGeneration iova length direction : UInt64) : UInt64 :=
  validateAssignedEDUTransferScalar version source assignmentGeneration iova length direction

/-- Bind the one-record VT-d fault observation to the current reviewed
assigned-EDU authority. Legacy FRCD carries requester and access direction but
not domain or assignment generation, so those current-state fields are checked
alongside the exact record. QEMU 8.2.2 records the unavailable PASID field as
all ones for this non-PASID request, and the pinned exact record retains that
emulator-visible boundary instead of silently masking it. -/
def validateAssignedEDUFault
    (version source domain assignmentGeneration iova direction faultStatus
      faultLow faultHigh : UInt64) : UInt64 :=
  if version != assignedProjectionVersion then 1
  else if direction != 1 && direction != 2 then 2
  else if source != 0 || domain != 0 || assignmentGeneration != 1 then 3
  else if faultStatus != 2 then 4
  else if direction == 1 && iova == 4096 then
    if faultLow != iova then 5
    else if faultHigh != 0xc0ffff0600000010 then 6
    else 0
  else if direction == 2 && iova == 0 then
    if faultLow != iova then 5
    else if faultHigh != 0x80ffff0500000010 then 6
    else 0
  else if direction == 1 && iova == 8192 then
    if faultLow != iova then 5
    else if faultHigh != 0xc0ffff0600000010 then 6
    else 0
  else 4

@[export leanos_validate_assigned_edu_fault]
def validateAssignedEDUFaultExport
    (version source domain assignmentGeneration iova direction faultStatus
      faultLow faultHigh : UInt64) : UInt64 :=
  validateAssignedEDUFault version source domain assignmentGeneration iova direction
    faultStatus faultLow faultHigh

example : validateAssignedEDUTransfer 1 0 1 0 16 1 = 0 := by native_decide
example : validateAssignedEDUTransfer 1 0 1 16 16 2 = 0 := by native_decide
example : validateAssignedEDUTransfer 1 0 1 0 16 2 = 5 := by native_decide
example : validateAssignedEDUTransfer 1 0 1 16 16 1 = 5 := by native_decide
example : validateAssignedEDUTransfer 1 0 1 8 16 1 = 4 := by native_decide
example : validateAssignedEDUTransfer 1 1 1 0 16 1 = 3 := by native_decide

/-- The allocation-free exported adapter refines the authoritative IOMMU
model on every transfer in the fixed assigned-EDU scenario: both authorized
directions and the reviewed wrong-direction, boundary-crossing, and
wrong-source denials. This is deliberately a bounded-scenario theorem, not a
claim about arbitrary assignments or devices. -/
theorem assignedEDUTransferScalar_refines_authoritative_scenario :
    validateAssignedEDUTransferScalar 1 0 1 0 16 1 =
        validateAssignedEDUTransfer 1 0 1 0 16 1 ∧
    validateAssignedEDUTransferScalar 1 0 1 16 16 2 =
        validateAssignedEDUTransfer 1 0 1 16 16 2 ∧
    validateAssignedEDUTransferScalar 1 0 1 0 16 2 =
        validateAssignedEDUTransfer 1 0 1 0 16 2 ∧
    validateAssignedEDUTransferScalar 1 0 1 16 16 1 =
        validateAssignedEDUTransfer 1 0 1 16 16 1 ∧
    validateAssignedEDUTransferScalar 1 0 1 8 16 1 =
        validateAssignedEDUTransfer 1 0 1 8 16 1 ∧
    validateAssignedEDUTransferScalar 1 1 1 0 16 1 =
        validateAssignedEDUTransfer 1 1 1 0 16 1 := by
  native_decide

example : validateAssignedEDUFault
    1 0 0 1 4096 1 2 4096 0xc0ffff0600000010 = 0 := by native_decide
example : validateAssignedEDUFault
    1 0 0 1 0 2 2 0 0x80ffff0500000010 = 0 := by native_decide
example : validateAssignedEDUFault
    1 0 0 1 8192 1 2 8192 0xc0ffff0600000010 = 0 := by native_decide
example : validateAssignedEDUFault
    1 0 0 1 4096 1 2 4096 0xc000000500000010 = 6 := by native_decide
example : validateAssignedEDUFault
    0 0 0 1 4096 1 2 4096 0xc0ffff0600000010 = 1 := by native_decide
example : validateAssignedEDUFault
    1 0 0 1 4096 3 2 4096 0xc0ffff0600000010 = 2 := by native_decide
example : validateAssignedEDUFault
    1 1 0 1 4096 1 2 4096 0xc0ffff0600000010 = 3 := by native_decide
example : validateAssignedEDUFault
    1 0 1 1 4096 1 2 4096 0xc0ffff0600000010 = 3 := by native_decide
example : validateAssignedEDUFault
    1 0 0 2 4096 1 2 4096 0xc0ffff0600000010 = 3 := by native_decide
example : validateAssignedEDUFault
    1 0 0 1 0 1 2 4096 0xc0ffff0600000010 = 4 := by native_decide
example : validateAssignedEDUFault
    1 0 0 1 4096 1 0 4096 0xc0ffff0600000010 = 4 := by native_decide
example : validateAssignedEDUFault
    1 0 0 1 4096 1 2 0 0xc0ffff0600000010 = 5 := by native_decide

example : validateAssignedEDUProjection
    1 0x0001000800020003 0 0 1 0 1 0 16
    3 4 5 7 8 0 16 0 1 0 1 16 16 0 1 16 2 = 0 := by native_decide

example : validateAssignedEDUProjection
    1 0x0001000800020003 0 0 1 0 1 0 16
    3 4 5 7 8 0 16 0 1 0 3 16 16 0 1 16 2 = 5 := by native_decide

theorem validateActivation_deterministic (version topology unitVersion capability
    extendedCapability globalStatus faultStatus rootTableAddress expectedRootTableAddress
    journal : UInt64) first second
    (hfirst : validateActivation version topology unitVersion capability extendedCapability
      globalStatus faultStatus rootTableAddress expectedRootTableAddress journal = first)
    (hsecond : validateActivation version topology unitVersion capability extendedCapability
      globalStatus faultStatus rootTableAddress expectedRootTableAddress journal = second) :
    first = second := by
  rw [hfirst] at hsecond
  exact hsecond

/-! ## Executable vectors -/

def sampleRootTableFrame : Nat := 8
def sampleContextTableFrame : Nat := 9

def sampleCpuTableFrames : List Nat :=
  BootPageTablePlan.tableFrames BootPageTablePlan.sampleInput

def sampleInput : Input :=
  { state := IOMMU.emptyState
    rootTableFrame := sampleRootTableFrame
    contextTableFrame := sampleContextTableFrame
    cpuTableFrames := sampleCpuTableFrames
    reservationResult := BootPageTablePlan.sampleReservationResult }

def rejectedAs (input : Input) (wanted : Error) : Bool :=
  match compile input with
  | .error actual => actual == wanted
  | .ok _ => false

example : (match compile sampleInput with | .ok _ => true | .error _ => false) = true := by
  native_decide
example : rejectedAs { sampleInput with reservationResult := none }
    .missingValidatedReservation = true := by native_decide
example : rejectedAs { sampleInput with state := IOMMU.assignedState }
    .assignmentsNotSupported = true := by native_decide
example : rejectedAs { sampleInput with contextTableFrame := sampleRootTableFrame }
    .duplicateTableFrame = true := by native_decide
example : rejectedAs { sampleInput with rootTableFrame := 10 }
    .tableAliasesCpuTables = true := by native_decide
example : rejectedAs { sampleInput with contextTableFrame := 31 }
    .tableAliasesCpuTables = true := by native_decide
example : rejectedAs { sampleInput with rootTableFrame := 35 }
    .unreservedTableFrame = true := by native_decide
example : rejectedAs { sampleInput with rootTableFrame := 0 }
    .frameOutOfRange = true := by native_decide
example : rejectedAs { sampleInput with contextTableFrame := physicalFrameLimit }
    .frameOutOfRange = true := by native_decide

/-- Canonical decoded unit for an accepted plan: pinned registers, activation
status, empty fault state, and the exact generated table words. -/
def expectedDecodedUnit (plan : Plan) : DecodedUnit :=
  { versionRegister := expectedVersionRegister
    capabilityRegister := expectedCapabilityRegister
    extendedCapabilityRegister := expectedExtendedCapabilityRegister
    globalStatus := enabledGlobalStatus
    faultStatus := 0
    rootTableAddress := UInt64.ofNat (plan.rootFrame * pageBytes)
    rootWords := (rootTableWords plan).map UInt64.ofNat
    contextWords := (contextTableWords plan).map UInt64.ofNat }

def reportRejectedAs (mutate : DecodedUnit → DecodedUnit) (wanted : ReportError) : Bool :=
  match compile sampleInput with
  | .ok plan =>
      match validateDecodedUnit plan (mutate (expectedDecodedUnit plan)) with
      | .error actual => actual == wanted
      | .ok _ => false
  | .error _ => false

example : (match compile sampleInput with
    | .ok plan => (validateDecodedUnit plan (expectedDecodedUnit plan)).isOk
    | .error _ => false) = true := by native_decide
example : reportRejectedAs (fun unit => { unit with versionRegister := 0x20 })
    .wrongVersion = true := by native_decide
example : reportRejectedAs (fun unit => { unit with
    capabilityRegister := unit.capabilityRegister ||| 0x80 }) .wrongCapability = true := by
  native_decide
/-- Passthrough support appearing in ECAP (bit 6) is exactly option drift. -/
example : reportRejectedAs (fun unit => { unit with
    extendedCapabilityRegister := 0x0f42 }) .wrongExtendedCapability = true := by native_decide
example : reportRejectedAs (fun unit => { unit with globalStatus := 0x8000_0000 })
    .translationDisabled = true := by native_decide
example : reportRejectedAs (fun unit => { unit with globalStatus := 0 })
    .translationDisabled = true := by native_decide
example : reportRejectedAs (fun unit => { unit with faultStatus := 2 })
    .faultRecorded = true := by native_decide
example : reportRejectedAs (fun unit => { unit with
    rootTableAddress := UInt64.ofNat ((sampleRootTableFrame + 1) * pageBytes) })
    .wrongRootPointer = true := by native_decide
/-- Dropping the bus 0 root entry silently disables the checked tables. -/
example : reportRejectedAs (fun unit => { unit with rootWords := unit.rootWords.set 0 0 })
    .wrongRootWords = true := by native_decide
/-- Pointing bus 0 at a different context table is a forged root entry. -/
example : reportRejectedAs (fun unit => { unit with
    rootWords := unit.rootWords.set 0 (UInt64.ofNat (35 * pageBytes + 1)) })
    .wrongRootWords = true := by native_decide
/-- A surprise present context entry would authorize a requester. -/
example : reportRejectedAs (fun unit => { unit with
    contextWords := unit.contextWords.set 0 (UInt64.ofNat (12 * pageBytes + 1)) })
    .wrongContextWords = true := by native_decide
example : reportRejectedAs (fun unit => { unit with
    contextWords := unit.contextWords.set 511 1 }) .wrongContextWords = true := by native_decide

def sampleActivation (journal : UInt64) : UInt64 :=
  validateActivation planVersion DMAQuarantine.q35TopologyVersion
    expectedVersionRegister expectedCapabilityRegister expectedExtendedCapabilityRegister
    enabledGlobalStatus 0 (UInt64.ofNat (sampleRootTableFrame * pageBytes))
    (UInt64.ofNat (sampleRootTableFrame * pageBytes)) journal

example : sampleActivation (UInt64.ofNat canonicalJournalWord) = 0 := by native_decide
/-- Reordered activation: publishing the root pointer before construction. -/
example : sampleActivation 0x87653421 = 9 := by native_decide
/-- Omitted invalidation step. -/
example : sampleActivation 0x876431 = 9 := by native_decide
example : validateActivation 2 DMAQuarantine.q35TopologyVersion expectedVersionRegister
    expectedCapabilityRegister expectedExtendedCapabilityRegister enabledGlobalStatus 0
    4096 4096 (UInt64.ofNat canonicalJournalWord) = 1 := by native_decide
example : validateActivation planVersion 0x0108_0002_0002 expectedVersionRegister
    expectedCapabilityRegister expectedExtendedCapabilityRegister enabledGlobalStatus 0
    4096 4096 (UInt64.ofNat canonicalJournalWord) = 2 := by native_decide
example : validateActivation planVersion DMAQuarantine.q35TopologyVersion 0
    expectedCapabilityRegister expectedExtendedCapabilityRegister enabledGlobalStatus 0
    4096 4096 (UInt64.ofNat canonicalJournalWord) = 3 := by native_decide
example : validateActivation planVersion DMAQuarantine.q35TopologyVersion
    expectedVersionRegister 0 expectedExtendedCapabilityRegister enabledGlobalStatus 0
    4096 4096 (UInt64.ofNat canonicalJournalWord) = 4 := by native_decide
example : validateActivation planVersion DMAQuarantine.q35TopologyVersion
    expectedVersionRegister expectedCapabilityRegister 0x0f42 enabledGlobalStatus 0
    4096 4096 (UInt64.ofNat canonicalJournalWord) = 5 := by native_decide
example : validateActivation planVersion DMAQuarantine.q35TopologyVersion
    expectedVersionRegister expectedCapabilityRegister expectedExtendedCapabilityRegister
    0x8000_0000 0 4096 4096 (UInt64.ofNat canonicalJournalWord) = 6 := by native_decide
example : validateActivation planVersion DMAQuarantine.q35TopologyVersion
    expectedVersionRegister expectedCapabilityRegister expectedExtendedCapabilityRegister
    enabledGlobalStatus 2 4096 4096 (UInt64.ofNat canonicalJournalWord) = 7 := by
  native_decide
example : validateActivation planVersion DMAQuarantine.q35TopologyVersion
    expectedVersionRegister expectedCapabilityRegister expectedExtendedCapabilityRegister
    enabledGlobalStatus 0 8192 4096 (UInt64.ofNat canonicalJournalWord) = 8 := by
  native_decide
example : validateActivation planVersion DMAQuarantine.q35TopologyVersion
    expectedVersionRegister expectedCapabilityRegister expectedExtendedCapabilityRegister
    enabledGlobalStatus 0 0 0 (UInt64.ofNat canonicalJournalWord) = 8 := by native_decide
example : validateActivation planVersion DMAQuarantine.q35TopologyVersion
    expectedVersionRegister expectedCapabilityRegister expectedExtendedCapabilityRegister
    enabledGlobalStatus 0 4097 4097 (UInt64.ofNat canonicalJournalWord) = 8 := by
  native_decide

end LeanOS.VTdBootPlan
