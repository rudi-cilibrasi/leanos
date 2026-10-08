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
    rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
      ite_eq_right (by omega)]
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
    rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
      ite_eq_right (by omega), ite_eq_right (by omega)]
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

`compile` is the only constructor, and it is the single authority for every
VT-d table a q35 image installs.  An accepted plan has one present root entry
for bus 0 selecting the reserved context table.  Without a grant binding the
projection is deny-all: 256 absent context entries, exactly the projection of
an accepted static device-domain state with no live assignments.  With exactly
one live assignment and its reviewed platform binding, the bound requester's
context entry selects a three-level second-level table: the top and directory
levels each hold one read/write entry at slot 0, and the leaf maps exactly the
assignment's granted pages, one 4 KiB hardware page per model page, with the
granted permission.  Any other shape is rejected. -/

/-- Entries per second-level table page: 4 KiB of 8-byte entries. -/
def secondLevelEntryCount : Nat := 512

/-- Reviewed platform binding that places the single model assignment on
hardware.  It names no authority of its own: which IOVA pages are mapped, with
which permission, and onto which model frame offsets still comes only from the
accepted `IOMMU.State`.  The binding supplies the requester the assigned
function answers as, the linked second-level table frames, and the hardware
frame holding model page 0 of each granted model frame; model page `k` of that
frame is hardware frame `base + k`. -/
structure GrantBinding where
  /-- Source identifier: bus number times 256 plus device/function. -/
  requester : Nat
  secondLevelRootFrame : Nat
  secondLevelDirectoryFrame : Nat
  secondLevelTableFrame : Nat
  frameBases : List (IOMMU.FrameId × Nat)
  deriving BEq, DecidableEq, Repr

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
  /-- Present exactly when the state has its one live assignment. -/
  grantBinding : Option GrantBinding := none

inductive Error where
  | missingValidatedReservation | unreservedTableFrame | duplicateTableFrame
  | tableAliasesCpuTables | frameOutOfRange | assignmentsNotSupported
  | mappingsNotSupported | missingGrantBinding | unexpectedGrantBinding
  | domainOutOfRange | requesterOutOfRange | unboundGrantFrame
  | emptyGrantPermission | grantOutOfRange | grantOverlapsReservedFrame
  deriving BEq, DecidableEq, Repr

def reservedFrame (input : Input) (frame : Nat) : Bool :=
  match input.reservationResult with
  | none => false
  | some reserved => BootReservation.reservedBy reserved.intervals frame

/-- Frames a grant may never reach: every reservation except the loaded-image
span (the linker places the reviewed DMA buffers inside the kernel image), the
CPU page-table frames, and every VT-d table frame.  Without a validated
reservation every frame is protected. -/
def protectedFrame (input : Input) (frame : Nat) : Bool :=
  (match input.reservationResult with
    | none => true
    | some reserved => reserved.intervals.any fun interval =>
        interval.identity != .loadedImage && interval.contains frame) ||
    input.cpuTableFrames.contains frame ||
    frame == input.rootTableFrame || frame == input.contextTableFrame ||
    match input.grantBinding with
    | none => false
    | some binding =>
        frame == binding.secondLevelRootFrame ||
          frame == binding.secondLevelDirectoryFrame ||
          frame == binding.secondLevelTableFrame

/-- Every table frame the plan installs, in walk order. -/
def tableFrames (input : Input) : List Nat :=
  [input.rootTableFrame, input.contextTableFrame] ++
    match input.grantBinding with
    | none => []
    | some binding =>
        [binding.secondLevelRootFrame, binding.secondLevelDirectoryFrame,
          binding.secondLevelTableFrame]

def frameBounded (frame : Nat) : Bool := 0 < frame && frame < physicalFrameLimit

/-! ### Granted pages

The model's 16-byte pages scale to 4 KiB hardware pages: model IOVA page `p`
(`iova / IOMMU.pageSize`) is hardware IOVA page `p`.  These definitions are the
specification the compiled tables are proved against. -/

def mappingFirstPage (mapping : IOMMU.Mapping) : Nat := mapping.iova / IOMMU.pageSize

def mappingEndPage (mapping : IOMMU.Mapping) : Nat :=
  (mapping.iova + mapping.length) / IOMMU.pageSize

def mappingCovers (mapping : IOMMU.Mapping) (page : Nat) : Bool :=
  mappingFirstPage mapping ≤ page && page < mappingEndPage mapping

def mappingBase (binding : GrantBinding) (mapping : IOMMU.Mapping) : Option Nat :=
  binding.frameBases.lookup mapping.frame.frame

/-- Hardware frame behind IOVA page `page` of a mapping whose model frame
starts at hardware frame `base`. -/
def mappingFrame (base : Nat) (mapping : IOMMU.Mapping) (page : Nat) : Nat :=
  base + mapping.frameOffset / IOMMU.pageSize + (page - mappingFirstPage mapping)

/-- The granted hardware frame and permission at one IOVA page, read directly
from the accepted model mappings and the binding. -/
def grantedPage (input : Input) (binding : GrantBinding) (page : Nat) :
    Option (Nat × IOMMU.Permission) :=
  match input.state.core.mappings.find? (mappingCovers · page) with
  | none => none
  | some mapping =>
      (mappingBase binding mapping).map fun base =>
        (mappingFrame base mapping page, mapping.permission)

/-- The granted IOVA→frame relation for every requester: only the bound
requester has any translation, and it has exactly the granted pages. -/
def grantedTranslation (input : Input) (requester page : Nat) :
    Option (Nat × IOMMU.Permission) :=
  match input.grantBinding with
  | none => none
  | some binding => if requester = binding.requester then grantedPage input binding page else none

/-- Domain identifier of the single live assignment (zero when deny-all). -/
def assignmentDomain (input : Input) : Nat :=
  (input.state.core.assignments.head?.map (·.domain.slot)).getD 0

/-! ### Checks

Each entry is a failing condition and the reason reported for it; `compile`
reports the first failing one.  The order keeps every deny-all rejection
reason of the original plan unchanged. -/

def grantChecks (input : Input) (binding : GrantBinding) : List (Bool × Error) :=
  [(decide (contextEntryCount ≤ binding.requester), .requesterOutOfRange),
   (input.state.core.mappings.any fun mapping => (mappingBase binding mapping).isNone,
     .unboundGrantFrame),
   (input.state.core.mappings.any fun mapping => !mapping.permission.nonempty,
     .emptyGrantPermission),
   (input.state.core.mappings.any fun mapping =>
      decide (secondLevelEntryCount < mappingEndPage mapping), .grantOutOfRange),
   ((List.range secondLevelEntryCount).any fun page =>
      match grantedPage input binding page with
      | none => false
      | some (frame, _) => !frameBounded frame, .frameOutOfRange),
   ((List.range secondLevelEntryCount).any fun page =>
      match grantedPage input binding page with
      | none => false
      | some (frame, _) => protectedFrame input frame, .grantOverlapsReservedFrame)]

def checks (input : Input) : List (Bool × Error) :=
  [(input.reservationResult.isNone, .missingValidatedReservation),
   (decide (1 < input.state.core.assignments.length), .assignmentsNotSupported),
   (input.state.core.mappings.any fun mapping =>
      !input.state.core.assignments.any (·.handle == mapping.assignment),
     .mappingsNotSupported),
   (input.state.core.assignments.isEmpty && input.grantBinding.isSome,
     .unexpectedGrantBinding),
   (!input.state.core.assignments.isEmpty && input.grantBinding.isNone,
     .missingGrantBinding),
   (input.state.core.assignments.any fun assignment =>
      decide (domainLimit ≤ assignment.domain.slot), .domainOutOfRange),
   (!decide (tableFrames input).Nodup, .duplicateTableFrame),
   ((tableFrames input).any input.cpuTableFrames.contains, .tableAliasesCpuTables),
   ((tableFrames input).any fun frame => !frameBounded frame, .frameOutOfRange),
   ((tableFrames input).any fun frame => !reservedFrame input frame,
     .unreservedTableFrame)] ++
  match input.grantBinding with
  | none => []
  | some binding => grantChecks input binding

def firstError (input : Input) : Option Error :=
  ((checks input).find? (·.1)).map (·.2)

/-- An accepted plan is a checked input; every table is a function of it, so
no consumer can assemble table words the checks did not see. -/
structure Plan where
  private mk ::
  private source : Input
  private accepted : firstError source = none

/-- Total compiler/checker for the deliberately finite supported subset. -/
def compile (input : Input) : Except Error Plan :=
  match h : firstError input with
  | some error => .error error
  | none => .ok ⟨input, h⟩

def Plan.rootFrame (plan : Plan) : Nat := plan.source.rootTableFrame
def Plan.contextFrame (plan : Plan) : Nat := plan.source.contextTableFrame
def Plan.grantBinding (plan : Plan) : Option GrantBinding := plan.source.grantBinding

/-- Exactly one present root entry: bus 0 selects the reserved context table. -/
def canonicalRootEntries (contextTableFrame : Nat) : List RootEntry :=
  (List.range rootEntryCount).map fun bus =>
    if bus == 0 then { present := true, contextTableFrame } else absentRootEntry

/-- The deny-all boot projection: every requester decodes to an absent entry. -/
def canonicalContextEntries : List ContextEntry :=
  List.replicate contextEntryCount absentContextEntry

/-- The bound requester's entry selects the second-level top table in the
assignment's domain; every other requester stays absent. -/
def compiledContextEntries (input : Input) : List ContextEntry :=
  match input.grantBinding with
  | none => canonicalContextEntries
  | some binding =>
      (List.range contextEntryCount).map fun requester =>
        if requester = binding.requester then
          { present := true, domain := assignmentDomain input,
            addressWidth := addressWidthEncoding,
            secondLevelFrame := binding.secondLevelRootFrame }
        else absentContextEntry

def Plan.roots (plan : Plan) : List RootEntry := canonicalRootEntries plan.contextFrame
def Plan.contexts (plan : Plan) : List ContextEntry := compiledContextEntries plan.source

/-- Whether every table frame was checked against the boot reservation. -/
def Plan.reservationChecked (plan : Plan) : Bool :=
  (tableFrames plan.source).all (reservedFrame plan.source)

/-- Whether every table frame was checked against the CPU page tables. -/
def Plan.cpuDisjoint (plan : Plan) : Bool :=
  (tableFrames plan.source).all fun frame => !plan.source.cpuTableFrames.contains frame

/-! ### Second-level entry codec

The supported subset sets only the read (bit 0) and write (bit 1) bits beside
the 4 KiB-aligned frame pointer; superpages, snoop, and every other attribute
stay zero.  An entry with neither permission bit is not present. -/

def permissionBits (permission : IOMMU.Permission) : Nat :=
  (if permission.read then 1 else 0) + (if permission.write then 2 else 0)

def secondLevelEntry (frame : Nat) (permission : IOMMU.Permission) : Nat :=
  frame * pageBytes + permissionBits permission

def decodeSecondLevelEntry (word : Nat) : Option (Nat × IOMMU.Permission) :=
  let bits := word % pageBytes
  if bits = 0 ∨ 3 < bits then none
  else some (word / pageBytes, ⟨bits % 2 == 1, bits / 2 == 1⟩)

theorem decode_secondLevelEntry (frame : Nat) (permission : IOMMU.Permission)
    (h : permission.nonempty = true) :
    decodeSecondLevelEntry (secondLevelEntry frame permission) = some (frame, permission) := by
  obtain ⟨read, write⟩ := permission
  unfold decodeSecondLevelEntry secondLevelEntry permissionBits
  rw [show pageBytes = 4096 from rfl]
  cases read <;> cases write <;> simp_all [IOMMU.Permission.nonempty] <;> omega

/-- A table page holding one entry. -/
def secondLevelPage (index value : Nat) : List Nat :=
  (List.range secondLevelEntryCount).map fun candidate =>
    if candidate = index then value else 0

def leafEntryWord : Option (Nat × IOMMU.Permission) → Nat
  | none => 0
  | some (frame, permission) => secondLevelEntry frame permission

def Plan.secondLevelRootWords (plan : Plan) : List Nat :=
  match plan.grantBinding with
  | none => []
  | some binding =>
      secondLevelPage 0 (secondLevelEntry binding.secondLevelDirectoryFrame IOMMU.readWrite)

def Plan.secondLevelDirectoryWords (plan : Plan) : List Nat :=
  match plan.grantBinding with
  | none => []
  | some binding =>
      secondLevelPage 0 (secondLevelEntry binding.secondLevelTableFrame IOMMU.readWrite)

def Plan.secondLevelTableWords (plan : Plan) : List Nat :=
  match plan.grantBinding with
  | none => []
  | some binding =>
      (List.range secondLevelEntryCount).map fun page =>
        leafEntryWord (grantedPage plan.source binding page)

theorem compile_deterministic input first second
    (hfirst : compile input = first) (hsecond : compile input = second) : first = second := by
  rw [hfirst] at hsecond
  exact hsecond

/-! ## Agreement with the accepted static domain projection -/

theorem compile_source {input plan} (h : compile input = .ok plan) : plan.source = input := by
  unfold compile at h
  split at h
  · contradiction
  · injection h with h
    subst h
    rfl

theorem checks_pass {input plan} (h : compile input = .ok plan) :
    ∀ check ∈ checks input, check.1 = false := by
  have haccepted := plan.accepted
  rw [compile_source h] at haccepted
  intro check hmem
  unfold firstError at haccepted
  rw [Option.map_eq_none_iff, List.find?_eq_none] at haccepted
  simpa using haccepted check hmem

theorem grantChecks_pass {input plan binding} (h : compile input = .ok plan)
    (hbinding : input.grantBinding = some binding) :
    ∀ check ∈ grantChecks input binding, check.1 = false := by
  intro check hmem
  apply checks_pass h
  simp only [checks, hbinding, List.mem_append]
  exact Or.inr hmem

/-- Acceptance without a grant binding requires the model state itself to be
deny-all. -/
theorem accepted_state_deny_all input plan (h : compile input = .ok plan)
    (hunbound : input.grantBinding = none) :
    input.state.core.assignments = [] ∧ input.state.core.mappings = [] := by
  have hpass := checks_pass h
  have hmissing := hpass (!input.state.core.assignments.isEmpty && input.grantBinding.isNone,
    .missingGrantBinding) (by simp [checks])
  have hmappings := hpass (input.state.core.mappings.any fun mapping =>
      !input.state.core.assignments.any (·.handle == mapping.assignment),
    .mappingsNotSupported) (by simp [checks])
  simp only [hunbound, Option.isNone_none, Bool.and_true, Bool.not_eq_false',
    List.isEmpty_iff] at hmissing
  refine ⟨hmissing, ?_⟩
  simp only [hmissing, List.any_nil, Bool.not_false, List.any_eq_false] at hmappings
  cases hmapping : input.state.core.mappings with
  | nil => rfl
  | cons head tail =>
      exact absurd (hmappings head (by simp [hmapping])) (by simp)

/-- Without a grant binding every context entry is absent. -/
theorem accepted_context_entries_absent input plan (h : compile input = .ok plan)
    (hunbound : input.grantBinding = none) :
    plan.contexts = List.replicate contextEntryCount absentContextEntry := by
  simp [Plan.contexts, compiledContextEntries, compile_source h, hunbound,
    canonicalContextEntries]

/-- Each requester decodes through exactly one context slot: the table has
exactly `contextEntryCount` entries, indexed by device/function number. -/
theorem accepted_requesters_bound_once input plan (_h : compile input = .ok plan) :
    plan.contexts.length = contextEntryCount := by
  unfold Plan.contexts compiledContextEntries
  split <;> simp [canonicalContextEntries]

/-- Without a grant binding no physical frame is reachable: there are no
present context entries, hence no second-level tables at all. -/
theorem accepted_maps_no_frame input plan (h : compile input = .ok plan)
    (hunbound : input.grantBinding = none) :
    (plan.contexts.filter (·.present)).map (·.secondLevelFrame) = [] := by
  rw [accepted_context_entries_absent input plan h hunbound]
  simp [absentContextEntry]

/-- Bus 0 selects exactly the reserved context table; every other root entry
is absent. -/
theorem accepted_root_shape input plan (_h : compile input = .ok plan) :
    plan.roots = canonicalRootEntries plan.contextFrame := rfl

theorem accepted_table_frames_distinct input plan (h : compile input = .ok plan) :
    (tableFrames input).Nodup := by
  have hdup := checks_pass h (!decide (tableFrames input).Nodup, .duplicateTableFrame)
    (by simp [checks])
  simpa using hdup

theorem accepted_tables_distinct input plan (h : compile input = .ok plan) :
    plan.rootFrame ≠ plan.contextFrame := by
  have hnodup := accepted_table_frames_distinct input plan h
  simp only [Plan.rootFrame, Plan.contextFrame, compile_source h]
  simp only [tableFrames, List.cons_append, List.nodup_cons, List.mem_cons,
    List.mem_append] at hnodup
  exact fun hequal => hnodup.1 (Or.inl hequal)

theorem accepted_table_frames_bounded input plan (h : compile input = .ok plan) :
    ∀ frame ∈ tableFrames input, frameBounded frame = true := by
  have hbound := checks_pass h ((tableFrames input).any fun frame => !frameBounded frame,
    .frameOutOfRange) (by simp [checks])
  simpa using hbound

theorem accepted_reservation_checked input plan (h : compile input = .ok plan) :
    plan.reservationChecked = true := by
  have hreserved := checks_pass h ((tableFrames input).any fun frame =>
      !reservedFrame input frame, .unreservedTableFrame) (by simp [checks])
  simp only [Plan.reservationChecked, compile_source h]
  simpa using hreserved

theorem accepted_cpu_tables_disjoint input plan (h : compile input = .ok plan) :
    plan.cpuDisjoint = true := by
  have hcpu := checks_pass h ((tableFrames input).any input.cpuTableFrames.contains,
    .tableAliasesCpuTables) (by simp [checks])
  simp only [Plan.cpuDisjoint, compile_source h]
  simpa using hcpu

/-- The accepted plan agrees with the model's authority lookup: without a
grant binding no source and generation resolves to a live assignment. -/
theorem accepted_agrees_with_domain_projection input plan (h : compile input = .ok plan)
    (hunbound : input.grantBinding = none)
    (source : IOMMU.SourceId) (generation : IOMMU.Generation) :
    IOMMU.findAssignmentBySource input.state.core source generation = none := by
  have hdeny := (accepted_state_deny_all input plan h hunbound).1
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

theorem pair_words_getElem? {α : Type} (entries : List α) (low high : α → Nat)
    (index : Nat) :
    (entries.flatMap fun entry => [low entry, high entry])[2 * index]? =
        entries[index]?.map low ∧
      (entries.flatMap fun entry => [low entry, high entry])[2 * index + 1]? =
        entries[index]?.map high := by
  induction entries generalizing index with
  | nil => simp
  | cons head tail ih =>
      cases index with
      | zero => simp
      | succ index =>
          have hshape : 2 * (index + 1) = 2 * index + 1 + 1 := by omega
          simp only [List.flatMap_cons, List.cons_append, List.nil_append, hshape,
            List.getElem?_cons_succ, Nat.add_assoc]
          simpa [Nat.add_assoc] using ih index

theorem accepted_root_words_length input plan (_h : compile input = .ok plan) :
    (rootTableWords plan).length = 2 * rootEntryCount := by
  rw [rootTableWords, pair_words_length]
  simp [Plan.roots, canonicalRootEntries]

theorem accepted_context_words_length input plan (h : compile input = .ok plan) :
    (contextTableWords plan).length = 2 * contextEntryCount := by
  rw [contextTableWords, pair_words_length, accepted_requesters_bound_once input plan h]

/-! ## Encoded-table translation

`Plan.translate` reads the emitted words the way the pinned walk is specified
to: the root entry selected by the requester's bus, the context entry selected
by its device/function, then the top, directory, and leaf second-level entries
selected by IOVA page bits 26:18, 17:9, and 8:0.  Each pointer must name one
of the plan's own table frames; permissions intersect down the walk.  This is a
statement about the encoded tables, not about the IOMMU's table walk, which
stays a trusted hardware boundary. -/

def wordAt (words : List Nat) (index : Nat) : Nat := words[index]?.getD 0

def Plan.tableAt (plan : Plan) (frame : Nat) : Option (List Nat) :=
  match plan.grantBinding with
  | none => none
  | some binding =>
      if frame = binding.secondLevelRootFrame then some plan.secondLevelRootWords
      else if frame = binding.secondLevelDirectoryFrame then some plan.secondLevelDirectoryWords
      else if frame = binding.secondLevelTableFrame then some plan.secondLevelTableWords
      else none

def intersectPermission (first second : IOMMU.Permission) : IOMMU.Permission :=
  ⟨first.read && second.read, first.write && second.write⟩

def Plan.walkSecondLevel (plan : Plan) (top : List Nat) (page : Nat) :
    Option (Nat × IOMMU.Permission) := do
  let (directoryFrame, topPermission) ←
    decodeSecondLevelEntry (wordAt top (page / secondLevelEntryCount / secondLevelEntryCount))
  let directory ← plan.tableAt directoryFrame
  let (leafFrame, directoryPermission) ←
    decodeSecondLevelEntry (wordAt directory (page / secondLevelEntryCount % secondLevelEntryCount))
  let leaf ← plan.tableAt leafFrame
  let (frame, permission) ← decodeSecondLevelEntry (wordAt leaf (page % secondLevelEntryCount))
  pure (frame,
    intersectPermission topPermission (intersectPermission directoryPermission permission))

def Plan.translate (plan : Plan) (requester page : Nat) : Option (Nat × IOMMU.Permission) :=
  let bus := requester / contextEntryCount
  let function := requester % contextEntryCount
  match decodeRootEntry (wordAt (rootTableWords plan) (2 * bus))
      (wordAt (rootTableWords plan) (2 * bus + 1)) with
  | .error _ => none
  | .ok root =>
      if root.present = false ∨ root.contextTableFrame ≠ plan.contextFrame then none
      else
        match decodeContextEntry (wordAt (contextTableWords plan) (2 * function))
            (wordAt (contextTableWords plan) (2 * function + 1)) with
        | .error _ => none
        | .ok context =>
            if context.present = false then none
            else match plan.tableAt context.secondLevelFrame with
              | none => none
              | some top => plan.walkSecondLevel top page

/-! ### Proof of the translation theorem -/

theorem grantedPage_some {input binding page frame permission}
    (h : grantedPage input binding page = some (frame, permission)) :
    ∃ mapping ∈ input.state.core.mappings, mappingCovers mapping page = true ∧
      permission = mapping.permission ∧
      ∃ base, mappingBase binding mapping = some base ∧
        frame = mappingFrame base mapping page := by
  unfold grantedPage at h
  split at h
  · contradiction
  next mapping hfind =>
    obtain ⟨base, hbase, hpair⟩ := Option.map_eq_some_iff.mp h
    injection hpair with hframe hpermission
    exact ⟨mapping, List.mem_of_find?_eq_some hfind, by simpa using List.find?_some hfind,
      hpermission.symm, base, hbase, hframe.symm⟩

theorem accepted_grant_pages_bounded {input plan binding} (h : compile input = .ok plan)
    (hbinding : input.grantBinding = some binding) {page frame permission}
    (hgrant : grantedPage input binding page = some (frame, permission)) :
    page < secondLevelEntryCount ∧ permission.nonempty = true := by
  obtain ⟨mapping, hmem, hcovers, hpermission, _⟩ := grantedPage_some hgrant
  have hpass := grantChecks_pass h hbinding
  have hrange := hpass (input.state.core.mappings.any fun mapping =>
      decide (secondLevelEntryCount < mappingEndPage mapping), .grantOutOfRange)
    (by simp [grantChecks])
  have hempty := hpass (input.state.core.mappings.any fun mapping =>
      !mapping.permission.nonempty, .emptyGrantPermission) (by simp [grantChecks])
  simp only [List.any_eq_false, decide_eq_true_eq, Nat.not_lt, Bool.not_eq_true'] at hrange hempty
  have hend := hrange mapping hmem
  simp only [mappingCovers, Bool.and_eq_true, decide_eq_true_eq] at hcovers
  refine ⟨by omega, ?_⟩
  rw [hpermission]
  simpa using hempty mapping hmem

theorem grantedPage_none_of_large {input plan binding} (h : compile input = .ok plan)
    (hbinding : input.grantBinding = some binding) {page}
    (hlarge : secondLevelEntryCount ≤ page) : grantedPage input binding page = none := by
  cases hgrant : grantedPage input binding page with
  | none => rfl
  | some pair =>
      obtain ⟨frame, permission⟩ := pair
      have := (accepted_grant_pages_bounded h hbinding hgrant).1
      omega

theorem secondLevelPage_getElem? (index value position : Nat) :
    wordAt (secondLevelPage index value) position =
      if position < secondLevelEntryCount ∧ position = index then value else 0 := by
  unfold wordAt secondLevelPage
  by_cases hlt : position < secondLevelEntryCount
  · simp [hlt]
  · simp [hlt]

theorem decode_zero_secondLevel : decodeSecondLevelEntry 0 = none := by
  simp [decodeSecondLevelEntry]

theorem intersect_readWrite (permission : IOMMU.Permission) :
    intersectPermission IOMMU.readWrite (intersectPermission IOMMU.readWrite permission) =
      permission := by
  cases permission
  simp [intersectPermission, IOMMU.readWrite]

theorem walkSecondLevel_exact {input plan binding} (h : compile input = .ok plan)
    (hbinding : input.grantBinding = some binding) (page : Nat) :
    plan.walkSecondLevel plan.secondLevelRootWords page = grantedPage input binding page := by
  have hsource := compile_source h
  have hplan : plan.grantBinding = some binding := by
    simp [Plan.grantBinding, hsource, hbinding]
  have hnodup := accepted_table_frames_distinct input plan h
  simp only [tableFrames, hbinding, List.cons_append, List.nil_append, List.nodup_cons,
    List.mem_cons, List.not_mem_nil, or_false, not_or] at hnodup
  obtain ⟨_, _, ⟨hrootDir, hrootLeaf⟩, hdirLeaf, _⟩ := hnodup
  have hpage : pageBytes = 4096 := rfl
  have hentries : secondLevelEntryCount = 512 := rfl
  have hrw : IOMMU.readWrite.nonempty = true := rfl
  have hdirTable : plan.tableAt binding.secondLevelDirectoryFrame =
      some plan.secondLevelDirectoryWords := by
    simp [Plan.tableAt, hplan, Ne.symm hrootDir]
  have hleafTable : plan.tableAt binding.secondLevelTableFrame =
      some plan.secondLevelTableWords := by
    simp [Plan.tableAt, hplan, Ne.symm hrootLeaf, Ne.symm hdirLeaf]
  have hrootWords : plan.secondLevelRootWords =
      secondLevelPage 0 (secondLevelEntry binding.secondLevelDirectoryFrame IOMMU.readWrite) := by
    simp [Plan.secondLevelRootWords, hplan]
  have hdirectoryWords : plan.secondLevelDirectoryWords =
      secondLevelPage 0 (secondLevelEntry binding.secondLevelTableFrame IOMMU.readWrite) := by
    simp [Plan.secondLevelDirectoryWords, hplan]
  by_cases hsmall : page < secondLevelEntryCount
  · have htop : page / secondLevelEntryCount / secondLevelEntryCount = 0 := by
      rw [hentries] at hsmall ⊢; omega
    have hdir : page / secondLevelEntryCount % secondLevelEntryCount = 0 := by
      rw [hentries] at hsmall ⊢; omega
    have hleaf : page % secondLevelEntryCount = page := Nat.mod_eq_of_lt hsmall
    have hleafWord : wordAt plan.secondLevelTableWords page =
        leafEntryWord (grantedPage input binding page) := by
      simp [wordAt, Plan.secondLevelTableWords, hplan, hsource, hsmall]
    have hrootWord : wordAt plan.secondLevelRootWords
        (page / secondLevelEntryCount / secondLevelEntryCount) =
          secondLevelEntry binding.secondLevelDirectoryFrame IOMMU.readWrite := by
      rw [hrootWords, secondLevelPage_getElem?, ite_eq_left ⟨by rw [htop]; decide, htop⟩]
    have hdirWord : wordAt plan.secondLevelDirectoryWords
        (page / secondLevelEntryCount % secondLevelEntryCount) =
          secondLevelEntry binding.secondLevelTableFrame IOMMU.readWrite := by
      rw [hdirectoryWords, secondLevelPage_getElem?, ite_eq_left ⟨by rw [hdir]; decide, hdir⟩]
    cases hgrant : grantedPage input binding page with
    | none =>
        simp [Plan.walkSecondLevel, hrootWord, decode_secondLevelEntry _ _ hrw, hdirTable,
          hdirWord, hleafTable, hleaf, hleafWord, hgrant, leafEntryWord, decode_zero_secondLevel]
    | some pair =>
        obtain ⟨frame, permission⟩ := pair
        have hnonempty := (accepted_grant_pages_bounded h hbinding hgrant).2
        simp [Plan.walkSecondLevel, hrootWord, decode_secondLevelEntry _ _ hrw, hdirTable,
          hdirWord, hleafTable, hleaf, hleafWord, hgrant, leafEntryWord,
          decode_secondLevelEntry _ _ hnonempty, intersect_readWrite]
  · rw [grantedPage_none_of_large h hbinding (by omega)]
    by_cases htop : page / secondLevelEntryCount / secondLevelEntryCount = 0
    · have hdir : ¬page / secondLevelEntryCount % secondLevelEntryCount = 0 := by
        rw [hentries] at hsmall htop ⊢; omega
      have hrootWord : wordAt plan.secondLevelRootWords
          (page / secondLevelEntryCount / secondLevelEntryCount) =
            secondLevelEntry binding.secondLevelDirectoryFrame IOMMU.readWrite := by
        rw [hrootWords, secondLevelPage_getElem?, ite_eq_left ⟨by rw [htop]; decide, htop⟩]
      have hdirWord : wordAt plan.secondLevelDirectoryWords
          (page / secondLevelEntryCount % secondLevelEntryCount) = 0 := by
        rw [hdirectoryWords, secondLevelPage_getElem?, ite_eq_right (fun hcase => hdir hcase.2)]
      simp [Plan.walkSecondLevel, hrootWord, decode_secondLevelEntry _ _ hrw, hdirTable,
        hdirWord, decode_zero_secondLevel]
    · have hrootWord : wordAt plan.secondLevelRootWords
          (page / secondLevelEntryCount / secondLevelEntryCount) = 0 := by
        rw [hrootWords, secondLevelPage_getElem?, ite_eq_right (fun hcase => htop hcase.2)]
      simp [Plan.walkSecondLevel, hrootWord, decode_zero_secondLevel]

theorem pair_wordAt {α : Type} (entries : List α) (low high : α → Nat) (index : Nat) :
    wordAt (entries.flatMap fun entry => [low entry, high entry]) (2 * index) =
        (entries[index]?.map low).getD 0 ∧
      wordAt (entries.flatMap fun entry => [low entry, high entry]) (2 * index + 1) =
        (entries[index]?.map high).getD 0 := by
  obtain ⟨hlow, hhigh⟩ := pair_words_getElem? entries low high index
  exact ⟨by rw [wordAt, hlow], by rw [wordAt, hhigh]⟩

theorem context_word_decode (plan : Plan) (function : Nat) (entry : ContextEntry)
    (hentry : plan.contexts[function]? = some entry) (hencodable : ContextEntryEncodable entry) :
    decodeContextEntry (wordAt (contextTableWords plan) (2 * function))
        (wordAt (contextTableWords plan) (2 * function + 1)) = .ok entry := by
  obtain ⟨hlow, hhigh⟩ := pair_wordAt plan.contexts contextEntryLow contextEntryHigh function
  rw [contextTableWords, hlow, hhigh, hentry]
  exact decode_encode_context entry hencodable

theorem accepted_requester_bound {input plan binding} (h : compile input = .ok plan)
    (hbinding : input.grantBinding = some binding) :
    binding.requester < contextEntryCount := by
  have hrequester := grantChecks_pass h hbinding
    (decide (contextEntryCount ≤ binding.requester), .requesterOutOfRange)
    (by simp [grantChecks])
  simpa using hrequester

theorem accepted_assignment_domain_bound {input plan} (h : compile input = .ok plan) :
    assignmentDomain input < domainLimit := by
  have hdomain := checks_pass h (input.state.core.assignments.any fun assignment =>
      decide (domainLimit ≤ assignment.domain.slot), .domainOutOfRange) (by simp [checks])
  simp only [List.any_eq_false, decide_eq_true_eq, Nat.not_le] at hdomain
  unfold assignmentDomain
  cases hassignments : input.state.core.assignments with
  | nil => simp [domainLimit]
  | cons head tail => simpa using hdomain head (by simp [hassignments])

/-- **The compiled tables translate exactly the granted pages.**  For every
requester and every IOVA page, walking the encoded root, context, and
second-level words of an accepted plan yields exactly the granted hardware
frame and permission, and nothing where nothing was granted: only the bound
requester translates at all, only the assignment's granted pages, and each at
the frame and permission the accepted model mapping names.  A deny-all plan
translates nothing for anyone.  This is about the encoded tables, not the
IOMMU's table walk. -/
theorem accepted_translation_exact input plan (h : compile input = .ok plan)
    (requester page : Nat) :
    plan.translate requester page = grantedTranslation input requester page := by
  have hsource := compile_source h
  have hbounded := accepted_table_frames_bounded input plan h
  have hcontextBound := hbounded input.contextTableFrame (by simp [tableFrames])
  have hcount : contextEntryCount = 256 := rfl
  have hrootCount : rootEntryCount = 256 := rfl
  obtain ⟨hrootLow, hrootHigh⟩ :=
    pair_wordAt plan.roots rootEntryLow (fun _ => 0) (requester / contextEntryCount)
  by_cases hbus : requester / contextEntryCount = 0
  · have hrootEntry : plan.roots[requester / contextEntryCount]? =
        some { present := true, contextTableFrame := plan.contextFrame } := by
      simp [Plan.roots, canonicalRootEntries, hbus, hrootCount]
    have hencodable : RootEntryEncodable
        { present := true, contextTableFrame := plan.contextFrame } := by
      simp only [frameBounded, Bool.and_eq_true, decide_eq_true_eq] at hcontextBound
      simpa [RootEntryEncodable, Plan.contextFrame, hsource] using hcontextBound
    have hrootDecode : decodeRootEntry
        (wordAt (rootTableWords plan) (2 * (requester / contextEntryCount)))
        (wordAt (rootTableWords plan) (2 * (requester / contextEntryCount) + 1)) =
          .ok { present := true, contextTableFrame := plan.contextFrame } := by
      rw [rootTableWords, hrootLow, hrootHigh, hrootEntry]
      exact decode_encode_root _ hencodable
    have hfunction : requester % contextEntryCount = requester := by
      rw [hcount] at hbus ⊢; omega
    have hrequesterSmall : requester < contextEntryCount := by rw [hcount] at hbus ⊢; omega
    have habsentEncodable : ContextEntryEncodable absentContextEntry := by
      simp [ContextEntryEncodable, absentContextEntry]
    unfold Plan.translate
    dsimp only
    rw [hrootDecode]
    simp only [Bool.true_eq_false, ne_eq, not_true_eq_false, or_self, ↓reduceIte]
    rw [hfunction]
    cases hbinding : input.grantBinding with
    | none =>
        have habsent := accepted_context_entries_absent input plan h hbinding
        have hentry : plan.contexts[requester]? = some absentContextEntry := by
          simp [habsent, hrequesterSmall]
        rw [context_word_decode plan requester _ hentry habsentEncodable]
        simp [absentContextEntry, grantedTranslation, hbinding]
    | some binding =>
        have hplan : plan.grantBinding = some binding := by
          simp [Plan.grantBinding, hsource, hbinding]
        by_cases hbound : requester = binding.requester
        · subst hbound
          have hentry : plan.contexts[binding.requester]? = some
              { present := true, domain := assignmentDomain input,
                addressWidth := addressWidthEncoding,
                secondLevelFrame := binding.secondLevelRootFrame } := by
            simp [Plan.contexts, compiledContextEntries, hsource, hbinding, hrequesterSmall]
          have hrootFrame := hbounded binding.secondLevelRootFrame
            (by simp [tableFrames, hbinding])
          have hencodableContext : ContextEntryEncodable
              { present := true, domain := assignmentDomain input,
                addressWidth := addressWidthEncoding,
                secondLevelFrame := binding.secondLevelRootFrame } := by
            simp only [frameBounded, Bool.and_eq_true, decide_eq_true_eq] at hrootFrame
            simpa [ContextEntryEncodable, hrootFrame] using
              accepted_assignment_domain_bound h
          have htop : plan.tableAt binding.secondLevelRootFrame =
              some plan.secondLevelRootWords := by
            simp [Plan.tableAt, hplan]
          rw [context_word_decode plan _ _ hentry hencodableContext]
          simp only [Bool.true_eq_false, ite_false, htop]
          simpa [grantedTranslation, hbinding] using walkSecondLevel_exact h hbinding page
        · have hentry : plan.contexts[requester]? = some absentContextEntry := by
            simp [Plan.contexts, compiledContextEntries, hsource, hbinding, hrequesterSmall,
              hbound]
          rw [context_word_decode plan requester _ hentry habsentEncodable]
          simp [absentContextEntry, grantedTranslation, hbinding, hbound]
  · have hrootWord : (plan.roots[requester / contextEntryCount]?.map rootEntryLow).getD 0 = 0 := by
      by_cases hrange : requester / contextEntryCount < rootEntryCount
      · simp [Plan.roots, canonicalRootEntries, hbus, hrange, absentRootEntry, rootEntryLow]
      · simp [Plan.roots, canonicalRootEntries, hrange]
    have hspec : grantedTranslation input requester page = none := by
      unfold grantedTranslation
      split
      · rfl
      next binding hbinding =>
        have := accepted_requester_bound h hbinding
        rw [ite_eq_right_iff.mpr (fun hequal => absurd hequal (by rw [hcount] at hbus this; omega))]
    have hhighZero : (plan.roots[requester / contextEntryCount]?.map
        (fun _ => (0 : Nat))).getD 0 = 0 := by
      cases plan.roots[requester / contextEntryCount]? <;> rfl
    rw [hspec]
    simp [Plan.translate, rootTableWords, hrootLow, hrootHigh, hrootWord, hhighZero,
      decodeRootEntry, absentRootEntry]

/-- Without a grant binding the encoded tables translate nothing for anyone. -/
theorem accepted_unbound_translates_nothing input plan (h : compile input = .ok plan)
    (hunbound : input.grantBinding = none) (requester page : Nat) :
    plan.translate requester page = none := by
  rw [accepted_translation_exact input plan h]
  simp [grantedTranslation, hunbound]

theorem translation_grant {input plan} (h : compile input = .ok plan)
    {requester page frame permission}
    (htranslate : plan.translate requester page = some (frame, permission)) :
    ∃ binding, input.grantBinding = some binding ∧ requester = binding.requester ∧
      grantedPage input binding page = some (frame, permission) := by
  rw [accepted_translation_exact input plan h] at htranslate
  unfold grantedTranslation at htranslate
  split at htranslate
  · contradiction
  next binding hbinding =>
    split at htranslate
    next hrequester => exact ⟨binding, hbinding, hrequester, htranslate⟩
    · contradiction

/-- Every translation the encoded tables yield comes from one accepted model
mapping: the bound requester, a page inside the mapping's IOVA range, the
mapping's own permission, and the frame its model offset names. -/
theorem accepted_translation_from_grant input plan (h : compile input = .ok plan)
    {requester page frame permission}
    (htranslate : plan.translate requester page = some (frame, permission)) :
    ∃ binding, input.grantBinding = some binding ∧ requester = binding.requester ∧
      ∃ mapping ∈ input.state.core.mappings, mappingCovers mapping page = true ∧
        permission = mapping.permission ∧
        ∃ base, mappingBase binding mapping = some base ∧
          frame = mappingFrame base mapping page := by
  obtain ⟨binding, hbinding, hrequester, hgrant⟩ := translation_grant h htranslate
  exact ⟨binding, hbinding, hrequester, grantedPage_some hgrant⟩

/-- No translation reaches a protected frame: every translated frame is in
range and outside the kernel reservations, the CPU page tables, and the VT-d
tables themselves. -/
theorem accepted_translation_avoids_protected input plan (h : compile input = .ok plan)
    {requester page frame permission}
    (htranslate : plan.translate requester page = some (frame, permission)) :
    frameBounded frame = true ∧ protectedFrame input frame = false := by
  obtain ⟨binding, hbinding, _, hgrant⟩ := translation_grant h htranslate
  have hsmall := (accepted_grant_pages_bounded h hbinding hgrant).1
  have hpass := grantChecks_pass h hbinding
  have hbounded := hpass ((List.range secondLevelEntryCount).any fun page =>
      match grantedPage input binding page with
      | none => false
      | some (frame, _) => !frameBounded frame, .frameOutOfRange) (by simp [grantChecks])
  have hprotected := hpass ((List.range secondLevelEntryCount).any fun page =>
      match grantedPage input binding page with
      | none => false
      | some (frame, _) => protectedFrame input frame, .grantOverlapsReservedFrame)
    (by simp [grantChecks])
  simp only [List.any_eq_false, List.mem_range] at hbounded hprotected
  have hpageBounded := hbounded page hsmall
  have hpageProtected := hprotected page hsmall
  rw [hgrant] at hpageBounded hpageProtected
  simp only [Bool.not_eq_true, Bool.not_eq_false'] at hpageBounded hpageProtected
  exact ⟨by simpa using hpageBounded, by simpa using hpageProtected⟩

/-- Every granted page translates for the bound requester. -/
theorem accepted_grant_translates input plan (h : compile input = .ok plan)
    {binding} (hbinding : input.grantBinding = some binding)
    {mapping page} (hmapping : mapping ∈ input.state.core.mappings)
    (hcovers : mappingCovers mapping page = true) :
    (plan.translate binding.requester page).isSome = true := by
  rw [accepted_translation_exact input plan h]
  simp only [grantedTranslation, hbinding, ↓reduceIte]
  unfold grantedPage
  obtain ⟨found, hfound⟩ := Option.isSome_iff_exists.mp
    (List.find?_isSome.mpr ⟨mapping, hmapping, hcovers⟩ :
      (input.state.core.mappings.find? (mappingCovers · page)).isSome = true)
  have hunbound := grantChecks_pass h hbinding
    (input.state.core.mappings.any fun mapping => (mappingBase binding mapping).isNone,
      .unboundGrantFrame) (by simp [grantChecks])
  simp only [List.any_eq_false, Option.isNone_iff_eq_none] at hunbound
  have hbase := hunbound found (List.mem_of_find?_eq_some hfound)
  rw [hfound]
  cases hlookup : mappingBase binding found with
  | none => exact absurd hlookup hbase
  | some base => simp [hlookup]

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

/-! ## Device-service xHCI assignment (issue #449)

The device-service image assigns q35 `qemu-xhci` at 00:02.0 through the same
requester slot (16) and second-level table storage as the assigned-EDU image.
Its authority is one read/write mapping of four model pages, IOVA `[64, 128)`,
which the generated hardware projection scales to IOVA `[16 KiB, 32 KiB)` over
the four 4 KiB pages at the start of the device executor's scratch: the `qemu`
layout of `LeanOS.Usb.Xhci` keeps every structure the controller reads or
writes inside them. The window starts above zero because the xHCI program
reads a zero bus address as "no DMA". -/

def deviceServiceTopologyVersion : UInt64 := 0x0001000800020004

def deviceServiceGrant : IOMMU.GrantRequest :=
  ⟨IOMMU.assignment0, ⟨0, 1⟩, 4 * IOMMU.pageSize, 0, 4 * IOMMU.pageSize, IOMMU.readWrite⟩

/-- The one reviewed device-service assignment and its read/write window.
Table generation reads this state; nothing in the image supplies authority. -/
def deviceServiceState : IOMMU.State :=
  (IOMMU.gate IOMMU.assignedState (.grant deviceServiceGrant)).state

/-- Transfer admission over `deviceServiceState`: 0 accepted, 3 stale or
foreign assignment, 4 outside the window, 5 permission, 6 stale frame, 7
other. Direction 1 is a device read, 2 a device write. -/
def validateDeviceServiceTransfer
    (source assignmentGeneration iova length direction : Nat) : Nat :=
  let request : IOMMU.TransferRequest := ⟨source, assignmentGeneration, iova, length⟩
  let result := IOMMU.translate deviceServiceState request
    (if direction == 1 then .read else .write)
  if direction != 1 && direction != 2 then 2
  else match result with
    | .ok _ => 0
    | .error .staleAssignment => 3
    | .error .invalidRange => 4
    | .error .permissionDenied => 5
    | .error .staleFrame => 6
    | .error _ => 7

/-- The grant is accepted and is the only mapping: one assignment (device 0,
source 0, domain 0) holding IOVA `[64, 128)` read/write at frame 0, offset 0. -/
theorem deviceServiceState_shape :
    deviceServiceState.core.assignments.map (fun a => (a.device, a.source, a.domain.slot)) =
        [(0, 0, 0)] ∧
    deviceServiceState.core.mappings.map
        (fun m => (m.iova, m.length, m.frame.frame, m.frameOffset, m.permission)) =
      [(64, 64, 0, 0, IOMMU.readWrite)] := by
  native_decide

/-- Both directions are admitted anywhere inside the window, and nothing
outside it or from another source is. -/
theorem deviceServiceTransfer_window :
    validateDeviceServiceTransfer 0 1 64 64 1 = 0 ∧
    validateDeviceServiceTransfer 0 1 64 64 2 = 0 ∧
    validateDeviceServiceTransfer 0 1 112 16 2 = 0 ∧
    validateDeviceServiceTransfer 0 1 112 32 1 = 4 ∧
    validateDeviceServiceTransfer 0 1 0 16 2 = 4 ∧
    validateDeviceServiceTransfer 0 1 128 16 2 = 4 ∧
    validateDeviceServiceTransfer 1 1 64 16 1 = 3 ∧
    validateDeviceServiceTransfer 0 2 64 16 1 = 3 := by
  native_decide

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
    .missingGrantBinding = true := by native_decide
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

/-! Assigned vectors: the sample manifest reserves frames 2-9 inside the
loaded image (8 and 9 hold the root and context tables) and frames 10-31 as
CPU page tables; frame 40 lies outside every reservation. -/

def sampleGrantBinding : GrantBinding :=
  { requester := 16, secondLevelRootFrame := 2, secondLevelDirectoryFrame := 3,
    secondLevelTableFrame := 4, frameBases := [(0, 40)] }

def sampleAssignedInput : Input :=
  { sampleInput with state := assignedEDUState, grantBinding := some sampleGrantBinding }

def sampleTranslate (input : Input) (requester page : Nat) :
    Option (Nat × IOMMU.Permission) :=
  match compile input with
  | .ok plan => plan.translate requester page
  | .error _ => none

def withFrameBase (base : Nat) : Input :=
  { sampleAssignedInput with
    grantBinding := some { sampleGrantBinding with frameBases := [(0, base)] } }

example : (match compile sampleAssignedInput with
    | .ok _ => true | .error _ => false) = true := by native_decide
/-- The read page and the write page translate with their own permission. -/
example : sampleTranslate sampleAssignedInput 16 0 = some (40, IOMMU.readOnly) := by
  native_decide
example : sampleTranslate sampleAssignedInput 16 1 = some (41, IOMMU.writeOnly) := by
  native_decide
/-- Nothing else translates: the next page, a neighbouring function, and the
same function on another bus. -/
example : sampleTranslate sampleAssignedInput 16 2 = none := by native_decide
example : sampleTranslate sampleAssignedInput 17 0 = none := by native_decide
example : sampleTranslate sampleAssignedInput (256 + 16) 0 = none := by native_decide
/-- The device-service window: model IOVA `[64, 128)` is pages 4 to 7. -/
example : sampleTranslate { sampleAssignedInput with state := deviceServiceState } 16 4 =
    some (40, IOMMU.readWrite) := by native_decide
example : sampleTranslate { sampleAssignedInput with state := deviceServiceState } 16 7 =
    some (43, IOMMU.readWrite) := by native_decide
example : sampleTranslate { sampleAssignedInput with state := deviceServiceState } 16 3 =
    none := by native_decide
example : sampleTranslate { sampleAssignedInput with state := deviceServiceState } 16 8 =
    none := by native_decide

/-- A grant overlapping a CPU page-table frame. -/
example : rejectedAs (withFrameBase 10) .grantOverlapsReservedFrame = true := by native_decide
/-- A grant overlapping a kernel-stack reservation. -/
example : rejectedAs (withFrameBase 4) .grantOverlapsReservedFrame = true := by native_decide
/-- A grant overlapping the VT-d root table itself. -/
example : rejectedAs (withFrameBase 8) .grantOverlapsReservedFrame = true := by native_decide
/-- A grant on frames 1 and 2: the boot-information reservation and the
second-level top table. -/
example : rejectedAs (withFrameBase 1) .grantOverlapsReservedFrame = true := by native_decide
example : rejectedAs (withFrameBase 0) .frameOutOfRange = true := by native_decide
example : rejectedAs { sampleAssignedInput with
    grantBinding := some { sampleGrantBinding with frameBases := [(1, 40)] } }
    .unboundGrantFrame = true := by native_decide
example : rejectedAs { sampleAssignedInput with
    grantBinding := some { sampleGrantBinding with requester := 256 } }
    .requesterOutOfRange = true := by native_decide
example : rejectedAs { sampleAssignedInput with
    grantBinding := some { sampleGrantBinding with secondLevelDirectoryFrame := 2 } }
    .duplicateTableFrame = true := by native_decide
example : rejectedAs { sampleAssignedInput with
    grantBinding := some { sampleGrantBinding with secondLevelTableFrame := 12 } }
    .tableAliasesCpuTables = true := by native_decide
example : rejectedAs { sampleAssignedInput with
    grantBinding := some { sampleGrantBinding with secondLevelTableFrame := 35 } }
    .unreservedTableFrame = true := by native_decide
example : rejectedAs { sampleAssignedInput with state := IOMMU.emptyState }
    .unexpectedGrantBinding = true := by native_decide

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
