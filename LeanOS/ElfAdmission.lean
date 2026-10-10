import LeanOS.BootPageTablePlan

/-!
# Build-time ELF64 admission for one pre-admitted subject (issue #492)

The build links one subject from `subjects/` (the #484 rule) into a separate
statically linked x86-64 executable, and this module decides whether that file
may be placed in the boot image's reserved frames as a future loader's input.

The checker is pure and total.  `parse` reads a fixed set of little-endian
fields at fixed offsets from a `ByteArray` (a missing byte reads as zero, so a
short file parses to a candidate that the checks then reject); it never
follows a pointer other than the program-header table offset, and it reads at
most `maxProgramHeaders` program headers.  `check` then tests a finite list of
typed rejection reasons, in a fixed priority order, and returns either the
first one that holds or the admitted plan.

The admitted plan is not a summary chosen by the checker: it is exactly the
file's `PT_LOAD` headers, in file order, projected to (virtual address, memory
size, file offset, file size, permissions), plus the entry point and the file
size (`check_ok_iff`, `admit_plan_exact`).  Every listed property of an
admitted file is a theorem below, every rejection names a check that really
fails (`check_error_sound`), and every candidate is either admitted or
rejected for a listed reason (`check_total`, `Rejection.mem_all`).

`place` binds an admitted plan to the frame range the image reserved for the
file and proves every segment's source bytes lie inside that range and inside
the enclosing embedded-user reservation.

Trusted, not proved: that `parse` matches the ELF64 specification's field
offsets, that the linker and `objcopy` place exactly these bytes in the
reserved range, and that the boot loader loads them unchanged.  The build
re-reads the bytes from the linked kernel image and re-runs this checker over
them (`scripts/check-admitted-subject.py`).  Nothing here loads, maps, or runs
the subject: the run-time loader is gated by ADR 0010.
-/
namespace LeanOS.ElfAdmission

/-! ## Fixed constants of the admission policy -/

def pageBytes : Nat := 4096

def elfMagic : Nat := 0x464C457F
def elfClass64 : Nat := 2
def elfDataLittleEndian : Nat := 1
def elfVersionCurrent : Nat := 1
def elfTypeExecutable : Nat := 2
def elfMachineX86_64 : Nat := 62
def elfHeaderBytes : Nat := 64
def programHeaderBytes : Nat := 56

def segmentLoad : Nat := 1
def segmentGnuStack : Nat := 0x6474E551

def flagExecute : Nat := 1
def flagWrite : Nat := 2
def flagRead : Nat := 4

/-- At most this many program headers, of every type. -/
def maxProgramHeaders : Nat := 8
/-- At most this many bytes of memory per loadable segment (16 pages). -/
def maxSegmentBytes : Nat := 16 * pageBytes
/-- At most this many bytes of file: the reserved frame range is bounded. -/
def maxFileBytes : Nat := 64 * pageBytes

/-- The admitted user window: 2 MiB starting at the first page the boot page
plan does not map (`userWindow_above_boot_plan`), so a future child address
space can hold the admitted segments without aliasing a boot mapping. -/
def userWindowStart : Nat := BootPageTablePlan.supportedPathPages * pageBytes
def userWindowBytes : Nat := 512 * pageBytes
def userWindowEnd : Nat := userWindowStart + userWindowBytes

/-! ## Parsing: fixed little-endian fields at fixed offsets -/

def byteAt (bytes : ByteArray) (offset : Nat) : Nat :=
  (bytes[offset]?.getD 0).toNat

/-- `width` little-endian bytes starting at `offset`; missing bytes read 0. -/
def readLE (bytes : ByteArray) (offset : Nat) : Nat → Nat
  | 0 => 0
  | width + 1 => byteAt bytes offset + 256 * readLE bytes (offset + 1) width

structure ProgramHeader where
  type : Nat
  flags : Nat
  offset : Nat
  vaddr : Nat
  fileBytes : Nat
  memBytes : Nat
  deriving DecidableEq, Repr, Inhabited

/-- The header fields the policy reads, and the first
`min phnum maxProgramHeaders` program headers. -/
structure Candidate where
  fileSize : Nat
  magic : Nat
  elfClass : Nat
  dataEncoding : Nat
  identVersion : Nat
  type : Nat
  machine : Nat
  version : Nat
  entry : Nat
  phoff : Nat
  ehsize : Nat
  phentsize : Nat
  phnum : Nat
  programHeaders : List ProgramHeader
  deriving DecidableEq, Repr

def parseProgramHeader (bytes : ByteArray) (base : Nat) : ProgramHeader :=
  { type := readLE bytes base 4, flags := readLE bytes (base + 4) 4,
    offset := readLE bytes (base + 8) 8, vaddr := readLE bytes (base + 16) 8,
    fileBytes := readLE bytes (base + 32) 8, memBytes := readLE bytes (base + 40) 8 }

def parse (bytes : ByteArray) : Candidate :=
  let phoff := readLE bytes 32 8
  let phnum := readLE bytes 56 2
  { fileSize := bytes.size, magic := readLE bytes 0 4, elfClass := byteAt bytes 4,
    dataEncoding := byteAt bytes 5, identVersion := byteAt bytes 6,
    type := readLE bytes 16 2, machine := readLE bytes 18 2,
    version := readLE bytes 20 4, entry := readLE bytes 24 8, phoff,
    ehsize := readLE bytes 52 2, phentsize := readLE bytes 54 2, phnum,
    programHeaders := (List.range (min phnum maxProgramHeaders)).map fun index =>
      parseProgramHeader bytes (phoff + index * programHeaderBytes) }

/-! ## Segments and the admitted plan -/

structure Segment where
  vaddr : Nat
  memBytes : Nat
  fileOffset : Nat
  fileBytes : Nat
  readable : Bool
  writable : Bool
  executable : Bool
  deriving DecidableEq, Repr

def flagSet (flags bit : Nat) : Bool := flags / bit % 2 == 1

def ProgramHeader.toSegment (header : ProgramHeader) : Segment :=
  { vaddr := header.vaddr, memBytes := header.memBytes, fileOffset := header.offset,
    fileBytes := header.fileBytes, readable := flagSet header.flags flagRead,
    writable := flagSet header.flags flagWrite,
    executable := flagSet header.flags flagExecute }

def loadHeaders (candidate : Candidate) : List ProgramHeader :=
  candidate.programHeaders.filter (·.type == segmentLoad)

def segments (candidate : Candidate) : List Segment :=
  (loadHeaders candidate).map ProgramHeader.toSegment

/-- The page-rounded end of a segment's memory image. -/
def Segment.pageEnd (segment : Segment) : Nat :=
  (segment.vaddr + segment.memBytes + pageBytes - 1) / pageBytes * pageBytes

/-- Two segments share no page. -/
def Segment.Disjoint (left right : Segment) : Prop :=
  left.pageEnd ≤ right.vaddr ∨ right.pageEnd ≤ left.vaddr

def Segment.disjoint (left right : Segment) : Bool :=
  decide (left.pageEnd ≤ right.vaddr) || decide (right.pageEnd ≤ left.vaddr)

def pairwiseDisjoint : List Segment → Bool
  | [] => true
  | segment :: rest => rest.all (segment.disjoint ·) && pairwiseDisjoint rest

/-- The entry point lies in the file-backed bytes of an executable segment. -/
def Segment.holdsEntry (segment : Segment) (entry : Nat) : Bool :=
  segment.executable && decide (segment.vaddr ≤ entry) &&
    decide (entry < segment.vaddr + segment.fileBytes)

structure Plan where
  fileBytes : Nat
  entry : Nat
  segments : List Segment
  deriving DecidableEq, Repr

def planOf (candidate : Candidate) : Plan :=
  { fileBytes := candidate.fileSize, entry := candidate.entry,
    segments := segments candidate }

/-! ## Typed rejection reasons -/

inductive Rejection where
  | truncatedHeader | badMagic | notElf64 | notLittleEndian | badVersion
  | notExecutable | wrongMachine | badHeaderLayout | tooManyProgramHeaders
  | truncatedProgramHeaders | fileTooLarge | unsupportedSegmentType
  | unknownSegmentFlags | noLoadSegment | misalignedSegment | writableExecutable
  | oversizeSegment | segmentOutsideFile | outsideUserRange | overlappingSegments
  | entryOutsideText
  deriving DecidableEq, Repr

/-- Every reason, in the order `check` tests them. -/
def Rejection.all : List Rejection :=
  [.truncatedHeader, .badMagic, .notElf64, .notLittleEndian, .badVersion,
   .notExecutable, .wrongMachine, .badHeaderLayout, .tooManyProgramHeaders,
   .truncatedProgramHeaders, .fileTooLarge, .unsupportedSegmentType,
   .unknownSegmentFlags, .noLoadSegment, .misalignedSegment, .writableExecutable,
   .oversizeSegment, .segmentOutsideFile, .outsideUserRange, .overlappingSegments,
   .entryOutsideText]

def Rejection.name : Rejection → String
  | .truncatedHeader => "truncated-header"
  | .badMagic => "bad-magic"
  | .notElf64 => "not-elf64"
  | .notLittleEndian => "not-little-endian"
  | .badVersion => "bad-version"
  | .notExecutable => "not-executable"
  | .wrongMachine => "wrong-machine"
  | .badHeaderLayout => "bad-header-layout"
  | .tooManyProgramHeaders => "too-many-program-headers"
  | .truncatedProgramHeaders => "truncated-program-headers"
  | .fileTooLarge => "file-too-large"
  | .unsupportedSegmentType => "unsupported-segment-type"
  | .unknownSegmentFlags => "unknown-segment-flags"
  | .noLoadSegment => "no-load-segment"
  | .misalignedSegment => "misaligned-segment"
  | .writableExecutable => "writable-executable"
  | .oversizeSegment => "oversize-segment"
  | .segmentOutsideFile => "segment-outside-file"
  | .outsideUserRange => "outside-user-range"
  | .overlappingSegments => "overlapping-segments"
  | .entryOutsideText => "entry-outside-text"

/-- A supported program header: a load segment, or a non-executable
`PT_GNU_STACK` marker that loads nothing. -/
def supportedHeader (header : ProgramHeader) : Bool :=
  header.type == segmentLoad ||
    (header.type == segmentGnuStack && !flagSet header.flags flagExecute)

/-- `violates reason candidate` holds exactly when the check named by
`reason` fails for `candidate`. -/
def violates : Rejection → Candidate → Bool
  | .truncatedHeader, c => decide (c.fileSize < elfHeaderBytes)
  | .badMagic, c => c.magic != elfMagic
  | .notElf64, c => c.elfClass != elfClass64
  | .notLittleEndian, c => c.dataEncoding != elfDataLittleEndian
  | .badVersion, c => c.identVersion != elfVersionCurrent || c.version != elfVersionCurrent
  | .notExecutable, c => c.type != elfTypeExecutable
  | .wrongMachine, c => c.machine != elfMachineX86_64
  | .badHeaderLayout, c => c.ehsize != elfHeaderBytes || c.phentsize != programHeaderBytes
  | .tooManyProgramHeaders, c =>
      decide (c.phnum > maxProgramHeaders) || decide (c.programHeaders.length > maxProgramHeaders)
  | .truncatedProgramHeaders, c =>
      decide (c.phoff + c.phnum * programHeaderBytes > c.fileSize)
  | .fileTooLarge, c => decide (c.fileSize > maxFileBytes)
  | .unsupportedSegmentType, c => c.programHeaders.any (!supportedHeader ·)
  | .unknownSegmentFlags, c => c.programHeaders.any (decide <| ·.flags ≥ 8)
  | .noLoadSegment, c => (segments c).isEmpty
  | .misalignedSegment, c => (segments c).any fun s =>
      s.vaddr % pageBytes != 0 || s.fileOffset % pageBytes != 0
  | .writableExecutable, c => (segments c).any fun s => s.writable && s.executable
  | .oversizeSegment, c => (segments c).any fun s =>
      s.memBytes == 0 || decide (s.memBytes > maxSegmentBytes) ||
        decide (s.fileBytes > s.memBytes)
  | .segmentOutsideFile, c => (segments c).any fun s =>
      decide (s.fileOffset + s.fileBytes > c.fileSize)
  | .outsideUserRange, c => (segments c).any fun s =>
      decide (s.vaddr < userWindowStart) || decide (s.vaddr + s.memBytes > userWindowEnd)
  | .overlappingSegments, c => !pairwiseDisjoint (segments c)
  | .entryOutsideText, c => !(segments c).any (·.holdsEntry c.entry)

def firstRejection (candidate : Candidate) : Option Rejection :=
  Rejection.all.find? (violates · candidate)

def check (candidate : Candidate) : Except Rejection Plan :=
  match firstRejection candidate with
  | some reason => .error reason
  | none => .ok (planOf candidate)

def admit (bytes : ByteArray) : Except Rejection Plan := check (parse bytes)

/-! ## Exhaustiveness and soundness of the rejection reasons -/

/-- The reason list names every rejection reason. -/
theorem Rejection.mem_all (reason : Rejection) : reason ∈ Rejection.all := by
  cases reason <;> simp [Rejection.all]

theorem firstRejection_none_iff (candidate : Candidate) :
    firstRejection candidate = none ↔ ∀ reason, violates reason candidate = false := by
  unfold firstRejection
  rw [List.find?_eq_none]
  constructor
  · intro h reason
    simpa using h reason (Rejection.mem_all reason)
  · intro h reason _
    simp [h reason]

/-- A candidate is admitted exactly when no listed check fails, and then the
plan is exactly `planOf` the candidate. -/
theorem check_ok_iff (candidate : Candidate) (plan : Plan) :
    check candidate = .ok plan ↔
      (∀ reason, violates reason candidate = false) ∧ plan = planOf candidate := by
  unfold check
  rw [← firstRejection_none_iff]
  cases firstRejection candidate with
  | some reason => simp
  | none => simp [eq_comm]

/-- Soundness: a reported rejection names a check that really fails. -/
theorem check_error_sound (candidate : Candidate) (reason : Rejection)
    (h : check candidate = .error reason) : violates reason candidate = true := by
  unfold check at h
  cases hfirst : firstRejection candidate with
  | none => simp [hfirst] at h
  | some found =>
    simp only [hfirst, Except.error.injEq] at h
    subst h
    unfold firstRejection at hfirst
    have hfound := List.find?_some hfirst
    exact hfound

/-- Exhaustiveness: every candidate is admitted with its exact plan, or
rejected for a listed reason whose check fails. -/
theorem check_total (candidate : Candidate) :
    check candidate = .ok (planOf candidate) ∨
      ∃ reason, check candidate = .error reason ∧ violates reason candidate = true := by
  cases h : check candidate with
  | ok plan =>
    left
    rw [(check_ok_iff candidate plan).mp h |>.2]
  | error reason =>
    right
    exact ⟨reason, rfl, check_error_sound candidate reason h⟩

/-- The admitted plan of a file is exactly its `PT_LOAD` headers, in file
order, projected to address, sizes, offset and permissions, plus its entry
point and size. -/
theorem admit_plan_exact (bytes : ByteArray) (plan : Plan)
    (h : admit bytes = .ok plan) :
    plan.fileBytes = bytes.size ∧ plan.entry = (parse bytes).entry ∧
      plan.segments = ((parse bytes).programHeaders.filter (·.type == segmentLoad)).map
        ProgramHeader.toSegment := by
  have hplan := ((check_ok_iff _ plan).mp h).2
  subst hplan
  exact ⟨rfl, rfl, rfl⟩

/-! ## Each listed property of an admitted file -/

section Admitted

variable {candidate : Candidate} {plan : Plan}

theorem admitted_no_violation (h : check candidate = .ok plan) (reason : Rejection) :
    violates reason candidate = false :=
  ((check_ok_iff candidate plan).mp h).1 reason

theorem admitted_plan (h : check candidate = .ok plan) : plan = planOf candidate :=
  ((check_ok_iff candidate plan).mp h).2

/-- ELF header sanity: a whole 64-byte header, the ELF magic, 64-bit class,
little-endian data, current version, an x86-64 executable, and the standard
header and program-header entry sizes. -/
theorem admitted_header (h : check candidate = .ok plan) :
    elfHeaderBytes ≤ candidate.fileSize ∧ candidate.magic = elfMagic ∧
      candidate.elfClass = elfClass64 ∧ candidate.dataEncoding = elfDataLittleEndian ∧
      candidate.identVersion = elfVersionCurrent ∧ candidate.version = elfVersionCurrent ∧
      candidate.type = elfTypeExecutable ∧ candidate.machine = elfMachineX86_64 ∧
      candidate.ehsize = elfHeaderBytes ∧ candidate.phentsize = programHeaderBytes := by
  have h1 := admitted_no_violation h .truncatedHeader
  have h2 := admitted_no_violation h .badMagic
  have h3 := admitted_no_violation h .notElf64
  have h4 := admitted_no_violation h .notLittleEndian
  have h5 := admitted_no_violation h .badVersion
  have h6 := admitted_no_violation h .notExecutable
  have h7 := admitted_no_violation h .wrongMachine
  have h8 := admitted_no_violation h .badHeaderLayout
  simp only [violates, decide_eq_false_iff_not, Nat.not_lt, bne_eq_false_iff_eq,
    Bool.or_eq_false_iff] at h1 h2 h3 h4 h5 h6 h7 h8
  exact ⟨h1, h2, h3, h4, h5.1, h5.2, h6, h7, h8.1, h8.2⟩

/-- The program-header table is bounded, lies inside the file, and yields at
least one and at most `maxProgramHeaders` load segments; the file itself is
bounded. -/
theorem admitted_program_headers_bounded (h : check candidate = .ok plan) :
    candidate.phnum ≤ maxProgramHeaders ∧
      candidate.phoff + candidate.phnum * programHeaderBytes ≤ candidate.fileSize ∧
      plan.fileBytes ≤ maxFileBytes ∧ plan.segments ≠ [] ∧
      plan.segments.length ≤ maxProgramHeaders := by
  have hplan := admitted_plan h
  have h1 := admitted_no_violation h .tooManyProgramHeaders
  have h2 := admitted_no_violation h .truncatedProgramHeaders
  have h3 := admitted_no_violation h .fileTooLarge
  have h4 := admitted_no_violation h .noLoadSegment
  simp only [violates, decide_eq_false_iff_not, Nat.not_lt, gt_iff_lt,
    List.isEmpty_eq_false_iff, Bool.or_eq_false_iff] at h1 h2 h3 h4
  subst hplan
  refine ⟨h1.1, h2, h3, h4, ?_⟩
  simp only [planOf, segments, loadHeaders, List.length_map]
  exact Nat.le_trans (List.length_filter_le _ _) h1.2

/-- Every admitted segment starts on a page boundary in memory and in the
file, so it can be mapped from page-aligned reserved frames. -/
theorem admitted_segments_aligned (h : check candidate = .ok plan) :
    ∀ segment ∈ plan.segments,
      segment.vaddr % pageBytes = 0 ∧ segment.fileOffset % pageBytes = 0 := by
  have hv := admitted_no_violation h .misalignedSegment
  rw [admitted_plan h]
  intro segment hmem
  simp only [violates, List.any_eq_false] at hv
  have := hv segment hmem
  simp_all

/-- No admitted segment is both writable and executable. -/
theorem admitted_no_writable_executable (h : check candidate = .ok plan) :
    ∀ segment ∈ plan.segments, ¬(segment.writable = true ∧ segment.executable = true) := by
  have hv := admitted_no_violation h .writableExecutable
  rw [admitted_plan h]
  intro segment hmem
  simp only [violates, List.any_eq_false] at hv
  have := hv segment hmem
  simp_all

/-- Every admitted segment occupies between one byte and `maxSegmentBytes`
of memory, and its file image is no larger than its memory image. -/
theorem admitted_segment_sizes (h : check candidate = .ok plan) :
    ∀ segment ∈ plan.segments,
      0 < segment.memBytes ∧ segment.memBytes ≤ maxSegmentBytes ∧
        segment.fileBytes ≤ segment.memBytes := by
  have hv := admitted_no_violation h .oversizeSegment
  rw [admitted_plan h]
  intro segment hmem
  simp only [violates, List.any_eq_false] at hv
  have := hv segment hmem
  simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, not_or, Nat.not_lt] at this
  exact ⟨Nat.pos_of_ne_zero this.1.1, this.1.2, this.2⟩

/-- Every admitted segment's file bytes lie inside the file. -/
theorem admitted_segments_in_file (h : check candidate = .ok plan) :
    ∀ segment ∈ plan.segments, segment.fileOffset + segment.fileBytes ≤ plan.fileBytes := by
  have hv := admitted_no_violation h .segmentOutsideFile
  rw [admitted_plan h]
  intro segment hmem
  simp only [violates, List.any_eq_false] at hv
  have := hv segment hmem
  simp only [decide_eq_true_eq, Nat.not_lt] at this
  exact this

/-- Every admitted segment's memory image lies inside the user window. -/
theorem admitted_segments_in_user_window (h : check candidate = .ok plan) :
    ∀ segment ∈ plan.segments,
      userWindowStart ≤ segment.vaddr ∧ segment.vaddr + segment.memBytes ≤ userWindowEnd := by
  have hv := admitted_no_violation h .outsideUserRange
  rw [admitted_plan h]
  intro segment hmem
  simp only [violates, List.any_eq_false] at hv
  have := hv segment hmem
  simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, Nat.not_lt] at this
  exact this

theorem pairwiseDisjoint_iff (segments : List Segment) :
    pairwiseDisjoint segments = true ↔ segments.Pairwise Segment.Disjoint := by
  induction segments with
  | nil => simp [pairwiseDisjoint]
  | cons segment rest ih =>
    simp only [pairwiseDisjoint, Bool.and_eq_true, List.all_eq_true, List.pairwise_cons, ih]
    constructor
    · rintro ⟨hall, hrest⟩
      refine ⟨fun other hmem => ?_, hrest⟩
      have := hall other hmem
      simpa [Segment.disjoint, Segment.Disjoint] using this
    · rintro ⟨hall, hrest⟩
      refine ⟨fun other hmem => ?_, hrest⟩
      have := hall other hmem
      simpa [Segment.disjoint, Segment.Disjoint] using this

/-- No two admitted segments share a page. -/
theorem admitted_segments_disjoint (h : check candidate = .ok plan) :
    plan.segments.Pairwise Segment.Disjoint := by
  have hv := admitted_no_violation h .overlappingSegments
  rw [admitted_plan h]
  simp only [violates, Bool.not_eq_false'] at hv
  exact (pairwiseDisjoint_iff _).mp hv

/-- The entry point lies in the file-backed bytes of an admitted segment that
is executable and, by W^X, not writable: the text segment. -/
theorem admitted_entry_in_text (h : check candidate = .ok plan) :
    ∃ segment ∈ plan.segments, segment.executable = true ∧ segment.writable = false ∧
      segment.vaddr ≤ plan.entry ∧ plan.entry < segment.vaddr + segment.fileBytes := by
  have hv := admitted_no_violation h .entryOutsideText
  have hwx := admitted_no_writable_executable h
  rw [admitted_plan h] at hwx ⊢
  simp only [violates, Bool.not_eq_false', List.any_eq_true] at hv
  obtain ⟨segment, hmem, hentry⟩ := hv
  simp only [Segment.holdsEntry, Bool.and_eq_true, decide_eq_true_eq] at hentry
  refine ⟨segment, hmem, hentry.1.1, ?_, hentry.1.2, hentry.2⟩
  have := hwx segment hmem
  cases hw : segment.writable <;> simp_all

/-- Every program header of an admitted file is a load segment or a
non-executable stack marker, with no flag bits beyond R, W and X. -/
theorem admitted_program_header_types (h : check candidate = .ok plan) :
    ∀ header ∈ candidate.programHeaders, supportedHeader header = true ∧ header.flags < 8 := by
  have h1 := admitted_no_violation h .unsupportedSegmentType
  have h2 := admitted_no_violation h .unknownSegmentFlags
  intro header hmem
  simp only [violates, List.any_eq_false] at h1 h2
  have a := h1 header hmem
  have b := h2 header hmem
  simp only [Bool.not_eq_true', Bool.not_eq_false] at a
  simp only [decide_eq_true_eq, Nat.not_le] at b
  exact ⟨by simpa using a, b⟩

end Admitted

/-! ## Placement in the image's reserved frame range -/

/-- The image range `[start, stop)` holding the admitted file's bytes, and
the enclosing embedded-user boot reservation `[reservationStart,
reservationStop)` (`BootReservation.Identity.embeddedUsers`). -/
structure Placement where
  start : Nat
  stop : Nat
  reservationStart : Nat
  reservationStop : Nat
  deriving DecidableEq, Repr

inductive PlacementRejection where
  | unaligned | wrongSize | outsideReservation
  deriving DecidableEq, Repr

def PlacementRejection.name : PlacementRejection → String
  | .unaligned => "placement-unaligned"
  | .wrongSize => "placement-wrong-size"
  | .outsideReservation => "placement-outside-reservation"

def roundUpPage (bytes : Nat) : Nat := (bytes + pageBytes - 1) / pageBytes * pageBytes

/-- One admitted segment and the physical address of its first file byte. -/
structure PlacedSegment where
  segment : Segment
  source : Nat
  deriving DecidableEq, Repr

def placementViolation (placement : Placement) (plan : Plan) : Option PlacementRejection :=
  if placement.start % pageBytes != 0 || placement.stop % pageBytes != 0 then some .unaligned
  else if placement.stop != placement.start + roundUpPage plan.fileBytes then some .wrongSize
  else if decide (placement.start < placement.reservationStart) ||
      decide (placement.stop > placement.reservationStop) then some .outsideReservation
  else none

/-- Bind an admitted plan to its reserved range: the range is page aligned,
holds exactly the file rounded up to a page, and lies inside the reservation.
Each segment's source is the range start plus its file offset. -/
def place (placement : Placement) (plan : Plan) : Except PlacementRejection (List PlacedSegment) :=
  match placementViolation placement plan with
  | some reason => .error reason
  | none => .ok (plan.segments.map fun segment =>
      { segment, source := placement.start + segment.fileOffset })

/-- A placed admitted plan keeps exactly the admitted segments, and every
segment's source bytes are page aligned and lie inside the reserved range and
the enclosing embedded-user reservation. -/
theorem placed_sources_reserved {candidate : Candidate} {plan : Plan}
    {placement : Placement} {placed : List PlacedSegment}
    (hadmit : check candidate = .ok plan) (h : place placement plan = .ok placed) :
    placed.map (·.segment) = plan.segments ∧
      ∀ entry ∈ placed, entry.source % pageBytes = 0 ∧
        placement.reservationStart ≤ placement.start ∧ placement.start ≤ entry.source ∧
        entry.source + entry.segment.fileBytes ≤ placement.stop ∧
        placement.stop ≤ placement.reservationStop := by
  unfold place at h
  cases hviolation : placementViolation placement plan with
  | some reason => simp [hviolation] at h
  | none =>
    simp only [hviolation, Except.ok.injEq] at h
    subst h
    simp only [placementViolation] at hviolation
    split at hviolation
    · contradiction
    rename_i haligned
    split at hviolation
    · contradiction
    rename_i hsize
    split at hviolation
    · contradiction
    rename_i hreserved
    simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, not_or, Decidable.not_not,
      decide_eq_true_eq, Nat.not_lt] at haligned hsize hreserved
    refine ⟨by simp [Function.comp_def], ?_⟩
    intro entry hmem
    simp only [List.mem_map] at hmem
    obtain ⟨segment, hseg, rfl⟩ := hmem
    have hal := (admitted_segments_aligned hadmit) segment hseg
    have hin := (admitted_segments_in_file hadmit) segment hseg
    simp only [roundUpPage, pageBytes] at hsize hal haligned ⊢
    refine ⟨by omega, hreserved.1, by omega, by omega, hreserved.2⟩

/-! ## Fixture encoder and rejection vectors

`encode` writes a candidate back out as ELF64 bytes (header at 0, program
headers at `phoff`, zero padding to `fileSize`, truncated to `fileSize`), so the vectors below run the
real byte parser.  The build additionally runs the checker over mutated
copies of the real example subject (`scripts/check-admitted-subject.py`). -/

def encodeLE (value width : Nat) : List UInt8 :=
  (List.range width).map fun index => UInt8.ofNat (value / 256 ^ index % 256)

def encodeProgramHeader (header : ProgramHeader) : List UInt8 :=
  encodeLE header.type 4 ++ encodeLE header.flags 4 ++ encodeLE header.offset 8 ++
    encodeLE header.vaddr 8 ++ encodeLE header.vaddr 8 ++ encodeLE header.fileBytes 8 ++
    encodeLE header.memBytes 8 ++ encodeLE pageBytes 8

def encodeHeader (c : Candidate) : List UInt8 :=
  encodeLE c.magic 4 ++ [UInt8.ofNat c.elfClass, UInt8.ofNat c.dataEncoding,
    UInt8.ofNat c.identVersion] ++ List.replicate 9 0 ++
  encodeLE c.type 2 ++ encodeLE c.machine 2 ++ encodeLE c.version 4 ++
  encodeLE c.entry 8 ++ encodeLE c.phoff 8 ++ encodeLE 0 8 ++ encodeLE 0 4 ++
  encodeLE c.ehsize 2 ++ encodeLE c.phentsize 2 ++ encodeLE c.phnum 2 ++
  encodeLE 0 6

def encode (c : Candidate) : ByteArray :=
  let header := encodeHeader c
  let gap := List.replicate (c.phoff - header.length) 0
  let body := header ++ gap ++ c.programHeaders.flatMap encodeProgramHeader
  ⟨((body ++ List.replicate (c.fileSize - body.length) 0).take c.fileSize).toArray⟩

/-- A minimal admissible file: a read/execute text segment holding the
headers and the entry point, and a read/write bss-only data segment. -/
def sample : Candidate :=
  { fileSize := 256, magic := elfMagic, elfClass := elfClass64,
    dataEncoding := elfDataLittleEndian, identVersion := elfVersionCurrent,
    type := elfTypeExecutable, machine := elfMachineX86_64, version := elfVersionCurrent,
    entry := userWindowStart + 0xB0, phoff := elfHeaderBytes, ehsize := elfHeaderBytes,
    phentsize := programHeaderBytes, phnum := 2,
    programHeaders :=
      [{ type := segmentLoad, flags := flagRead + flagExecute, offset := 0,
         vaddr := userWindowStart, fileBytes := 256, memBytes := 256 },
       { type := segmentLoad, flags := flagRead + flagWrite, offset := 0,
         vaddr := userWindowStart + pageBytes, fileBytes := 0, memBytes := pageBytes }] }

def withHeaders (headers : List ProgramHeader) : Candidate :=
  { sample with programHeaders := headers, phnum := headers.length }

def text : ProgramHeader := sample.programHeaders[0]!
def data : ProgramHeader := sample.programHeaders[1]!

/-- The encoder round-trips through the parser, and the sample is admitted
with the plan of its two load segments. -/
example : parse (encode sample) = sample := by native_decide
example : (admit (encode sample)).toOption = some (planOf sample) := by native_decide

/-- One vector per rejection reason, each through the byte parser. -/
def vectors : List (Candidate × Rejection) :=
  [({ sample with fileSize := 40, phnum := 0, programHeaders := [] }, .truncatedHeader),
   ({ sample with magic := 0x464C457E }, .badMagic),
   ({ sample with elfClass := 1 }, .notElf64),
   ({ sample with dataEncoding := 2 }, .notLittleEndian),
   ({ sample with version := 0 }, .badVersion),
   ({ sample with type := 3 }, .notExecutable),
   ({ sample with machine := 3 }, .wrongMachine),
   ({ sample with phentsize := 32 }, .badHeaderLayout),
   (withHeaders (List.replicate 9 data), .tooManyProgramHeaders),
   ({ sample with phoff := 200 }, .truncatedProgramHeaders),
   ({ sample with fileSize := maxFileBytes + 1 }, .fileTooLarge),
   (withHeaders [text, data, { data with type := 4 }], .unsupportedSegmentType),
   (withHeaders [text, { data with flags := flagRead + flagWrite + 8 }], .unknownSegmentFlags),
   (withHeaders [{ data with type := segmentGnuStack }], .noLoadSegment),
   (withHeaders [text, { data with vaddr := data.vaddr + 16 }], .misalignedSegment),
   (withHeaders [{ text with flags := flagRead + flagWrite + flagExecute }, data],
     .writableExecutable),
   (withHeaders [text, { data with memBytes := maxSegmentBytes + pageBytes }], .oversizeSegment),
   (withHeaders [{ text with fileBytes := 300, memBytes := 300 }, data], .segmentOutsideFile),
   (withHeaders [text, { data with vaddr := userWindowEnd }], .outsideUserRange),
   (withHeaders [text, { data with vaddr := userWindowStart }], .overlappingSegments),
   ({ sample with entry := userWindowStart + pageBytes }, .entryOutsideText)]

/-- Every rejection reason has a vector, and each vector is rejected with
exactly its reason. -/
example : Rejection.all.all (fun reason => vectors.any (·.2 == reason)) = true := by decide
example : vectors.all (fun (candidate, reason) =>
    match admit (encode candidate) with
    | .error found => found == reason
    | .ok _ => false) = true := by native_decide

def samplePlacement : Placement :=
  { start := 0x200000, stop := 0x201000, reservationStart := 0x1F0000,
    reservationStop := 0x210000 }

def placementRejection (placement : Placement) (plan : Plan) : Option PlacementRejection :=
  match place placement plan with
  | .error reason => some reason
  | .ok _ => none

/-- Placement vectors: the sample at one page inside a reservation, then each
placement rejection. -/
example : (place samplePlacement (planOf sample)).isOk = true := by decide
example : placementRejection { samplePlacement with start := 0x200010 } (planOf sample) =
    some .unaligned := by decide
example : placementRejection { samplePlacement with stop := 0x202000 } (planOf sample) =
    some .wrongSize := by decide
example : placementRejection { samplePlacement with reservationStart := 0x201000 }
    (planOf sample) = some .outsideReservation := by decide

/-- The parser reads at most `maxProgramHeaders` program headers. -/
theorem parse_programHeaders_length (bytes : ByteArray) :
    (parse bytes).programHeaders.length = min (readLE bytes 56 2) maxProgramHeaders := by
  simp [parse]

/-- The admitted user window starts at or above the last page the boot page
plan maps, so admitted segments never alias a boot identity mapping. -/
theorem userWindow_above_boot_plan :
    BootPageTablePlan.supportedPathPages * BootMemoryMap.pageBytes ≤ userWindowStart := by
  decide

end LeanOS.ElfAdmission
