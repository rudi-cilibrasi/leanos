import LeanOS.BootMemoryMapDecoder
import LeanOS.BootMemoryMapStreamAuthority
import LeanOS.BootMemoryMapStreaming
import LeanOS.BootReservation

/-!
# Exact stream-to-allocation composition

This proof-side module connects a completed version-two byte stream to the
existing authoritative decoder, normalizer, reservation overlay, and first
allocator selection.  It adds no freestanding export and is not reachable from
the restricted generated-C artifact.  The scalar ABI still transports chunks;
this module states which rich result those chunks must reconstruct before any
allocation authority may be granted.

`run` accepts no caller-supplied parsed fields or policy flags.  Its immutable
decoder input is exactly the concatenation of one continuous stream.  The
returned `Authority` retains equations for every authoritative transition.
`authorize` additionally compares the complete canonical projection, so a
mutated entry, region, reservation interval, or selected frame rejects rather
than becoming authority.
-/
namespace LeanOS.BootMemoryMapStreamPipeline

open LeanOS
open LeanOS.BootMemoryMap
open LeanOS.BootMemoryMapDecoder
open LeanOS.BootMemoryMapStreaming

inductive Error where
  | invalidExtent
  | discontinuousStream
  | incompleteStream
  | internalLengthMismatch
  | decode (reason : BootMemoryMapDecoder.Error)
  | reservation (reason : BootReservation.Error)
  | allocation (reason : FrameAllocator.AllocationError)
  | internalSelectionInvariant
  | outputMutation
  deriving BEq, DecidableEq, Repr

def initialState (identity : UInt64) (extent : Nat) : ModelState :=
  { identity, extent, offset := 0, complete := false }

def streamBytes (chunks : List ModelChunk) : List UInt8 :=
  chunks.flatMap (·.bytes)

/-- Reconstruct the one immutable input accepted by the rich decoder.  Bounds
match the version-two reset contract.  Replay continuity is checked before any
byte list is exposed to the decoder. -/
def assemble (magic infoAddress : UInt64) (extent : Nat)
    (chunks : List ModelChunk) : Except Error Input :=
  if extent < 16 || extent > maxTagBytes || extent % 8 != 0 then
    .error .invalidExtent
  else
    match replay (initialState infoAddress extent) chunks with
    | none => .error .discontinuousStream
    | some final =>
        if !final.complete || final.offset != extent then .error .incompleteStream
        else
          let bytes := streamBytes chunks
          if bytes.length != extent then .error .internalLengthMismatch
          else .ok { magic := magic.toNat, infoAddress := infoAddress.toNat, bytes }

theorem assemble_exact_bytes magic infoAddress extent chunks input
    (h : assemble magic infoAddress extent chunks = .ok input) :
    input.bytes = streamBytes chunks ∧ input.bytes.length = extent := by
  unfold assemble at h
  by_cases hbound : extent < 16 || extent > maxTagBytes || extent % 8 != 0
  · rw [if_pos hbound] at h
    contradiction
  · simp only [hbound, Bool.false_eq_true, ↓reduceIte] at h
    cases hreplay : replay (initialState infoAddress extent) chunks with
    | none =>
        rw [hreplay] at h
        contradiction
    | some final =>
        simp only [hreplay] at h
        by_cases hincomplete : !final.complete || final.offset != extent
        · rw [if_pos hincomplete] at h
          contradiction
        · simp only [hincomplete, Bool.false_eq_true, ↓reduceIte] at h
          by_cases hlength : (streamBytes chunks).length = extent
          · rw [if_neg (by simpa using hlength)] at h
            injection h with hinput
            rw [← hinput]
            exact ⟨rfl, hlength⟩
          · rw [if_pos (by simpa using hlength)] at h
            contradiction

/-- Every arbitrary aligned buffer within the reviewed bound has one canonical
continuous chunk replay, and assembling that replay returns exactly the
immutable decoder input.  This replaces fixture-only byte reconstruction with
the universal precondition needed by scalar/rich decoder refinement. -/
theorem assemble_canonicalChunks (magic infoAddress : UInt64) (bytes : List UInt8)
    (hsmall : 16 ≤ bytes.length) (hlarge : bytes.length ≤ maxTagBytes)
    (haligned : bytes.length % 8 = 0) :
    assemble magic infoAddress bytes.length (canonicalChunks infoAddress bytes) =
      .ok { magic := magic.toNat, infoAddress := infoAddress.toNat, bytes } := by
  unfold assemble
  have hreplay := canonicalChunks_replay infoAddress bytes (by omega) haligned
  have hbound : (bytes.length < 16 || bytes.length > maxTagBytes ||
      bytes.length % 8 != 0) ≠ true := by
    intro h
    simp at h
    omega
  rw [if_neg hbound]
  unfold initialState at hreplay ⊢
  rw [hreplay]
  simp [streamBytes, canonicalChunks_reconstruct infoAddress bytes haligned]

structure Authority where
  magic : UInt64
  infoAddress : UInt64
  extent : Nat
  chunks : List ModelChunk
  manifest : List BootReservation.Reservation
  owner : FrameAllocator.OwnerId
  input : Input
  decoded : Decoded
  reserved : BootReservation.Result
  allocation : FrameAllocator.Allocation
  assembled :
    assemble magic infoAddress extent chunks = .ok input
  decodedBy : BootMemoryMapDecoder.decode input = .ok decoded
  decodedTraversal :
    BootMemoryMapDecoder.SuccessfulRichDecodeTraversal input decoded
  reservedBy :
    BootReservation.initializeAllocator decoded.handoff manifest = .ok reserved
  allocatedBy :
    FrameAllocator.allocate reserved.allocator owner = .ok allocation
  selectedUsable :
    usableFrameSound decoded.entries allocation.frame = true
  selectedWithinBound : allocation.frame < frameLimit

def run (magic infoAddress : UInt64) (extent : Nat) (chunks : List ModelChunk)
    (manifest : List BootReservation.Reservation) (owner : FrameAllocator.OwnerId) :
    Except Error Authority :=
  match hassemble : assemble magic infoAddress extent chunks with
  | .error reason => .error reason
  | .ok input =>
      match hdecode : BootMemoryMapDecoder.decode input with
      | .error reason => .error (.decode reason)
      | .ok decoded =>
          match hreserve :
              BootReservation.initializeAllocator decoded.handoff manifest with
          | .error reason => .error (.reservation reason)
          | .ok reserved =>
              match hallocate : FrameAllocator.allocate reserved.allocator owner with
              | .error reason => .error (.allocation reason)
              | .ok allocation =>
                  if hsound : usableFrameSound decoded.entries allocation.frame then
                    if hbound : allocation.frame < frameLimit then
                      .ok
                        { magic, infoAddress, extent, chunks, manifest, owner, input, decoded,
                          reserved, allocation, assembled := hassemble, decodedBy := hdecode,
                          decodedTraversal :=
                            BootMemoryMapDecoder.successful_decode_constructs_traversal
                              input decoded hdecode,
                          reservedBy := hreserve, allocatedBy := hallocate,
                          selectedUsable := hsound, selectedWithinBound := hbound }
                    else .error .internalSelectionInvariant
                  else .error .internalSelectionInvariant

theorem run_functional magic infoAddress extent chunks manifest owner first second
    (hfirst : run magic infoAddress extent chunks manifest owner = first)
    (hsecond : run magic infoAddress extent chunks manifest owner = second) :
    first = second := by
  rw [hfirst] at hsecond
  exact hsecond

structure Projection where
  entries : List RawEntry
  normalizedRegions : List FrameAllocator.Region
  intervals : List BootReservation.Interval
  reservedRegions : List FrameAllocator.Region
  selectedFrame : FrameAllocator.FrameId
  deriving BEq, DecidableEq

def projection (authority : Authority) : Projection :=
  { entries := authority.decoded.entries
    normalizedRegions := authority.reserved.firmware.regions
    intervals := authority.reserved.intervals
    reservedRegions := authority.reserved.regions
    selectedFrame := authority.allocation.frame }

/-- Full-output binding.  A caller cannot substitute a selected frame or repair
any decoded/normalized/reserved projection and still receive `Authority`. -/
def authorize (magic infoAddress : UInt64) (extent : Nat) (chunks : List ModelChunk)
    (manifest : List BootReservation.Reservation) (owner : FrameAllocator.OwnerId)
    (claimed : Projection) : Except Error Authority := do
  let authority ← run magic infoAddress extent chunks manifest owner
  if claimed = projection authority then pure authority else throw .outputMutation

theorem authorize_functional magic infoAddress extent chunks manifest owner claimed first second
    (hfirst : authorize magic infoAddress extent chunks manifest owner claimed = first)
    (hsecond : authorize magic infoAddress extent chunks manifest owner claimed = second) :
    first = second := by
  rw [hfirst] at hsecond
  exact hsecond

theorem accepted_assembled_bytes authority
    (_h : run authority.magic authority.infoAddress authority.extent authority.chunks
      authority.manifest authority.owner = .ok authority) :
    authority.input.bytes = streamBytes authority.chunks ∧
      authority.input.bytes.length = authority.extent := by
  exact assemble_exact_bytes _ _ _ _ _ authority.assembled

theorem accepted_authority_chain authority
    (_h : run authority.magic authority.infoAddress authority.extent authority.chunks
      authority.manifest authority.owner = .ok authority) :
    BootMemoryMapDecoder.decode authority.input = .ok authority.decoded ∧
      BootReservation.initializeAllocator authority.decoded.handoff authority.manifest =
        .ok authority.reserved ∧
      FrameAllocator.allocate authority.reserved.allocator authority.owner =
        .ok authority.allocation :=
  ⟨authority.decodedBy, authority.reservedBy, authority.allocatedBy⟩

theorem accepted_selection_excludes_reservations authority
    (_h : run authority.magic authority.infoAddress authority.extent authority.chunks
      authority.manifest authority.owner = .ok authority) :
    BootReservation.reservedBy authority.reserved.intervals authority.allocation.frame =
      false :=
  BootReservation.allocation_excludes_reservations authority.reserved authority.owner
    authority.allocation authority.allocatedBy

/-- The selected frame has full decoded usable coverage, no decoded non-usable
overlap, lies in the boot-accessible scan, and is outside every checked live
reservation. -/
theorem accepted_selection_sound authority
    (_h : run authority.magic authority.infoAddress authority.extent authority.chunks
      authority.manifest authority.owner = .ok authority) :
    usableFrameSound authority.decoded.entries authority.allocation.frame = true ∧
      authority.allocation.frame < frameLimit ∧
      BootReservation.reservedBy authority.reserved.intervals authority.allocation.frame =
        false :=
  ⟨authority.selectedUsable, authority.selectedWithinBound,
    accepted_selection_excludes_reservations authority _h⟩

theorem accepted_claim_is_canonical magic infoAddress extent chunks manifest owner claimed
    authority
    (h : authorize magic infoAddress extent chunks manifest owner claimed = .ok authority) :
    claimed = projection authority := by
  unfold authorize at h
  cases hrun : run magic infoAddress extent chunks manifest owner with
  | error reason =>
      rw [hrun] at h
      contradiction
  | ok canonical =>
      rw [hrun] at h
      change (if claimed = projection canonical then Except.ok canonical
        else Except.error Error.outputMutation) = Except.ok authority at h
      by_cases heq : claimed = projection canonical
      · rw [if_pos heq] at h
        injection h with hauthority
        rw [← hauthority]
        exact heq
      · rw [if_neg heq] at h
        contradiction

theorem rejected_exposes_no_authority magic infoAddress extent chunks manifest owner claimed
    reason (h : authorize magic infoAddress extent chunks manifest owner claimed =
      .error reason) :
    (authorize magic infoAddress extent chunks manifest owner claimed).toOption = none := by
  rw [h]
  rfl

/-! ## Universal scalar/rich chunk refinement

These definitions are proof-side only.  They model the production loop that
queries all nineteen words from one pure generated transition.  Packing is
defined through the rich decoder's little-endian `readU64`, so the scalar word
and the byte decoder cannot silently adopt different byte order. -/

structure ScalarState where
  word : Array UInt64

def scalarInitialAt (streamIdentity : UInt64) (extent target : Nat) : ScalarState :=
  { word := Array.ofFn fun query : Fin 19 =>
      BootMemoryMapStreamAuthority.initWord
        (UInt64.ofNat multiboot2Magic) streamIdentity (UInt64.ofNat extent)
        (UInt64.ofNat target) (UInt64.ofNat query.val) }

/-- Every successful rich decode and bounded rich-selected target constructs
the exact admitted scalar parser state.  This is the first structural slice of
the terminal scalar/rich refinement: no terminal status or coverage word is
assumed or checked here. -/
theorem scalarInitialAt_of_decode
    (input : Input) (decoded : Decoded) (target : Nat)
    (hdecode : BootMemoryMapDecoder.decode input = .ok decoded)
    (htarget : target < frameLimit) :
    let initial :=
      scalarInitialAt (UInt64.ofNat input.infoAddress) input.bytes.length target
    initial.word[1]! = BootMemoryMapStreamAuthority.active ∧
      initial.word[2]! = BootMemoryMapStreamAuthority.noError ∧
      initial.word[3]! = UInt64.ofNat input.infoAddress ∧
      initial.word[4]! = UInt64.ofNat input.bytes.length ∧
      initial.word[5]! = 0 ∧
      initial.word[7]! = BootMemoryMapStreamAuthority.phaseInfo ∧
      initial.word[14]! = 0 ∧
      initial.word[15]! = 0 ∧
      initial.word[16]! = UInt64.ofNat target := by
  have hheader :=
    BootMemoryMapDecoder.accepted_input_scalar_header input decoded hdecode
  have haddressLt : input.infoAddress < UInt64.size := by
    simpa [wordLimit] using hheader.2.1
  have hextentLt : input.bytes.length < UInt64.size := by
    simpa [wordLimit] using hheader.2.2.1
  have htargetLt : target < UInt64.size := by
    exact Nat.lt_trans htarget (by decide)
  have haligned :
      UInt64.ofNat input.infoAddress % 8 = 0 := by
    apply UInt64.toNat.inj
    simp [UInt64.toNat_ofNat_of_lt' haddressLt, hheader.2.2.2.2.1]
  have hlow : 4096 ≤ UInt64.ofNat input.infoAddress := by
    rw [UInt64.le_iff_toNat_le, UInt64.toNat_ofNat_of_lt' haddressLt]
    exact hheader.2.2.2.2.2.2.2.2
  have hextentLow : 16 ≤ UInt64.ofNat input.bytes.length := by
    rw [UInt64.le_iff_toNat_le, UInt64.toNat_ofNat_of_lt' hextentLt]
    exact hheader.2.2.2.2.2.1
  have hextentHigh : UInt64.ofNat input.bytes.length ≤ 65536 := by
    rw [UInt64.le_iff_toNat_le, UInt64.toNat_ofNat_of_lt' hextentLt]
    exact hheader.2.2.2.2.2.2.2.1
  have hextentAligned :
      UInt64.ofNat input.bytes.length % 8 = 0 := by
    apply UInt64.toNat.inj
    simp [UInt64.toNat_ofNat_of_lt' hextentLt, hheader.2.2.2.2.2.2.1]
  have hnoOverflow :
      UInt64.ofNat input.bytes.length ≤
        0xffffffffffffffff - UInt64.ofNat input.infoAddress := by
    have haddressMax :
        UInt64.ofNat input.infoAddress ≤ 0xffffffffffffffff := by
      rw [UInt64.le_iff_toNat_le,
        UInt64.toNat_ofNat_of_lt' haddressLt]
      simp only [UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
      simpa [UInt64.size] using Nat.le_pred_of_lt haddressLt
    rw [UInt64.le_iff_toNat_le, UInt64.toNat_ofNat_of_lt' hextentLt,
      UInt64.toNat_sub_of_le _ _ haddressMax,
      UInt64.toNat_ofNat_of_lt' haddressLt]
    simp only [UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    exact hheader.2.2.2.1
  have htargetWord : UInt64.ofNat target < 4096 := by
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat_of_lt' htargetLt]
    simpa [frameLimit, physicalLimit, pageBytes] using htarget
  have hinit (query : UInt64) :=
    BootMemoryMapStreamAuthority.initWord_of_admitted
      (UInt64.ofNat input.infoAddress) (UInt64.ofNat input.bytes.length)
      (UInt64.ofNat target) query haligned hlow hextentLow hextentHigh
      hextentAligned hnoOverflow htargetWord
  simp [scalarInitialAt, multiboot2Magic, hinit,
    BootMemoryMapStreamAuthority.active,
    BootMemoryMapStreamAuthority.noError,
    BootMemoryMapStreamAuthority.phaseInfo]

def chunkWord (bytes : List UInt8) : UInt64 :=
  match BootMemoryMapDecoder.readU64 bytes 0 with
  | .ok value => UInt64.ofNat value
  | .error _ => 0

/-- Byte-to-word packing agrees with the rich decoder for every successfully
read eight-byte sequence, rather than only for checked-in fixtures. -/
theorem chunkWord_readU64_agreement (bytes : List UInt8) (value : Nat)
    (hread : BootMemoryMapDecoder.readU64 bytes 0 = .ok value) :
    chunkWord bytes = UInt64.ofNat value := by
  simp [chunkWord, hread]

/-- The generated usable-entry predicate and the rich typed-entry predicate
agree for every decoder-admitted entry word and bounded target frame. -/
theorem entryUsableCoverage_rich_agreement
    (base length kind target : Nat)
    (hbase : base < wordLimit)
    (hstop : base + length < wordLimit)
    (hkind : kind < 2 ^ 32)
    (htarget : target < frameLimit) :
    BootMemoryMapStreamAuthority.entryUsableCoverage
        (UInt64.ofNat base) (UInt64.ofNat length)
        (UInt64.ofNat kind) (UInt64.ofNat target) =
      (BootMemoryMapDecoder.memoryKind kind == MemoryKind.usable &&
        covers { base, length, kind := BootMemoryMapDecoder.memoryKind kind }
          (target * pageBytes) (target * pageBytes + pageBytes)) := by
  have hfirst : target * pageBytes < UInt64.size := by
    unfold frameLimit physicalLimit pageBytes at htarget
    unfold pageBytes UInt64.size
    omega
  have hpast : target * pageBytes + pageBytes < UInt64.size := by
    unfold frameLimit physicalLimit pageBytes at htarget
    unfold pageBytes UInt64.size
    omega
  have hkind64 : kind < wordLimit := by
    unfold wordLimit
    omega
  have hkindWord :=
    BootMemoryMapDecoder.low32Word_ofNat kind hkind64
  apply Bool.eq_iff_iff.mpr
  simp only [BootMemoryMapStreamAuthority.entryUsableCoverage,
    Bool.and_eq_true, beq_iff_eq, covers, decide_eq_true_eq]
  rw [hkindWord]
  have hfirstWord :
      UInt64.ofNat target * 4096 =
        UInt64.ofNat (target * pageBytes) := by
    simp [pageBytes]
  have hpastWord :
      UInt64.ofNat target * 4096 + 4096 =
        UInt64.ofNat (target * pageBytes + pageBytes) := by
    rw [hfirstWord]
    simp [pageBytes]
  have hstopWord :
      UInt64.ofNat base + UInt64.ofNat length =
        UInt64.ofNat (base + length) := by
    simp
  rw [hpastWord, hfirstWord, hstopWord]
  rw [UInt64.ofNat_le_iff_le hbase hfirst,
    UInt64.ofNat_le_iff_le hpast hstop]
  have hkindEq :
      UInt64.ofNat (BootMemoryMapDecoder.low32Nat kind) = 1 ↔
        BootMemoryMapDecoder.low32Nat kind = 1 := by
    have hlow :
        BootMemoryMapDecoder.low32Nat kind < UInt64.size := by
      unfold BootMemoryMapDecoder.low32Nat UInt64.size
      omega
    constructor
    · intro heq
      have := congrArg UInt64.toNat heq
      simpa [UInt64.toNat_ofNat_of_lt' hlow] using this
    · intro heq
      rw [heq]
      decide
  rw [hkindEq]
  rw [BootMemoryMapDecoder.memoryKind_usable_word]
  simp [BootMemoryMapDecoder.low32Nat, Nat.mod_eq_of_lt hkind,
    pageBytes, and_assoc]

/-- The generated non-usable-overlap predicate and the rich typed-entry
predicate agree under the same decoder bounds. -/
theorem entryNonUsableOverlap_rich_agreement
    (base length kind target : Nat)
    (hbase : base < wordLimit)
    (hstop : base + length < wordLimit)
    (hkind : kind < 2 ^ 32)
    (htarget : target < frameLimit) :
    BootMemoryMapStreamAuthority.entryNonUsableOverlap
        (UInt64.ofNat base) (UInt64.ofNat length)
        (UInt64.ofNat kind) (UInt64.ofNat target) =
      (BootMemoryMapDecoder.memoryKind kind != MemoryKind.usable &&
        overlaps { base, length, kind := BootMemoryMapDecoder.memoryKind kind }
          (target * pageBytes) (target * pageBytes + pageBytes)) := by
  have hfirst : target * pageBytes < UInt64.size := by
    unfold frameLimit physicalLimit pageBytes at htarget
    unfold pageBytes UInt64.size
    omega
  have hpast : target * pageBytes + pageBytes < UInt64.size := by
    unfold frameLimit physicalLimit pageBytes at htarget
    unfold pageBytes UInt64.size
    omega
  have hkind64 : kind < wordLimit := by
    unfold wordLimit
    omega
  have hkindWord :=
    BootMemoryMapDecoder.low32Word_ofNat kind hkind64
  apply Bool.eq_iff_iff.mpr
  simp only [BootMemoryMapStreamAuthority.entryNonUsableOverlap,
    Bool.and_eq_true, bne_iff_ne, overlaps, decide_eq_true_eq]
  rw [hkindWord]
  have hfirstWord :
      UInt64.ofNat target * 4096 =
        UInt64.ofNat (target * pageBytes) := by
    simp [pageBytes]
  have hpastWord :
      UInt64.ofNat target * 4096 + 4096 =
        UInt64.ofNat (target * pageBytes + pageBytes) := by
    rw [hfirstWord]
    simp [pageBytes]
  have hstopWord :
      UInt64.ofNat base + UInt64.ofNat length =
        UInt64.ofNat (base + length) := by
    simp
  rw [hpastWord, hfirstWord, hstopWord]
  rw [UInt64.ofNat_lt_iff_lt hbase hpast,
    UInt64.ofNat_lt_iff_lt hfirst hstop]
  have hkindEq :
      UInt64.ofNat (BootMemoryMapDecoder.low32Nat kind) ≠ 1 ↔
        BootMemoryMapDecoder.low32Nat kind ≠ 1 := by
    have hlow :
        BootMemoryMapDecoder.low32Nat kind < UInt64.size := by
      unfold BootMemoryMapDecoder.low32Nat UInt64.size
      omega
    constructor
    · intro hne heq
      apply hne
      rw [heq]
      decide
    · intro hne heq
      apply hne
      have := congrArg UInt64.toNat heq
      simpa [UInt64.toNat_ofNat_of_lt' hlow] using this
  rw [hkindEq]
  rw [show
      (BootMemoryMapDecoder.memoryKind kind != MemoryKind.usable) =
        (kind != 1) by
    simp only [bne]
    rw [BootMemoryMapDecoder.memoryKind_usable_word]]
  simp [BootMemoryMapDecoder.low32Nat, Nat.mod_eq_of_lt hkind,
    pageBytes, and_assoc]

def scalarStep (state : ScalarState) (chunk : ModelChunk) : ScalarState :=
  { word := Array.ofFn fun query : Fin 19 =>
      BootMemoryMapStreamAuthority.stepWord
        state.word[0]! state.word[1]! state.word[2]! state.word[3]!
        state.word[4]! state.word[5]! state.word[6]! state.word[7]!
        state.word[8]! state.word[9]! state.word[10]! state.word[11]!
        state.word[12]! state.word[13]! state.word[14]! state.word[15]!
        state.word[16]! state.word[17]! state.word[18]!
        chunk.identity (UInt64.ofNat chunk.offset) (chunkWord chunk.bytes)
        (if chunk.terminal then 1 else 0) (UInt64.ofNat query.val) }

/-- Every successful rich traversal takes the same first canonical
information-header step as the scalar production parser.  The step consumes
the exact source slice, preserves the immutable stream identity and extent,
and establishes the tag-phase cursor from which tag/layout/entry induction
continues. -/
theorem canonicalInfoStep_of_richTraversal
    (input : Input) (decoded : Decoded) (target : Nat)
    (hdecode : decode input = .ok decoded)
    (htraversal : SuccessfulRichDecodeTraversal input decoded)
    (htarget : target < frameLimit) :
    let identity := UInt64.ofNat input.infoAddress
    let initial := scalarInitialAt identity input.bytes.length target
    ∃ first rest,
      canonicalChunks identity input.bytes = first :: rest ∧
      first =
        { identity
          offset := 0
          bytes := input.bytes.take 8
          terminal := false } ∧
      let next := scalarStep initial first
      next.word[0]! = BootMemoryMapStreamAuthority.abiVersion ∧
        next.word[1]! = BootMemoryMapStreamAuthority.active ∧
        next.word[2]! = BootMemoryMapStreamAuthority.noError ∧
        next.word[3]! = identity ∧
        next.word[4]! = UInt64.ofNat input.bytes.length ∧
        next.word[5]! = 8 ∧
        next.word[7]! = BootMemoryMapStreamAuthority.phaseTag ∧
        next.word[8]! = 0 ∧
        next.word[9]! = 0 ∧
        next.word[10]! = 0 ∧
        next.word[11]! = 0 ∧
        next.word[12]! = 0 ∧
        next.word[13]! = 0 ∧
        next.word[14]! = 0 ∧
        next.word[15]! = 0 ∧
        next.word[16]! = UInt64.ofNat target ∧
        next.word[17]! = 0 ∧
        next.word[18]! = 0 := by
  dsimp only
  obtain ⟨infoWord, tags, hinfo, hlow, hhigh, htags, htagTraversal,
    hhandoff, hvalid, hentries, hbounds⟩ := htraversal.traversed
  have hheader := accepted_input_scalar_header input decoded hdecode
  have haligned := hheader.2.2.2.2.2.2.1
  have hcount : 0 < input.bytes.length / 8 := by omega
  have hget :=
    canonicalChunks_get?_source
      (UInt64.ofNat input.infoAddress) input.bytes haligned 0 hcount
  cases hchunks :
      canonicalChunks (UInt64.ofNat input.infoAddress) input.bytes with
  | nil =>
      rw [hchunks] at hget
      contradiction
  | cons first rest =>
      rw [hchunks] at hget
      simp only [List.getElem?_cons_zero, Option.some.injEq, Nat.zero_mul,
        List.drop_zero, Nat.zero_add] at hget
      have hterminal :
          (1 == input.bytes.length / 8) = false := by
        exact beq_false_of_ne (by omega)
      rw [hterminal] at hget
      subst first
      refine ⟨
        { identity := UInt64.ofNat input.infoAddress
          offset := 0
          bytes := input.bytes.take 8
          terminal := false },
        rest, ?_, rfl, ?_⟩
      · rfl
      have haddressLt : input.infoAddress < UInt64.size := by
        simpa [wordLimit] using hheader.2.1
      have hextentLt : input.bytes.length < UInt64.size := by
        simpa [wordLimit] using hheader.2.2.1
      have htargetLt : target < UInt64.size :=
        Nat.lt_trans htarget (by decide)
      have hinfoLt := readU64_lt_wordLimit input.bytes 0 infoWord hinfo
      have hchunkWord :
          chunkWord (input.bytes.take 8) = UInt64.ofNat infoWord := by
        apply chunkWord_readU64_agreement
        rw [show input.bytes.take 8 =
            (input.bytes.drop 0).take 8 by simp]
        rw [readU64_drop_take]
        exact hinfo
      have hlowWord :
          UInt64.ofNat infoWord &&& 0xffffffff =
            UInt64.ofNat input.bytes.length := by
        rw [low32Word_ofNat infoWord hinfoLt, hlow]
      have hhighWord :
          UInt64.ofNat infoWord >>> 32 = 0 := by
        rw [high32Word_ofNat infoWord hinfoLt, hhigh]
        rfl
      have haddressAligned :
          UInt64.ofNat input.infoAddress % 8 = 0 := by
        apply UInt64.toNat.inj
        simp [UInt64.toNat_ofNat_of_lt' haddressLt,
          hheader.2.2.2.2.1]
      have hextentLow : 16 ≤ UInt64.ofNat input.bytes.length := by
        rw [UInt64.le_iff_toNat_le, UInt64.toNat_ofNat_of_lt' hextentLt]
        exact hheader.2.2.2.2.2.1
      have hextentHigh : UInt64.ofNat input.bytes.length ≤ 65536 := by
        rw [UInt64.le_iff_toNat_le, UInt64.toNat_ofNat_of_lt' hextentLt]
        exact hheader.2.2.2.2.2.2.2.1
      have hextentAligned :
          UInt64.ofNat input.bytes.length % 8 = 0 := by
        apply UInt64.toNat.inj
        simp [UInt64.toNat_ofNat_of_lt' hextentLt, haligned]
      have htargetWord : UInt64.ofNat target < 4096 := by
        rw [UInt64.lt_iff_toNat_lt,
          UInt64.toNat_ofNat_of_lt' htargetLt]
        simpa [frameLimit, physicalLimit, pageBytes] using htarget
      have hextentNe8 : UInt64.ofNat input.bytes.length ≠ 8 := by
        intro heq
        have := congrArg UInt64.toNat heq
        simp [UInt64.toNat_ofNat_of_lt' hextentLt] at this
        omega
      have haddressLow : 4096 ≤ UInt64.ofNat input.infoAddress := by
        rw [UInt64.le_iff_toNat_le,
          UInt64.toNat_ofNat_of_lt' haddressLt]
        exact hheader.2.2.2.2.2.2.2.2
      have hnoOverflow :
          UInt64.ofNat input.bytes.length ≤
            0xffffffffffffffff - UInt64.ofNat input.infoAddress := by
        have haddressMax :
            UInt64.ofNat input.infoAddress ≤ 0xffffffffffffffff := by
          rw [UInt64.le_iff_toNat_le,
            UInt64.toNat_ofNat_of_lt' haddressLt]
          simp only [UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
          simpa [UInt64.size] using Nat.le_pred_of_lt haddressLt
        rw [UInt64.le_iff_toNat_le,
          UInt64.toNat_ofNat_of_lt' hextentLt,
          UInt64.toNat_sub_of_le _ _ haddressMax,
          UInt64.toNat_ofNat_of_lt' haddressLt]
        simp only [UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
        exact hheader.2.2.2.1
      have h8NeExtent : 8 ≠ UInt64.ofNat input.bytes.length :=
        Ne.symm hextentNe8
      have hstep :=
        BootMemoryMapStreamAuthority.infoStepWords_of_admitted
          (UInt64.ofNat input.infoAddress)
          (UInt64.ofNat input.bytes.length)
          (UInt64.ofNat target) (UInt64.ofNat infoWord)
          haddressAligned haddressLow hextentLow hextentHigh
          hextentAligned hnoOverflow htargetWord hlowWord hhighWord
          h8NeExtent
      simpa [scalarStep, scalarInitialAt, multiboot2Magic, hchunkWord]
        using hstep

def scalarReplay : List ModelChunk → ScalarState → ScalarState
  | [], state => state
  | chunk :: rest, state =>
      let next := scalarStep state chunk
      if next.word[2]! != BootMemoryMapStreamAuthority.noError then next
      else scalarReplay rest next

/-- Querying the proof-side state is definitionally the corresponding query of
the generated scalar transition. -/
theorem scalarStep_word (state : ScalarState) (chunk : ModelChunk) (query : Fin 19) :
    (scalarStep state chunk).word[query.val]! =
      BootMemoryMapStreamAuthority.stepWord
        state.word[0]! state.word[1]! state.word[2]! state.word[3]!
        state.word[4]! state.word[5]! state.word[6]! state.word[7]!
        state.word[8]! state.word[9]! state.word[10]! state.word[11]!
        state.word[12]! state.word[13]! state.word[14]! state.word[15]!
        state.word[16]! state.word[17]! state.word[18]!
        chunk.identity (UInt64.ofNat chunk.offset) (chunkWord chunk.bytes)
        (if chunk.terminal then 1 else 0) (UInt64.ofNat query.val) := by
  simp [scalarStep]

/-- Every accepted scalar entry-type transition classifies the same rich
decoded entry fields with the same usable-coverage and non-usable-overlap
predicates.  The existing accumulator is retained when the current entry does
not satisfy the corresponding predicate. -/
theorem scalarStep_entryType_classifies_rich
    (state : ScalarState) (chunk : ModelChunk)
    (base length kind target : Nat)
    (hphase :
      state.word[7]! = BootMemoryMapStreamAuthority.phaseEntryType)
    (hbaseWord : state.word[12]! = UInt64.ofNat base)
    (hlengthWord : state.word[13]! = UInt64.ofNat length)
    (htargetWord : state.word[16]! = UInt64.ofNat target)
    (hchunkWord : chunkWord chunk.bytes = UInt64.ofNat kind)
    (haccepted :
      (scalarStep state chunk).word[2]! =
        BootMemoryMapStreamAuthority.noError)
    (hbase : base < wordLimit)
    (hstop : base + length < wordLimit)
    (hkind : kind < 2 ^ 32)
    (htarget : target < frameLimit) :
    (scalarStep state chunk).word[14]! =
        (if BootMemoryMapDecoder.memoryKind kind == MemoryKind.usable &&
            covers
              { base, length,
                kind := BootMemoryMapDecoder.memoryKind kind }
              (target * pageBytes) (target * pageBytes + pageBytes)
          then (1 : UInt64) else state.word[14]!) ∧
      (scalarStep state chunk).word[15]! =
        (if BootMemoryMapDecoder.memoryKind kind != MemoryKind.usable &&
            overlaps
              { base, length,
                kind := BootMemoryMapDecoder.memoryKind kind }
              (target * pageBytes) (target * pageBytes + pageBytes)
          then (1 : UInt64) else state.word[15]!) := by
  have hacceptedStep := haccepted
  rw [scalarStep_word state chunk (⟨2, by decide⟩ : Fin 19)] at hacceptedStep
  have hclassification :=
    BootMemoryMapStreamAuthority.accepted_entryType_classification_words
      state.word[0]! state.word[1]! state.word[2]! state.word[3]!
      state.word[4]! state.word[5]! state.word[6]! state.word[7]!
      state.word[8]! state.word[9]! state.word[10]! state.word[11]!
      state.word[12]! state.word[13]! state.word[14]! state.word[15]!
      state.word[16]! state.word[17]! state.word[18]!
      chunk.identity (UInt64.ofNat chunk.offset) (chunkWord chunk.bytes)
      (if chunk.terminal then 1 else 0) hphase hacceptedStep
  rw [hbaseWord, hlengthWord, htargetWord, hchunkWord] at hclassification
  rw [entryUsableCoverage_rich_agreement base length kind target
      hbase hstop hkind htarget,
    entryNonUsableOverlap_rich_agreement base length kind target
      hbase hstop hkind htarget] at hclassification
  rw [scalarStep_word state chunk (⟨14, by decide⟩ : Fin 19),
    scalarStep_word state chunk (⟨15, by decide⟩ : Fin 19)]
  rw [hbaseWord, hlengthWord, htargetWord, hchunkWord]
  simpa using hclassification

/-- Every accepted scalar transition outside the entry-type phase preserves
both rich classification accumulators. -/
theorem scalarStep_nonEntry_preserves_classification
    (state : ScalarState) (chunk : ModelChunk)
    (hphase :
      state.word[7]! ≠ BootMemoryMapStreamAuthority.phaseEntryType)
    (haccepted :
      (scalarStep state chunk).word[2]! =
        BootMemoryMapStreamAuthority.noError) :
    (scalarStep state chunk).word[14]! = state.word[14]! ∧
      (scalarStep state chunk).word[15]! = state.word[15]! := by
  have hacceptedStep := haccepted
  rw [scalarStep_word state chunk (⟨2, by decide⟩ : Fin 19)] at hacceptedStep
  have hpreserved :=
    BootMemoryMapStreamAuthority.accepted_nonEntry_preserves_classification_words
      state.word[0]! state.word[1]! state.word[2]! state.word[3]!
      state.word[4]! state.word[5]! state.word[6]! state.word[7]!
      state.word[8]! state.word[9]! state.word[10]! state.word[11]!
      state.word[12]! state.word[13]! state.word[14]! state.word[15]!
      state.word[16]! state.word[17]! state.word[18]!
      chunk.identity (UInt64.ofNat chunk.offset) (chunkWord chunk.bytes)
      (if chunk.terminal then 1 else 0) hphase hacceptedStep
  rw [scalarStep_word state chunk (⟨14, by decide⟩ : Fin 19),
    scalarStep_word state chunk (⟨15, by decide⟩ : Fin 19)]
  exact hpreserved

def updateUsableClassification
    (target : Nat) (current : UInt64) (entry : RawEntry) : UInt64 :=
  if entry.kind == MemoryKind.usable &&
      covers entry (target * pageBytes) (target * pageBytes + pageBytes)
    then 1 else current

def updateBlockedClassification
    (target : Nat) (current : UInt64) (entry : RawEntry) : UInt64 :=
  if entry.kind != MemoryKind.usable &&
      overlaps entry (target * pageBytes) (target * pageBytes + pageBytes)
    then 1 else current

/-- A proof-side certificate for an arbitrary successful rich/scalar
traversal.  Non-entry words preserve the classification state; each entry-type
word is tied to the exact rich entry decoded from its base, length, and type
words.  The terminal constructor fixes successful completion.  No fixture or
canonical-output comparison appears in this relation. -/
inductive SuccessfulScalarRichTraversal (target : Nat) :
    List RawEntry → ScalarState → List ModelChunk → ScalarState → Prop
  | done (state : ScalarState)
      (hstatus : state.word[1]! = BootMemoryMapStreamAuthority.complete)
      (herror : state.word[2]! = BootMemoryMapStreamAuthority.noError) :
      SuccessfulScalarRichTraversal target [] state [] state
  | nonEntry (entries : List RawEntry) (state terminal : ScalarState)
      (chunk : ModelChunk) (rest : List ModelChunk)
      (hphase :
        state.word[7]! ≠ BootMemoryMapStreamAuthority.phaseEntryType)
      (haccepted :
        (scalarStep state chunk).word[2]! =
          BootMemoryMapStreamAuthority.noError)
      (hrest :
        SuccessfulScalarRichTraversal target entries
          (scalarStep state chunk) rest terminal) :
      SuccessfulScalarRichTraversal target entries state (chunk :: rest) terminal
  | entry (base length kind : Nat) (entries : List RawEntry)
      (state terminal : ScalarState) (chunk : ModelChunk) (rest : List ModelChunk)
      (hphase :
        state.word[7]! = BootMemoryMapStreamAuthority.phaseEntryType)
      (hbaseWord : state.word[12]! = UInt64.ofNat base)
      (hlengthWord : state.word[13]! = UInt64.ofNat length)
      (htargetWord : state.word[16]! = UInt64.ofNat target)
      (hchunkWord : chunkWord chunk.bytes = UInt64.ofNat kind)
      (haccepted :
        (scalarStep state chunk).word[2]! =
          BootMemoryMapStreamAuthority.noError)
      (hbase : base < wordLimit)
      (hstop : base + length < wordLimit)
      (hkind : kind < 2 ^ 32)
      (htarget : target < frameLimit)
      (hrest :
        SuccessfulScalarRichTraversal target entries
          (scalarStep state chunk) rest terminal) :
      SuccessfulScalarRichTraversal target
        ({ base, length, kind := BootMemoryMapDecoder.memoryKind kind } :: entries)
        state (chunk :: rest) terminal

/-- The canonical information-header step is the first constructive phase of
the scalar/rich traversal.  Any continuation certificate over the remaining
canonical chunks therefore lifts to a certificate over the complete source
stream.  This theorem fixes the phase boundary without assuming any terminal
status or classification agreement. -/
theorem successfulScalarRichTraversal_prepend_info
    (input : Input) (decoded : Decoded) (target : Nat)
    (terminal : ScalarState)
    (hdecode : decode input = .ok decoded)
    (htraversal : SuccessfulRichDecodeTraversal input decoded)
    (htarget : target < frameLimit)
    (hrest :
      let identity := UInt64.ofNat input.infoAddress
      let initial := scalarInitialAt identity input.bytes.length target
      let first : ModelChunk :=
        { identity
          offset := 0
          bytes := input.bytes.take 8
          terminal := false }
      SuccessfulScalarRichTraversal target decoded.entries
        (scalarStep initial first)
        (canonicalChunks identity input.bytes).tail terminal) :
    let identity := UInt64.ofNat input.infoAddress
    let initial := scalarInitialAt identity input.bytes.length target
    SuccessfulScalarRichTraversal target decoded.entries initial
      (canonicalChunks identity input.bytes) terminal := by
  dsimp only at hrest ⊢
  obtain ⟨first, rest, hchunks, hfirst, hnext⟩ :=
    canonicalInfoStep_of_richTraversal
      input decoded target hdecode htraversal htarget
  have hinitial :=
    scalarInitialAt_of_decode input decoded target hdecode htarget
  rw [hchunks] at hrest ⊢
  simp only [List.tail_cons] at hrest
  subst first
  refine SuccessfulScalarRichTraversal.nonEntry
    decoded.entries
    (scalarInitialAt (UInt64.ofNat input.infoAddress)
      input.bytes.length target)
    terminal
    { identity := UInt64.ofNat input.infoAddress
      offset := 0
      bytes := input.bytes.take 8
      terminal := false }
    rest ?_ ?_ hrest
  · rw [hinitial.2.2.2.2.2.1]
    decide
  · exact hnext.2.2.1

/-- One admitted ignored-tag header is a non-entry traversal step.  The
production transition proves acceptance from the exact rich header word and
records the cursor, content, and rounded-padding state needed by the remaining
ignored-body induction. -/
theorem successfulScalarRichTraversal_ignoredTagHeader
    (identity extent offset word : UInt64) (target : Nat)
    (entries : List RawEntry) (state terminal : ScalarState)
    (chunk : ModelChunk) (rest : List ModelChunk)
    (hchunkIdentity : chunk.identity = identity)
    (hchunkOffset : UInt64.ofNat chunk.offset = offset)
    (hchunkTerminal : chunk.terminal = false)
    (hchunkWord : chunkWord chunk.bytes = word)
    (hversion :
      state.word[0]! = BootMemoryMapStreamAuthority.abiVersion)
    (hstatus :
      state.word[1]! = BootMemoryMapStreamAuthority.active)
    (herror :
      state.word[2]! = BootMemoryMapStreamAuthority.noError)
    (hidentity : state.word[3]! = identity)
    (hidentityAligned : identity % 8 = 0)
    (hextent : state.word[4]! = extent)
    (hextentLow : 16 ≤ extent)
    (hextentHigh : extent ≤ 65536)
    (hextentAligned : extent % 8 = 0)
    (hoffset : state.word[5]! = offset)
    (hoffsetLt : offset < extent)
    (hoffsetNotFinal : offset + 8 ≠ extent)
    (hphase :
      state.word[7]! = BootMemoryMapStreamAuthority.phaseTag)
    (husable : state.word[14]! ≤ 1)
    (hblocked : state.word[15]! ≤ 1)
    (hsawMap : state.word[10]! ≤ 1)
    (htargetWord : state.word[16]! = UInt64.ofNat target)
    (htarget : target < frameLimit)
    (htagCount : state.word[18]! < 64)
    (htypeEnd : BootMemoryMapStreamAuthority.low32 word ≠ 0)
    (htypeMap : BootMemoryMapStreamAuthority.low32 word ≠ 6)
    (hsizeLow : 8 ≤ BootMemoryMapStreamAuthority.high32 word)
    (hsizeFits :
      BootMemoryMapStreamAuthority.high32 word ≤ extent - offset)
    (hsizeNoOverflow :
      BootMemoryMapStreamAuthority.high32 word ≤ 0xfffffffffffffff8)
    (hroundedFits :
      ((BootMemoryMapStreamAuthority.high32 word + 7) &&&
          0xfffffffffffffff8) ≤ extent - offset)
    (hrest :
      SuccessfulScalarRichTraversal target entries
        (scalarStep state chunk) rest terminal) :
    SuccessfulScalarRichTraversal target entries state
      (chunk :: rest) terminal := by
  have htargetLt : target < UInt64.size :=
    Nat.lt_trans htarget (by decide)
  have htargetBound : UInt64.ofNat target < 4096 := by
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat_of_lt' htargetLt]
    simpa [frameLimit, physicalLimit, pageBytes] using htarget
  have hstep :=
    BootMemoryMapStreamAuthority.ignoredTagHeaderStepWords_of_admitted
      identity extent offset state.word[6]! state.word[8]! state.word[9]!
      state.word[10]! state.word[11]! state.word[12]! state.word[13]!
      state.word[14]! state.word[15]! (UInt64.ofNat target)
      state.word[17]! state.word[18]! word
      hidentityAligned hextentLow hextentHigh hextentAligned hoffsetLt
      hoffsetNotFinal husable hblocked hsawMap htargetBound htagCount
      htypeEnd htypeMap hsizeLow hsizeFits hsizeNoOverflow hroundedFits
  apply SuccessfulScalarRichTraversal.nonEntry entries state terminal chunk rest
  · rw [hphase]
    decide
  · simpa [scalarStep, hchunkIdentity, hchunkOffset, hchunkTerminal, hchunkWord,
      hversion, hstatus, herror, hidentity, hextent, hoffset, hphase,
      htargetWord] using hstep.2.2.1
  · exact hrest

/-- One admitted ignored-tag content or padding word is a non-entry traversal
step.  The production transition supplies the exact next cursor and remaining
content/padding counters, while the continuation carries the induction through
the rest of the ignored body. -/
theorem successfulScalarRichTraversal_ignoredTagBody
    (identity extent offset word : UInt64) (target : Nat)
    (entries : List RawEntry) (state terminal : ScalarState)
    (chunk : ModelChunk) (rest : List ModelChunk)
    (hchunkIdentity : chunk.identity = identity)
    (hchunkOffset : UInt64.ofNat chunk.offset = offset)
    (hchunkTerminal : chunk.terminal = false)
    (hchunkWord : chunkWord chunk.bytes = word)
    (hversion :
      state.word[0]! = BootMemoryMapStreamAuthority.abiVersion)
    (hstatus :
      state.word[1]! = BootMemoryMapStreamAuthority.active)
    (herror :
      state.word[2]! = BootMemoryMapStreamAuthority.noError)
    (hidentity : state.word[3]! = identity)
    (hidentityAligned : identity % 8 = 0)
    (hextent : state.word[4]! = extent)
    (hextentLow : 16 ≤ extent)
    (hextentHigh : extent ≤ 65536)
    (hextentAligned : extent % 8 = 0)
    (hoffset : state.word[5]! = offset)
    (hoffsetLt : offset < extent)
    (hoffsetNotFinal : offset + 8 ≠ extent)
    (hphase :
      state.word[7]! = BootMemoryMapStreamAuthority.phaseIgnored)
    (hpadded : (8 : UInt64) ≤ state.word[9]!)
    (hcontent : state.word[8]! ≤ state.word[9]!)
    (husable : state.word[14]! ≤ 1)
    (hblocked : state.word[15]! ≤ 1)
    (hsawMap : state.word[10]! ≤ 1)
    (htargetWord : state.word[16]! = UInt64.ofNat target)
    (htarget : target < frameLimit)
    (htagCount : state.word[18]! ≤ 64)
    (hrest :
      SuccessfulScalarRichTraversal target entries
        (scalarStep state chunk) rest terminal) :
    SuccessfulScalarRichTraversal target entries state
      (chunk :: rest) terminal := by
  have htargetLt : target < UInt64.size :=
    Nat.lt_trans htarget (by decide)
  have htargetBound : UInt64.ofNat target < 4096 := by
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat_of_lt' htargetLt]
    simpa [frameLimit, physicalLimit, pageBytes] using htarget
  have hstep :=
    BootMemoryMapStreamAuthority.ignoredTagBodyStepWords_of_admitted
      identity extent offset state.word[6]! state.word[8]! state.word[9]!
      state.word[10]! state.word[11]! state.word[12]! state.word[13]!
      state.word[14]! state.word[15]! (UInt64.ofNat target)
      state.word[17]! state.word[18]! word
      hidentityAligned hextentLow hextentHigh hextentAligned hoffsetLt
      hoffsetNotFinal husable hblocked hsawMap htargetBound htagCount
      hpadded hcontent
  apply SuccessfulScalarRichTraversal.nonEntry entries state terminal chunk rest
  · rw [hphase]
    decide
  · simpa [scalarStep, hchunkIdentity, hchunkOffset, hchunkTerminal, hchunkWord,
      hversion, hstatus, herror, hidentity, hextent, hoffset, hphase,
      htargetWord] using hstep.2.2.1
  · exact hrest

/-- Exact list-level evidence that a sequence consists only of accepted
ignored-tag body or padding words.  The state is threaded through the
production scalar transition, so adjacent words cannot be reordered or
spliced without invalidating the certificate. -/
inductive SuccessfulIgnoredTagSpan :
    ScalarState → List ModelChunk → ScalarState → Prop
  | done (state : ScalarState) :
      SuccessfulIgnoredTagSpan state [] state
  | step (state terminal : ScalarState) (chunk : ModelChunk)
      (rest : List ModelChunk)
      (hphase :
        state.word[7]! = BootMemoryMapStreamAuthority.phaseIgnored)
      (haccepted :
        (scalarStep state chunk).word[2]! =
          BootMemoryMapStreamAuthority.noError)
      (hrest :
        SuccessfulIgnoredTagSpan (scalarStep state chunk) rest terminal) :
      SuccessfulIgnoredTagSpan state (chunk :: rest) terminal

/-- Canonical source chunks for an ignored tag body and its alignment padding
form one exact accepted scalar span.  The induction is indexed by the retained
source position and word count: every head is selected from
`canonicalChunks`, and the production transition supplies the next cursor,
remaining byte counters, and parser phase. -/
theorem successfulIgnoredTagSpan_canonical
    (identity : UInt64) (bytes : List UInt8) (total index count target : Nat)
    (state : ScalarState)
    (htotal : total = bytes.length)
    (htotalLow : 16 ≤ total)
    (htotalHigh : total ≤ maxTagBytes)
    (htotalAligned : total % 8 = 0)
    (hidentityAligned : identity % 8 = 0)
    (hroom : index + count < total / 8)
    (hversion :
      state.word[0]! = BootMemoryMapStreamAuthority.abiVersion)
    (hstatus :
      state.word[1]! = BootMemoryMapStreamAuthority.active)
    (herror :
      state.word[2]! = BootMemoryMapStreamAuthority.noError)
    (hidentity : state.word[3]! = identity)
    (hextent : state.word[4]! = UInt64.ofNat total)
    (hoffset : state.word[5]! = UInt64.ofNat (index * 8))
    (hphase :
      state.word[7]! =
        if count = 0 then BootMemoryMapStreamAuthority.phaseTag
        else BootMemoryMapStreamAuthority.phaseIgnored)
    (hcontent : state.word[8]! ≤ state.word[9]!)
    (hpadded : state.word[9]! = UInt64.ofNat (count * 8))
    (hsawMap : state.word[10]! ≤ 1)
    (husable : state.word[14]! ≤ 1)
    (hblocked : state.word[15]! ≤ 1)
    (htargetWord : state.word[16]! = UInt64.ofNat target)
    (htarget : target < frameLimit)
    (htagCount : state.word[18]! ≤ 64) :
    let body :=
      ((canonicalChunks identity bytes).drop index).take count
    ∃ after,
      SuccessfulIgnoredTagSpan state body after ∧
        after.word[0]! = BootMemoryMapStreamAuthority.abiVersion ∧
        after.word[1]! = BootMemoryMapStreamAuthority.active ∧
        after.word[2]! = BootMemoryMapStreamAuthority.noError ∧
        after.word[3]! = identity ∧
        after.word[4]! = UInt64.ofNat total ∧
        after.word[5]! = UInt64.ofNat ((index + count) * 8) ∧
        after.word[7]! = BootMemoryMapStreamAuthority.phaseTag ∧
        after.word[8]! = 0 ∧
        after.word[9]! = 0 ∧
        after.word[10]! ≤ 1 ∧
        after.word[14]! ≤ 1 ∧
        after.word[15]! ≤ 1 ∧
        after.word[16]! = UInt64.ofNat target ∧
        after.word[18]! ≤ 64 := by
  dsimp only
  induction count generalizing index state with
  | zero =>
      refine ⟨state, ?_, hversion, hstatus, herror, hidentity, hextent, ?_,
        ?_, ?_, ?_, hsawMap, husable, hblocked, htargetWord, htagCount⟩
      · exact SuccessfulIgnoredTagSpan.done state
      · simpa using hoffset
      · simpa using hphase
      · have : state.word[8]! = 0 := by
          rw [hpadded] at hcontent
          simpa using hcontent
        exact this
      · simpa using hpadded
  | succ count ih =>
      have htotalLt : total < UInt64.size :=
        Nat.lt_of_le_of_lt htotalHigh (by decide)
      have htargetLt : target < UInt64.size :=
        Nat.lt_trans htarget (by decide)
      have hindex : index < bytes.length / 8 := by
        rw [← htotal]
        omega
      let chunk : ModelChunk :=
        { identity
          offset := index * 8
          bytes := (bytes.drop (index * 8)).take 8
          terminal := false }
      have hchunkSource :=
        canonicalChunks_get?_source identity bytes (by simpa [← htotal])
          index hindex
      have hterminal : (index + 1 == bytes.length / 8) = false := by
        rw [← htotal]
        exact beq_false_of_ne (by omega)
      rw [hterminal] at hchunkSource
      have hchunksLength :=
        canonicalChunks_length identity bytes
      have hchunkGet :
          (canonicalChunks identity bytes)[index] = chunk := by
        have hsome :
            (canonicalChunks identity bytes)[index]? = some chunk := by
          simpa [chunk] using hchunkSource
        have hindexChunks :
            index < (canonicalChunks identity bytes).length := by
          simpa [hchunksLength] using hindex
        rw [List.getElem?_eq_getElem hindexChunks] at hsome
        exact Option.some.inj hsome
      have hbody :
          ((canonicalChunks identity bytes).drop index).take (count + 1) =
            chunk ::
              ((canonicalChunks identity bytes).drop (index + 1)).take count := by
        rw [List.drop_eq_getElem_cons]
        · rw [hchunkGet]
          rfl
        · simpa [hchunksLength] using hindex
      have hextentLow : 16 ≤ UInt64.ofNat total := by
        rw [UInt64.le_iff_toNat_le, UInt64.toNat_ofNat_of_lt' htotalLt]
        exact htotalLow
      have hextentHigh : UInt64.ofNat total ≤ 65536 := by
        rw [UInt64.le_iff_toNat_le, UInt64.toNat_ofNat_of_lt' htotalLt]
        simpa [maxTagBytes] using htotalHigh
      have hextentAligned : UInt64.ofNat total % 8 = 0 := by
        apply UInt64.toNat.inj
        simp [UInt64.toNat_ofNat_of_lt' htotalLt, htotalAligned]
      have htotalWords : total / 8 * 8 = total := by
        have := Nat.mod_add_div total 8
        rw [htotalAligned, Nat.zero_add] at this
        simpa [Nat.mul_comm] using this
      have hoffsetNat : index * 8 < total := by
        omega
      have hoffsetLt :
          UInt64.ofNat (index * 8) < UInt64.ofNat total := by
        rw [UInt64.lt_iff_toNat_lt,
          UInt64.toNat_ofNat_of_lt' htotalLt]
        have hoffsetLt : index * 8 < UInt64.size := by
          exact Nat.lt_trans hoffsetNat htotalLt
        rw [UInt64.toNat_ofNat_of_lt' hoffsetLt]
        exact hoffsetNat
      have hoffsetNotFinal :
          UInt64.ofNat (index * 8) + 8 ≠ UInt64.ofNat total := by
        intro heq
        have hwordAdd :
            UInt64.ofNat (index * 8) + 8 =
              UInt64.ofNat (index * 8 + 8) := by
          simp
        rw [hwordAdd] at heq
        have := congrArg UInt64.toNat heq
        have hoffsetNextLt : index * 8 + 8 < UInt64.size := by
          have : index * 8 + 8 < total := by omega
          exact Nat.lt_trans this htotalLt
        rw [UInt64.toNat_ofNat_of_lt' hoffsetNextLt,
          UInt64.toNat_ofNat_of_lt' htotalLt] at this
        omega
      have htargetBound : UInt64.ofNat target < 4096 := by
        rw [UInt64.lt_iff_toNat_lt,
          UInt64.toNat_ofNat_of_lt' htargetLt]
        simpa [frameLimit, physicalLimit, pageBytes] using htarget
      have hpaddedLow : (8 : UInt64) ≤ state.word[9]! := by
        rw [hpadded]
        have hpaddedLt : (count + 1) * 8 < UInt64.size := by
          have : (count + 1) * 8 < total := by omega
          exact Nat.lt_trans this htotalLt
        have h8Nat : (8 : UInt64).toNat = 8 := by decide
        rw [UInt64.le_iff_toNat_le, h8Nat,
          UInt64.toNat_ofNat_of_lt' hpaddedLt]
        omega
      have hstep :=
        BootMemoryMapStreamAuthority.ignoredTagBodyStepWords_of_admitted
          identity (UInt64.ofNat total) (UInt64.ofNat (index * 8))
          state.word[6]! state.word[8]! state.word[9]!
          state.word[10]! state.word[11]! state.word[12]! state.word[13]!
          state.word[14]! state.word[15]! (UInt64.ofNat target)
          state.word[17]! state.word[18]! (chunkWord chunk.bytes)
          hidentityAligned hextentLow hextentHigh hextentAligned hoffsetLt
          hoffsetNotFinal husable hblocked hsawMap htargetBound htagCount
          hpaddedLow hcontent
      have hphaseIgnored :
          state.word[7]! = BootMemoryMapStreamAuthority.phaseIgnored := by
        simpa using hphase
      have hnext :
          let next := scalarStep state chunk
          next.word[0]! = BootMemoryMapStreamAuthority.abiVersion ∧
            next.word[1]! = BootMemoryMapStreamAuthority.active ∧
            next.word[2]! = BootMemoryMapStreamAuthority.noError ∧
            next.word[3]! = identity ∧
            next.word[4]! = UInt64.ofNat total ∧
            next.word[5]! = UInt64.ofNat (index * 8) + 8 ∧
            next.word[7]! =
              (if state.word[9]! == 8
                then BootMemoryMapStreamAuthority.phaseTag
                else BootMemoryMapStreamAuthority.phaseIgnored) ∧
            next.word[8]! =
              (if state.word[8]! > 8 then state.word[8]! - 8 else 0) ∧
            next.word[9]! = state.word[9]! - 8 ∧
            next.word[10]! = state.word[10]! ∧
            next.word[11]! = state.word[11]! ∧
            next.word[12]! = state.word[12]! ∧
            next.word[13]! = state.word[13]! ∧
            next.word[14]! = state.word[14]! ∧
            next.word[15]! = state.word[15]! ∧
            next.word[16]! = UInt64.ofNat target ∧
            next.word[17]! = state.word[17]! ∧
            next.word[18]! = state.word[18]! := by
        dsimp only
        simpa [scalarStep, chunk, hversion, hstatus, herror, hidentity,
          hextent, hoffset, hphaseIgnored, htargetWord] using hstep
      rcases hnext with ⟨hnextVersion, hnextStatus, haccepted,
        hnextIdentity, hnextExtent, hnextOffsetRaw, hnextPhaseRaw,
        hnextContentRaw, hnextPaddedRaw, hnextSawMapRaw, hnextEntries,
        hnextBase, hnextLength, hnextUsableRaw, hnextBlockedRaw,
        hnextTarget, hnextHighest, hnextTagCountRaw⟩
      have hnextOffset :
          (scalarStep state chunk).word[5]! =
            UInt64.ofNat ((index + 1) * 8) := by
        simpa [Nat.add_mul] using hnextOffsetRaw
      have hnextPhase :
          (scalarStep state chunk).word[7]! =
            if count = 0 then BootMemoryMapStreamAuthority.phaseTag
            else BootMemoryMapStreamAuthority.phaseIgnored := by
        by_cases hcountZero : count = 0
        · subst count
          simpa [hpadded] using hnextPhaseRaw
        · have hcountPositive : 0 < count := Nat.pos_of_ne_zero hcountZero
          have hpaddedNe : state.word[9]! ≠ 8 := by
            rw [hpadded]
            intro heq
            have := congrArg UInt64.toNat heq
            have hpaddedLt : (count + 1) * 8 < UInt64.size := by
              omega
            rw [UInt64.toNat_ofNat_of_lt' hpaddedLt] at this
            simp at this
            omega
          simpa [hcountZero, hpaddedNe] using hnextPhaseRaw
      have hnextContent :
          (scalarStep state chunk).word[8]! ≤
            (scalarStep state chunk).word[9]! := by
        have hcontentNext :
            (if state.word[8]! > 8 then state.word[8]! - 8 else 0) ≤
              state.word[9]! - 8 := by
          by_cases hcontentHigh : state.word[8]! > 8
          · simp only [hcontentHigh, ↓reduceIte]
            have h8Content : (8 : UInt64) ≤ state.word[8]! :=
              Nat.le_of_lt hcontentHigh
            have h8Padded : (8 : UInt64) ≤ state.word[9]! :=
              Nat.le_trans h8Content hcontent
            rw [UInt64.le_iff_toNat_le,
              UInt64.toNat_sub_of_le _ _ h8Content,
              UInt64.toNat_sub_of_le _ _ h8Padded]
            rw [UInt64.le_iff_toNat_le] at hcontent
            omega
          · simp only [hcontentHigh, ↓reduceIte, UInt64.zero_le]
        rw [hnextContentRaw, hnextPaddedRaw]
        exact hcontentNext
      have hnextPadded :
          (scalarStep state chunk).word[9]! = UInt64.ofNat (count * 8) := by
        rw [hnextPaddedRaw, hpadded]
        have hpaddedLt : (count + 1) * 8 < UInt64.size := by
          have : (count + 1) * 8 < total := by omega
          exact Nat.lt_trans this htotalLt
        have h8Nat : (8 : UInt64).toNat = 8 := by decide
        apply UInt64.toNat.inj
        rw [UInt64.toNat_sub_of_le]
        · rw [UInt64.toNat_ofNat_of_lt' hpaddedLt]
          have hcountLt : count * 8 < UInt64.size := by omega
          rw [UInt64.toNat_ofNat_of_lt' hcountLt, h8Nat]
          omega
        · rw [UInt64.le_iff_toNat_le, h8Nat,
            UInt64.toNat_ofNat_of_lt' hpaddedLt]
          omega
      have hnextSawMap :
          (scalarStep state chunk).word[10]! ≤ 1 := by
        rw [hnextSawMapRaw]
        exact hsawMap
      have hnextUsable :
          (scalarStep state chunk).word[14]! ≤ 1 := by
        rw [hnextUsableRaw]
        exact husable
      have hnextBlocked :
          (scalarStep state chunk).word[15]! ≤ 1 := by
        rw [hnextBlockedRaw]
        exact hblocked
      have hnextTagCount :
          (scalarStep state chunk).word[18]! ≤ 64 := by
        rw [hnextTagCountRaw]
        exact htagCount
      obtain ⟨after, hspan, hafter⟩ :=
        ih (index := index + 1) (state := scalarStep state chunk)
          (by omega) hnextVersion hnextStatus haccepted hnextIdentity
          hnextExtent hnextOffset hnextPhase hnextContent hnextPadded
          hnextSawMap hnextUsable hnextBlocked hnextTarget hnextTagCount
      refine ⟨after, ?_, ?_⟩
      · rw [hbody]
        exact SuccessfulIgnoredTagSpan.step state after chunk
          (((canonicalChunks identity bytes).drop (index + 1)).take count)
          hphaseIgnored haccepted hspan
      · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hafter

/-- The continuation retained by one rich ignored-tag constructor fixes the
next tag header after its aligned body.  Consequently the intervening
canonical chunks satisfy the source-indexed span theorem above: their count is
the rounded tag size minus the already-consumed header, and the next retained
header proves that none of them is terminal. -/
theorem successfulIgnoredTagSpan_of_ignoredTagTraversal
    (identity : UInt64) (bytes : List UInt8)
    (total offset fuel tagWord target : Nat) (sawMemoryMap : Bool)
    (tagsRev tags : List Tag) (state : ScalarState)
    (htotal : total = bytes.length)
    (htotalLow : 16 ≤ total)
    (htotalHigh : total ≤ maxTagBytes)
    (htotalAligned : total % 8 = 0)
    (hoffsetAligned : offset % 8 = 0)
    (hidentityAligned : identity % 8 = 0)
    (hsize : 8 ≤ high32Nat tagWord)
    (hrest :
      SuccessfulTagDecodeTraversal bytes total
        (offset + aligned8 (high32Nat tagWord)) fuel sawMemoryMap
        (.ignored (high32Nat tagWord) :: tagsRev) tags)
    (hversion :
      state.word[0]! = BootMemoryMapStreamAuthority.abiVersion)
    (hstatus :
      state.word[1]! = BootMemoryMapStreamAuthority.active)
    (herror :
      state.word[2]! = BootMemoryMapStreamAuthority.noError)
    (hidentity : state.word[3]! = identity)
    (hextent : state.word[4]! = UInt64.ofNat total)
    (hoffset : state.word[5]! = UInt64.ofNat (offset + 8))
    (hphase :
      state.word[7]! =
        if aligned8 (high32Nat tagWord) = 8
        then BootMemoryMapStreamAuthority.phaseTag
        else BootMemoryMapStreamAuthority.phaseIgnored)
    (hcontent : state.word[8]! ≤ state.word[9]!)
    (hpadded :
      state.word[9]! =
        UInt64.ofNat (aligned8 (high32Nat tagWord) - 8))
    (hsawMap : state.word[10]! ≤ 1)
    (husable : state.word[14]! ≤ 1)
    (hblocked : state.word[15]! ≤ 1)
    (htargetWord : state.word[16]! = UInt64.ofNat target)
    (htarget : target < frameLimit)
    (htagCount : state.word[18]! ≤ 64) :
    let bodyIndex := offset / 8 + 1
    let bodyCount := aligned8 (high32Nat tagWord) / 8 - 1
    let body :=
      ((canonicalChunks identity bytes).drop bodyIndex).take bodyCount
    ∃ after,
      SuccessfulIgnoredTagSpan state body after ∧
        after.word[0]! = BootMemoryMapStreamAuthority.abiVersion ∧
        after.word[1]! = BootMemoryMapStreamAuthority.active ∧
        after.word[2]! = BootMemoryMapStreamAuthority.noError ∧
        after.word[3]! = identity ∧
        after.word[4]! = UInt64.ofNat total ∧
        after.word[5]! =
          UInt64.ofNat (offset + aligned8 (high32Nat tagWord)) ∧
        after.word[7]! = BootMemoryMapStreamAuthority.phaseTag ∧
        after.word[8]! = 0 ∧
        after.word[9]! = 0 ∧
        after.word[10]! ≤ 1 ∧
        after.word[14]! ≤ 1 ∧
        after.word[15]! ≤ 1 ∧
        after.word[16]! = UInt64.ofNat target ∧
        after.word[18]! ≤ 64 := by
  dsimp only
  let advance := aligned8 (high32Nat tagWord)
  let bodyIndex := offset / 8 + 1
  let bodyCount := advance / 8 - 1
  have hadvanceLow : 8 ≤ advance := by
    unfold advance aligned8
    omega
  have hadvanceAligned : advance % 8 = 0 := by
    unfold advance aligned8
    omega
  have hoffsetWords : offset / 8 * 8 = offset := by
    have := Nat.mod_add_div offset 8
    rw [hoffsetAligned, Nat.zero_add] at this
    simpa [Nat.mul_comm] using this
  have hadvanceWords : advance / 8 * 8 = advance := by
    have := Nat.mod_add_div advance 8
    rw [hadvanceAligned, Nat.zero_add] at this
    simpa [Nat.mul_comm] using this
  have hbodyBytes : bodyCount * 8 = advance - 8 := by
    unfold bodyCount
    omega
  have hbodyOffset : bodyIndex * 8 = offset + 8 := by
    unfold bodyIndex
    omega
  have hnextBound :=
    successfulTagDecodeTraversal_offset_lt_total bytes total
      (offset + aligned8 (high32Nat tagWord)) fuel sawMemoryMap
      (.ignored (high32Nat tagWord) :: tagsRev) tags hrest
  have htotalWords : total / 8 * 8 = total := by
    have := Nat.mod_add_div total 8
    rw [htotalAligned, Nat.zero_add] at this
    simpa [Nat.mul_comm] using this
  have hroom : bodyIndex + bodyCount < total / 8 := by
    unfold bodyIndex bodyCount advance at *
    omega
  have hbodyPhase :
      state.word[7]! =
        if bodyCount = 0 then BootMemoryMapStreamAuthority.phaseTag
        else BootMemoryMapStreamAuthority.phaseIgnored := by
    unfold bodyCount advance
    by_cases hrounded : aligned8 (high32Nat tagWord) = 8
    · simp [hrounded, hphase]
    · have : aligned8 (high32Nat tagWord) / 8 - 1 ≠ 0 := by
        omega
      simp [hrounded, this, hphase]
  have hbodyPadded :
      state.word[9]! = UInt64.ofNat (bodyCount * 8) := by
    rw [hbodyBytes]
    exact hpadded
  obtain ⟨after, hspan, hafter⟩ :=
    successfulIgnoredTagSpan_canonical identity bytes total bodyIndex
      bodyCount target state htotal htotalLow htotalHigh htotalAligned
      hidentityAligned hroom hversion hstatus herror hidentity hextent
      (by simpa [hbodyOffset] using hoffset) hbodyPhase hcontent hbodyPadded
      hsawMap husable hblocked htargetWord htarget htagCount
  rcases hafter with ⟨hafterVersion, hafterStatus, hafterError,
    hafterIdentity, hafterExtent, hafterOffset, hafterPhase,
    hafterContent, hafterPadded, hafterSawMap, hafterUsable,
    hafterBlocked, hafterTarget, hafterTagCount⟩
  have hafterOffsetNat :
      (bodyIndex + bodyCount) * 8 = offset + advance := by
    omega
  refine ⟨after, hspan, ?_⟩
  refine ⟨hafterVersion, hafterStatus, hafterError, hafterIdentity,
    hafterExtent, ?_, hafterPhase, hafterContent, hafterPadded,
    hafterSawMap, hafterUsable, hafterBlocked, hafterTarget, hafterTagCount⟩
  simpa [hafterOffsetNat, advance] using hafterOffset

/-- A complete accepted ignored-tag span composes around any later
scalar/rich traversal.  This turns the one-word body rule into the induction
step needed for arbitrary ignored payload and alignment padding. -/
theorem successfulScalarRichTraversal_ignoredTagSpan
    (target : Nat) (entries : List RawEntry)
    (state after terminal : ScalarState)
    (body rest : List ModelChunk)
    (hspan : SuccessfulIgnoredTagSpan state body after)
    (hrest :
      SuccessfulScalarRichTraversal target entries after rest terminal) :
    SuccessfulScalarRichTraversal target entries state
      (body ++ rest) terminal := by
  induction hspan with
  | done state =>
      exact hrest
  | step state after chunk body hphase haccepted hbody ih =>
      rw [List.cons_append]
      apply SuccessfulScalarRichTraversal.nonEntry entries state terminal
        chunk (body ++ rest)
      · rw [hphase]
        decide
      · exact haccepted
      · exact ih hrest

/-- A rich ignored-tag continuation now supplies the exact canonical body
certificate expected by `successfulScalarRichTraversal_ignoredTagSpan`.
This corollary exposes the composition step without inventing a shadow body
list or a caller-selected intermediate scalar state. -/
theorem successfulScalarRichTraversal_ignoredTagTraversal
    (identity : UInt64) (bytes : List UInt8)
    (total offset fuel tagWord target : Nat) (sawMemoryMap : Bool)
    (tagsRev tags : List Tag) (state terminal : ScalarState)
    (entries : List RawEntry) (rest : List ModelChunk)
    (htotal : total = bytes.length)
    (htotalLow : 16 ≤ total)
    (htotalHigh : total ≤ maxTagBytes)
    (htotalAligned : total % 8 = 0)
    (hoffsetAligned : offset % 8 = 0)
    (hidentityAligned : identity % 8 = 0)
    (hsize : 8 ≤ high32Nat tagWord)
    (htagRest :
      SuccessfulTagDecodeTraversal bytes total
        (offset + aligned8 (high32Nat tagWord)) fuel sawMemoryMap
        (.ignored (high32Nat tagWord) :: tagsRev) tags)
    (hversion :
      state.word[0]! = BootMemoryMapStreamAuthority.abiVersion)
    (hstatus :
      state.word[1]! = BootMemoryMapStreamAuthority.active)
    (herror :
      state.word[2]! = BootMemoryMapStreamAuthority.noError)
    (hidentity : state.word[3]! = identity)
    (hextent : state.word[4]! = UInt64.ofNat total)
    (hoffset : state.word[5]! = UInt64.ofNat (offset + 8))
    (hphase :
      state.word[7]! =
        if aligned8 (high32Nat tagWord) = 8
        then BootMemoryMapStreamAuthority.phaseTag
        else BootMemoryMapStreamAuthority.phaseIgnored)
    (hcontent : state.word[8]! ≤ state.word[9]!)
    (hpadded :
      state.word[9]! =
        UInt64.ofNat (aligned8 (high32Nat tagWord) - 8))
    (hsawMap : state.word[10]! ≤ 1)
    (husable : state.word[14]! ≤ 1)
    (hblocked : state.word[15]! ≤ 1)
    (htargetWord : state.word[16]! = UInt64.ofNat target)
    (htarget : target < frameLimit)
    (htagCount : state.word[18]! ≤ 64) :
    let bodyIndex := offset / 8 + 1
    let bodyCount := aligned8 (high32Nat tagWord) / 8 - 1
    let body :=
      ((canonicalChunks identity bytes).drop bodyIndex).take bodyCount
    ∃ after,
      SuccessfulIgnoredTagSpan state body after ∧
        (SuccessfulScalarRichTraversal target entries after rest terminal →
          SuccessfulScalarRichTraversal target entries state
            (body ++ rest) terminal) := by
  dsimp only
  obtain ⟨after, hspan, hafter⟩ :=
    successfulIgnoredTagSpan_of_ignoredTagTraversal identity bytes total
      offset fuel tagWord target sawMemoryMap tagsRev tags state htotal
      htotalLow htotalHigh htotalAligned hoffsetAligned hidentityAligned
      hsize htagRest hversion hstatus herror hidentity hextent hoffset hphase
      hcontent hpadded hsawMap husable hblocked htargetWord htarget htagCount
  refine ⟨after, hspan, ?_⟩
  exact fun htail =>
    successfulScalarRichTraversal_ignoredTagSpan target entries state after
      terminal
      (((canonicalChunks identity bytes).drop (offset / 8 + 1)).take
        (aligned8 (high32Nat tagWord) / 8 - 1))
      rest hspan htail

/-- One admitted unique memory-map header is a non-entry traversal step.  The
production transition enters the layout phase with the exact entry-byte count
and the continuation carries the subsequent layout and entry traversal. -/
theorem successfulScalarRichTraversal_memoryMapTagHeader
    (identity extent offset word : UInt64) (target : Nat)
    (entries : List RawEntry) (state terminal : ScalarState)
    (chunk : ModelChunk) (rest : List ModelChunk)
    (hchunkIdentity : chunk.identity = identity)
    (hchunkOffset : UInt64.ofNat chunk.offset = offset)
    (hchunkTerminal : chunk.terminal = false)
    (hchunkWord : chunkWord chunk.bytes = word)
    (hversion :
      state.word[0]! = BootMemoryMapStreamAuthority.abiVersion)
    (hstatus :
      state.word[1]! = BootMemoryMapStreamAuthority.active)
    (herror :
      state.word[2]! = BootMemoryMapStreamAuthority.noError)
    (hidentity : state.word[3]! = identity)
    (hidentityAligned : identity % 8 = 0)
    (hextent : state.word[4]! = extent)
    (hextentLow : 16 ≤ extent)
    (hextentHigh : extent ≤ 65536)
    (hextentAligned : extent % 8 = 0)
    (hoffset : state.word[5]! = offset)
    (hoffsetLt : offset < extent)
    (hoffsetNotFinal : offset + 8 ≠ extent)
    (hphase :
      state.word[7]! = BootMemoryMapStreamAuthority.phaseTag)
    (hsawMap : state.word[10]! = 0)
    (husable : state.word[14]! ≤ 1)
    (hblocked : state.word[15]! ≤ 1)
    (htargetWord : state.word[16]! = UInt64.ofNat target)
    (htarget : target < frameLimit)
    (htagCount : state.word[18]! < 64)
    (htype : BootMemoryMapStreamAuthority.low32 word = 6)
    (hsizeLow : 16 ≤ BootMemoryMapStreamAuthority.high32 word)
    (hsizeFits :
      BootMemoryMapStreamAuthority.high32 word ≤ extent - offset)
    (hsizeNoOverflow :
      BootMemoryMapStreamAuthority.high32 word ≤ 0xfffffffffffffff8)
    (hroundedFits :
      ((BootMemoryMapStreamAuthority.high32 word + 7) &&&
          0xfffffffffffffff8) ≤ extent - offset)
    (halignedEntries :
      (BootMemoryMapStreamAuthority.high32 word - 16) % 24 = 0)
    (hentryBound :
      (BootMemoryMapStreamAuthority.high32 word - 16) / 24 ≤
        BootMemoryMapStreamAuthority.entryLimit)
    (hrest :
      SuccessfulScalarRichTraversal target entries
        (scalarStep state chunk) rest terminal) :
    SuccessfulScalarRichTraversal target entries state
      (chunk :: rest) terminal := by
  have htargetLt : target < UInt64.size :=
    Nat.lt_trans htarget (by decide)
  have htargetBound : UInt64.ofNat target < 4096 := by
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat_of_lt' htargetLt]
    simpa [frameLimit, physicalLimit, pageBytes] using htarget
  have hstep :=
    BootMemoryMapStreamAuthority.memoryMapTagHeaderStepWords_of_admitted
      identity extent offset state.word[6]! state.word[8]! state.word[9]!
      state.word[11]! state.word[12]! state.word[13]!
      state.word[14]! state.word[15]! (UInt64.ofNat target)
      state.word[17]! state.word[18]! word
      hidentityAligned hextentLow hextentHigh hextentAligned hoffsetLt
      hoffsetNotFinal husable hblocked htargetBound htagCount htype hsizeLow
      hsizeFits hsizeNoOverflow hroundedFits halignedEntries hentryBound
  apply SuccessfulScalarRichTraversal.nonEntry entries state terminal chunk rest
  · rw [hphase]
    decide
  · simpa [scalarStep, hchunkIdentity, hchunkOffset, hchunkTerminal, hchunkWord,
      hversion, hstatus, herror, hidentity, hextent, hoffset, hphase,
      hsawMap, htargetWord] using hstep.2.2.1
  · exact hrest

/-- The retained rich end-tag constructor and an admitted scalar tag cursor
construct the terminal one-chunk tail of `SuccessfulScalarRichTraversal`.
The scalar completion status is derived from `stepWord`; no terminal word is
assumed or compared against a caller-provided rich result. -/
theorem successfulScalarRichTraversal_endTag
    (identity : UInt64) (total offset tagWord target : Nat)
    (state : ScalarState) (chunk : ModelChunk)
    (htotalLow : 16 ≤ total)
    (htotalHigh : total ≤ maxTagBytes)
    (htotalAligned : total % 8 = 0)
    (hoffsetEnd : offset + 8 = total)
    (hchunkIdentity : chunk.identity = identity)
    (hchunkOffset : chunk.offset = offset)
    (hchunkTerminal : chunk.terminal = true)
    (hread : readU64 chunk.bytes 0 = .ok tagWord)
    (htype : low32Nat tagWord = 0)
    (hsize : high32Nat tagWord = 8)
    (hversion :
      state.word[0]! = BootMemoryMapStreamAuthority.abiVersion)
    (hstatus :
      state.word[1]! = BootMemoryMapStreamAuthority.active)
    (herror :
      state.word[2]! = BootMemoryMapStreamAuthority.noError)
    (hidentity : state.word[3]! = identity)
    (hidentityAligned : identity % 8 = 0)
    (hextent : state.word[4]! = UInt64.ofNat total)
    (hoffset : state.word[5]! = UInt64.ofNat offset)
    (hphase :
      state.word[7]! = BootMemoryMapStreamAuthority.phaseTag)
    (hsawMap : state.word[10]! = 1)
    (husable : state.word[14]! ≤ 1)
    (hblocked : state.word[15]! ≤ 1)
    (htargetWord : state.word[16]! = UInt64.ofNat target)
    (htarget : target < frameLimit)
    (htagCount : state.word[18]! < 64) :
    SuccessfulScalarRichTraversal target [] state [chunk]
      (scalarStep state chunk) := by
  have htotalLt : total < UInt64.size :=
    Nat.lt_of_le_of_lt htotalHigh (by decide)
  have htargetLt : target < UInt64.size :=
    Nat.lt_trans htarget (by decide)
  have hextentLow : 16 ≤ UInt64.ofNat total := by
    rw [UInt64.le_iff_toNat_le, UInt64.toNat_ofNat_of_lt' htotalLt]
    exact htotalLow
  have hextentHigh : UInt64.ofNat total ≤ 65536 := by
    rw [UInt64.le_iff_toNat_le, UInt64.toNat_ofNat_of_lt' htotalLt]
    simpa [maxTagBytes] using htotalHigh
  have hextentAligned : UInt64.ofNat total % 8 = 0 := by
    apply UInt64.toNat.inj
    simp [UInt64.toNat_ofNat_of_lt' htotalLt, htotalAligned]
  have hoffsetWord :
      UInt64.ofNat offset + 8 = UInt64.ofNat total := by
    rw [← hoffsetEnd]
    simp
  have htargetBound : UInt64.ofNat target < 4096 := by
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat_of_lt' htargetLt]
    simpa [frameLimit, physicalLimit, pageBytes] using htarget
  have htagWordLt := readU64_lt_wordLimit chunk.bytes 0 tagWord hread
  have hchunkWord : chunkWord chunk.bytes = UInt64.ofNat tagWord :=
    chunkWord_readU64_agreement chunk.bytes tagWord hread
  have hchunkLow :
      BootMemoryMapStreamAuthority.low32 (UInt64.ofNat tagWord) = 0 := by
    rw [BootMemoryMapStreamAuthority.low32, low32Word_ofNat tagWord htagWordLt,
      htype]
    rfl
  have hchunkHigh :
      BootMemoryMapStreamAuthority.high32 (UInt64.ofNat tagWord) = 8 := by
    rw [BootMemoryMapStreamAuthority.high32,
      high32Word_ofNat tagWord htagWordLt, hsize]
    rfl
  have hstep :=
    BootMemoryMapStreamAuthority.endTagStepWords_of_admitted
      identity (UInt64.ofNat total) (UInt64.ofNat offset)
      state.word[6]! state.word[8]! state.word[9]!
      state.word[11]! state.word[12]! state.word[13]!
      state.word[14]! state.word[15]! (UInt64.ofNat target)
      state.word[17]! state.word[18]! (UInt64.ofNat tagWord)
      hidentityAligned hextentLow hextentHigh hextentAligned
      hoffsetWord husable hblocked htargetBound htagCount
      hchunkLow hchunkHigh
  have haccepted :
      (scalarStep state chunk).word[2]! =
        BootMemoryMapStreamAuthority.noError := by
    simpa [scalarStep, hchunkWord, hchunkIdentity, hchunkOffset,
      hchunkTerminal, hversion, hstatus, herror, hidentity, hextent,
      hoffset, hphase, hsawMap, htargetWord] using hstep.2.2.1
  apply SuccessfulScalarRichTraversal.nonEntry [] state
    (scalarStep state chunk) chunk []
  · rw [hphase]
    decide
  · exact haccepted
  · apply SuccessfulScalarRichTraversal.done
    · simpa [scalarStep, hchunkWord, hchunkIdentity, hchunkOffset,
        hchunkTerminal, hversion, hstatus, herror, hidentity, hextent,
        hoffset, hphase, hsawMap, htargetWord] using hstep.2.1
    · exact haccepted

/-- Direct whole-replay induction over an arbitrary successful traversal.
The terminal status and diagnostic are fixed by successful completion, while
words 14 and 15 are the left folds of every exact rich entry encountered by
the traversal. -/
theorem successfulScalarRichTraversal_terminal_words
    (target : Nat) (entries : List RawEntry)
    (initial terminal : ScalarState) (chunks : List ModelChunk)
    (h :
      SuccessfulScalarRichTraversal target entries initial chunks terminal) :
    scalarReplay chunks initial = terminal ∧
      terminal.word[1]! = BootMemoryMapStreamAuthority.complete ∧
      terminal.word[2]! = BootMemoryMapStreamAuthority.noError ∧
      terminal.word[14]! =
        entries.foldl (updateUsableClassification target) initial.word[14]! ∧
      terminal.word[15]! =
        entries.foldl (updateBlockedClassification target) initial.word[15]! := by
  induction h with
  | done state hstatus herror =>
      exact ⟨rfl, hstatus, herror, rfl, rfl⟩
  | nonEntry entries state terminal chunk rest hphase haccepted hrest ih =>
      have hpreserved :=
        scalarStep_nonEntry_preserves_classification state chunk hphase haccepted
      simp [scalarReplay, haccepted]
      exact ⟨ih.1, ih.2.1, ih.2.2.1,
        by simpa [hpreserved.1] using ih.2.2.2.1,
        by simpa [hpreserved.2] using ih.2.2.2.2⟩
  | entry base length kind entries state terminal chunk rest hphase hbaseWord
      hlengthWord htargetWord hchunkWord haccepted hbase hstop hkind htarget
      hrest ih =>
      have hclassified :=
        scalarStep_entryType_classifies_rich state chunk base length kind target
          hphase hbaseWord hlengthWord htargetWord hchunkWord haccepted
          hbase hstop hkind htarget
      simp [scalarReplay, haccepted]
      refine ⟨ih.1, ih.2.1, ih.2.2.1, ?_, ?_⟩
      · simpa [List.foldl_cons, updateUsableClassification, hclassified.1]
          using ih.2.2.2.1
      · simpa [List.foldl_cons, updateBlockedClassification, hclassified.2]
          using ih.2.2.2.2

/-- Folding the usable classification from the canonical zero accumulator is
exactly the complete-list usable word consumed by the rich/scalar boundary. -/
theorem foldl_updateUsableClassification_zero
    (entries : List RawEntry) (target : Nat) :
    entries.foldl (updateUsableClassification target) 0 =
      (if entries.any (fun entry =>
          entry.kind == MemoryKind.usable &&
            covers entry (target * pageBytes) (target * pageBytes + pageBytes))
        then 1 else 0) := by
  have sticky (rest : List RawEntry) :
      rest.foldl (updateUsableClassification target) 1 = 1 := by
    induction rest with
    | nil => rfl
    | cons entry rest ih =>
        simp only [List.foldl_cons]
        simp [updateUsableClassification, ih]
  induction entries with
  | nil =>
      rfl
  | cons entry entries ih =>
      simp only [List.foldl_cons, List.any_cons]
      by_cases hentry :
          entry.kind == MemoryKind.usable &&
            covers entry (target * pageBytes) (target * pageBytes + pageBytes)
      · simp [updateUsableClassification, hentry, sticky]
      · simp [updateUsableClassification, hentry, ih]

/-- Folding the non-usable overlap classification from zero is exactly the
complete-list blocked word. -/
theorem foldl_updateBlockedClassification_zero
    (entries : List RawEntry) (target : Nat) :
    entries.foldl (updateBlockedClassification target) 0 =
      (if entries.any (fun entry =>
          entry.kind != MemoryKind.usable &&
            overlaps entry (target * pageBytes) (target * pageBytes + pageBytes))
        then 1 else 0) := by
  have sticky (rest : List RawEntry) :
      rest.foldl (updateBlockedClassification target) 1 = 1 := by
    induction rest with
    | nil => rfl
    | cons entry rest ih =>
        simp only [List.foldl_cons]
        simp [updateBlockedClassification, ih]
  induction entries with
  | nil =>
      rfl
  | cons entry entries ih =>
      simp only [List.foldl_cons, List.any_cons]
      by_cases hentry :
          entry.kind != MemoryKind.usable &&
            overlaps entry (target * pageBytes) (target * pageBytes + pageBytes)
      · simp [updateBlockedClassification, hentry, sticky]
      · simp [updateBlockedClassification, hentry, ih]

/-- Whole-replay terminal classification from the canonical zero
accumulators.  This is the direct-induction replacement for a terminal
fail-closed comparison once the rich decoder supplies a
`SuccessfulScalarRichTraversal` certificate. -/
theorem successfulScalarRichTraversal_canonical_terminal
    (target : Nat) (entries : List RawEntry)
    (initial terminal : ScalarState) (chunks : List ModelChunk)
    (husable : initial.word[14]! = 0)
    (hblocked : initial.word[15]! = 0)
    (h :
      SuccessfulScalarRichTraversal target entries initial chunks terminal) :
    scalarReplay chunks initial = terminal ∧
      terminal.word[1]! = BootMemoryMapStreamAuthority.complete ∧
      terminal.word[2]! = BootMemoryMapStreamAuthority.noError ∧
      terminal.word[14]! =
        (if entries.any (fun entry =>
            entry.kind == MemoryKind.usable &&
              covers entry (target * pageBytes) (target * pageBytes + pageBytes))
          then 1 else 0) ∧
      terminal.word[15]! =
        (if entries.any (fun entry =>
            entry.kind != MemoryKind.usable &&
              overlaps entry (target * pageBytes) (target * pageBytes + pageBytes))
          then 1 else 0) := by
  have hterminal :=
    successfulScalarRichTraversal_terminal_words target entries initial terminal chunks h
  rw [husable, hblocked,
    foldl_updateUsableClassification_zero entries target,
    foldl_updateBlockedClassification_zero entries target] at hterminal
  exact hterminal

/-- Each word of an arbitrary accepted rich-byte scalar step is exactly the
corresponding generated transition queried with the decoder-agreed packed
word.  No fixture, initial-state, or parser-phase assumption is required. -/
theorem scalarStep_readU64_refines
    (state : ScalarState) (chunk : ModelChunk) (value : Nat)
    (hread : BootMemoryMapDecoder.readU64 chunk.bytes 0 = .ok value)
    (query : Fin 19) :
    (scalarStep state chunk).word[query.val]! =
      BootMemoryMapStreamAuthority.stepWord
        state.word[0]! state.word[1]! state.word[2]! state.word[3]!
        state.word[4]! state.word[5]! state.word[6]! state.word[7]!
        state.word[8]! state.word[9]! state.word[10]! state.word[11]!
        state.word[12]! state.word[13]! state.word[14]! state.word[15]!
        state.word[16]! state.word[17]! state.word[18]!
        chunk.identity (UInt64.ofNat chunk.offset) (UInt64.ofNat value)
        (if chunk.terminal then 1 else 0) (UInt64.ofNat query.val) := by
  simp [scalarStep, chunkWord_readU64_agreement _ _ hread]

/-- At every canonical list index, the scalar transition consumes the exact
rich-decoder word at the corresponding immutable source offset.  This is the
index-local checkpoint needed before inducting over parser phases: identity,
offset, bytes, terminal status, and packed word all come from one canonical
source position. -/
theorem canonicalScalarStep_source_refines
    (identity : UInt64) (bytes : List UInt8)
    (haligned : bytes.length % 8 = 0)
    (index : Nat) (hindex : index < bytes.length / 8)
    (state : ScalarState) (value : Nat)
    (hread :
      BootMemoryMapDecoder.readU64 bytes (index * 8) = .ok value)
    (query : Fin 19) :
    let chunk : ModelChunk :=
      { identity
        offset := index * 8
        bytes := (bytes.drop (index * 8)).take 8
        terminal := index + 1 == bytes.length / 8 }
    (canonicalChunks identity bytes)[index]? = some chunk ∧
      (scalarStep state chunk).word[query.val]! =
        BootMemoryMapStreamAuthority.stepWord
          state.word[0]! state.word[1]! state.word[2]! state.word[3]!
          state.word[4]! state.word[5]! state.word[6]! state.word[7]!
          state.word[8]! state.word[9]! state.word[10]! state.word[11]!
          state.word[12]! state.word[13]! state.word[14]! state.word[15]!
          state.word[16]! state.word[17]! state.word[18]!
          identity (UInt64.ofNat (index * 8)) (UInt64.ofNat value)
          (if index + 1 == bytes.length / 8 then 1 else 0)
          (UInt64.ofNat query.val) := by
  dsimp only
  have hchunk :=
    canonicalChunks_get?_source identity bytes haligned index hindex
  have hchunkRead :
      BootMemoryMapDecoder.readU64
          ((bytes.drop (index * 8)).take 8) 0 =
        .ok value := by
    rw [BootMemoryMapDecoder.readU64_drop_take]
    exact hread
  exact ⟨hchunk,
    scalarStep_readU64_refines state
      { identity
        offset := index * 8
        bytes := (bytes.drop (index * 8)).take 8
        terminal := index + 1 == bytes.length / 8 }
      value hchunkRead query⟩

/-- Every retained tag traversal exposes its current header as the canonical
chunk at the corresponding byte offset.  This offset-parametric form carries
the exact terminal bit as well as the rich-decoder word, so a structural
induction can reuse one source lemma for ignored, map, and end-tag cases. -/
theorem canonicalTagStep_source_refines
    (identity : UInt64) (bytes : List UInt8) (total offset fuel : Nat)
    (sawMemoryMap : Bool) (tagsRev tags : List Tag) (state : ScalarState)
    (htotal : total = bytes.length)
    (haligned : bytes.length % 8 = 0)
    (hoffsetAligned : offset % 8 = 0)
    (htraversal :
      SuccessfulTagDecodeTraversal bytes total offset fuel
        sawMemoryMap tagsRev tags) :
    ∃ tagWord,
      let terminal := offset + 8 == total
      let chunk : ModelChunk :=
        { identity
          offset
          bytes := (bytes.drop offset).take 8
          terminal }
      BootMemoryMapDecoder.readU64 bytes offset = .ok tagWord ∧
        (canonicalChunks identity bytes)[offset / 8]? = some chunk ∧
        ∀ query : Fin 19,
          (scalarStep state chunk).word[query.val]! =
            BootMemoryMapStreamAuthority.stepWord
              state.word[0]! state.word[1]! state.word[2]! state.word[3]!
              state.word[4]! state.word[5]! state.word[6]! state.word[7]!
              state.word[8]! state.word[9]! state.word[10]! state.word[11]!
              state.word[12]! state.word[13]! state.word[14]! state.word[15]!
              state.word[16]! state.word[17]! state.word[18]!
              identity (UInt64.ofNat offset) (UInt64.ofNat tagWord)
              (if terminal then 1 else 0) (UInt64.ofNat query.val) := by
  have hbound :=
    successfulTagDecodeTraversal_offset_lt_total
      bytes total offset fuel sawMemoryMap tagsRev tags htraversal
  have hoffset := Nat.mod_add_div offset 8
  rw [hoffsetAligned, Nat.zero_add] at hoffset
  have hposition : offset / 8 * 8 = offset := by
    omega
  have hbytes := Nat.mod_add_div bytes.length 8
  rw [haligned, Nat.zero_add] at hbytes
  have hindex : offset / 8 < bytes.length / 8 := by
    omega
  have hterminal :
      (offset / 8 + 1 == bytes.length / 8) =
        (offset + 8 == total) := by
    rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
    omega
  cases htraversal with
  | endTag offset fuel tagWord tagsRev hread htype hsize hend =>
      refine ⟨tagWord, ?_⟩
      dsimp only
      have hrefines :=
        canonicalScalarStep_source_refines
          identity bytes haligned (offset / 8) hindex state tagWord (by
            rw [hposition]
            exact hread)
      refine ⟨hread, ?_, ?_⟩
      · simpa only [hposition, hterminal] using
          (hrefines (⟨0, by decide⟩ : Fin 19)).1
      · intro query
        simpa only [hposition, hterminal] using (hrefines query).2
  | ignoredTag offset fuel tagWord sawMemoryMap tagsRev tags hread hsize
      hcontent hadvance htypeEnd htypeMap hrest =>
      refine ⟨tagWord, ?_⟩
      dsimp only
      have hrefines :=
        canonicalScalarStep_source_refines
          identity bytes haligned (offset / 8) hindex state tagWord (by
            rw [hposition]
            exact hread)
      refine ⟨hread, ?_, ?_⟩
      · simpa only [hposition, hterminal] using
          (hrefines (⟨0, by decide⟩ : Fin 19)).1
      · intro query
        simpa only [hposition, hterminal] using (hrefines query).2
  | memoryMapTag offset fuel tagWord layoutWord tagsRev tags entries hread
      hsize hcontent hadvance htype hlayout hentrySize hentryVersion
      halignedEntries hentryBound hentryTraversal hrest =>
      refine ⟨tagWord, ?_⟩
      dsimp only
      have hrefines :=
        canonicalScalarStep_source_refines
          identity bytes haligned (offset / 8) hindex state tagWord (by
            rw [hposition]
            exact hread)
      refine ⟨hread, ?_, ?_⟩
      · simpa only [hposition, hterminal] using
          (hrefines (⟨0, by decide⟩ : Fin 19)).1
      · intro query
        simpa only [hposition, hterminal] using (hrefines query).2

/-- The retained rich tag traversal selects the exact first tag-header chunk
immediately after the information header.  Its source word, stream identity,
offset, terminal bit, and every scalar transition query are therefore fixed
by the immutable input.  This is the tag-phase source checkpoint used before
splitting the structural induction into ignored, map, and end-tag cases. -/
theorem canonicalFirstTagStep_source_refines
    (input : Input) (decoded : Decoded) (state : ScalarState)
    (hdecode : decode input = .ok decoded)
    (htraversal : SuccessfulRichDecodeTraversal input decoded) :
    ∃ tagWord,
      let identity := UInt64.ofNat input.infoAddress
      let chunk : ModelChunk :=
        { identity
          offset := 8
          bytes := (input.bytes.drop 8).take 8
          terminal := false }
      BootMemoryMapDecoder.readU64 input.bytes 8 = .ok tagWord ∧
        (canonicalChunks identity input.bytes)[1]? = some chunk ∧
        ∀ query : Fin 19,
          (scalarStep state chunk).word[query.val]! =
            BootMemoryMapStreamAuthority.stepWord
              state.word[0]! state.word[1]! state.word[2]! state.word[3]!
              state.word[4]! state.word[5]! state.word[6]! state.word[7]!
              state.word[8]! state.word[9]! state.word[10]! state.word[11]!
              state.word[12]! state.word[13]! state.word[14]! state.word[15]!
              state.word[16]! state.word[17]! state.word[18]!
              identity 8 (UInt64.ofNat tagWord) 0
              (UInt64.ofNat query.val) := by
  obtain ⟨infoWord, tags, hinfo, htotal, hreserved, htags, htagTraversal,
    hhandoff, hvalid, hentries, hbounds⟩ := htraversal.traversed
  have htagBound :=
    successfulTagDecodeTraversal_offset_lt_total
      input.bytes (low32Nat infoWord) 8 maxTags false [] tags htagTraversal
  have hheader := accepted_input_scalar_header input decoded hdecode
  have haligned : input.bytes.length % 8 = 0 :=
    hheader.2.2.2.2.2.2.1
  have hindex : 1 < input.bytes.length / 8 := by
    rw [htotal] at htagBound
    have hdiv := Nat.mod_add_div input.bytes.length 8
    rw [haligned, Nat.zero_add] at hdiv
    omega
  cases htagTraversal with
  | ignoredTag offset fuel tagWord sawMemoryMap tagsRev tags hread hsize
      hcontent hadvance htypeEnd htypeMap hrest =>
      have hrestBound :=
        successfulTagDecodeTraversal_offset_lt_total
          input.bytes (low32Nat infoWord)
          (8 + aligned8 (high32Nat tagWord)) (maxTags - 1)
          false [Tag.ignored (high32Nat tagWord)] tags hrest
      rw [htotal] at hrestBound
      have hdiv := Nat.mod_add_div input.bytes.length 8
      rw [haligned, Nat.zero_add] at hdiv
      have hterminal : (2 == input.bytes.length / 8) = false := by
        exact beq_false_of_ne (by
          unfold aligned8 at hrestBound
          omega)
      refine ⟨tagWord, ?_⟩
      dsimp only
      have hrefines :=
        canonicalScalarStep_source_refines
          (UInt64.ofNat input.infoAddress) input.bytes haligned
          1 hindex state tagWord hread
      simp only [hterminal] at hrefines
      exact ⟨hread, (hrefines (⟨0, by decide⟩ : Fin 19)).1,
        fun query => (hrefines query).2⟩
  | memoryMapTag offset fuel tagWord layoutWord tagsRev tags entries hread
      hsize hcontent hadvance htype hlayout hentrySize hentryVersion
      halignedEntries hentryBound hentryTraversal hrest =>
      have hdiv := Nat.mod_add_div input.bytes.length 8
      rw [haligned, Nat.zero_add] at hdiv
      have hterminal : (2 == input.bytes.length / 8) = false := by
        exact beq_false_of_ne (by
          rw [htotal] at hcontent
          simp [memoryMapTagHeaderSize] at hsize
          omega)
      refine ⟨tagWord, ?_⟩
      dsimp only
      have hrefines :=
        canonicalScalarStep_source_refines
          (UInt64.ofNat input.infoAddress) input.bytes haligned
          1 hindex state tagWord hread
      simp only [hterminal] at hrefines
      exact ⟨hread, (hrefines (⟨0, by decide⟩ : Fin 19)).1,
        fun query => (hrefines query).2⟩

/-- Checked byte-side form of one scalar transition.  Unlike `scalarStep`, a
short chunk remains an explicit rich-decoder error rather than being packed as
zero. -/
def checkedScalarStep (state : ScalarState) (chunk : ModelChunk) :
    Except BootMemoryMapDecoder.Error ScalarState := do
  let value ← BootMemoryMapDecoder.readU64 chunk.bytes 0
  pure
    { word := Array.ofFn fun query : Fin 19 =>
        BootMemoryMapStreamAuthority.stepWord
          state.word[0]! state.word[1]! state.word[2]! state.word[3]!
          state.word[4]! state.word[5]! state.word[6]! state.word[7]!
          state.word[8]! state.word[9]! state.word[10]! state.word[11]!
          state.word[12]! state.word[13]! state.word[14]! state.word[15]!
          state.word[16]! state.word[17]! state.word[18]!
          chunk.identity (UInt64.ofNat chunk.offset) (UInt64.ofNat value)
          (if chunk.terminal then 1 else 0) (UInt64.ofNat query.val) }

/-- The checked rich-byte step and scalar step coincide whenever the decoder
can read the complete chunk. -/
theorem checkedScalarStep_eq_scalarStep
    (state : ScalarState) (chunk : ModelChunk) (value : Nat)
    (hread : BootMemoryMapDecoder.readU64 chunk.bytes 0 = .ok value) :
    checkedScalarStep state chunk = .ok (scalarStep state chunk) := by
  unfold checkedScalarStep scalarStep
  rw [hread]
  rw [chunkWord_readU64_agreement chunk.bytes value hread]
  simp [bind, Except.bind, pure, Except.pure]

/-- Whole checked-byte replay.  It mirrors the production loop's early stop on
a scalar diagnostic while retaining short-chunk rejection in the rich
decoder's typed error vocabulary. -/
def checkedScalarReplay : List ModelChunk → ScalarState →
    Except BootMemoryMapDecoder.Error ScalarState
  | [], state => .ok state
  | chunk :: rest, state => do
      let next ← checkedScalarStep state chunk
      if next.word[2]! != BootMemoryMapStreamAuthority.noError then
        pure next
      else
        checkedScalarReplay rest next

/-- If every chunk admits the rich decoder's checked eight-byte read, the
entire checked replay equals the scalar production-model replay, including its
first-error stopping point. -/
theorem checkedScalarReplay_eq_scalarReplay
    (chunks : List ModelChunk) (state : ScalarState)
    (hreads : ∀ chunk ∈ chunks,
      ∃ value, BootMemoryMapDecoder.readU64 chunk.bytes 0 = .ok value) :
    checkedScalarReplay chunks state = .ok (scalarReplay chunks state) := by
  induction chunks generalizing state with
  | nil =>
      rfl
  | cons chunk rest ih =>
      obtain ⟨value, hread⟩ := hreads chunk (by simp)
      rw [checkedScalarReplay, checkedScalarStep_eq_scalarStep state chunk value hread]
      simp only [bind, Except.bind]
      by_cases hrejected :
          (scalarStep state chunk).word[2]! !=
            BootMemoryMapStreamAuthority.noError
      · simp [scalarReplay, hrejected, pure, Except.pure]
      · simp only [scalarReplay, hrejected, Bool.false_eq_true, ↓reduceIte]
        apply ih
        intro member hmember
        exact hreads member (by simp [hmember])

/-- Canonical decomposition of any aligned byte buffer supplies exactly the
checked reads required above. -/
theorem canonicalChunks_readU64
    (identity : UInt64) (bytes : List UInt8)
    (haligned : bytes.length % 8 = 0)
    (chunk : ModelChunk) (hchunk : chunk ∈ canonicalChunks identity bytes) :
    ∃ value, BootMemoryMapDecoder.readU64 chunk.bytes 0 = .ok value := by
  have hlength : chunk.bytes.length = 8 := by
    have aux :
        ∀ count offset (tail : List UInt8) (member : ModelChunk),
          tail.length = count * 8 →
          member ∈ canonicalChunksAux identity offset count tail →
          member.bytes.length = 8 := by
      intro count
      induction count with
      | zero =>
          intro offset tail member _ hmember
          simp [canonicalChunksAux] at hmember
      | succ count ih =>
          intro offset tail member htail hmember
          simp only [canonicalChunksAux, List.mem_cons] at hmember
          rcases hmember with heq | hrest
          · subst member
            simp [List.length_take]
            omega
          · exact ih (offset + 8) (tail.drop 8) member (by
              simp [List.length_drop]
              omega) hrest
    unfold canonicalChunks at hchunk
    apply aux (bytes.length / 8) 0 bytes chunk
    · omega
    · exact hchunk
  exact BootMemoryMapDecoder.readU64_succeeds_of_length chunk.bytes (by omega)

/-- Universal whole-replay scalar/rich chunk equivalence for the canonical
decomposition of an arbitrary aligned immutable byte buffer. -/
theorem checkedScalarReplay_canonical_eq
    (identity : UInt64) (bytes : List UInt8) (state : ScalarState)
    (haligned : bytes.length % 8 = 0) :
    checkedScalarReplay (canonicalChunks identity bytes) state =
      .ok (scalarReplay (canonicalChunks identity bytes) state) := by
  apply checkedScalarReplay_eq_scalarReplay
  intro chunk hchunk
  exact canonicalChunks_readU64 identity bytes haligned chunk hchunk

/-- Universal rich-decoder-to-scalar terminal-state structural refinement.
Every successful rich decode and bounded target supplies the admitted scalar
initial state, and the checked byte-side replay terminates at exactly the same
state as the production-model scalar replay.  This theorem is deliberately
structural: semantic agreement of the terminal coverage words remains the
subsequent entry/classification refinement obligation. -/
theorem canonicalTerminalReplay_of_decode
    (input : Input) (decoded : Decoded) (target : Nat)
    (hdecode : BootMemoryMapDecoder.decode input = .ok decoded)
    (htarget : target < frameLimit) :
    let identity := UInt64.ofNat input.infoAddress
    let initial := scalarInitialAt identity input.bytes.length target
    initial.word[1]! = BootMemoryMapStreamAuthority.active ∧
      initial.word[2]! = BootMemoryMapStreamAuthority.noError ∧
      initial.word[3]! = identity ∧
      initial.word[4]! = UInt64.ofNat input.bytes.length ∧
      initial.word[5]! = 0 ∧
      initial.word[7]! = BootMemoryMapStreamAuthority.phaseInfo ∧
      initial.word[14]! = 0 ∧
      initial.word[15]! = 0 ∧
      initial.word[16]! = UInt64.ofNat target ∧
      checkedScalarReplay (canonicalChunks identity input.bytes) initial =
        .ok (scalarReplay (canonicalChunks identity input.bytes) initial) := by
  dsimp only
  have hinitial := scalarInitialAt_of_decode input decoded target hdecode htarget
  have hheader :=
    BootMemoryMapDecoder.accepted_input_scalar_header input decoded hdecode
  refine ⟨hinitial.1, hinitial.2.1, hinitial.2.2.1,
    hinitial.2.2.2.1, hinitial.2.2.2.2.1,
    hinitial.2.2.2.2.2.1, hinitial.2.2.2.2.2.2.1,
    hinitial.2.2.2.2.2.2.2.1, hinitial.2.2.2.2.2.2.2.2, ?_⟩
  exact checkedScalarReplay_canonical_eq
    (UInt64.ofNat input.infoAddress) input.bytes
    (scalarInitialAt (UInt64.ofNat input.infoAddress) input.bytes.length target)
    hheader.2.2.2.2.2.2.1

/-- The immutable rich-decoder input and the checked/scalar whole replays are
bound to one canonical chunk decomposition.  This is a proof-side production
boundary statement only: it does not refine generated C, the compiler, or the
boot chain. -/
theorem assembled_canonical_checkedScalarReplay
    (magic identity : UInt64) (bytes : List UInt8) (state : ScalarState)
    (hsmall : 16 ≤ bytes.length) (hlarge : bytes.length ≤ maxTagBytes)
    (haligned : bytes.length % 8 = 0) :
    assemble magic identity bytes.length (canonicalChunks identity bytes) =
        .ok { magic := magic.toNat, infoAddress := identity.toNat, bytes } ∧
      checkedScalarReplay (canonicalChunks identity bytes) state =
        .ok (scalarReplay (canonicalChunks identity bytes) state) := by
  exact ⟨assemble_canonicalChunks magic identity bytes hsmall hlarge haligned,
    checkedScalarReplay_canonical_eq identity bytes state haligned⟩

/-- Any arbitrary rejected scalar step exposes no parser state, entry
classification, target, or tag counter. -/
theorem scalarStep_rejected_exposes_no_state
    (state : ScalarState) (chunk : ModelChunk)
    (hrejected :
      (scalarStep state chunk).word[2]! != BootMemoryMapStreamAuthority.noError)
    (query : Fin 19) (hstate : 3 ≤ query.val) :
    (scalarStep state chunk).word[query.val]! = 0 := by
  rw [scalarStep_word state chunk query]
  apply BootMemoryMapStreamAuthority.rejected_step_exposes_no_state
  · have hscalar :
        (scalarStep state chunk).word[2]! ≠
          BootMemoryMapStreamAuthority.noError := by
      intro heq
      simp [heq] at hrejected
    have herrorWord :=
      scalarStep_word state chunk (⟨2, by decide⟩ : Fin 19)
    simpa using herrorWord ▸ hscalar
  · intro h
    have heq := congrArg UInt64.toNat h
    simp at heq
    omega
  · intro h
    have heq := congrArg UInt64.toNat h
    simp at heq
    omega
  · intro h
    have heq := congrArg UInt64.toNat h
    simp at heq
    omega

namespace Fixtures

open BootMemoryMapDecoder.Fixtures
open LeanOS.BootMemoryMapStreamAuthority

def identity : UInt64 := 0x1000

def allocationBytes : List UInt8 :=
  information
    (memoryMapTag [entry 0 (14 * pageBytes) 1] ++ endTag)

def chunkedAt (streamIdentity : UInt64) (bytes : List UInt8) : List ModelChunk :=
  canonicalChunks streamIdentity bytes

def chunked (bytes : List UInt8) : List ModelChunk :=
  chunkedAt identity bytes

def allocationChunks : List ModelChunk := chunked allocationBytes

def scalarInitial (extent target : Nat) : ScalarState :=
  scalarInitialAt identity extent target

def accepted : Except Error Authority :=
  run (UInt64.ofNat multiboot2Magic) identity allocationBytes.length allocationChunks
    BootReservation.twoSidedManifest 7

example : accepted.toOption.map (·.input.bytes) = some allocationBytes := by native_decide
example : accepted.toOption.map (·.decoded.entries) =
    some [{ base := 0, length := 14 * pageBytes, kind := .usable }] := by native_decide
example : accepted.toOption.map (·.reserved.regions) = some
    [{ start := 0, count := 1, kind := .reserved },
     { start := 1, count := 2, kind := .usable },
     { start := 3, count := 9, kind := .reserved },
     { start := 12, count := 2, kind := .usable }] := by native_decide
example : accepted.toOption.map (·.allocation.frame) = some 1 := by native_decide

def acceptedProjection : Projection :=
  match accepted with
  | .ok authority => projection authority
  | .error _ =>
      { entries := [], normalizedRegions := [], intervals := [], reservedRegions := [],
        selectedFrame := 0 }

def mutatedProjection : Projection :=
  { acceptedProjection with selectedFrame := 2 }

def errorOf {α : Type} : Except Error α → Option Error
  | .error reason => some reason
  | .ok _ => none

def sixtyFiveTagBytes : List UInt8 :=
  information
    (ignoredTags 63 ++ memoryMapTag [entry 0 (4 * pageBytes) 1] ++ endTag)

def sixtyFiveTagChunks : List ModelChunk :=
  chunked sixtyFiveTagBytes

def sixtyFiveTagInput : Input :=
  { magic := multiboot2Magic, infoAddress := identity.toNat,
    bytes := sixtyFiveTagBytes }

def sixtyFiveTagScalar : ScalarState :=
  scalarReplay sixtyFiveTagChunks (scalarInitial sixtyFiveTagBytes.length 1)

/-- Raw malformed handoffs shared byte-for-byte by the rich decoder and the
allocation-free scalar production decoder. -/
def malformedTagSizeBytes : List UInt8 :=
  information (u32 42 ++ u32 4)

def duplicateMapBytes : List UInt8 :=
  information (memoryMapTag [] ++ memoryMapTag [])

def badMapLayoutBytes : List UInt8 :=
  information (memoryMapTag [] (entrySize := 32) ++ endTag)

def zeroLengthEntryBytes : List UInt8 :=
  information (memoryMapTag [entry 0 0 1] ++ endTag)

def reservedEntryWordBytes : List UInt8 :=
  information (memoryMapTag [entry 0 0x1000 1 1] ++ endTag)

def overflowingEntryBytes : List UInt8 :=
  information (memoryMapTag [entry (wordLimit - 1) 2 1] ++ endTag)

def missingMapBytes : List UInt8 :=
  information endTag

def missingEndBytes : List UInt8 :=
  information (tag 42 [])

def rawInput (bytes : List UInt8) : Input :=
  { magic := multiboot2Magic, infoAddress := identity.toNat, bytes }

def scalarFor (bytes : List UInt8) : ScalarState :=
  scalarReplay (chunked bytes) (scalarInitial bytes.length 1)

def richRunFor (bytes : List UInt8) : Except Error Authority :=
  run (UInt64.ofNat multiboot2Magic) identity bytes.length (chunked bytes)
    BootReservation.twoSidedManifest 7

/-- Each broader malformed raw fixture has an exact typed diagnostic on both
the rich transition and the generated scalar production decoder.  The scalar
codes intentionally coarsen layout, entry, and normalization failures, but
never accept or expose candidate authority for a rich rejection. -/
theorem malformedRawCorpus_scalar_rich_exactDiagnostics :
    BootMemoryMapDecoder.Fixtures.errorOf
        (BootMemoryMapDecoder.decode (rawInput malformedTagSizeBytes)) =
        some .malformedTagSize ∧
      (scalarFor malformedTagSizeBytes).word[2]! = badTag ∧
      BootMemoryMapDecoder.Fixtures.errorOf
        (BootMemoryMapDecoder.decode (rawInput duplicateMapBytes)) =
        some .duplicateMemoryMap ∧
      (scalarFor duplicateMapBytes).word[2]! = duplicateMap ∧
      BootMemoryMapDecoder.Fixtures.errorOf
        (BootMemoryMapDecoder.decode (rawInput badMapLayoutBytes)) =
        some .badEntrySize ∧
      (scalarFor badMapLayoutBytes).word[2]! = badMapLayout ∧
      errorOf (richRunFor zeroLengthEntryBytes) =
        some (.decode .zeroLengthEntry) ∧
      (scalarFor zeroLengthEntryBytes).word[2]! = badEntry ∧
      BootMemoryMapDecoder.Fixtures.errorOf
        (BootMemoryMapDecoder.decode (rawInput reservedEntryWordBytes)) =
        some .nonzeroEntryReserved ∧
      (scalarFor reservedEntryWordBytes).word[2]! = badEntry ∧
      errorOf (richRunFor overflowingEntryBytes) =
        some (.decode .entryAddressOverflow) ∧
      (scalarFor overflowingEntryBytes).word[2]! = badEntry ∧
      BootMemoryMapDecoder.Fixtures.errorOf
        (BootMemoryMapDecoder.decode (rawInput missingMapBytes)) =
        some .missingMemoryMap ∧
      (scalarFor missingMapBytes).word[2]! = missingMap ∧
      BootMemoryMapDecoder.Fixtures.errorOf
        (BootMemoryMapDecoder.decode (rawInput missingEndBytes)) =
        some .missingEndTag ∧
      (scalarFor missingEndBytes).word[2]! = missingEnd := by
  native_decide

/-- The reviewed 65-tag counterexample is one exact immutable byte sequence on
both sides of the comparison.  The rich stream pipeline reconstructs those
bytes before rejecting at its decoder bound, and scalar ABI v4 rejects the
same sequence with its dedicated error code before granting authority. -/
theorem sixtyFiveTag_exactByte_scalar_richPipeline_agreement :
    streamBytes sixtyFiveTagChunks = sixtyFiveTagBytes ∧
      sixtyFiveTagBytes.length = 560 ∧
      BootMemoryMapDecoder.Fixtures.errorOf
          (BootMemoryMapDecoder.decode sixtyFiveTagInput) =
        some BootMemoryMapDecoder.Error.tooManyTags ∧
      sixtyFiveTagScalar.word[0]! = BootMemoryMapStreamAuthority.abiVersion ∧
      sixtyFiveTagScalar.word[1]! = BootMemoryMapStreamAuthority.rejected ∧
      sixtyFiveTagScalar.word[2]! = BootMemoryMapStreamAuthority.tooManyTags ∧
      errorOf (run (UInt64.ofNat multiboot2Magic) identity sixtyFiveTagBytes.length
        sixtyFiveTagChunks BootReservation.twoSidedManifest 7) =
          some (.decode .tooManyTags) := by
  constructor
  · native_decide
  constructor
  · native_decide
  constructor
  · native_decide
  constructor
  · native_decide
  constructor
  · native_decide
  constructor
  · native_decide
  · native_decide

def gapIdentity : UInt64 := 0x300000

def gapBytes : List UInt8 :=
  information
    (tag 42 (zeroes 25) ++
      memoryMapTag [entry 0 (4 * 1024 * 1024) 1] ++ endTag)

def gapChunks : List ModelChunk :=
  chunkedAt gapIdentity gapBytes

def gapManifest : List BootReservation.Reservation :=
  [{ identity := .lowMemory, start := 0, length := 0x100000,
     lifetime := .permanent },
   { identity := .loadedImage, start := 0x200000, length := 0x100000,
     lifetime := .permanent },
   { identity := .pageTables, start := 0x210000, length := 0x1000,
     lifetime := .permanent },
   { identity := .descriptorTables, start := 0x220000, length := 0x1000,
     lifetime := .permanent },
   { identity := .kernelStacks, start := 0x230000, length := 0x1000,
     lifetime := .permanent },
   { identity := .ordinaryEntryGuard, start := 0x240000, length := 0x1000,
     lifetime := .permanent },
   { identity := .ordinaryEntryStack, start := 0x241000, length := 0x4000,
     lifetime := .permanent },
   { identity := .embeddedUsers, start := 0x280000, length := 0x2000,
     lifetime := .permanent },
   { identity := .multibootInfo, start := 0x300000, length := 96,
     lifetime := .bootstrap }]

def gapRich : Except Error Authority :=
  run (UInt64.ofNat multiboot2Magic) gapIdentity gapBytes.length gapChunks gapManifest 7

def gapScalar : ScalarState :=
  scalarReplay gapChunks (scalarInitialAt gapIdentity gapBytes.length 256)

def physicalLimitBytes : List UInt8 :=
  information
    (memoryMapTag [entry 0 BootMemoryMap.physicalLimit 1] ++ endTag)

def physicalLimitChunks : List ModelChunk :=
  chunkedAt gapIdentity physicalLimitBytes

def physicalLimitManifest (imageLength infoStart infoLength : Nat) :
    List BootReservation.Reservation :=
  [{ identity := .lowMemory, start := 0, length := 0x100000,
     lifetime := .permanent },
   { identity := .loadedImage, start := 0xf00000, length := imageLength,
     lifetime := .permanent },
   { identity := .pageTables, start := 0xf10000, length := 0x1000,
     lifetime := .permanent },
   { identity := .descriptorTables, start := 0xf20000, length := 0x1000,
     lifetime := .permanent },
   { identity := .kernelStacks, start := 0xf30000, length := 0x1000,
     lifetime := .permanent },
   { identity := .ordinaryEntryGuard, start := 0xf40000, length := 0x1000,
     lifetime := .permanent },
   { identity := .ordinaryEntryStack, start := 0xf41000, length := 0x4000,
     lifetime := .permanent },
   { identity := .embeddedUsers, start := 0xf80000, length := 0x2000,
     lifetime := .permanent },
   { identity := .multibootInfo, start := infoStart, length := infoLength,
     lifetime := .bootstrap }]

def physicalLimitRich : Except Error Authority :=
  run (UInt64.ofNat multiboot2Magic) gapIdentity physicalLimitBytes.length
    physicalLimitChunks (physicalLimitManifest 0x100000 0x300000 96) 7

def outsideImageLimitRich : Except Error Authority :=
  run (UInt64.ofNat multiboot2Magic) gapIdentity physicalLimitBytes.length
    physicalLimitChunks (physicalLimitManifest 0x100001 0x300000 96) 7

def exactInfoLimitRich : Except Error Authority :=
  run (UInt64.ofNat multiboot2Magic) gapIdentity physicalLimitBytes.length
    physicalLimitChunks
      (physicalLimitManifest 0x100000 (BootMemoryMap.physicalLimit - 96) 96) 7

def outsideInfoLimitRich : Except Error Authority :=
  run (UInt64.ofNat multiboot2Magic) gapIdentity physicalLimitBytes.length
    physicalLimitChunks
      (physicalLimitManifest 0x100000 (BootMemoryMap.physicalLimit - 32) 96) 7

def physicalLimitScalar : ScalarState :=
  scalarReplay physicalLimitChunks
    (scalarInitialAt gapIdentity physicalLimitBytes.length 256)

def peerOverlapManifest (identity : BootReservation.Identity) :
    List BootReservation.Reservation :=
  gapManifest.map fun reservation =>
    if reservation.identity == identity then
      { reservation with start :=
          if identity == .descriptorTables || identity == .embeddedUsers then
            0x241000
          else
            0x240000 }
    else reservation

def peerOverlapRich (identity : BootReservation.Identity) : Except Error Authority :=
  run (UInt64.ofNat multiboot2Magic) gapIdentity gapBytes.length gapChunks
    (peerOverlapManifest identity) 7

/-! Each independently owned peer class is rejected by both the rich
reservation path and the scalar production decision when it shares rounded
frames with the ordinary-entry guard or stack. -/
theorem ordinaryEntryPeerOverlap_scalar_richPipeline_sharedRejection :
    errorOf (peerOverlapRich .pageTables) =
        some (.reservation .ordinaryEntryOverlap) ∧
      manifestCandidate 256 0 0x100000 0x200000 0x100000
        0x240000 0x1000 0x220000 0x1000 0x230000 0x1000
        0x240000 0x1000 0x241000 0x4000 0x280000 0x2000 0x300000 96 = 0 ∧
      errorOf (peerOverlapRich .descriptorTables) =
        some (.reservation .ordinaryEntryOverlap) ∧
      manifestCandidate 256 0 0x100000 0x200000 0x100000
        0x210000 0x1000 0x241000 0x1000 0x230000 0x1000
        0x240000 0x1000 0x241000 0x4000 0x280000 0x2000 0x300000 96 = 0 ∧
      errorOf (peerOverlapRich .kernelStacks) =
        some (.reservation .ordinaryEntryOverlap) ∧
      manifestCandidate 256 0 0x100000 0x200000 0x100000
        0x210000 0x1000 0x220000 0x1000 0x240000 0x1000
        0x240000 0x1000 0x241000 0x4000 0x280000 0x2000 0x300000 96 = 0 ∧
      errorOf (peerOverlapRich .embeddedUsers) =
        some (.reservation .ordinaryEntryOverlap) ∧
      manifestCandidate 256 0 0x100000 0x200000 0x100000
        0x210000 0x1000 0x220000 0x1000 0x230000 0x1000
        0x240000 0x1000 0x241000 0x4000 0x241000 0x2000 0x300000 96 = 0 := by
  native_decide

/-! The reviewed low-memory-gap handoff is shared byte-for-byte across the rich
pipeline and production scalar replay.  The rich reservation overlay and
allocator select frame 256 in [1 MiB, 2 MiB); the scalar start and selection
choose that same first free frame instead of skipping past the later image and
Multiboot reservations. -/
theorem lowMemoryGap_scalar_richPipeline_firstFree_agreement :
    streamBytes gapChunks = gapBytes ∧
      gapBytes.length = 96 ∧
      gapRich.toOption.map (·.allocation.frame) = some 256 ∧
      manifestStart 0 0x100000 0x200000 0x100000
        0x210000 0x1000 0x220000 0x1000 0x230000 0x1000
        0x240000 0x1000 0x241000 0x4000 0x280000 0x2000 0x300000 96 = 256 ∧
      gapScalar.word[1]! = complete ∧
      gapScalar.word[2]! = noError ∧
      gapScalar.word[14]! = 1 ∧
      gapScalar.word[15]! = 0 ∧
      manifestCandidate 256 0 0x100000 0x200000 0x100000
        0x210000 0x1000 0x220000 0x1000 0x230000 0x1000
        0x240000 0x1000 0x241000 0x4000 0x280000 0x2000 0x300000 96 = 1 ∧
      selectFrame 4096 256 gapScalar.word[1]! gapScalar.word[14]!
        gapScalar.word[15]! 1 = 256 := by
  native_decide

/-! The scalar production manifest and the rich
`BootMemoryMapDecoder` -> `BootReservation.initializeAllocator` ->
`FrameAllocator.allocate` boundary agree at the canonical 16 MiB endpoint.
An image or Multiboot reservation ending exactly at the limit is accepted and
selects the same first free frame. Advancing either endpoint past the limit is
rejected by the rich reservation transition and makes scalar selection and
publication impossible. -/
theorem physicalLimit_scalar_richPipeline_boundary_agreement :
    streamBytes physicalLimitChunks = physicalLimitBytes ∧
      physicalLimitBytes.length = 56 ∧
      physicalLimitScalar.word[1]! = complete ∧
      physicalLimitScalar.word[2]! = noError ∧
      physicalLimitScalar.word[14]! = 1 ∧
      physicalLimitScalar.word[15]! = 0 ∧
      physicalLimitRich.toOption.map (·.allocation.frame) = some 256 ∧
      manifestCandidate 256 0 0x100000 0xf00000 0x100000
        0xf10000 0x1000 0xf20000 0x1000 0xf30000 0x1000
        0xf40000 0x1000 0xf41000 0x4000 0xf80000 0x2000 0x300000 96 = 1 ∧
      exactInfoLimitRich.toOption.map (·.allocation.frame) = some 256 ∧
      manifestCandidate 256 0 0x100000 0xf00000 0x100000
        0xf10000 0x1000 0xf20000 0x1000 0xf30000 0x1000
        0xf40000 0x1000 0xf41000 0x4000 0xf80000 0x2000 0xffffa0 96 = 1 ∧
      errorOf outsideImageLimitRich =
        some (.reservation .outsidePhysicalLimit) ∧
      manifestCandidate 256 0 0x100000 0xf00000 0x100001
        0xf10000 0x1000 0xf20000 0x1000 0xf30000 0x1000
        0xf40000 0x1000 0xf41000 0x4000 0xf80000 0x2000 0x300000 96 = 0 ∧
      selectFrame 4096 256 physicalLimitScalar.word[1]!
        physicalLimitScalar.word[14]! physicalLimitScalar.word[15]! 0 = 4096 ∧
      errorOf outsideInfoLimitRich =
        some (.reservation .outsidePhysicalLimit) ∧
      manifestCandidate 256 0 0x100000 0x200000 0x100000
        0x210000 0x1000 0x220000 0x1000 0x230000 0x1000
        0x240000 0x1000 0x241000 0x4000 0x280000 0x2000 0xfffff0 96 = 0 ∧
      publishAuthority 4096 4096 physicalLimitScalar.word[1]!
        physicalLimitScalar.word[14]! physicalLimitScalar.word[15]! 0 1 = 0 := by
  native_decide

def zeroEntryBytes : List UInt8 :=
  information (memoryMapTag [] ++ endTag)

def zeroEntryChunks : List ModelChunk :=
  chunked zeroEntryBytes

def zeroEntryInput : Input :=
  { magic := multiboot2Magic, infoAddress := identity.toNat,
    bytes := zeroEntryBytes }

def zeroEntryScalar : ScalarState :=
  scalarReplay zeroEntryChunks (scalarInitial zeroEntryBytes.length 1)

/-! The rich and scalar decoders share the Multiboot2 tag-shape policy for an
exact empty memory-map tag.  Both decode the same 32 bytes successfully.  The
rich pipeline rejects only when reservation overlay has no regions to publish;
the scalar production path likewise reaches selection with no usable coverage,
so it cannot select or publish a frame. -/
theorem zeroEntry_exactByte_scalar_richPipeline_sharedRejection :
    streamBytes zeroEntryChunks = zeroEntryBytes ∧
      zeroEntryBytes.length = 32 ∧
      (BootMemoryMapDecoder.decode zeroEntryInput).toOption.map (·.entries) =
        some [] ∧
      errorOf (run (UInt64.ofNat multiboot2Magic) identity zeroEntryBytes.length
        zeroEntryChunks BootReservation.twoSidedManifest 7) =
          some (.reservation .emptyOutput) ∧
      zeroEntryScalar.word[1]! = complete ∧
      zeroEntryScalar.word[2]! = noError ∧
      zeroEntryScalar.word[11]! = 0 ∧
      zeroEntryScalar.word[14]! = 0 ∧
      zeroEntryScalar.word[15]! = 0 ∧
      selectFrame 4096 1 zeroEntryScalar.word[1]! zeroEntryScalar.word[14]!
        zeroEntryScalar.word[15]! 1 = 4096 ∧
      publishAuthority 4096 4096 zeroEntryScalar.word[1]! zeroEntryScalar.word[14]!
        zeroEntryScalar.word[15]! 1 1 = 0 := by
  native_decide

example : errorOf (authorize (UInt64.ofNat multiboot2Magic) identity
    allocationBytes.length allocationChunks BootReservation.twoSidedManifest 7
    mutatedProjection) = some .outputMutation := by native_decide

def splicedChunks : List ModelChunk :=
  allocationChunks.map fun chunk =>
    if chunk.offset == 8 then { chunk with identity := 0x2000 } else chunk

example : errorOf (assemble (UInt64.ofNat multiboot2Magic) identity
    allocationBytes.length splicedChunks) = some .discontinuousStream := by native_decide

def reorderedChunks : List ModelChunk :=
  match allocationChunks with
  | first :: second :: rest => second :: first :: rest
  | chunks => chunks

example : errorOf (assemble (UInt64.ofNat multiboot2Magic) identity
    allocationBytes.length reorderedChunks) = some .discontinuousStream := by native_decide

end Fixtures

end LeanOS.BootMemoryMapStreamPipeline
