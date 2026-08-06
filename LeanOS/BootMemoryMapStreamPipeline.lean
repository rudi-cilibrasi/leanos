import LeanOS.BootMemoryMapDecoder
import LeanOS.BootMemoryMapStreamAuthority
import LeanOS.BootMemoryMapStreaming
import LeanOS.BootReservation
import Std.Tactic.BVDecide

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

/-- The scalar parser's fixed-width alignment expression is exactly the rich
decoder's `aligned8` advance throughout the admitted 64 KiB handoff bound.
The addition is kept inside the quotient on both sides; replacing it with a
floor-alignment identity is false for non-aligned ignored-tag sizes. -/
theorem scalarAligned8_eq_richAligned8
    (size : Nat) (hsize : size ≤ maxTagBytes) :
    ((UInt64.ofNat size + 7) &&& 0xfffffffffffffff8) =
      UInt64.ofNat (aligned8 size) := by
  have hsum : size + 7 < UInt64.size := by
    have hword : maxTagBytes + 7 < UInt64.size := by decide
    omega
  have hmask (value : UInt64) :
      ((value + 7) &&& 0xfffffffffffffff8) = (value + 7) / 8 * 8 := by
    bv_decide
  rw [hmask]
  apply UInt64.toNat.inj
  simp [aligned8, UInt64.toNat_div, UInt64.toNat_mul,
    Nat.mod_eq_of_lt hsum]

/-- A retained rich tag traversal exposes one exact source header and the same
rounded cursor advance used by the scalar parser.  This packages the local
cursor/fuel induction step without assuming an aligned tag size: ignored tags
may have arbitrary admitted sizes, while their scalar and rich successors
still coincide. -/
theorem successfulTagDecodeTraversal_header_advance
    (bytes : List UInt8) (total offset fuel : Nat)
    (sawMemoryMap : Bool) (tagsRev tags : List Tag)
    (htotal : total ≤ maxTagBytes)
    (h :
      SuccessfulTagDecodeTraversal bytes total offset fuel sawMemoryMap
        tagsRev tags) :
    ∃ tagWord,
      readU64 bytes offset = .ok tagWord ∧
        offset + aligned8 (high32Nat tagWord) ≤ total ∧
        ((UInt64.ofNat (high32Nat tagWord) + 7) &&& 0xfffffffffffffff8) =
          UInt64.ofNat (aligned8 (high32Nat tagWord)) := by
  cases h with
  | endTag offset fuel tagWord tagsRev hread htype hsize hend =>
      refine ⟨tagWord, hread, ?_, ?_⟩
      · simp [hsize, aligned8]
        omega
      · apply scalarAligned8_eq_richAligned8
        rw [hsize]
        omega
  | ignoredTag offset fuel tagWord sawMemoryMap tagsRev tags hread hsize
      hcontent hadvance htypeEnd htypeMap hrest =>
      refine ⟨tagWord, hread, hadvance, ?_⟩
      apply scalarAligned8_eq_richAligned8
      omega
  | memoryMapTag offset fuel tagWord layoutWord tagsRev tags entries hread
      hsize hcontent hadvance htype hlayout hentrySize hentryVersion
      halignedEntries hentryBound hentries hrest =>
      refine ⟨tagWord, hread, hadvance, ?_⟩
      apply scalarAligned8_eq_richAligned8
      omega

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

/-- Immutable stream authority reconstructed from the production scalar
initializer.  Phase-local traversal proofs carry this single witness instead
of accepting independently supplied alignment and extent premises. -/
structure AdmittedScalarStream
    (identity : UInt64) (extent target : Nat) : Prop where
  identityAligned : identity % 8 = 0
  identityLow : 4096 ≤ identity
  extentLow : 16 ≤ extent
  extentHigh : extent ≤ maxTagBytes
  extentAligned : extent % 8 = 0
  noOverflow :
    UInt64.ofNat extent ≤ 0xffffffffffffffff - identity
  targetWord : UInt64.ofNat target < 4096

/-- An active production scalar initializer reconstructs its immutable stream
admission facts.  The only extra premise is the representation bridge that the
proof-side `Nat` extent fits in the `UInt64` word supplied to production; none
of the alignment or bounded-admission facts may be supplied independently. -/
theorem scalarInitialAt_active_implies_admitted
    (identity : UInt64) (extent target : Nat)
    (hextentWord : extent < UInt64.size)
    (hactive :
      (scalarInitialAt identity extent target).word[1]! =
        BootMemoryMapStreamAuthority.active) :
    AdmittedScalarStream identity extent target := by
  have hactiveWord :
      BootMemoryMapStreamAuthority.initWord
          (UInt64.ofNat multiboot2Magic) identity (UInt64.ofNat extent)
          (UInt64.ofNat target) 1 =
        BootMemoryMapStreamAuthority.active := by
    simpa [scalarInitialAt] using hactive
  have hnoError :=
    BootMemoryMapStreamAuthority.initWord_active_implies_noError
      (UInt64.ofNat multiboot2Magic) identity (UInt64.ofNat extent)
      (UInt64.ofNat target) hactiveWord
  obtain ⟨_hmagic, hidentityAligned, hidentityLow, hextentLowWord,
      hextentHighWord, hextentAlignedWord, hnoOverflow, htarget⟩ :=
    BootMemoryMapStreamAuthority.initWord_noError_implies_admitted
      (UInt64.ofNat multiboot2Magic) identity (UInt64.ofNat extent)
      (UInt64.ofNat target) hnoError
  have hextentLow : 16 ≤ extent := by
    rw [UInt64.le_iff_toNat_le,
      UInt64.toNat_ofNat_of_lt' hextentWord] at hextentLowWord
    simpa using hextentLowWord
  have hextentHigh : extent ≤ maxTagBytes := by
    rw [UInt64.le_iff_toNat_le,
      UInt64.toNat_ofNat_of_lt' hextentWord] at hextentHighWord
    simpa [maxTagBytes] using hextentHighWord
  have hextentAligned : extent % 8 = 0 := by
    have := congrArg UInt64.toNat hextentAlignedWord
    simpa [UInt64.toNat_mod, UInt64.toNat_ofNat_of_lt' hextentWord] using this
  exact
    { identityAligned := hidentityAligned
      identityLow := hidentityLow
      extentLow := hextentLow
      extentHigh := hextentHigh
      extentAligned := hextentAligned
      noOverflow := hnoOverflow
      targetWord := htarget }

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
      have hextentNe8 : UInt64.ofNat input.bytes.length ≠ 8 := by
        intro heq
        have := congrArg UInt64.toNat heq
        simp [UInt64.toNat_ofNat_of_lt' hextentLt] at this
        omega
      have h8NeExtent : 8 ≠ UInt64.ofNat input.bytes.length :=
        Ne.symm hextentNe8
      have hinitial :=
        scalarInitialAt_of_decode input decoded target hdecode htarget
      have hactive :
          BootMemoryMapStreamAuthority.initWord
              (UInt64.ofNat multiboot2Magic)
              (UInt64.ofNat input.infoAddress)
              (UInt64.ofNat input.bytes.length)
              (UInt64.ofNat target) 1 =
            BootMemoryMapStreamAuthority.active := by
        simpa [scalarInitialAt] using hinitial.1
      have hstep :=
        BootMemoryMapStreamAuthority.infoStepWords_of_active
          (UInt64.ofNat multiboot2Magic)
          (UInt64.ofNat input.infoAddress)
          (UInt64.ofNat input.bytes.length)
          (UInt64.ofNat target) (UInt64.ofNat infoWord)
          hactive hlowWord hhighWord h8NeExtent
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

/-- Substitute the admitted stream fields into one scalar query without
unfolding the generated transition.  Keeping this bridge outside larger
structural proofs gives every phase-local use a small, reusable proof term. -/
theorem scalarStep_word_of_stream_fields
    (state : ScalarState) (chunk : ModelChunk)
    (identity extent offset phase padded saw target word terminal : UInt64)
    (query : Fin 19)
    (hversion :
      state.word[0]! = BootMemoryMapStreamAuthority.abiVersion)
    (hstatus :
      state.word[1]! = BootMemoryMapStreamAuthority.active)
    (herror :
      state.word[2]! = BootMemoryMapStreamAuthority.noError)
    (hidentity : state.word[3]! = identity)
    (hextent : state.word[4]! = extent)
    (hoffset : state.word[5]! = offset)
    (hphase : state.word[7]! = phase)
    (hpadded : state.word[9]! = padded)
    (hsaw : state.word[10]! = saw)
    (htarget : state.word[16]! = target)
    (hchunkIdentity : chunk.identity = identity)
    (hchunkOffset : UInt64.ofNat chunk.offset = offset)
    (hchunkWord : chunkWord chunk.bytes = word)
    (hchunkTerminal :
      (if chunk.terminal then 1 else 0) = terminal) :
    (scalarStep state chunk).word[query.val]! =
      BootMemoryMapStreamAuthority.stepWord
        BootMemoryMapStreamAuthority.abiVersion
        BootMemoryMapStreamAuthority.active
        BootMemoryMapStreamAuthority.noError
        identity extent offset state.word[6]! phase state.word[8]! padded saw
        state.word[11]! state.word[12]! state.word[13]! state.word[14]!
        state.word[15]! target state.word[17]! state.word[18]!
        identity offset word terminal (UInt64.ofNat query.val) := by
  rw [scalarStep_word, hversion, hstatus, herror, hidentity, hextent, hoffset,
    hphase, hpadded, hsaw, htarget, hchunkIdentity, hchunkOffset, hchunkWord,
    hchunkTerminal]

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

/-- Ignored payload and padding preserve the map-seen flag, entry count,
classification accumulators, and consumed tag count.  This is the exact
tag-budget preservation obligation needed by a whole-tag induction: ignored
body words cannot spend another tag-header unit. -/
theorem successfulIgnoredTagSpan_preserves_tag_fields
    (state terminal : ScalarState) (chunks : List ModelChunk)
    (hspan : SuccessfulIgnoredTagSpan state chunks terminal) :
    terminal.word[10]! = state.word[10]! ∧
      terminal.word[11]! = state.word[11]! ∧
      terminal.word[14]! = state.word[14]! ∧
      terminal.word[15]! = state.word[15]! ∧
      terminal.word[18]! = state.word[18]! := by
  induction hspan with
  | done =>
      exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  | step state terminal chunk rest hphase haccepted hrest ih =>
      have hacceptedStep := haccepted
      rw [scalarStep_word state chunk (⟨2, by decide⟩ : Fin 19)]
        at hacceptedStep
      have htag :=
        BootMemoryMapStreamAuthority.accepted_ignored_preserves_tag_fields
          state.word[0]! state.word[1]! state.word[2]! state.word[3]!
          state.word[4]! state.word[5]! state.word[6]! state.word[7]!
          state.word[8]! state.word[9]! state.word[10]! state.word[11]!
          state.word[12]! state.word[13]! state.word[14]! state.word[15]!
          state.word[16]! state.word[17]! state.word[18]!
          chunk.identity (UInt64.ofNat chunk.offset) (chunkWord chunk.bytes)
          (if chunk.terminal then 1 else 0) hphase hacceptedStep
      have hclassification :=
        scalarStep_nonEntry_preserves_classification state chunk
          (by rw [hphase]; decide) haccepted
      have hstep :
          (scalarStep state chunk).word[10]! = state.word[10]! ∧
            (scalarStep state chunk).word[11]! = state.word[11]! ∧
            (scalarStep state chunk).word[14]! = state.word[14]! ∧
            (scalarStep state chunk).word[15]! = state.word[15]! ∧
            (scalarStep state chunk).word[18]! = state.word[18]! := by
        rw [scalarStep_word state chunk (⟨10, by decide⟩ : Fin 19),
          scalarStep_word state chunk (⟨11, by decide⟩ : Fin 19),
          scalarStep_word state chunk (⟨18, by decide⟩ : Fin 19)]
        exact ⟨htag.1, htag.2.1, hclassification.1,
          hclassification.2, htag.2.2⟩
      exact ⟨ih.1.trans hstep.1, ih.2.1.trans hstep.2.1,
        ih.2.2.1.trans hstep.2.2.1, ih.2.2.2.1.trans hstep.2.2.2.1,
        ih.2.2.2.2.trans hstep.2.2.2.2⟩

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

/-- One admitted memory-map layout word is a non-entry traversal step.  Its
exact rich layout value selects either the first entry-base phase or the tag
phase for an empty map, while preserving the pending rich entry list and both
classification accumulators. -/
theorem successfulScalarRichTraversal_memoryMapLayout
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
      state.word[7]! = BootMemoryMapStreamAuthority.phaseMapLayout)
    (hcontentAligned : state.word[8]! % 24 = 0)
    (hpadded : state.word[9]! = 0)
    (hsawMap : state.word[10]! = 1)
    (husable : state.word[14]! ≤ 1)
    (hblocked : state.word[15]! ≤ 1)
    (htargetWord : state.word[16]! = UInt64.ofNat target)
    (htarget : target < frameLimit)
    (htagCount : state.word[18]! ≤ 64)
    (hlayoutLow : BootMemoryMapStreamAuthority.low32 word = 24)
    (hlayoutHigh : BootMemoryMapStreamAuthority.high32 word = 0)
    (hentryBound :
      state.word[8]! / 24 ≤ BootMemoryMapStreamAuthority.entryLimit)
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
    BootMemoryMapStreamAuthority.memoryMapLayoutStepWords_of_admitted
      identity extent offset state.word[6]! state.word[8]! state.word[11]!
      state.word[12]! state.word[13]! state.word[14]! state.word[15]!
      (UInt64.ofNat target) state.word[17]! state.word[18]! word
      hidentityAligned hextentLow hextentHigh hextentAligned hoffsetLt
      hoffsetNotFinal husable hblocked htargetBound htagCount hlayoutLow
      hlayoutHigh hcontentAligned hentryBound
  apply SuccessfulScalarRichTraversal.nonEntry entries state terminal chunk rest
  · rw [hphase]
    decide
  · simpa [scalarStep, hchunkIdentity, hchunkOffset, hchunkTerminal, hchunkWord,
      hversion, hstatus, herror, hidentity, hextent, hoffset, hphase,
      hpadded, hsawMap, htargetWord] using hstep.2.2.1
  · exact hrest

/-- One admitted rich memory-map entry supplies the exact three scalar words
for its base, length, and type.  The first two words are non-entry traversal
steps; the third is the entry constructor that attaches the exact decoded
`RawEntry`.  This packages the production phase transitions as the unit used
by the recursive entry/source induction. -/
theorem successfulScalarRichTraversal_memoryMapEntry_with_successor
    (identity extent offset : UInt64) (target base length kindWord : Nat)
    (entries : List RawEntry) (state terminal : ScalarState)
    (baseChunk lengthChunk kindChunk : ModelChunk) (rest : List ModelChunk)
    (hbaseIdentity : baseChunk.identity = identity)
    (hlengthIdentity : lengthChunk.identity = identity)
    (hkindIdentity : kindChunk.identity = identity)
    (hbaseOffset : UInt64.ofNat baseChunk.offset = offset)
    (hlengthOffset : UInt64.ofNat lengthChunk.offset = offset + 8)
    (hkindOffset : UInt64.ofNat kindChunk.offset = offset + 8 + 8)
    (hbaseTerminal : baseChunk.terminal = false)
    (hlengthTerminal : lengthChunk.terminal = false)
    (hkindTerminal : kindChunk.terminal = false)
    (hbaseChunkWord : chunkWord baseChunk.bytes = UInt64.ofNat base)
    (hlengthChunkWord : chunkWord lengthChunk.bytes = UInt64.ofNat length)
    (hkindChunkWord : chunkWord kindChunk.bytes = UInt64.ofNat kindWord)
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
    (hbaseOffsetLt : offset < extent)
    (hbaseOffsetNotFinal : offset + 8 ≠ extent)
    (hlengthOffsetLt : offset + 8 < extent)
    (hlengthOffsetNotFinal : offset + 8 + 8 ≠ extent)
    (hkindOffsetLt : offset + 8 + 8 < extent)
    (hkindOffsetNotFinal : offset + 8 + 8 + 8 ≠ extent)
    (hphase :
      state.word[7]! = BootMemoryMapStreamAuthority.phaseEntryBase)
    (hpadded : state.word[9]! = 0)
    (hsawMap : state.word[10]! = 1)
    (hentryCount : state.word[11]! < BootMemoryMapStreamAuthority.entryLimit)
    (husable : state.word[14]! ≤ 1)
    (hblocked : state.word[15]! ≤ 1)
    (htargetWord : state.word[16]! = UInt64.ofNat target)
    (htarget : target < frameLimit)
    (htagCount : state.word[18]! ≤ 64)
    (hlengthNonzero : length ≠ 0)
    (hbaseBound : base < wordLimit)
    (hstopBound : base + length < wordLimit)
    (hkindBound : kindWord < 2 ^ 32) :
    (SuccessfulScalarRichTraversal target entries
          (scalarStep (scalarStep (scalarStep state baseChunk) lengthChunk)
            kindChunk)
          rest terminal →
        SuccessfulScalarRichTraversal target
          ({ base, length, kind := BootMemoryMapDecoder.memoryKind kindWord } :: entries)
          state (baseChunk :: lengthChunk :: kindChunk :: rest) terminal) ∧
      let next :=
        scalarStep (scalarStep (scalarStep state baseChunk) lengthChunk)
          kindChunk
      next.word[0]! = BootMemoryMapStreamAuthority.abiVersion ∧
        next.word[1]! = BootMemoryMapStreamAuthority.active ∧
        next.word[2]! = BootMemoryMapStreamAuthority.noError ∧
        next.word[3]! = identity ∧
        next.word[4]! = extent ∧
        next.word[5]! = offset + 8 + 8 + 8 ∧
        next.word[7]! =
          (if state.word[8]! = 24
            then BootMemoryMapStreamAuthority.phaseTag
            else BootMemoryMapStreamAuthority.phaseEntryBase) ∧
        next.word[8]! = state.word[8]! - 24 ∧
        next.word[9]! = 0 ∧
        next.word[10]! = 1 ∧
        next.word[11]! = state.word[11]! + 1 ∧
        next.word[12]! = UInt64.ofNat base ∧
        next.word[13]! = UInt64.ofNat length ∧
        next.word[14]! ≤ 1 ∧
        next.word[15]! ≤ 1 ∧
        next.word[16]! = UInt64.ofNat target ∧
        next.word[18]! = state.word[18]! := by
  have htargetLt : target < UInt64.size :=
    Nat.lt_trans htarget (by decide)
  have htargetBound : UInt64.ofNat target < 4096 := by
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat_of_lt' htargetLt]
    simpa [frameLimit, physicalLimit, pageBytes] using htarget
  have hbaseLt : base < UInt64.size := by
    simpa [wordLimit] using hbaseBound
  have hlengthLt : length < UInt64.size := by
    have : length < wordLimit := by omega
    simpa [wordLimit] using this
  have hkindLt : kindWord < UInt64.size := by
    exact Nat.lt_trans hkindBound (by decide)
  have hkindHigh :
      BootMemoryMapStreamAuthority.high32 (UInt64.ofNat kindWord) = 0 := by
    rw [BootMemoryMapStreamAuthority.high32,
      high32Word_ofNat kindWord hkindLt]
    apply UInt64.toNat.inj
    simp [BootMemoryMapDecoder.high32Nat]
    omega
  have hlengthWordNonzero : UInt64.ofNat length ≠ 0 := by
    intro hzero
    have hzeroNat := congrArg UInt64.toNat hzero
    rw [UInt64.toNat_ofNat_of_lt' hlengthLt] at hzeroNat
    simp only [UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at hzeroNat
    exact hlengthNonzero hzeroNat
  have hbaseMax :
      UInt64.ofNat base ≤ 0xffffffffffffffff := by
    rw [UInt64.le_iff_toNat_le, UInt64.toNat_ofNat_of_lt' hbaseLt]
    simp only [UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    simpa [UInt64.size] using Nat.le_pred_of_lt hbaseLt
  have hstopWord :
      UInt64.ofNat length ≤
        0xffffffffffffffff - UInt64.ofNat base := by
    have hstopNat :
        length ≤ (2 ^ 64 - 1) - base := by
      unfold wordLimit at hstopBound
      omega
    rw [UInt64.le_iff_toNat_le, UInt64.toNat_ofNat_of_lt' hlengthLt,
      UInt64.toNat_sub_of_le _ _ hbaseMax,
      UInt64.toNat_ofNat_of_lt' hbaseLt]
    simp only [UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    exact hstopNat
  have hbaseRaw :=
    BootMemoryMapStreamAuthority.entryBaseStepWords_of_admitted
      identity extent offset state.word[6]! state.word[8]!
      state.word[11]! state.word[12]! state.word[13]!
      state.word[14]! state.word[15]! (UInt64.ofNat target)
      state.word[17]! state.word[18]! (UInt64.ofNat base)
      hidentityAligned hextentLow hextentHigh hextentAligned hbaseOffsetLt
      hbaseOffsetNotFinal husable hblocked htargetBound htagCount
  have hbaseStep :
      (scalarStep state baseChunk).word[0]! =
          BootMemoryMapStreamAuthority.abiVersion ∧
        (scalarStep state baseChunk).word[1]! =
          BootMemoryMapStreamAuthority.active ∧
        (scalarStep state baseChunk).word[2]! =
          BootMemoryMapStreamAuthority.noError ∧
        (scalarStep state baseChunk).word[3]! = identity ∧
        (scalarStep state baseChunk).word[4]! = extent ∧
        (scalarStep state baseChunk).word[5]! = offset + 8 ∧
        (scalarStep state baseChunk).word[7]! =
          BootMemoryMapStreamAuthority.phaseEntryLength ∧
        (scalarStep state baseChunk).word[8]! = state.word[8]! ∧
        (scalarStep state baseChunk).word[9]! = 0 ∧
        (scalarStep state baseChunk).word[10]! = 1 ∧
        (scalarStep state baseChunk).word[11]! = state.word[11]! ∧
        (scalarStep state baseChunk).word[12]! = UInt64.ofNat base ∧
        (scalarStep state baseChunk).word[13]! = state.word[13]! ∧
        (scalarStep state baseChunk).word[14]! = state.word[14]! ∧
        (scalarStep state baseChunk).word[15]! = state.word[15]! ∧
        (scalarStep state baseChunk).word[16]! = UInt64.ofNat target ∧
        (scalarStep state baseChunk).word[17]! = state.word[17]! ∧
        (scalarStep state baseChunk).word[18]! = state.word[18]! := by
    simpa [scalarStep, hbaseIdentity, hbaseOffset, hbaseTerminal,
      hbaseChunkWord, hversion, hstatus, herror, hidentity, hextent, hoffset,
      hphase, hpadded, hsawMap, htargetWord] using hbaseRaw
  rcases hbaseStep with ⟨hbaseVersion, hbaseStatus, hbaseError,
    hbaseIdentityWord, hbaseExtent, hbaseCursor, hbasePhase, hbaseContent,
    hbasePadded, hbaseSawMap, hbaseEntries, hbaseWord, hbaseLength,
    hbaseUsable, hbaseBlocked, hbaseTarget, hbaseHighest, hbaseTagCount⟩
  have hlengthRaw :=
    BootMemoryMapStreamAuthority.entryLengthStepWords_of_admitted
      identity extent (offset + 8) (scalarStep state baseChunk).word[6]!
      state.word[8]! state.word[11]! (UInt64.ofNat base) state.word[13]!
      state.word[14]! state.word[15]! (UInt64.ofNat target)
      state.word[17]! state.word[18]! (UInt64.ofNat length)
      hidentityAligned hextentLow hextentHigh hextentAligned hlengthOffsetLt
      hlengthOffsetNotFinal husable hblocked htargetBound htagCount
  rcases hlengthRaw with ⟨hlengthVersionRaw, hlengthStatusRaw,
    hlengthErrorRaw, hlengthIdentityRaw, hlengthExtentRaw, hlengthCursorRaw,
    hlengthPhaseRaw, hlengthContentRaw, hlengthPaddedRaw, hlengthSawMapRaw,
    hlengthEntriesRaw, hlengthBaseRaw, hlengthWordRaw, hlengthUsableRaw,
    hlengthBlockedRaw, hlengthTargetRaw, hlengthHighestRaw,
    hlengthTagCountRaw⟩
  have hlengthRefines (query : Fin 19) :
      (scalarStep (scalarStep state baseChunk) lengthChunk).word[query.val]! =
        BootMemoryMapStreamAuthority.stepWord
          BootMemoryMapStreamAuthority.abiVersion
          BootMemoryMapStreamAuthority.active
          BootMemoryMapStreamAuthority.noError identity extent (offset + 8)
          (scalarStep state baseChunk).word[6]!
          BootMemoryMapStreamAuthority.phaseEntryLength state.word[8]! 0 1
          state.word[11]! (UInt64.ofNat base) state.word[13]!
          state.word[14]! state.word[15]! (UInt64.ofNat target)
          state.word[17]! state.word[18]! identity (offset + 8)
          (UInt64.ofNat length) 0 (UInt64.ofNat query.val) := by
    rw [scalarStep_word]
    simp only [hlengthIdentity, hlengthOffset, hlengthTerminal,
      hlengthChunkWord, hbaseVersion, hbaseStatus, hbaseError,
      hbaseIdentityWord, hbaseExtent, hbaseCursor, hbasePhase, hbaseContent,
      hbasePadded, hbaseSawMap, hbaseEntries, hbaseWord, hbaseLength,
      hbaseUsable, hbaseBlocked, hbaseTarget, hbaseHighest, hbaseTagCount,
      Bool.false_eq_true, ↓reduceIte]
  have hlengthVersion :
      (scalarStep (scalarStep state baseChunk) lengthChunk).word[0]! =
        BootMemoryMapStreamAuthority.abiVersion := by
    exact (hlengthRefines (⟨0, by decide⟩ : Fin 19)).trans hlengthVersionRaw
  have hlengthStatus :
      (scalarStep (scalarStep state baseChunk) lengthChunk).word[1]! =
        BootMemoryMapStreamAuthority.active := by
    exact (hlengthRefines (⟨1, by decide⟩ : Fin 19)).trans hlengthStatusRaw
  have hlengthError :
      (scalarStep (scalarStep state baseChunk) lengthChunk).word[2]! =
        BootMemoryMapStreamAuthority.noError := by
    exact (hlengthRefines (⟨2, by decide⟩ : Fin 19)).trans hlengthErrorRaw
  have hlengthIdentityWord :
      (scalarStep (scalarStep state baseChunk) lengthChunk).word[3]! =
        identity := by
    exact (hlengthRefines (⟨3, by decide⟩ : Fin 19)).trans
      hlengthIdentityRaw
  have hlengthExtent :
      (scalarStep (scalarStep state baseChunk) lengthChunk).word[4]! =
        extent := by
    exact (hlengthRefines (⟨4, by decide⟩ : Fin 19)).trans hlengthExtentRaw
  have hlengthCursor :
      (scalarStep (scalarStep state baseChunk) lengthChunk).word[5]! =
        offset + 8 + 8 := by
    exact (hlengthRefines (⟨5, by decide⟩ : Fin 19)).trans hlengthCursorRaw
  have hlengthPhase :
      (scalarStep (scalarStep state baseChunk) lengthChunk).word[7]! =
        BootMemoryMapStreamAuthority.phaseEntryType := by
    exact (hlengthRefines (⟨7, by decide⟩ : Fin 19)).trans hlengthPhaseRaw
  have hlengthContent :
      (scalarStep (scalarStep state baseChunk) lengthChunk).word[8]! =
        state.word[8]! := by
    exact (hlengthRefines (⟨8, by decide⟩ : Fin 19)).trans hlengthContentRaw
  have hlengthPadded :
      (scalarStep (scalarStep state baseChunk) lengthChunk).word[9]! = 0 := by
    exact (hlengthRefines (⟨9, by decide⟩ : Fin 19)).trans hlengthPaddedRaw
  have hlengthSawMap :
      (scalarStep (scalarStep state baseChunk) lengthChunk).word[10]! = 1 := by
    exact (hlengthRefines (⟨10, by decide⟩ : Fin 19)).trans
      hlengthSawMapRaw
  have hlengthEntries :
      (scalarStep (scalarStep state baseChunk) lengthChunk).word[11]! =
        state.word[11]! := by
    exact (hlengthRefines (⟨11, by decide⟩ : Fin 19)).trans
      hlengthEntriesRaw
  have hlengthBaseWord :
      (scalarStep (scalarStep state baseChunk) lengthChunk).word[12]! =
        UInt64.ofNat base := by
    exact (hlengthRefines (⟨12, by decide⟩ : Fin 19)).trans hlengthBaseRaw
  have hlengthWord :
      (scalarStep (scalarStep state baseChunk) lengthChunk).word[13]! =
        UInt64.ofNat length := by
    exact (hlengthRefines (⟨13, by decide⟩ : Fin 19)).trans hlengthWordRaw
  have hlengthUsable :
      (scalarStep (scalarStep state baseChunk) lengthChunk).word[14]! =
        state.word[14]! := by
    exact (hlengthRefines (⟨14, by decide⟩ : Fin 19)).trans
      hlengthUsableRaw
  have hlengthBlocked :
      (scalarStep (scalarStep state baseChunk) lengthChunk).word[15]! =
        state.word[15]! := by
    exact (hlengthRefines (⟨15, by decide⟩ : Fin 19)).trans
      hlengthBlockedRaw
  have hlengthTarget :
      (scalarStep (scalarStep state baseChunk) lengthChunk).word[16]! =
        UInt64.ofNat target := by
    exact (hlengthRefines (⟨16, by decide⟩ : Fin 19)).trans
      hlengthTargetRaw
  have hlengthHighest :
      (scalarStep (scalarStep state baseChunk) lengthChunk).word[17]! =
        state.word[17]! := by
    exact (hlengthRefines (⟨17, by decide⟩ : Fin 19)).trans
      hlengthHighestRaw
  have hlengthTagCount :
      (scalarStep (scalarStep state baseChunk) lengthChunk).word[18]! =
        state.word[18]! := by
    exact (hlengthRefines (⟨18, by decide⟩ : Fin 19)).trans
      hlengthTagCountRaw
  have hkindRaw :=
    BootMemoryMapStreamAuthority.entryTypeStepWords_of_admitted
      identity extent (offset + 8 + 8)
      (scalarStep (scalarStep state baseChunk) lengthChunk).word[6]!
      state.word[8]! state.word[11]! (UInt64.ofNat base)
      (UInt64.ofNat length) state.word[14]! state.word[15]!
      (UInt64.ofNat target) state.word[17]! state.word[18]!
      (UInt64.ofNat kindWord)
      hidentityAligned hextentLow hextentHigh hextentAligned hkindOffsetLt
      hkindOffsetNotFinal husable hblocked htargetBound htagCount hkindHigh
      hlengthWordNonzero hstopWord hentryCount
  have hkindRefines (query : Fin 19) :
      (scalarStep (scalarStep (scalarStep state baseChunk) lengthChunk)
          kindChunk).word[query.val]! =
        BootMemoryMapStreamAuthority.stepWord
          BootMemoryMapStreamAuthority.abiVersion
          BootMemoryMapStreamAuthority.active
          BootMemoryMapStreamAuthority.noError identity extent
          (offset + 8 + 8)
          (scalarStep (scalarStep state baseChunk) lengthChunk).word[6]!
          BootMemoryMapStreamAuthority.phaseEntryType state.word[8]! 0 1
          state.word[11]! (UInt64.ofNat base) (UInt64.ofNat length)
          state.word[14]! state.word[15]! (UInt64.ofNat target)
          state.word[17]! state.word[18]! identity (offset + 8 + 8)
          (UInt64.ofNat kindWord) 0 (UInt64.ofNat query.val) := by
    rw [scalarStep_word]
    simp only [hkindIdentity, hkindOffset, hkindTerminal, hkindChunkWord,
      hlengthVersion, hlengthStatus, hlengthError, hlengthIdentityWord,
      hlengthExtent, hlengthCursor, hlengthPhase, hlengthContent,
      hlengthPadded, hlengthSawMap, hlengthEntries, hlengthBaseWord,
      hlengthWord, hlengthUsable, hlengthBlocked, hlengthTarget,
      hlengthHighest, hlengthTagCount, Bool.false_eq_true,
      ↓reduceIte]
  rcases hkindRaw with ⟨hkindVersionRaw, hkindStatusRaw, hkindErrorRaw,
    hkindIdentityRaw, hkindExtentRaw, hkindCursorRaw, hkindPhaseRaw,
    hkindContentRaw, hkindPaddedRaw, hkindSawMapRaw, hkindEntriesRaw,
    hkindBaseRaw, hkindLengthRaw, hkindUsableRaw, hkindBlockedRaw,
    hkindTargetRaw, hkindHighestRaw, hkindTagCountRaw⟩
  have hkindVersion :=
    (hkindRefines (⟨0, by decide⟩ : Fin 19)).trans hkindVersionRaw
  have hkindStatus :=
    (hkindRefines (⟨1, by decide⟩ : Fin 19)).trans hkindStatusRaw
  have hkindStep :=
    (hkindRefines (⟨2, by decide⟩ : Fin 19)).trans hkindErrorRaw
  have hkindIdentityWord :=
    (hkindRefines (⟨3, by decide⟩ : Fin 19)).trans hkindIdentityRaw
  have hkindExtent :=
    (hkindRefines (⟨4, by decide⟩ : Fin 19)).trans hkindExtentRaw
  have hkindCursor :=
    (hkindRefines (⟨5, by decide⟩ : Fin 19)).trans hkindCursorRaw
  have hkindPhase :=
    (hkindRefines (⟨7, by decide⟩ : Fin 19)).trans hkindPhaseRaw
  have hkindContent :=
    (hkindRefines (⟨8, by decide⟩ : Fin 19)).trans hkindContentRaw
  have hkindPadded :=
    (hkindRefines (⟨9, by decide⟩ : Fin 19)).trans hkindPaddedRaw
  have hkindSawMap :=
    (hkindRefines (⟨10, by decide⟩ : Fin 19)).trans hkindSawMapRaw
  have hkindEntries :=
    (hkindRefines (⟨11, by decide⟩ : Fin 19)).trans hkindEntriesRaw
  have hkindBase :=
    (hkindRefines (⟨12, by decide⟩ : Fin 19)).trans hkindBaseRaw
  have hkindLength :=
    (hkindRefines (⟨13, by decide⟩ : Fin 19)).trans hkindLengthRaw
  have hkindUsable :=
    (hkindRefines (⟨14, by decide⟩ : Fin 19)).trans hkindUsableRaw
  have hkindBlocked :=
    (hkindRefines (⟨15, by decide⟩ : Fin 19)).trans hkindBlockedRaw
  have hkindTarget :=
    (hkindRefines (⟨16, by decide⟩ : Fin 19)).trans hkindTargetRaw
  have hkindTagCount :=
    (hkindRefines (⟨18, by decide⟩ : Fin 19)).trans hkindTagCountRaw
  have hkindUsableBound :
      (scalarStep (scalarStep (scalarStep state baseChunk) lengthChunk)
          kindChunk).word[14]! ≤ 1 := by
    rw [hkindUsable]
    split <;> simp_all
  have hkindBlockedBound :
      (scalarStep (scalarStep (scalarStep state baseChunk) lengthChunk)
          kindChunk).word[15]! ≤ 1 := by
    rw [hkindBlocked]
    split <;> simp_all
  have hcomposed :
      SuccessfulScalarRichTraversal target entries
          (scalarStep (scalarStep (scalarStep state baseChunk) lengthChunk)
            kindChunk)
          rest terminal →
        SuccessfulScalarRichTraversal target
          ({ base, length, kind := BootMemoryMapDecoder.memoryKind kindWord } ::
            entries)
          state (baseChunk :: lengthChunk :: kindChunk :: rest) terminal := by
    intro hrest
    apply SuccessfulScalarRichTraversal.nonEntry
      ({ base, length, kind := BootMemoryMapDecoder.memoryKind kindWord } :: entries)
      state terminal baseChunk (lengthChunk :: kindChunk :: rest)
    · rw [hphase]
      decide
    · exact hbaseError
    apply SuccessfulScalarRichTraversal.nonEntry
      ({ base, length, kind := BootMemoryMapDecoder.memoryKind kindWord } :: entries)
      (scalarStep state baseChunk) terminal lengthChunk (kindChunk :: rest)
    · rw [hbasePhase]
      decide
    · exact hlengthError
    apply SuccessfulScalarRichTraversal.entry
      base length kindWord entries
      (scalarStep (scalarStep state baseChunk) lengthChunk)
      terminal kindChunk rest
    · exact hlengthPhase
    · exact hlengthBaseWord
    · exact hlengthWord
    · exact hlengthTarget
    · exact hkindChunkWord
    · exact hkindStep
    · exact hbaseBound
    · exact hstopBound
    · exact hkindBound
    · exact htarget
    · exact hrest
  exact ⟨hcomposed, hkindVersion, hkindStatus, hkindStep,
    hkindIdentityWord, hkindExtent, hkindCursor, hkindPhase, hkindContent,
    hkindPadded, hkindSawMap, hkindEntries, hkindBase, hkindLength,
    hkindUsableBound, hkindBlockedBound, hkindTarget, hkindTagCount⟩

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

/-- A successful indexed lookup fixes the corresponding dropped-list head.
This small list fact lets source-indexed canonical chunk certificates feed the
continuation-style scalar/rich traversal constructors without reassembling a
second chunk list. -/
private theorem drop_eq_cons_drop_succ_of_get?_eq_some
    {α : Type} (values : List α) (index : Nat) (value : α)
    (hget : values[index]? = some value) :
    values.drop index = value :: values.drop (index + 1) := by
  induction values generalizing index with
  | nil =>
      simp at hget
  | cons head tail ih =>
      cases index with
      | zero =>
          simp at hget
          subst value
          rfl
      | succ index =>
          simp only [List.getElem?_cons_succ] at hget
          simpa [Nat.add_assoc] using ih index hget

/-- The layout word retained by a successful memory-map tag is the exact
canonical chunk immediately after that tag's header.  The following retained
tag header makes the layout chunk nonterminal even for an empty map.  Besides
binding identity, offset, bytes, and packed word, the result exposes every
production scalar query so it can be consumed directly by the admitted layout
transition theorem. -/
theorem canonicalMemoryMapLayoutStep_source_refines
    (identity : UInt64) (bytes : List UInt8)
    (total offset fuel tagWord layoutWord : Nat)
    (tagsRev tags : List Tag) (entries : List RawEntry)
    (htotal : total = bytes.length)
    (htotalAligned : total % 8 = 0)
    (hoffsetAligned : offset % 8 = 0)
    (hsize : memoryMapTagHeaderSize ≤ high32Nat tagWord)
    (hrest :
      SuccessfulTagDecodeTraversal bytes total
        (offset + aligned8 (high32Nat tagWord)) fuel true
        (.memoryMap (high32Nat tagWord) (low32Nat layoutWord)
          (high32Nat layoutWord) entries :: tagsRev) tags)
    (hlayout : readU64 bytes (offset + 8) = .ok layoutWord)
    (state : ScalarState) :
    let index := offset / 8 + 1
    let chunk : ModelChunk :=
      { identity
        offset := offset + 8
        bytes := (bytes.drop (offset + 8)).take 8
        terminal := false }
    (canonicalChunks identity bytes)[index]? = some chunk ∧
      (canonicalChunks identity bytes).drop index =
        chunk :: (canonicalChunks identity bytes).drop (index + 1) ∧
      chunkWord chunk.bytes = UInt64.ofNat layoutWord ∧
      ∀ query : Fin 19,
        (scalarStep state chunk).word[query.val]! =
          BootMemoryMapStreamAuthority.stepWord
            state.word[0]! state.word[1]! state.word[2]! state.word[3]!
            state.word[4]! state.word[5]! state.word[6]! state.word[7]!
            state.word[8]! state.word[9]! state.word[10]! state.word[11]!
            state.word[12]! state.word[13]! state.word[14]! state.word[15]!
            state.word[16]! state.word[17]! state.word[18]!
            identity (UInt64.ofNat (offset + 8)) (UInt64.ofNat layoutWord) 0
            (UInt64.ofNat query.val) := by
  dsimp only
  have hnextBound :=
    successfulTagDecodeTraversal_offset_lt_total bytes total
      (offset + aligned8 (high32Nat tagWord)) fuel true
      (.memoryMap (high32Nat tagWord) (low32Nat layoutWord)
        (high32Nat layoutWord) entries :: tagsRev) tags hrest
  have htotalWords : total / 8 * 8 = total := by
    have h := Nat.mod_add_div total 8
    rw [htotalAligned, Nat.zero_add] at h
    simpa [Nat.mul_comm] using h
  have hoffsetWords : offset / 8 * 8 = offset := by
    have h := Nat.mod_add_div offset 8
    rw [hoffsetAligned, Nat.zero_add] at h
    simpa [Nat.mul_comm] using h
  have hadvanceLow : 16 ≤ aligned8 (high32Nat tagWord) := by
    simp only [memoryMapTagHeaderSize, aligned8] at hsize ⊢
    omega
  have hindex : offset / 8 + 1 < bytes.length / 8 := by
    rw [← htotal]
    omega
  have hterminal : (offset / 8 + 1 + 1 == bytes.length / 8) = false := by
    apply beq_false_of_ne
    rw [← htotal]
    omega
  have hrefines :=
    canonicalScalarStep_source_refines identity bytes
      (by simpa [← htotal] using htotalAligned)
      (offset / 8 + 1) hindex state layoutWord (by
        simpa [hoffsetWords, Nat.add_mul] using hlayout)
  have hget :
      (canonicalChunks identity bytes)[offset / 8 + 1]? =
        some
          { identity
            offset := offset + 8
            bytes := (bytes.drop (offset + 8)).take 8
            terminal := false } := by
    simpa only [hoffsetWords, Nat.add_mul, hterminal] using
      (hrefines (⟨0, by decide⟩ : Fin 19)).1
  have hreadChunk :
      readU64 ((bytes.drop (offset + 8)).take 8) 0 = .ok layoutWord := by
    rw [readU64_drop_take]
    exact hlayout
  refine ⟨hget,
    drop_eq_cons_drop_succ_of_get?_eq_some
      (canonicalChunks identity bytes) (offset / 8 + 1) _ hget,
    chunkWord_readU64_agreement _ _ hreadChunk, ?_⟩
  intro query
  simpa only [hoffsetWords, Nat.add_mul, Nat.one_mul, hterminal,
    Bool.false_eq_true, ↓reduceIte] using (hrefines query).2

/-- The canonical layout source certificate is directly consumable by the
continuation-style scalar/rich layout constructor.  In particular, the chunk
list in the resulting traversal is the exact dropped suffix of the immutable
buffer's canonical decomposition; callers cannot substitute an equal packed
word at a different source position. -/
theorem successfulScalarRichTraversal_canonicalMemoryMapLayout
    (identity : UInt64) (bytes : List UInt8)
    (total offset fuel tagWord layoutWord target : Nat)
    (tagsRev tags : List Tag) (entries : List RawEntry)
    (state terminal : ScalarState)
    (htotal : total = bytes.length)
    (htotalAligned : total % 8 = 0)
    (hoffsetAligned : offset % 8 = 0)
    (hsize : memoryMapTagHeaderSize ≤ high32Nat tagWord)
    (htagRest :
      SuccessfulTagDecodeTraversal bytes total
        (offset + aligned8 (high32Nat tagWord)) fuel true
        (.memoryMap (high32Nat tagWord) (low32Nat layoutWord)
          (high32Nat layoutWord) entries :: tagsRev) tags)
    (hlayout : readU64 bytes (offset + 8) = .ok layoutWord)
    (hidentityAligned : identity % 8 = 0)
    (hextentLow : 16 ≤ UInt64.ofNat total)
    (hextentHigh : UInt64.ofNat total ≤ 65536)
    (hextentAligned : UInt64.ofNat total % 8 = 0)
    (hoffsetLt : UInt64.ofNat (offset + 8) < UInt64.ofNat total)
    (hoffsetNotFinal :
      UInt64.ofNat (offset + 8) + 8 ≠ UInt64.ofNat total)
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
      state.word[7]! = BootMemoryMapStreamAuthority.phaseMapLayout)
    (hcontentAligned : state.word[8]! % 24 = 0)
    (hpadded : state.word[9]! = 0)
    (hsawMap : state.word[10]! = 1)
    (husable : state.word[14]! ≤ 1)
    (hblocked : state.word[15]! ≤ 1)
    (htargetWord : state.word[16]! = UInt64.ofNat target)
    (htarget : target < frameLimit)
    (htagCount : state.word[18]! ≤ 64)
    (hlayoutLow :
      BootMemoryMapStreamAuthority.low32 (UInt64.ofNat layoutWord) = 24)
    (hlayoutHigh :
      BootMemoryMapStreamAuthority.high32 (UInt64.ofNat layoutWord) = 0)
    (hentryBound :
      state.word[8]! / 24 ≤ BootMemoryMapStreamAuthority.entryLimit)
    (hrest :
      SuccessfulScalarRichTraversal target entries
        (scalarStep state
          { identity
            offset := offset + 8
            bytes := (bytes.drop (offset + 8)).take 8
            terminal := false })
        ((canonicalChunks identity bytes).drop (offset / 8 + 2)) terminal) :
    SuccessfulScalarRichTraversal target entries state
      ((canonicalChunks identity bytes).drop (offset / 8 + 1)) terminal := by
  obtain ⟨hget, hdrop, hword, hrefines⟩ :=
    canonicalMemoryMapLayoutStep_source_refines identity bytes total offset
      fuel tagWord layoutWord tagsRev tags entries htotal htotalAligned
      hoffsetAligned hsize htagRest hlayout state
  rw [hdrop]
  apply successfulScalarRichTraversal_memoryMapLayout
    identity (UInt64.ofNat total) (UInt64.ofNat (offset + 8))
    (UInt64.ofNat layoutWord) target entries state terminal
      { identity
        offset := offset + 8
        bytes := (bytes.drop (offset + 8)).take 8
        terminal := false }
      ((canonicalChunks identity bytes).drop (offset / 8 + 2))
  · rfl
  · rfl
  · rfl
  · exact hword
  · exact hversion
  · exact hstatus
  · exact herror
  · exact hidentity
  · exact hidentityAligned
  · exact hextent
  · exact hextentLow
  · exact hextentHigh
  · exact hextentAligned
  · exact hoffset
  · exact hoffsetLt
  · exact hoffsetNotFinal
  · exact hphase
  · exact hcontentAligned
  · exact hpadded
  · exact hsawMap
  · exact husable
  · exact hblocked
  · exact htargetWord
  · exact htarget
  · exact htagCount
  · exact hlayoutLow
  · exact hlayoutHigh
  · exact hentryBound
  · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hrest

/-- The three exact source reads retained by one rich entry traversal fix
three consecutive canonical chunks.  The following-header room supplied by
the tag traversal makes the type chunk nonterminal even for the final map
entry.  This packages the source slices and packed words needed by the
continuation-style entry constructor. -/
theorem canonicalMemoryMapEntrySteps_source_refines
    (identity : UInt64) (bytes : List UInt8) (total entryOffset : Nat)
    (base length kindWord : Nat)
    (htotal : total = bytes.length)
    (htotalAligned : total % 8 = 0)
    (hentryOffsetAligned : entryOffset % 8 = 0)
    (hroom : entryOffset + memoryMapEntrySize + 8 ≤ total)
    (hbase : readU64 bytes entryOffset = .ok base)
    (hlength : readU64 bytes (entryOffset + 8) = .ok length)
    (hkind : readU64 bytes (entryOffset + 16) = .ok kindWord) :
    let index := entryOffset / 8
    let baseChunk : ModelChunk :=
      { identity
        offset := entryOffset
        bytes := (bytes.drop entryOffset).take 8
        terminal := false }
    let lengthChunk : ModelChunk :=
      { identity
        offset := entryOffset + 8
        bytes := (bytes.drop (entryOffset + 8)).take 8
        terminal := false }
    let kindChunk : ModelChunk :=
      { identity
        offset := entryOffset + 16
        bytes := (bytes.drop (entryOffset + 16)).take 8
        terminal := false }
    (canonicalChunks identity bytes).drop index =
        baseChunk :: lengthChunk :: kindChunk ::
          (canonicalChunks identity bytes).drop (index + 3) ∧
      chunkWord baseChunk.bytes = UInt64.ofNat base ∧
      chunkWord lengthChunk.bytes = UInt64.ofNat length ∧
      chunkWord kindChunk.bytes = UInt64.ofNat kindWord := by
  dsimp only
  next =>
      simp only [memoryMapEntrySize] at hroom
      have hoffsetWords : entryOffset / 8 * 8 = entryOffset := by
        have h := Nat.mod_add_div entryOffset 8
        rw [hentryOffsetAligned, Nat.zero_add] at h
        simpa [Nat.mul_comm] using h
      have htotalWords : total / 8 * 8 = total := by
        have h := Nat.mod_add_div total 8
        rw [htotalAligned, Nat.zero_add] at h
        simpa [Nat.mul_comm] using h
      have haligned : bytes.length % 8 = 0 := by
        simpa [← htotal] using htotalAligned
      have hindex0 : entryOffset / 8 < bytes.length / 8 := by
        rw [← htotal]
        omega
      have hindex1 : entryOffset / 8 + 1 < bytes.length / 8 := by
        rw [← htotal]
        omega
      have hindex2 : entryOffset / 8 + 2 < bytes.length / 8 := by
        rw [← htotal]
        omega
      have hterminal0 :
          (entryOffset / 8 + 1 == bytes.length / 8) = false := by
        apply beq_false_of_ne
        rw [← htotal]
        omega
      have hterminal1 :
          (entryOffset / 8 + 1 + 1 == bytes.length / 8) = false := by
        apply beq_false_of_ne
        rw [← htotal]
        omega
      have hterminal2 :
          (entryOffset / 8 + 2 + 1 == bytes.length / 8) = false := by
        apply beq_false_of_ne
        rw [← htotal]
        omega
      have hget0 :=
        canonicalChunks_get?_source identity bytes haligned
          (entryOffset / 8) hindex0
      have hget1 :=
        canonicalChunks_get?_source identity bytes haligned
          (entryOffset / 8 + 1) hindex1
      have hget2 :=
        canonicalChunks_get?_source identity bytes haligned
          (entryOffset / 8 + 2) hindex2
      have hbaseGet :
          (canonicalChunks identity bytes)[entryOffset / 8]? =
            some
              { identity
                offset := entryOffset
                bytes := (bytes.drop entryOffset).take 8
                terminal := false } := by
        simpa only [hoffsetWords, hterminal0] using hget0
      have hlengthGet :
          (canonicalChunks identity bytes)[entryOffset / 8 + 1]? =
            some
              { identity
                offset := entryOffset + 8
                bytes := (bytes.drop (entryOffset + 8)).take 8
                terminal := false } := by
        simpa only [hoffsetWords, Nat.add_mul, Nat.one_mul, hterminal1] using
          hget1
      have hkindGet :
          (canonicalChunks identity bytes)[entryOffset / 8 + 2]? =
            some
              { identity
                offset := entryOffset + 16
                bytes := (bytes.drop (entryOffset + 16)).take 8
                terminal := false } := by
        simpa only [hoffsetWords, Nat.add_mul, hterminal2] using hget2
      have hdrop0 :=
        drop_eq_cons_drop_succ_of_get?_eq_some
          (canonicalChunks identity bytes) (entryOffset / 8) _ hbaseGet
      have hdrop1 :=
        drop_eq_cons_drop_succ_of_get?_eq_some
          (canonicalChunks identity bytes) (entryOffset / 8 + 1) _ hlengthGet
      have hdrop2 :=
        drop_eq_cons_drop_succ_of_get?_eq_some
          (canonicalChunks identity bytes) (entryOffset / 8 + 2) _ hkindGet
      have hbaseRead :
          readU64 ((bytes.drop entryOffset).take 8) 0 = .ok base := by
        rw [readU64_drop_take]
        exact hbase
      have hlengthRead :
          readU64 ((bytes.drop (entryOffset + 8)).take 8) 0 = .ok length := by
        rw [readU64_drop_take]
        exact hlength
      have hkindRead :
          readU64 ((bytes.drop (entryOffset + 16)).take 8) 0 =
            .ok kindWord := by
        rw [readU64_drop_take]
        exact hkind
      refine ⟨?_,
        chunkWord_readU64_agreement _ _ hbaseRead,
        chunkWord_readU64_agreement _ _ hlengthRead,
        chunkWord_readU64_agreement _ _ hkindRead⟩
      rw [hdrop0, hdrop1, hdrop2]

/-- The exact three canonical chunks retained by one rich entry traversal can
be consumed by the production scalar entry transition.  Thus any traversal
over the following canonical suffix lifts to the suffix beginning at this
entry, with the precise decoded `RawEntry` attached to its classification
fold. -/
theorem successfulScalarRichTraversal_canonicalMemoryMapEntry_with_successor
    (identity : UInt64) (bytes : List UInt8) (total entryOffset target : Nat)
    (base length kindWord : Nat) (restEntries : List RawEntry)
    (state terminal : ScalarState)
    (htotal : total = bytes.length)
    (htotalAligned : total % 8 = 0)
    (hentryOffsetAligned : entryOffset % 8 = 0)
    (hroom : entryOffset + memoryMapEntrySize + 8 ≤ total)
    (hbaseOffsetLt : UInt64.ofNat entryOffset < UInt64.ofNat total)
    (hbaseOffsetNotFinal :
      UInt64.ofNat entryOffset + 8 ≠ UInt64.ofNat total)
    (hlengthOffsetLt :
      UInt64.ofNat entryOffset + 8 < UInt64.ofNat total)
    (hlengthOffsetNotFinal :
      UInt64.ofNat entryOffset + 8 + 8 ≠ UInt64.ofNat total)
    (hkindOffsetLt :
      UInt64.ofNat entryOffset + 8 + 8 < UInt64.ofNat total)
    (hkindOffsetNotFinal :
      UInt64.ofNat entryOffset + 8 + 8 + 8 ≠ UInt64.ofNat total)
    (hbase : readU64 bytes entryOffset = .ok base)
    (hlength : readU64 bytes (entryOffset + 8) = .ok length)
    (hkind : readU64 bytes (entryOffset + 16) = .ok kindWord)
    (hreserved : high32Nat kindWord = 0)
    (hlengthNonzero : length ≠ 0)
    (hbaseBound : base < wordLimit)
    (hstopBound : length < wordLimit - base)
    (hidentityAligned : identity % 8 = 0)
    (hextentLow : 16 ≤ UInt64.ofNat total)
    (hextentHigh : UInt64.ofNat total ≤ 65536)
    (hextentAligned : UInt64.ofNat total % 8 = 0)
    (hversion :
      state.word[0]! = BootMemoryMapStreamAuthority.abiVersion)
    (hstatus :
      state.word[1]! = BootMemoryMapStreamAuthority.active)
    (herror :
      state.word[2]! = BootMemoryMapStreamAuthority.noError)
    (hidentity : state.word[3]! = identity)
    (hextent : state.word[4]! = UInt64.ofNat total)
    (hoffset : state.word[5]! = UInt64.ofNat entryOffset)
    (hphase :
      state.word[7]! = BootMemoryMapStreamAuthority.phaseEntryBase)
    (hpadded : state.word[9]! = 0)
    (hsawMap : state.word[10]! = 1)
    (hentryCount :
      state.word[11]! < BootMemoryMapStreamAuthority.entryLimit)
    (husable : state.word[14]! ≤ 1)
    (hblocked : state.word[15]! ≤ 1)
    (htargetWord : state.word[16]! = UInt64.ofNat target)
    (htarget : target < frameLimit)
    (htagCount : state.word[18]! ≤ 64) :
    (SuccessfulScalarRichTraversal target restEntries
          (scalarStep
            (scalarStep
              (scalarStep state
                { identity
                  offset := entryOffset
                  bytes := (bytes.drop entryOffset).take 8
                  terminal := false })
              { identity
                offset := entryOffset + 8
                bytes := (bytes.drop (entryOffset + 8)).take 8
                terminal := false })
            { identity
              offset := entryOffset + 16
              bytes := (bytes.drop (entryOffset + 16)).take 8
              terminal := false })
          ((canonicalChunks identity bytes).drop (entryOffset / 8 + 3))
          terminal →
        SuccessfulScalarRichTraversal target
          ({ base, length, kind := memoryKind (low32Nat kindWord) } :: restEntries)
          state ((canonicalChunks identity bytes).drop (entryOffset / 8))
          terminal) ∧
      let next :=
        scalarStep
          (scalarStep
            (scalarStep state
              { identity
                offset := entryOffset
                bytes := (bytes.drop entryOffset).take 8
                terminal := false })
            { identity
              offset := entryOffset + 8
              bytes := (bytes.drop (entryOffset + 8)).take 8
              terminal := false })
          { identity
            offset := entryOffset + 16
            bytes := (bytes.drop (entryOffset + 16)).take 8
            terminal := false }
      next.word[0]! = BootMemoryMapStreamAuthority.abiVersion ∧
        next.word[1]! = BootMemoryMapStreamAuthority.active ∧
        next.word[2]! = BootMemoryMapStreamAuthority.noError ∧
        next.word[3]! = identity ∧
        next.word[4]! = UInt64.ofNat total ∧
        next.word[5]! = UInt64.ofNat entryOffset + 8 + 8 + 8 ∧
        next.word[7]! =
          (if state.word[8]! = 24
            then BootMemoryMapStreamAuthority.phaseTag
            else BootMemoryMapStreamAuthority.phaseEntryBase) ∧
        next.word[8]! = state.word[8]! - 24 ∧
        next.word[9]! = 0 ∧
        next.word[10]! = 1 ∧
        next.word[11]! = state.word[11]! + 1 ∧
        next.word[12]! = UInt64.ofNat base ∧
        next.word[13]! = UInt64.ofNat length ∧
        next.word[14]! ≤ 1 ∧
        next.word[15]! ≤ 1 ∧
        next.word[16]! = UInt64.ofNat target ∧
        next.word[18]! = state.word[18]! := by
      obtain ⟨hchunks, hbaseWord, hlengthWord, hkindWord⟩ :=
        canonicalMemoryMapEntrySteps_source_refines identity bytes total
          entryOffset base length kindWord htotal htotalAligned
          hentryOffsetAligned hroom hbase hlength hkind
      rw [hchunks]
      apply successfulScalarRichTraversal_memoryMapEntry_with_successor
        identity (UInt64.ofNat total) (UInt64.ofNat entryOffset) target
        base length (low32Nat kindWord) restEntries state terminal
        { identity
          offset := entryOffset
          bytes := (bytes.drop entryOffset).take 8
          terminal := false }
        { identity
          offset := entryOffset + 8
          bytes := (bytes.drop (entryOffset + 8)).take 8
          terminal := false }
        { identity
          offset := entryOffset + 16
          bytes := (bytes.drop (entryOffset + 16)).take 8
          terminal := false }
        ((canonicalChunks identity bytes).drop (entryOffset / 8 + 3))
      · rfl
      · rfl
      · rfl
      · rfl
      · simp [UInt64.ofNat_add]
      · calc
          UInt64.ofNat (entryOffset + 16) =
              UInt64.ofNat entryOffset + UInt64.ofNat 16 := by
                rw [UInt64.ofNat_add]
          _ = UInt64.ofNat entryOffset + 8 + 8 := by
            rw [show UInt64.ofNat 16 = 8 + 8 by decide]
            exact (UInt64.add_assoc _ _ _).symm
      · rfl
      · rfl
      · rfl
      · exact hbaseWord
      · exact hlengthWord
      · have hkindEq : kindWord = low32Nat kindWord := by
          unfold high32Nat at hreserved
          unfold low32Nat
          omega
        rw [← hkindEq]
        exact hkindWord
      · exact hversion
      · exact hstatus
      · exact herror
      · exact hidentity
      · exact hidentityAligned
      · exact hextent
      · exact hextentLow
      · exact hextentHigh
      · exact hextentAligned
      · exact hoffset
      · exact hbaseOffsetLt
      · exact hbaseOffsetNotFinal
      · exact hlengthOffsetLt
      · exact hlengthOffsetNotFinal
      · exact hkindOffsetLt
      · exact hkindOffsetNotFinal
      · exact hphase
      · exact hpadded
      · exact hsawMap
      · exact hentryCount
      · exact husable
      · exact hblocked
      · exact htargetWord
      · exact htarget
      · exact htagCount
      · exact hlengthNonzero
      · exact hbaseBound
      · omega
      · unfold low32Nat
        omega

/-- The raw successor returned by one canonical entry step preserves the
induction invariant for the exact number of entries still encoded in the
memory-map payload.  In particular, the rich entry count fixes whether the
next canonical word is another entry base or the following tag header; the
remaining byte count and bounded scalar entry counter cannot be supplied
independently by a caller. -/
theorem canonicalMemoryMapEntrySuccessor_threads_remaining
    (state next : ScalarState) (remaining : Nat)
    (hremaining : remaining < maxEntries)
    (hcontent :
      state.word[8]! =
        UInt64.ofNat ((remaining + 1) * memoryMapEntrySize))
    (hentryBudget :
      state.word[11]!.toNat + remaining + 1 ≤ maxEntries)
    (hphase :
      next.word[7]! =
        (if state.word[8]! = 24
          then BootMemoryMapStreamAuthority.phaseTag
          else BootMemoryMapStreamAuthority.phaseEntryBase))
    (hbytes : next.word[8]! = state.word[8]! - 24)
    (hcount : next.word[11]! = state.word[11]! + 1) :
    next.word[7]! =
        (if remaining = 0
          then BootMemoryMapStreamAuthority.phaseTag
          else BootMemoryMapStreamAuthority.phaseEntryBase) ∧
      next.word[8]! = UInt64.ofNat (remaining * memoryMapEntrySize) ∧
      next.word[11]!.toNat + remaining ≤ maxEntries := by
  have hremainingBytes :
      (remaining + 1) * memoryMapEntrySize < UInt64.size := by
    have hremainingNat : remaining < 256 := by
      simpa [maxEntries] using hremaining
    unfold memoryMapEntrySize UInt64.size
    omega
  have hphaseTest :
      (UInt64.ofNat ((remaining + 1) * memoryMapEntrySize) = 24) =
        (remaining = 0) := by
    apply propext
    constructor
    · intro heq
      have := congrArg UInt64.toNat heq
      rw [UInt64.toNat_ofNat_of_lt' hremainingBytes] at this
      change (remaining + 1) * memoryMapEntrySize = 24 at this
      unfold memoryMapEntrySize at this
      omega
    · rintro rfl
      unfold memoryMapEntrySize
      decide
  have hnextBytes :
      next.word[8]! = UInt64.ofNat (remaining * memoryMapEntrySize) := by
    rw [hbytes, hcontent]
    rw [show (24 : UInt64) = UInt64.ofNat 24 by decide]
    rw [← UInt64.ofNat_sub (by
      simp [memoryMapEntrySize]
      omega)]
    congr 1
    unfold memoryMapEntrySize
    omega
  have hstateCount : state.word[11]!.toNat + 1 < UInt64.size := by
    have hbudgetNat : state.word[11]!.toNat + remaining + 1 ≤ 256 := by
      simpa [maxEntries] using hentryBudget
    unfold UInt64.size
    omega
  have hnextCount :
      next.word[11]!.toNat = state.word[11]!.toNat + 1 := by
    rw [hcount, UInt64.toNat_add]
    simp only [UInt64.toNat_ofNat]
    exact Nat.mod_eq_of_lt hstateCount
  refine ⟨?_, hnextBytes, ?_⟩
  · rw [hphase, hcontent]
    by_cases hzero : remaining = 0
    · rw [if_pos (hphaseTest.mpr hzero), if_pos hzero]
    · rw [if_neg (fun heq => hzero (hphaseTest.mp heq)), if_neg hzero]
  · rw [hnextCount]
    omega

/-- The scalar state invariant at a canonical memory-map entry boundary.
`remaining` counts complete entries beginning at `offset`; zero therefore
describes the following tag-header boundary.  The byte count, phase, and
bounded accumulated entry count are carried together so recursive consumers
cannot splice an unrelated scalar state into the rich entry traversal. -/
def CanonicalMemoryMapEntryState
    (identity : UInt64) (total offset target remaining : Nat)
    (state : ScalarState) : Prop :=
  state.word[0]! = BootMemoryMapStreamAuthority.abiVersion ∧
    state.word[1]! = BootMemoryMapStreamAuthority.active ∧
    state.word[2]! = BootMemoryMapStreamAuthority.noError ∧
    state.word[3]! = identity ∧
    state.word[4]! = UInt64.ofNat total ∧
    state.word[5]! = UInt64.ofNat offset ∧
    state.word[7]! =
      (if remaining = 0
        then BootMemoryMapStreamAuthority.phaseTag
        else BootMemoryMapStreamAuthority.phaseEntryBase) ∧
    state.word[8]! = UInt64.ofNat (remaining * memoryMapEntrySize) ∧
    state.word[9]! = 0 ∧
    state.word[10]! = 1 ∧
    state.word[11]!.toNat + remaining ≤ maxEntries ∧
    state.word[14]! ≤ 1 ∧
    state.word[15]! ≤ 1 ∧
    state.word[16]! = UInt64.ofNat target ∧
    target < frameLimit ∧
    state.word[18]! ≤ 64

/-- The complete canonical entry-boundary invariant follows from the raw
production successor equations alone.  In particular, this theorem has no
scalar/rich continuation premise: the successor state can be established
before recursively constructing the traversal over later entries. -/
theorem canonicalMemoryMapEntryState_of_successor
    (identity : UInt64) (total offset target remaining : Nat)
    (state next : ScalarState)
    (hstate :
      CanonicalMemoryMapEntryState identity total offset target
        (remaining + 1) state)
    (hversion :
      next.word[0]! = BootMemoryMapStreamAuthority.abiVersion)
    (hstatus :
      next.word[1]! = BootMemoryMapStreamAuthority.active)
    (herror :
      next.word[2]! = BootMemoryMapStreamAuthority.noError)
    (hidentity : next.word[3]! = identity)
    (hextent : next.word[4]! = UInt64.ofNat total)
    (hoffset :
      next.word[5]! = UInt64.ofNat offset + 8 + 8 + 8)
    (hphase :
      next.word[7]! =
        (if state.word[8]! = 24
          then BootMemoryMapStreamAuthority.phaseTag
          else BootMemoryMapStreamAuthority.phaseEntryBase))
    (hcontent : next.word[8]! = state.word[8]! - 24)
    (hpadded : next.word[9]! = 0)
    (hsawMap : next.word[10]! = 1)
    (hentryCount : next.word[11]! = state.word[11]! + 1)
    (husable : next.word[14]! ≤ 1)
    (hblocked : next.word[15]! ≤ 1)
    (htargetWord : next.word[16]! = UInt64.ofNat target)
    (htagCount : next.word[18]! = state.word[18]!) :
    CanonicalMemoryMapEntryState identity total
      (offset + memoryMapEntrySize) target remaining next := by
  rcases hstate with ⟨_, _, _, _, _, _, _, hstateContent, _, _,
    hentryBudget, _, _, _, htarget, hstateTagCount⟩
  have hremaining : remaining < maxEntries := by
    omega
  obtain ⟨hnextPhase, hnextContent, hnextBudget⟩ :=
    canonicalMemoryMapEntrySuccessor_threads_remaining state next remaining
      hremaining hstateContent hentryBudget hphase hcontent hentryCount
  refine ⟨hversion, hstatus, herror, hidentity, hextent, ?_, hnextPhase,
    hnextContent, hpadded, hsawMap, hnextBudget, husable, hblocked,
    htargetWord, htarget, ?_⟩
  · simpa [memoryMapEntrySize, UInt64.ofNat_add, UInt64.add_assoc] using
      hoffset
  · rw [htagCount]
    exact hstateTagCount

/-- One canonical rich entry and its production scalar successor preserve the
complete entry-boundary invariant.  This is the recursive step needed by the
universal entry traversal: it composes the immutable three-chunk source
certificate with `canonicalMemoryMapEntrySuccessor_threads_remaining`, while
also retaining the exact rich entry attached to the scalar classification
step. -/
theorem successfulScalarRichTraversal_canonicalMemoryMapEntry_threads_remaining
    (identity : UInt64) (bytes : List UInt8)
    (total entryOffset target remaining : Nat)
    (base length kindWord : Nat) (restEntries : List RawEntry)
    (state terminal : ScalarState)
    (htotal : total = bytes.length)
    (htotalAligned : total % 8 = 0)
    (hentryOffsetAligned : entryOffset % 8 = 0)
    (hroom : entryOffset + memoryMapEntrySize + 8 ≤ total)
    (hbaseOffsetLt : UInt64.ofNat entryOffset < UInt64.ofNat total)
    (hbaseOffsetNotFinal :
      UInt64.ofNat entryOffset + 8 ≠ UInt64.ofNat total)
    (hlengthOffsetLt :
      UInt64.ofNat entryOffset + 8 < UInt64.ofNat total)
    (hlengthOffsetNotFinal :
      UInt64.ofNat entryOffset + 8 + 8 ≠ UInt64.ofNat total)
    (hkindOffsetLt :
      UInt64.ofNat entryOffset + 8 + 8 < UInt64.ofNat total)
    (hkindOffsetNotFinal :
      UInt64.ofNat entryOffset + 8 + 8 + 8 ≠ UInt64.ofNat total)
    (hbase : readU64 bytes entryOffset = .ok base)
    (hlength : readU64 bytes (entryOffset + 8) = .ok length)
    (hkind : readU64 bytes (entryOffset + 16) = .ok kindWord)
    (hreserved : high32Nat kindWord = 0)
    (hlengthNonzero : length ≠ 0)
    (hbaseBound : base < wordLimit)
    (hstopBound : length < wordLimit - base)
    (hidentityAligned : identity % 8 = 0)
    (hextentLow : 16 ≤ UInt64.ofNat total)
    (hextentHigh : UInt64.ofNat total ≤ 65536)
    (hextentAligned : UInt64.ofNat total % 8 = 0)
    (hstate :
      CanonicalMemoryMapEntryState identity total entryOffset target
        (remaining + 1) state)
    (hrest :
      SuccessfulScalarRichTraversal target restEntries
        (scalarStep
          (scalarStep
            (scalarStep state
              { identity
                offset := entryOffset
                bytes := (bytes.drop entryOffset).take 8
                terminal := false })
            { identity
              offset := entryOffset + 8
              bytes := (bytes.drop (entryOffset + 8)).take 8
              terminal := false })
          { identity
            offset := entryOffset + 16
            bytes := (bytes.drop (entryOffset + 16)).take 8
            terminal := false })
        ((canonicalChunks identity bytes).drop (entryOffset / 8 + 3))
        terminal) :
    let next :=
      scalarStep
        (scalarStep
          (scalarStep state
            { identity
              offset := entryOffset
              bytes := (bytes.drop entryOffset).take 8
              terminal := false })
          { identity
            offset := entryOffset + 8
            bytes := (bytes.drop (entryOffset + 8)).take 8
            terminal := false })
        { identity
          offset := entryOffset + 16
          bytes := (bytes.drop (entryOffset + 16)).take 8
          terminal := false }
    SuccessfulScalarRichTraversal target
        ({ base, length, kind := memoryKind (low32Nat kindWord) } :: restEntries)
        state ((canonicalChunks identity bytes).drop (entryOffset / 8))
        terminal ∧
      CanonicalMemoryMapEntryState identity total
        (entryOffset + memoryMapEntrySize) target remaining next := by
  dsimp only
  rcases hstate with ⟨hversion, hstatus, herror, hidentity, hextent,
    hoffset, hphase, hcontent, hpadded, hsawMap, hentryBudget, husable,
    hblocked, htargetWord, htarget, htagCount⟩
  have hstateOriginal :
      CanonicalMemoryMapEntryState identity total entryOffset target
        (remaining + 1) state := by
    exact ⟨hversion, hstatus, herror, hidentity, hextent, hoffset, hphase,
      hcontent, hpadded, hsawMap, hentryBudget, husable, hblocked,
      htargetWord, htarget, htagCount⟩
  have hremaining : remaining < maxEntries := by
    omega
  have hentryCount :
      state.word[11]! < BootMemoryMapStreamAuthority.entryLimit := by
    rw [UInt64.lt_iff_toNat_lt]
    change state.word[11]!.toNat < (UInt64.ofNat maxEntries).toNat
    rw [UInt64.toNat_ofNat_of_lt' (by
      unfold maxEntries UInt64.size
      omega)]
    omega
  have hphaseEntry :
      state.word[7]! = BootMemoryMapStreamAuthority.phaseEntryBase := by
    simpa using hphase
  obtain ⟨hprepend, hnextVersion, hnextStatus, hnextError,
    hnextIdentity, hnextExtent, hnextOffset, hnextPhase, hnextContent,
    hnextPadded, hnextSawMap, hnextCount, hnextBase, hnextLength,
    hnextUsable, hnextBlocked, hnextTarget, hnextTagCount⟩ :=
    successfulScalarRichTraversal_canonicalMemoryMapEntry_with_successor
      identity bytes total entryOffset target base length kindWord restEntries
      state terminal htotal htotalAligned hentryOffsetAligned hroom
      hbaseOffsetLt hbaseOffsetNotFinal hlengthOffsetLt
      hlengthOffsetNotFinal hkindOffsetLt hkindOffsetNotFinal hbase hlength
      hkind hreserved hlengthNonzero hbaseBound hstopBound hidentityAligned
      hextentLow hextentHigh hextentAligned hversion hstatus herror hidentity
      hextent hoffset hphaseEntry hpadded hsawMap hentryCount husable hblocked
      htargetWord htarget htagCount
  refine ⟨hprepend hrest, ?_⟩
  apply canonicalMemoryMapEntryState_of_successor
    identity total entryOffset target remaining state
      (scalarStep
        (scalarStep
          (scalarStep state
            { identity
              offset := entryOffset
              bytes := (bytes.drop entryOffset).take 8
              terminal := false })
          { identity
            offset := entryOffset + 8
            bytes := (bytes.drop (entryOffset + 8)).take 8
            terminal := false })
        { identity
          offset := entryOffset + 16
          bytes := (bytes.drop (entryOffset + 16)).take 8
          terminal := false })
    hstateOriginal hnextVersion hnextStatus hnextError hnextIdentity
    hnextExtent hnextOffset hnextPhase hnextContent hnextPadded hnextSawMap
    hnextCount hnextUsable hnextBlocked hnextTarget hnextTagCount

/-- Every rich entry traversal can be consumed from one packaged canonical
entry-boundary state.  The continuation begins only after all retained entries
have advanced that same state to the following tag-header boundary, so neither
an intermediate scalar state nor its remaining-entry count can be supplied
independently. -/
theorem successfulScalarRichTraversal_canonicalMemoryMapEntries
    (identity : UInt64) (bytes : List UInt8)
    (total entryOffset target count : Nat) (entries : List RawEntry)
    (state terminal : ScalarState)
    (htotal : total = bytes.length)
    (htotalLow : 16 ≤ total)
    (htotalHigh : total ≤ maxTagBytes)
    (htotalAligned : total % 8 = 0)
    (hentryOffsetAligned : entryOffset % 8 = 0)
    (hroom : entryOffset + count * memoryMapEntrySize + 8 ≤ total)
    (hidentityAligned : identity % 8 = 0)
    (hentries :
      SuccessfulEntryDecodeTraversal bytes entryOffset count entries)
    (hstate :
      CanonicalMemoryMapEntryState identity total entryOffset target count state)
    (hcontinuation :
      ∀ after,
        CanonicalMemoryMapEntryState identity total
            (entryOffset + count * memoryMapEntrySize) target 0 after →
          after.word[18]! = state.word[18]! →
          SuccessfulScalarRichTraversal target [] after
            ((canonicalChunks identity bytes).drop
              ((entryOffset + count * memoryMapEntrySize) / 8))
            terminal) :
    SuccessfulScalarRichTraversal target entries state
      ((canonicalChunks identity bytes).drop (entryOffset / 8)) terminal := by
  induction hentries generalizing state with
  | done offset =>
      simpa using hcontinuation state hstate rfl
  | entry offset count base length kindWord rest hbase hlength hkind
      hreserved hlengthNonzero hbaseBound hlengthBound hstopBound hrest ih =>
      have htotalHigh' : total ≤ 65536 := by
        simpa [maxTagBytes] using htotalHigh
      have htotalLt : total < UInt64.size :=
        Nat.lt_of_le_of_lt htotalHigh' (by
          unfold UInt64.size
          omega)
      have hcurrentRoom : offset + memoryMapEntrySize + 8 ≤ total := by
        unfold memoryMapEntrySize at hroom ⊢
        omega
      have hoffsetLtNat : offset < total := by
        unfold memoryMapEntrySize at hcurrentRoom
        omega
      have hoffset8LtNat : offset + 8 < total := by
        unfold memoryMapEntrySize at hcurrentRoom
        omega
      have hoffset16LtNat : offset + 16 < total := by
        unfold memoryMapEntrySize at hcurrentRoom
        omega
      have hoffset24LtNat : offset + 24 < total := by
        unfold memoryMapEntrySize at hcurrentRoom
        omega
      have hbaseOffsetLt :
          UInt64.ofNat offset < UInt64.ofNat total := by
        rw [UInt64.lt_iff_toNat_lt,
          UInt64.toNat_ofNat_of_lt' htotalLt]
        rw [UInt64.toNat_ofNat_of_lt'
          (Nat.lt_trans hoffsetLtNat htotalLt)]
        exact hoffsetLtNat
      have hbaseOffsetNotFinal :
          UInt64.ofNat offset + 8 ≠ UInt64.ofNat total := by
        intro heq
        have := congrArg UInt64.toNat heq
        rw [show UInt64.ofNat offset + 8 = UInt64.ofNat (offset + 8) by
          rw [UInt64.ofNat_add]
          rfl] at this
        rw [UInt64.toNat_ofNat_of_lt' (Nat.lt_trans hoffset8LtNat htotalLt),
          UInt64.toNat_ofNat_of_lt' htotalLt] at this
        omega
      have hlengthOffsetLt :
          UInt64.ofNat offset + 8 < UInt64.ofNat total := by
        rw [show UInt64.ofNat offset + 8 = UInt64.ofNat (offset + 8) by
          rw [UInt64.ofNat_add]
          rfl]
        rw [UInt64.lt_iff_toNat_lt,
          UInt64.toNat_ofNat_of_lt' htotalLt]
        rw [UInt64.toNat_ofNat_of_lt'
          (Nat.lt_trans hoffset8LtNat htotalLt)]
        exact hoffset8LtNat
      have hlengthOffsetNotFinal :
          UInt64.ofNat offset + 8 + 8 ≠ UInt64.ofNat total := by
        intro heq
        have := congrArg UInt64.toNat heq
        rw [show UInt64.ofNat offset + 8 + 8 =
          UInt64.ofNat (offset + 16) by
            rw [show offset + 16 = (offset + 8) + 8 by omega,
              UInt64.ofNat_add, UInt64.ofNat_add]
            rfl] at this
        rw [UInt64.toNat_ofNat_of_lt'
            (Nat.lt_trans hoffset16LtNat htotalLt),
          UInt64.toNat_ofNat_of_lt' htotalLt] at this
        omega
      have hkindOffsetLt :
          UInt64.ofNat offset + 8 + 8 < UInt64.ofNat total := by
        rw [show UInt64.ofNat offset + 8 + 8 =
          UInt64.ofNat (offset + 16) by
            rw [show offset + 16 = (offset + 8) + 8 by omega,
              UInt64.ofNat_add, UInt64.ofNat_add]
            rfl]
        rw [UInt64.lt_iff_toNat_lt,
          UInt64.toNat_ofNat_of_lt' htotalLt]
        rw [UInt64.toNat_ofNat_of_lt'
          (Nat.lt_trans hoffset16LtNat htotalLt)]
        exact hoffset16LtNat
      have hkindOffsetNotFinal :
          UInt64.ofNat offset + 8 + 8 + 8 ≠ UInt64.ofNat total := by
        intro heq
        have := congrArg UInt64.toNat heq
        rw [show UInt64.ofNat offset + 8 + 8 + 8 =
          UInt64.ofNat (offset + 24) by
            rw [show offset + 24 = ((offset + 8) + 8) + 8 by omega,
              UInt64.ofNat_add, UInt64.ofNat_add, UInt64.ofNat_add]
            rfl] at this
        rw [UInt64.toNat_ofNat_of_lt'
            (Nat.lt_trans hoffset24LtNat htotalLt),
          UInt64.toNat_ofNat_of_lt' htotalLt] at this
        omega
      have hextentLow : 16 ≤ UInt64.ofNat total := by
        rw [UInt64.le_iff_toNat_le, UInt64.toNat_ofNat_of_lt' htotalLt]
        exact htotalLow
      have hextentHigh : UInt64.ofNat total ≤ 65536 := by
        rw [UInt64.le_iff_toNat_le, UInt64.toNat_ofNat_of_lt' htotalLt]
        simpa [maxTagBytes] using htotalHigh
      have hextentAligned : UInt64.ofNat total % 8 = 0 := by
        apply UInt64.toNat.inj
        simp [UInt64.toNat_ofNat_of_lt' htotalLt, htotalAligned]
      let next :=
        scalarStep
          (scalarStep
            (scalarStep state
              { identity
                offset
                bytes := (bytes.drop offset).take 8
                terminal := false })
            { identity
              offset := offset + 8
              bytes := (bytes.drop (offset + 8)).take 8
              terminal := false })
          { identity
            offset := offset + 16
            bytes := (bytes.drop (offset + 16)).take 8
            terminal := false }
      have hstateOriginal := hstate
      rcases hstate with ⟨hversion, hstatus, herror, hidentity, hextent,
        hoffset, hphase, hcontent, hpadded, hsawMap, hentryBudget, husable,
        hblocked, htargetWord, htarget, htagCount⟩
      have hentryCount :
          state.word[11]! < BootMemoryMapStreamAuthority.entryLimit := by
        rw [UInt64.lt_iff_toNat_lt]
        change state.word[11]!.toNat < (UInt64.ofNat maxEntries).toNat
        rw [UInt64.toNat_ofNat_of_lt' (by
          unfold maxEntries UInt64.size
          omega)]
        omega
      have hphaseEntry :
          state.word[7]! = BootMemoryMapStreamAuthority.phaseEntryBase := by
        simpa using hphase
      obtain ⟨hprepend, hnextVersion, hnextStatus, hnextError,
        hnextIdentity, hnextExtent, hnextOffset, hnextPhase, hnextContent,
        hnextPadded, hnextSawMap, hnextCount, hnextBase, hnextLength,
        hnextUsable, hnextBlocked, hnextTarget, hnextTagCount⟩ :=
        successfulScalarRichTraversal_canonicalMemoryMapEntry_with_successor
          identity bytes total offset target base length kindWord rest
          state terminal htotal htotalAligned hentryOffsetAligned
          hcurrentRoom hbaseOffsetLt hbaseOffsetNotFinal hlengthOffsetLt
          hlengthOffsetNotFinal hkindOffsetLt hkindOffsetNotFinal hbase
          hlength hkind hreserved hlengthNonzero hbaseBound hstopBound
          hidentityAligned hextentLow hextentHigh hextentAligned hversion
          hstatus herror hidentity hextent hoffset hphaseEntry hpadded hsawMap
          hentryCount husable hblocked htargetWord htarget htagCount
      have hnextState :
          CanonicalMemoryMapEntryState identity total
            (offset + memoryMapEntrySize) target count next := by
        apply canonicalMemoryMapEntryState_of_successor
          identity total offset target count state next hstateOriginal
          hnextVersion hnextStatus hnextError hnextIdentity hnextExtent
          hnextOffset hnextPhase hnextContent hnextPadded hnextSawMap
          hnextCount hnextUsable hnextBlocked hnextTarget hnextTagCount
      have hnextTraversal :
          SuccessfulScalarRichTraversal target rest next
            ((canonicalChunks identity bytes).drop ((offset + 24) / 8))
            terminal := by
        apply ih (state := next)
        · simp [memoryMapEntrySize, Nat.add_mod, hentryOffsetAligned]
        · unfold memoryMapEntrySize at hroom ⊢
          omega
        · exact hnextState
        · intro after hafter
          intro hafterTagCount
          have hendOffset :
              offset + memoryMapEntrySize + count * memoryMapEntrySize =
                offset + (count + 1) * memoryMapEntrySize := by
            unfold memoryMapEntrySize
            omega
          rw [hendOffset]
          apply hcontinuation
          rw [← hendOffset]
          · exact hafter
          · exact hafterTagCount.trans hnextTagCount
      have hoffsetWords : (offset + 24) / 8 = offset / 8 + 3 := by
        have hdiv := Nat.mod_add_div offset 8
        rw [hentryOffsetAligned, Nat.zero_add] at hdiv
        omega
      exact hprepend (by simpa [next, hoffsetWords] using hnextTraversal)

/-- The existential-continuation form of the canonical entry traversal.
Unlike the fixed-terminal theorem above, this theorem carries the terminal
state produced by the post-entry continuation through the entry induction.
This avoids constructing a dependent choice function over every hypothetical
entry successor merely to consume the one canonical successor. -/
theorem successfulScalarRichTraversal_canonicalMemoryMapEntries_exists
    (identity : UInt64) (bytes : List UInt8)
    (total entryOffset target count : Nat) (entries : List RawEntry)
    (state : ScalarState)
    (htotal : total = bytes.length)
    (htotalLow : 16 ≤ total)
    (htotalHigh : total ≤ maxTagBytes)
    (htotalAligned : total % 8 = 0)
    (hentryOffsetAligned : entryOffset % 8 = 0)
    (hroom : entryOffset + count * memoryMapEntrySize + 8 ≤ total)
    (hidentityAligned : identity % 8 = 0)
    (hentries :
      SuccessfulEntryDecodeTraversal bytes entryOffset count entries)
    (hstate :
      CanonicalMemoryMapEntryState identity total entryOffset target count state)
    (hcontinuation :
      ∀ after,
        CanonicalMemoryMapEntryState identity total
            (entryOffset + count * memoryMapEntrySize) target 0 after →
          after.word[18]! = state.word[18]! →
          ∃ terminal,
            SuccessfulScalarRichTraversal target [] after
              ((canonicalChunks identity bytes).drop
                ((entryOffset + count * memoryMapEntrySize) / 8))
              terminal) :
    ∃ terminal,
      SuccessfulScalarRichTraversal target entries state
        ((canonicalChunks identity bytes).drop (entryOffset / 8)) terminal := by
  induction hentries generalizing state with
  | done offset =>
      simpa using hcontinuation state hstate rfl
  | entry offset count base length kindWord rest hbase hlength hkind
      hreserved hlengthNonzero hbaseBound hlengthBound hstopBound hrest ih =>
      have htotalHigh' : total ≤ 65536 := by
        simpa [maxTagBytes] using htotalHigh
      have htotalLt : total < UInt64.size :=
        Nat.lt_of_le_of_lt htotalHigh' (by
          unfold UInt64.size
          omega)
      have hcurrentRoom : offset + memoryMapEntrySize + 8 ≤ total := by
        unfold memoryMapEntrySize at hroom ⊢
        omega
      have hoffsetLtNat : offset < total := by
        unfold memoryMapEntrySize at hcurrentRoom
        omega
      have hoffset8LtNat : offset + 8 < total := by
        unfold memoryMapEntrySize at hcurrentRoom
        omega
      have hoffset16LtNat : offset + 16 < total := by
        unfold memoryMapEntrySize at hcurrentRoom
        omega
      have hoffset24LtNat : offset + 24 < total := by
        unfold memoryMapEntrySize at hcurrentRoom
        omega
      have hbaseOffsetLt :
          UInt64.ofNat offset < UInt64.ofNat total := by
        rw [UInt64.lt_iff_toNat_lt,
          UInt64.toNat_ofNat_of_lt' htotalLt,
          UInt64.toNat_ofNat_of_lt' (Nat.lt_trans hoffsetLtNat htotalLt)]
        exact hoffsetLtNat
      have hbaseOffsetNotFinal :
          UInt64.ofNat offset + 8 ≠ UInt64.ofNat total := by
        intro heq
        have heqNat := congrArg UInt64.toNat heq
        rw [show UInt64.ofNat offset + 8 = UInt64.ofNat (offset + 8) by
          rw [UInt64.ofNat_add]
          rfl] at heqNat
        rw [UInt64.toNat_ofNat_of_lt' (Nat.lt_trans hoffset8LtNat htotalLt),
          UInt64.toNat_ofNat_of_lt' htotalLt] at heqNat
        omega
      have hlengthOffsetLt :
          UInt64.ofNat offset + 8 < UInt64.ofNat total := by
        rw [show UInt64.ofNat offset + 8 = UInt64.ofNat (offset + 8) by
          rw [UInt64.ofNat_add]
          rfl]
        rw [UInt64.lt_iff_toNat_lt,
          UInt64.toNat_ofNat_of_lt' htotalLt,
          UInt64.toNat_ofNat_of_lt' (Nat.lt_trans hoffset8LtNat htotalLt)]
        exact hoffset8LtNat
      have hlengthOffsetNotFinal :
          UInt64.ofNat offset + 8 + 8 ≠ UInt64.ofNat total := by
        intro heq
        have heqNat := congrArg UInt64.toNat heq
        rw [show UInt64.ofNat offset + 8 + 8 =
          UInt64.ofNat (offset + 16) by
            rw [show offset + 16 = (offset + 8) + 8 by omega,
              UInt64.ofNat_add, UInt64.ofNat_add]
            rfl] at heqNat
        rw [UInt64.toNat_ofNat_of_lt'
            (Nat.lt_trans hoffset16LtNat htotalLt),
          UInt64.toNat_ofNat_of_lt' htotalLt] at heqNat
        omega
      have hkindOffsetLt :
          UInt64.ofNat offset + 8 + 8 < UInt64.ofNat total := by
        rw [show UInt64.ofNat offset + 8 + 8 =
          UInt64.ofNat (offset + 16) by
            rw [show offset + 16 = (offset + 8) + 8 by omega,
              UInt64.ofNat_add, UInt64.ofNat_add]
            rfl]
        rw [UInt64.lt_iff_toNat_lt,
          UInt64.toNat_ofNat_of_lt' htotalLt,
          UInt64.toNat_ofNat_of_lt' (Nat.lt_trans hoffset16LtNat htotalLt)]
        exact hoffset16LtNat
      have hkindOffsetNotFinal :
          UInt64.ofNat offset + 8 + 8 + 8 ≠ UInt64.ofNat total := by
        intro heq
        have heqNat := congrArg UInt64.toNat heq
        rw [show UInt64.ofNat offset + 8 + 8 + 8 =
          UInt64.ofNat (offset + 24) by
            rw [show offset + 24 = ((offset + 8) + 8) + 8 by omega,
              UInt64.ofNat_add, UInt64.ofNat_add, UInt64.ofNat_add]
            rfl] at heqNat
        rw [UInt64.toNat_ofNat_of_lt'
            (Nat.lt_trans hoffset24LtNat htotalLt),
          UInt64.toNat_ofNat_of_lt' htotalLt] at heqNat
        omega
      have hextentLow : 16 ≤ UInt64.ofNat total := by
        rw [UInt64.le_iff_toNat_le, UInt64.toNat_ofNat_of_lt' htotalLt]
        exact htotalLow
      have hextentHigh : UInt64.ofNat total ≤ 65536 := by
        rw [UInt64.le_iff_toNat_le, UInt64.toNat_ofNat_of_lt' htotalLt]
        simpa [maxTagBytes] using htotalHigh
      have hextentAligned : UInt64.ofNat total % 8 = 0 := by
        apply UInt64.toNat.inj
        simp [UInt64.toNat_ofNat_of_lt' htotalLt, htotalAligned]
      let next :=
        scalarStep
          (scalarStep
            (scalarStep state
              { identity
                offset
                bytes := (bytes.drop offset).take 8
                terminal := false })
            { identity
              offset := offset + 8
              bytes := (bytes.drop (offset + 8)).take 8
              terminal := false })
          { identity
            offset := offset + 16
            bytes := (bytes.drop (offset + 16)).take 8
            terminal := false }
      have hstateOriginal := hstate
      rcases hstate with ⟨hversion, hstatus, herror, hidentity, hextent,
        hoffset, hphase, hcontent, hpadded, hsawMap, hentryBudget, husable,
        hblocked, htargetWord, htarget, htagCount⟩
      have hentryCount :
          state.word[11]! < BootMemoryMapStreamAuthority.entryLimit := by
        rw [UInt64.lt_iff_toNat_lt]
        change state.word[11]!.toNat < (UInt64.ofNat maxEntries).toNat
        rw [UInt64.toNat_ofNat_of_lt' (by
          unfold maxEntries UInt64.size
          omega)]
        omega
      have hphaseEntry :
          state.word[7]! = BootMemoryMapStreamAuthority.phaseEntryBase := by
        simpa using hphase
      obtain ⟨_, hnextVersion, hnextStatus, hnextError,
        hnextIdentity, hnextExtent, hnextOffset, hnextPhase, hnextContent,
        hnextPadded, hnextSawMap, hnextCount, _hnextBase, _hnextLength,
        hnextUsable, hnextBlocked, hnextTarget, hnextTagCount⟩ :=
        successfulScalarRichTraversal_canonicalMemoryMapEntry_with_successor
          identity bytes total offset target base length kindWord rest
          state state htotal htotalAligned hentryOffsetAligned
          hcurrentRoom hbaseOffsetLt hbaseOffsetNotFinal hlengthOffsetLt
          hlengthOffsetNotFinal hkindOffsetLt hkindOffsetNotFinal hbase
          hlength hkind hreserved hlengthNonzero hbaseBound hstopBound
          hidentityAligned hextentLow hextentHigh hextentAligned hversion
          hstatus herror hidentity hextent hoffset hphaseEntry hpadded hsawMap
          hentryCount husable hblocked htargetWord htarget htagCount
      have hnextState :
          CanonicalMemoryMapEntryState identity total
            (offset + memoryMapEntrySize) target count next := by
        apply canonicalMemoryMapEntryState_of_successor
          identity total offset target count state next hstateOriginal
          hnextVersion hnextStatus hnextError hnextIdentity hnextExtent
          hnextOffset hnextPhase hnextContent hnextPadded hnextSawMap
          hnextCount hnextUsable hnextBlocked hnextTarget hnextTagCount
      obtain ⟨terminal, hnextTraversal⟩ := ih (state := next)
        (by simp [memoryMapEntrySize, Nat.add_mod, hentryOffsetAligned])
        (by
          unfold memoryMapEntrySize at hroom ⊢
          omega)
        hnextState
        (by
          intro after hafter hafterTagCount
          have hendOffset :
              offset + memoryMapEntrySize + count * memoryMapEntrySize =
                offset + (count + 1) * memoryMapEntrySize := by
            unfold memoryMapEntrySize
            omega
          rw [hendOffset]
          apply hcontinuation
          rw [← hendOffset]
          · exact hafter
          · exact hafterTagCount.trans hnextTagCount)
      obtain ⟨hprepend, _⟩ :=
        successfulScalarRichTraversal_canonicalMemoryMapEntry_with_successor
          identity bytes total offset target base length kindWord rest
          state terminal htotal htotalAligned hentryOffsetAligned
          hcurrentRoom hbaseOffsetLt hbaseOffsetNotFinal hlengthOffsetLt
          hlengthOffsetNotFinal hkindOffsetLt hkindOffsetNotFinal hbase
          hlength hkind hreserved hlengthNonzero hbaseBound hstopBound
          hidentityAligned hextentLow hextentHigh hextentAligned hversion
          hstatus herror hidentity hextent hoffset hphaseEntry hpadded hsawMap
          hentryCount husable hblocked htargetWord htarget htagCount
      have hoffsetWords : (offset + 24) / 8 = offset / 8 + 3 := by
        have hdiv := Nat.mod_add_div offset 8
        rw [hentryOffsetAligned, Nat.zero_add] at hdiv
        omega
      exact ⟨terminal,
        hprepend (by
          simpa [next, hoffsetWords, memoryMapEntrySize]
            using hnextTraversal)⟩

/-- A complete canonical rich entry traversal fixes both production
classification words to the folds over exactly those decoded entries.  This
is the field-agreement projection consumed by the later whole-tag refinement:
no caller-selected entry list or intermediate classification state appears in
the conclusion. -/
theorem canonicalMemoryMapEntries_terminal_classification
    (identity : UInt64) (bytes : List UInt8)
    (total entryOffset target count : Nat) (entries : List RawEntry)
    (state terminal : ScalarState)
    (htotal : total = bytes.length)
    (htotalLow : 16 ≤ total)
    (htotalHigh : total ≤ maxTagBytes)
    (htotalAligned : total % 8 = 0)
    (hentryOffsetAligned : entryOffset % 8 = 0)
    (hroom : entryOffset + count * memoryMapEntrySize + 8 ≤ total)
    (hidentityAligned : identity % 8 = 0)
    (hentries :
      SuccessfulEntryDecodeTraversal bytes entryOffset count entries)
    (hstate :
      CanonicalMemoryMapEntryState identity total entryOffset target count state)
    (hcontinuation :
      ∀ after,
        CanonicalMemoryMapEntryState identity total
            (entryOffset + count * memoryMapEntrySize) target 0 after →
          after.word[18]! = state.word[18]! →
          SuccessfulScalarRichTraversal target [] after
            ((canonicalChunks identity bytes).drop
              ((entryOffset + count * memoryMapEntrySize) / 8))
            terminal) :
    scalarReplay ((canonicalChunks identity bytes).drop (entryOffset / 8))
        state = terminal ∧
      terminal.word[1]! = BootMemoryMapStreamAuthority.complete ∧
      terminal.word[2]! = BootMemoryMapStreamAuthority.noError ∧
      terminal.word[14]! =
        entries.foldl (updateUsableClassification target) state.word[14]! ∧
      terminal.word[15]! =
        entries.foldl (updateBlockedClassification target) state.word[15]! := by
  apply successfulScalarRichTraversal_terminal_words target entries state terminal
  exact successfulScalarRichTraversal_canonicalMemoryMapEntries
    identity bytes total entryOffset target count entries state terminal
    htotal htotalLow htotalHigh htotalAligned hentryOffsetAligned hroom
    hidentityAligned hentries hstate hcontinuation

/-- The exact production state at a retained rich tag header.  The remaining
rich fuel and the consumed scalar tag count share one budget, which supplies
the strict count premise for every later header, including the end tag. -/
def CanonicalTagState
    (identity : UInt64) (total offset target fuel : Nat)
    (sawMemoryMap : Bool) (state : ScalarState) : Prop :=
  state.word[0]! = BootMemoryMapStreamAuthority.abiVersion ∧
    state.word[1]! = BootMemoryMapStreamAuthority.active ∧
    state.word[2]! = BootMemoryMapStreamAuthority.noError ∧
    state.word[3]! = identity ∧
    state.word[4]! = UInt64.ofNat total ∧
    state.word[5]! = UInt64.ofNat offset ∧
    state.word[7]! = BootMemoryMapStreamAuthority.phaseTag ∧
    state.word[8]! = 0 ∧
    state.word[9]! = 0 ∧
    state.word[10]! = (if sawMemoryMap then 1 else 0) ∧
    state.word[11]!.toNat ≤ maxEntries ∧
    (sawMemoryMap = false → state.word[11]! = 0) ∧
    state.word[14]! ≤ 1 ∧
    state.word[15]! ≤ 1 ∧
    state.word[16]! = UInt64.ofNat target ∧
    target < frameLimit ∧
    state.word[18]!.toNat + fuel ≤ maxTags

/-- Finishing the exact memory-map entry walk re-establishes the canonical tag
cursor.  This phase bridge is kept separate so large structural traversals do
not repeatedly normalize the zero-entry endpoint inside their heartbeat
budget. -/
theorem canonicalTagState_of_completedMemoryMapEntries
    (identity : UInt64) (total entryOffset tagOffset target fuel : Nat)
    (state : ScalarState)
    (hoffset : entryOffset = tagOffset)
    (hstate :
      CanonicalMemoryMapEntryState identity total entryOffset target 0 state)
    (htagBudget : state.word[18]!.toNat + fuel ≤ maxTags) :
    CanonicalTagState identity total tagOffset target fuel true state := by
  subst tagOffset
  rcases hstate with ⟨hversion, hstatus, herror, hidentity, hextent,
    hoffset, hphase, hcontent, hpadded, hsaw, hentryBudget, husable,
    hblocked, htarget, htargetBound, _htagBound⟩
  simp only [Nat.zero_mul] at hcontent
  simp only [Nat.add_zero] at hentryBudget
  exact ⟨hversion, hstatus, herror, hidentity, hextent, hoffset, hphase,
    hcontent, hpadded, hsaw, hentryBudget, by intro h; contradiction,
    husable, hblocked, htarget, htargetBound, htagBudget⟩

set_option maxHeartbeats 2000000 in
/-- Consume one retained ignored tag, including all payload and alignment
padding, while preserving the exact canonical tag-boundary invariant. -/
theorem canonicalIgnoredTag_successor
    (identity : UInt64) (bytes : List UInt8)
    (total offset fuel tagWord target : Nat) (sawMemoryMap : Bool)
    (tagsRev tags : List Tag) (state : ScalarState)
    (htotal : total = bytes.length)
    (hadmitted : AdmittedScalarStream identity total target)
    (hoffsetAligned : offset % 8 = 0)
    (hread : readU64 bytes offset = .ok tagWord)
    (hsize : 8 ≤ high32Nat tagWord)
    (hcontent : offset + high32Nat tagWord ≤ total)
    (hadvance : offset + aligned8 (high32Nat tagWord) ≤ total)
    (htypeEnd : low32Nat tagWord ≠ 0)
    (htypeMap : low32Nat tagWord ≠ 6)
    (hrest :
      SuccessfulTagDecodeTraversal bytes total
        (offset + aligned8 (high32Nat tagWord)) fuel sawMemoryMap
        (.ignored (high32Nat tagWord) :: tagsRev) tags)
    (hstate :
      CanonicalTagState identity total offset target (fuel + 1)
        sawMemoryMap state) :
    ∃ after,
      CanonicalTagState identity total
        (offset + aligned8 (high32Nat tagWord)) target fuel
        sawMemoryMap after ∧
      ∀ (entries : List RawEntry) (terminal : ScalarState),
        SuccessfulScalarRichTraversal target entries after
            ((canonicalChunks identity bytes).drop
              ((offset + aligned8 (high32Nat tagWord)) / 8))
            terminal →
          SuccessfulScalarRichTraversal target entries state
            ((canonicalChunks identity bytes).drop (offset / 8)) terminal := by
  have htotalLow := hadmitted.extentLow
  have htotalHigh := hadmitted.extentHigh
  have htotalAligned := hadmitted.extentAligned
  have hidentityAligned := hadmitted.identityAligned
  rcases hstate with ⟨hversion, hstatus, herror, hidentity, hextent,
    hoffset, hphase, hzeroContent, hzeroPadded, hsawMap, hentryCount,
    hentryCountZero, husable, hblocked, htargetWord, htarget, htagBudget⟩
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
  have hoffsetLtNat : offset < total := by
    have := successfulTagDecodeTraversal_offset_lt_total
      bytes total offset (fuel + 1) sawMemoryMap tagsRev tags
      (.ignoredTag offset fuel tagWord sawMemoryMap tagsRev tags hread hsize
        hcontent hadvance htypeEnd htypeMap hrest)
    omega
  have hoffsetLt :
      UInt64.ofNat offset < UInt64.ofNat total := by
    rw [UInt64.lt_iff_toNat_lt,
      UInt64.toNat_ofNat_of_lt' htotalLt,
      UInt64.toNat_ofNat_of_lt' (Nat.lt_trans hoffsetLtNat htotalLt)]
    exact hoffsetLtNat
  have hoffsetNotFinal :
      UInt64.ofNat offset + 8 ≠ UInt64.ofNat total := by
    intro heq
    have := congrArg UInt64.toNat heq
    have hoffset8 : offset + 8 < total := by
      have hnext := successfulTagDecodeTraversal_offset_lt_total
        bytes total (offset + aligned8 (high32Nat tagWord)) fuel sawMemoryMap
        (.ignored (high32Nat tagWord) :: tagsRev) tags hrest
      unfold aligned8 at hnext
      omega
    rw [show UInt64.ofNat offset + 8 = UInt64.ofNat (offset + 8) by simp,
      UInt64.toNat_ofNat_of_lt' (Nat.lt_trans hoffset8 htotalLt),
      UInt64.toNat_ofNat_of_lt' htotalLt] at this
    omega
  have htagCount : state.word[18]! < 64 := by
    rw [UInt64.lt_iff_toNat_lt]
    simp only [UInt64.toNat_ofNat]
    have hbudget := htagBudget
    simp only [maxTags] at hbudget
    omega
  have htagWordLt := readU64_lt_wordLimit bytes offset tagWord hread
  have hlow :
      BootMemoryMapStreamAuthority.low32 (UInt64.ofNat tagWord) =
        UInt64.ofNat (low32Nat tagWord) := by
    rw [BootMemoryMapStreamAuthority.low32,
      low32Word_ofNat tagWord htagWordLt]
  have hhigh :
      BootMemoryMapStreamAuthority.high32 (UInt64.ofNat tagWord) =
        UInt64.ofNat (high32Nat tagWord) := by
    rw [BootMemoryMapStreamAuthority.high32,
      high32Word_ofNat tagWord htagWordLt]
  have hsizeNoOverflow :
      UInt64.ofNat (high32Nat tagWord) ≤ 0xfffffffffffffff8 := by
    have hsizeBound : high32Nat tagWord < UInt64.size :=
      Nat.lt_of_le_of_lt (by omega) htotalLt
    rw [UInt64.le_iff_toNat_le,
      UInt64.toNat_ofNat_of_lt' hsizeBound]
    simp only [UInt64.toNat_ofNat]
    change high32Nat tagWord ≤ 18446744073709551608
    calc
      high32Nat tagWord ≤ offset + high32Nat tagWord :=
        Nat.le_add_left _ _
      _ ≤ total := hcontent
      _ ≤ maxTagBytes := htotalHigh
      _ ≤ 18446744073709551608 := by decide
  have hroundedNat :
      ((UInt64.ofNat (high32Nat tagWord) + 7) &&& 0xfffffffffffffff8) =
        UInt64.ofNat (aligned8 (high32Nat tagWord)) := by
    apply scalarAligned8_eq_richAligned8
    omega
  have hsizeFits :
      UInt64.ofNat (high32Nat tagWord) ≤
        UInt64.ofNat total - UInt64.ofNat offset := by
    rw [UInt64.le_iff_toNat_le,
      UInt64.toNat_sub_of_le]
    · rw [UInt64.toNat_ofNat_of_lt' htotalLt,
        UInt64.toNat_ofNat_of_lt' (Nat.lt_trans hoffsetLtNat htotalLt),
        UInt64.toNat_ofNat_of_lt'
          (Nat.lt_of_le_of_lt (by omega : high32Nat tagWord ≤ total) htotalLt)]
      omega
    · exact Nat.le_of_lt hoffsetLt
  have hroundedFits :
      ((UInt64.ofNat (high32Nat tagWord) + 7) &&& 0xfffffffffffffff8) ≤
        UInt64.ofNat total - UInt64.ofNat offset := by
    rw [hroundedNat, UInt64.le_iff_toNat_le, UInt64.toNat_sub_of_le]
    · rw [UInt64.toNat_ofNat_of_lt' htotalLt,
        UInt64.toNat_ofNat_of_lt' (Nat.lt_trans hoffsetLtNat htotalLt)]
      have hr : aligned8 (high32Nat tagWord) < UInt64.size := by
        exact Nat.lt_of_le_of_lt (by omega) htotalLt
      rw [UInt64.toNat_ofNat_of_lt' hr]
      omega
    · exact Nat.le_of_lt hoffsetLt
  let chunk : ModelChunk :=
    { identity
      offset
      bytes := (bytes.drop offset).take 8
      terminal := false }
  have hchunkRead : readU64 chunk.bytes 0 = .ok tagWord := by
    rw [readU64_drop_take]
    exact hread
  have hchunkWord : chunkWord chunk.bytes = UInt64.ofNat tagWord :=
    chunkWord_readU64_agreement _ _ hchunkRead
  have hheaderStep :=
    BootMemoryMapStreamAuthority.ignoredTagHeaderStepWords_of_admitted
      identity (UInt64.ofNat total) (UInt64.ofNat offset)
      state.word[6]! state.word[8]! state.word[9]! state.word[10]!
      state.word[11]! state.word[12]! state.word[13]! state.word[14]!
      state.word[15]! (UInt64.ofNat target) state.word[17]!
      state.word[18]! (UInt64.ofNat tagWord)
      hidentityAligned hextentLow hextentHigh hextentAligned hoffsetLt
      hoffsetNotFinal husable hblocked
      (by rw [hsawMap]; split <;> decide)
      (by
        rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat_of_lt' htargetLt]
        simpa [frameLimit, physicalLimit, pageBytes] using htarget)
      htagCount
      (by
        rw [hlow]
        intro h
        apply htypeEnd
        have hlowBound : low32Nat tagWord < UInt64.size := by
          unfold low32Nat UInt64.size
          omega
        have := congrArg UInt64.toNat h
        simpa [UInt64.toNat_ofNat_of_lt' hlowBound] using this)
      (by
        rw [hlow]
        intro h
        apply htypeMap
        have hlowBound : low32Nat tagWord < UInt64.size := by
          unfold low32Nat UInt64.size
          omega
        have := congrArg UInt64.toNat h
        simpa [UInt64.toNat_ofNat_of_lt' hlowBound] using this)
      (by
        rw [hhigh, UInt64.le_iff_toNat_le]
        have hhighBound : high32Nat tagWord < UInt64.size := by
          exact Nat.lt_of_le_of_lt
            (Nat.le_trans (Nat.le_add_left _ _) hcontent) htotalLt
        simpa [UInt64.toNat_ofNat_of_lt' hhighBound] using hsize)
      (by simpa [hhigh] using hsizeFits)
      (by simpa [hhigh] using hsizeNoOverflow)
      (by simpa [hhigh] using hroundedFits)
  let next := scalarStep state chunk
  have halignedBound :
      aligned8 (high32Nat tagWord) < UInt64.size :=
    Nat.lt_of_le_of_lt (by omega) htotalLt
  have hhighBound : high32Nat tagWord < UInt64.size :=
    Nat.lt_of_le_of_lt
      (Nat.le_trans (Nat.le_add_left _ _) hcontent) htotalLt
  have hnext :
      next.word[0]! = BootMemoryMapStreamAuthority.abiVersion ∧
        next.word[1]! = BootMemoryMapStreamAuthority.active ∧
        next.word[2]! = BootMemoryMapStreamAuthority.noError ∧
        next.word[3]! = identity ∧
        next.word[4]! = UInt64.ofNat total ∧
        next.word[5]! = UInt64.ofNat (offset + 8) ∧
        next.word[7]! =
          (if aligned8 (high32Nat tagWord) = 8
            then BootMemoryMapStreamAuthority.phaseTag
            else BootMemoryMapStreamAuthority.phaseIgnored) ∧
        next.word[8]! = UInt64.ofNat (high32Nat tagWord) - 8 ∧
        next.word[9]! = UInt64.ofNat (aligned8 (high32Nat tagWord)) - 8 ∧
        next.word[10]! = state.word[10]! ∧
        next.word[11]! = state.word[11]! ∧
        next.word[14]! = state.word[14]! ∧
        next.word[15]! = state.word[15]! ∧
        next.word[16]! = UInt64.ofNat target ∧
        next.word[18]! = state.word[18]! + 1 := by
    rcases hheaderStep with ⟨hnVersion, hnStatus, hnError, hnIdentity,
      hnExtent, hnOffset, hnPhase, hnContent, hnPadded, hnSaw, hnEntries,
      _hnBase, _hnLength, hnUsable, hnBlocked, hnTarget, _hnHighest,
      hnTagCount⟩
    rw [hhigh] at hnPhase hnContent hnPadded
    rw [hroundedNat] at hnPhase hnPadded
    have hphaseBridge :
        (if UInt64.ofNat (aligned8 (high32Nat tagWord)) == 8
          then BootMemoryMapStreamAuthority.phaseTag
          else BootMemoryMapStreamAuthority.phaseIgnored) =
        (if aligned8 (high32Nat tagWord) = 8
          then BootMemoryMapStreamAuthority.phaseTag
          else BootMemoryMapStreamAuthority.phaseIgnored) := by
      by_cases heq : aligned8 (high32Nat tagWord) = 8
      · simp [heq]
      · have hwordNe :
            UInt64.ofNat (aligned8 (high32Nat tagWord)) ≠ 8 := by
          intro hword
          apply heq
          have := congrArg UInt64.toNat hword
          simpa [UInt64.toNat_ofNat_of_lt' halignedBound] using this
        simp [heq, hwordNe]
    rw [hphaseBridge] at hnPhase
    simpa [next, scalarStep, chunk, hchunkWord, hversion, hstatus, herror,
      hidentity, hextent, hoffset, hphase, htargetWord, hroundedNat, hhigh]
      using ⟨hnVersion, hnStatus, hnError, hnIdentity, hnExtent, hnOffset,
        hnPhase, hnContent, hnPadded, hnSaw, hnEntries, hnUsable, hnBlocked,
        hnTarget, hnTagCount⟩
  have hnextFields := hnext
  rcases hnextFields with ⟨nxVersion, nxStatus, nxError, nxIdentity,
    nxExtent, nxOffset, nxPhase, nxContent, nxPadded, nxSaw, nxEntries,
    nxUsable, nxBlocked, nxTarget, nxTagCount⟩
  have h8High :
      (8 : UInt64) ≤ UInt64.ofNat (high32Nat tagWord) := by
    rw [UInt64.le_iff_toNat_le,
      UInt64.toNat_ofNat_of_lt' hhighBound]
    simpa using hsize
  have h8AlignedNat : 8 ≤ aligned8 (high32Nat tagWord) := by
    have hdiv :=
      Nat.mod_add_div (high32Nat tagWord + 7) 8
    have hmod :
        (high32Nat tagWord + 7) % 8 < 8 :=
      Nat.mod_lt _ (by decide)
    unfold aligned8
    omega
  have h8Aligned :
      (8 : UInt64) ≤ UInt64.ofNat (aligned8 (high32Nat tagWord)) := by
    rw [UInt64.le_iff_toNat_le,
      UInt64.toNat_ofNat_of_lt' halignedBound]
    simpa using h8AlignedNat
  obtain ⟨after, hspan, hafter⟩ :=
    successfulIgnoredTagSpan_of_ignoredTagTraversal identity bytes total
      offset fuel tagWord target sawMemoryMap tagsRev tags next htotal
      htotalLow htotalHigh htotalAligned hoffsetAligned hidentityAligned
      hsize hrest nxVersion nxStatus nxError nxIdentity nxExtent nxOffset nxPhase
      (by
        rw [nxContent, nxPadded, UInt64.le_iff_toNat_le,
          UInt64.toNat_sub_of_le _ _ h8High,
          UInt64.toNat_sub_of_le _ _ h8Aligned,
          UInt64.toNat_ofNat_of_lt' hhighBound,
          UInt64.toNat_ofNat_of_lt' halignedBound]
        unfold aligned8
        omega)
      (by
        rw [nxPadded]
        change UInt64.ofNat (aligned8 (high32Nat tagWord)) -
            UInt64.ofNat 8 =
          UInt64.ofNat (aligned8 (high32Nat tagWord) - 8)
        exact (UInt64.ofNat_sub h8AlignedNat).symm)
      (by rw [nxSaw, hsawMap]; split <;> decide)
      (by rw [nxUsable]; exact husable)
      (by rw [nxBlocked]; exact hblocked)
      nxTarget htarget
      (by
        rw [nxTagCount]
        rw [UInt64.le_iff_toNat_le, UInt64.toNat_add]
        simp only [UInt64.toNat_ofNat]
        have hcountNat : state.word[18]!.toNat < 64 := by
          rw [UInt64.lt_iff_toNat_lt] at htagCount
          simpa using htagCount
        have hsumLt : state.word[18]!.toNat + 1 < UInt64.size :=
          Nat.lt_trans (by omega : state.word[18]!.toNat + 1 < 65) (by decide)
        rw [Nat.mod_eq_of_lt hsumLt]
        omega)
  have hpreserved :=
    successfulIgnoredTagSpan_preserves_tag_fields next after
      (((canonicalChunks identity bytes).drop (offset / 8 + 1)).take
        (aligned8 (high32Nat tagWord) / 8 - 1)) hspan
  rcases hafter with ⟨hafterVersion, hafterStatus, hafterError,
    hafterIdentity, hafterExtent, hafterOffset, hafterPhase,
    hafterContent, hafterPadded, hafterSawBound, hafterUsableBound,
    hafterBlockedBound, hafterTarget, hafterTagBound⟩
  have hafterState :
      CanonicalTagState identity total
        (offset + aligned8 (high32Nat tagWord)) target fuel
        sawMemoryMap after := by
    refine ⟨hafterVersion, hafterStatus, hafterError, hafterIdentity,
      hafterExtent, hafterOffset, hafterPhase, hafterContent, hafterPadded,
      ?_, ?_, ?_, hafterUsableBound, hafterBlockedBound, hafterTarget, htarget, ?_⟩
    · rw [hpreserved.1, nxSaw, hsawMap]
    · rw [hpreserved.2.1, nxEntries]
      exact hentryCount
    · intro hsawFalse
      rw [hpreserved.2.1, nxEntries]
      exact hentryCountZero hsawFalse
    · rw [hpreserved.2.2.2.2, nxTagCount]
      rw [UInt64.toNat_add]
      simp only [UInt64.toNat_ofNat]
      omega
  refine ⟨after, hafterState, ?_⟩
  intro entries terminal htail
  have hbody :=
    successfulScalarRichTraversal_ignoredTagSpan target entries next after
      terminal
      (((canonicalChunks identity bytes).drop (offset / 8 + 1)).take
        (aligned8 (high32Nat tagWord) / 8 - 1))
      ((canonicalChunks identity bytes).drop
        ((offset + aligned8 (high32Nat tagWord)) / 8))
      hspan htail
  have hoffsetWords : offset / 8 * 8 = offset := by
    have := Nat.mod_add_div offset 8
    rw [hoffsetAligned, Nat.zero_add] at this
    omega
  have hadvanceAligned : aligned8 (high32Nat tagWord) % 8 = 0 := by
    unfold aligned8
    omega
  have hsplit :
      ((canonicalChunks identity bytes).drop (offset / 8 + 1)).take
          (aligned8 (high32Nat tagWord) / 8 - 1) ++
        (canonicalChunks identity bytes).drop
          ((offset + aligned8 (high32Nat tagWord)) / 8) =
      (canonicalChunks identity bytes).drop (offset / 8 + 1) := by
    have hadvanceWords :
        aligned8 (high32Nat tagWord) / 8 * 8 =
          aligned8 (high32Nat tagWord) := by
      have h := Nat.mod_add_div (aligned8 (high32Nat tagWord)) 8
      rw [hadvanceAligned, Nat.zero_add] at h
      omega
    have hindexEq :
        offset / 8 + 1 + (aligned8 (high32Nat tagWord) / 8 - 1) =
          (offset + aligned8 (high32Nat tagWord)) / 8 := by
      rw [← hoffsetWords, ← hadvanceWords, ← Nat.add_mul,
        Nat.mul_div_cancel _ (by decide : 0 < 8)]
      have : 1 ≤ aligned8 (high32Nat tagWord) / 8 := by
        omega
      omega
    have htailEq :
        (canonicalChunks identity bytes).drop
            ((offset + aligned8 (high32Nat tagWord)) / 8) =
          ((canonicalChunks identity bytes).drop (offset / 8 + 1)).drop
            (aligned8 (high32Nat tagWord) / 8 - 1) := by
      simp only [List.drop_drop, hindexEq]
    rw [htailEq]
    exact List.take_append_drop _ _
  rw [hsplit] at hbody
  obtain ⟨_, _, hget, _⟩ :=
    canonicalTagStep_source_refines identity bytes total offset (fuel + 1)
      sawMemoryMap tagsRev tags state htotal
      (by simpa [← htotal] using htotalAligned) hoffsetAligned
      (.ignoredTag offset fuel tagWord sawMemoryMap tagsRev tags hread hsize
        hcontent hadvance htypeEnd htypeMap hrest)
  have hterminalFalse : (offset + 8 == total) = false := by
    apply beq_false_of_ne
    intro heq
    apply hoffsetNotFinal
    rw [show UInt64.ofNat offset + 8 = UInt64.ofNat (offset + 8) by
      exact (UInt64.ofNat_add offset 8).symm, heq]
  have hdrop :=
    drop_eq_cons_drop_succ_of_get?_eq_some
      (canonicalChunks identity bytes) (offset / 8) chunk
      (by simpa [chunk, hoffsetWords, hterminalFalse] using hget)
  rw [hdrop]
  apply successfulScalarRichTraversal_ignoredTagHeader
    identity (UInt64.ofNat total) (UInt64.ofNat offset)
      (UInt64.ofNat tagWord) target entries state terminal chunk
      ((canonicalChunks identity bytes).drop (offset / 8 + 1))
    rfl rfl rfl hchunkWord hversion hstatus herror hidentity
    hidentityAligned hextent hextentLow hextentHigh hextentAligned
    hoffset hoffsetLt hoffsetNotFinal hphase husable hblocked
    (by rw [hsawMap]; split <;> decide) htargetWord htarget htagCount
    (by
      rw [hlow]
      intro h
      apply htypeEnd
      have hlowBound : low32Nat tagWord < UInt64.size := by
        unfold low32Nat UInt64.size
        omega
      have := congrArg UInt64.toNat h
      simpa [UInt64.toNat_ofNat_of_lt' hlowBound] using this)
    (by
      rw [hlow]
      intro h
      apply htypeMap
      have hlowBound : low32Nat tagWord < UInt64.size := by
        unfold low32Nat UInt64.size
        omega
      have := congrArg UInt64.toNat h
      simpa [UInt64.toNat_ofNat_of_lt' hlowBound] using this)
    (by
      rw [hhigh, UInt64.le_iff_toNat_le]
      simpa [UInt64.toNat_ofNat_of_lt' hhighBound] using hsize)
    (by simpa [hhigh] using hsizeFits)
    (by simpa [hhigh] using hsizeNoOverflow)
    (by simpa [hhigh] using hroundedFits) hbody

/-- Once the unique map has been consumed, the retained tag traversal consists
only of ignored spans followed by the retained end tag.  Induction over that
source certificate constructs the exact canonical scalar/rich suffix. -/
theorem successfulScalarRichTraversal_afterMemoryMap
    (identity : UInt64) (bytes : List UInt8)
    (total offset fuel target : Nat) (sawMemoryMap : Bool)
    (tagsRev tags : List Tag)
    (state : ScalarState)
    (htotal : total = bytes.length)
    (hadmitted : AdmittedScalarStream identity total target)
    (hoffsetAligned : offset % 8 = 0)
    (htraversal :
      SuccessfulTagDecodeTraversal bytes total offset fuel sawMemoryMap tagsRev tags)
    (hstate :
      CanonicalTagState identity total offset target fuel sawMemoryMap state)
    (hsaw : sawMemoryMap = true) :
    ∃ terminal,
      SuccessfulScalarRichTraversal target [] state
        ((canonicalChunks identity bytes).drop (offset / 8)) terminal := by
  have htotalLow := hadmitted.extentLow
  have htotalHigh := hadmitted.extentHigh
  have htotalAligned := hadmitted.extentAligned
  have hidentityAligned := hadmitted.identityAligned
  induction htraversal generalizing state with
  | endTag offset fuel tagWord tagsRev hread htype hsize hend =>
      rcases hstate with ⟨hversion, hstatus, herror, hidentity, hextent,
        hoffset, hphase, hcontent, hpadded, hsawMap, hentryCount,
        hentryCountZero, husable, hblocked, htargetWord, htarget, htagBudget⟩
      have htagCount : state.word[18]! < 64 := by
        rw [UInt64.lt_iff_toNat_lt]
        simp only [UInt64.toNat_ofNat]
        have hbudget := htagBudget
        simp only [maxTags] at hbudget
        omega
      have htotalWords : total / 8 * 8 = total := by
        have := Nat.mod_add_div total 8
        rw [htotalAligned, Nat.zero_add] at this
        omega
      have hoffsetWords : offset / 8 * 8 = offset := by
        have := Nat.mod_add_div offset 8
        rw [hoffsetAligned, Nat.zero_add] at this
        omega
      let chunk : ModelChunk :=
        { identity
          offset
          bytes := (bytes.drop offset).take 8
          terminal := true }
      have hchunkRead : readU64 chunk.bytes 0 = .ok tagWord := by
        rw [readU64_drop_take]
        exact hread
      obtain ⟨_, _, hget, _⟩ :=
        canonicalTagStep_source_refines identity bytes total offset (fuel + 1)
          true tagsRev (tagsRev.reverse ++ [.end 8]) state htotal
          (by simpa [← htotal] using htotalAligned) hoffsetAligned
          (.endTag offset fuel tagWord tagsRev hread htype hsize hend)
      have hdropHead :=
        drop_eq_cons_drop_succ_of_get?_eq_some
          (canonicalChunks identity bytes) (offset / 8) chunk
          (by simpa [chunk, hoffsetWords, hend] using hget)
      have hdropTail :
          (canonicalChunks identity bytes).drop (offset / 8 + 1) = [] := by
        apply List.eq_nil_of_length_eq_zero
        rw [List.length_drop, canonicalChunks_length identity bytes]
        rw [← htotal, ← htotalWords]
        omega
      rw [hdropTail] at hdropHead
      refine ⟨scalarStep state chunk, ?_⟩
      rw [hdropHead]
      apply successfulScalarRichTraversal_endTag identity total offset tagWord
        target state chunk htotalLow htotalHigh htotalAligned hend rfl rfl rfl
        hchunkRead htype hsize hversion hstatus herror hidentity
        hidentityAligned hextent hoffset hphase (by simpa using hsawMap)
        husable hblocked htargetWord htarget htagCount
  | ignoredTag offset fuel tagWord sawMemoryMap tagsRev tags hread hsize
      hcontent hadvance htypeEnd htypeMap hrest ih =>
      subst sawMemoryMap
      have hnextAligned :
          (offset + aligned8 (high32Nat tagWord)) % 8 = 0 := by
        simp [Nat.add_mod, hoffsetAligned, aligned8]
      obtain ⟨after, hafter, hwrap⟩ :=
        canonicalIgnoredTag_successor identity bytes total offset fuel tagWord
          target true tagsRev tags state htotal hadmitted
          hoffsetAligned hread hsize hcontent
          hadvance htypeEnd htypeMap hrest hstate
      obtain ⟨terminal, htail⟩ :=
        ih after hnextAligned hafter rfl
      exact ⟨terminal, hwrap [] terminal htail⟩
  | memoryMapTag =>
      contradiction

set_option maxHeartbeats 2000000 in
/-- Consume the unique retained map header, layout, and complete entry walk,
then continue through the post-map ignored/end suffix. -/
theorem successfulScalarRichTraversal_memoryMapTag_complete
    (identity : UInt64) (bytes : List UInt8)
    (total offset fuel tagWord layoutWord target : Nat)
    (tagsRev tags : List Tag) (entries : List RawEntry)
    (state : ScalarState)
    (htotal : total = bytes.length)
    (hadmitted : AdmittedScalarStream identity total target)
    (hoffsetAligned : offset % 8 = 0)
    (hread : readU64 bytes offset = .ok tagWord)
    (hsize : memoryMapTagHeaderSize ≤ high32Nat tagWord)
    (hcontent : offset + high32Nat tagWord ≤ total)
    (hadvance : offset + aligned8 (high32Nat tagWord) ≤ total)
    (htype : low32Nat tagWord = 6)
    (hlayout : readU64 bytes (offset + 8) = .ok layoutWord)
    (hentrySize : low32Nat layoutWord = memoryMapEntrySize)
    (hentryVersion : high32Nat layoutWord = 0)
    (halignedEntries :
      (high32Nat tagWord - memoryMapTagHeaderSize) % memoryMapEntrySize = 0)
    (hentryBound :
      (high32Nat tagWord - memoryMapTagHeaderSize) / memoryMapEntrySize ≤
        maxEntries)
    (hentries :
      SuccessfulEntryDecodeTraversal bytes
        (offset + memoryMapTagHeaderSize)
        ((high32Nat tagWord - memoryMapTagHeaderSize) / memoryMapEntrySize)
        entries)
    (hrest :
      SuccessfulTagDecodeTraversal bytes total
        (offset + aligned8 (high32Nat tagWord)) fuel true
        (.memoryMap (high32Nat tagWord) (low32Nat layoutWord)
          (high32Nat layoutWord) entries :: tagsRev) tags)
    (hstate :
      CanonicalTagState identity total offset target (fuel + 1) false state) :
    ∃ terminal,
      SuccessfulScalarRichTraversal target entries state
        ((canonicalChunks identity bytes).drop (offset / 8)) terminal := by
  have htotalLow := hadmitted.extentLow
  have htotalHigh := hadmitted.extentHigh
  have htotalAligned := hadmitted.extentAligned
  have hidentityAligned := hadmitted.identityAligned
  rcases hstate with ⟨hversion, hstatus, herror, hidentity, hextent,
    hoffset, hphase, hzeroContent, hzeroPadded, hsawMap, hentryCount,
    hentryCountZero, husable, hblocked, htargetWord, htarget, htagBudget⟩
  have hstateEntryZero : state.word[11]! = 0 := hentryCountZero rfl
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
  have hoffsetLtNat : offset < total := by
    simp only [memoryMapTagHeaderSize] at hsize
    omega
  have hoffsetLt :
      UInt64.ofNat offset < UInt64.ofNat total := by
    rw [UInt64.lt_iff_toNat_lt,
      UInt64.toNat_ofNat_of_lt' htotalLt,
      UInt64.toNat_ofNat_of_lt' (Nat.lt_trans hoffsetLtNat htotalLt)]
    exact hoffsetLtNat
  have hoffsetNotFinal :
      UInt64.ofNat offset + 8 ≠ UInt64.ofNat total := by
    intro heq
    have := congrArg UInt64.toNat heq
    have hoffset8Lt : offset + 8 < total := by
      simp only [memoryMapTagHeaderSize] at hsize
      omega
    rw [show UInt64.ofNat offset + 8 = UInt64.ofNat (offset + 8) by simp,
      UInt64.toNat_ofNat_of_lt' (Nat.lt_trans hoffset8Lt htotalLt),
      UInt64.toNat_ofNat_of_lt' htotalLt] at this
    omega
  have htagCount : state.word[18]! < 64 := by
    rw [UInt64.lt_iff_toNat_lt]
    simp only [UInt64.toNat_ofNat]
    have hbudget := htagBudget
    simp only [maxTags] at hbudget
    omega
  have htagCountSucc : state.word[18]! + 1 ≤ 64 := by
    rw [UInt64.le_iff_toNat_le, UInt64.toNat_add]
    simp only [UInt64.toNat_ofNat]
    have hcountNat : state.word[18]!.toNat < 64 := by
      rw [UInt64.lt_iff_toNat_lt] at htagCount
      simpa using htagCount
    have hsumLt : state.word[18]!.toNat + 1 < UInt64.size :=
      Nat.lt_trans (by omega : state.word[18]!.toNat + 1 < 65) (by decide)
    rw [Nat.mod_eq_of_lt hsumLt]
    omega
  have htargetBound : UInt64.ofNat target < 4096 := by
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat_of_lt' htargetLt]
    simpa [frameLimit, physicalLimit, pageBytes] using htarget
  have htagWordLt := readU64_lt_wordLimit bytes offset tagWord hread
  have hlow :
      BootMemoryMapStreamAuthority.low32 (UInt64.ofNat tagWord) =
        UInt64.ofNat (low32Nat tagWord) := by
    rw [BootMemoryMapStreamAuthority.low32,
      low32Word_ofNat tagWord htagWordLt]
  have hhigh :
      BootMemoryMapStreamAuthority.high32 (UInt64.ofNat tagWord) =
        UInt64.ofNat (high32Nat tagWord) := by
    rw [BootMemoryMapStreamAuthority.high32,
      high32Word_ofNat tagWord htagWordLt]
  have hhighBound : high32Nat tagWord < UInt64.size :=
    Nat.lt_of_le_of_lt (by omega) htotalLt
  have h16High :
      (16 : UInt64) ≤ UInt64.ofNat (high32Nat tagWord) := by
    rw [UInt64.le_iff_toNat_le,
      UInt64.toNat_ofNat_of_lt' hhighBound]
    simpa [memoryMapTagHeaderSize] using hsize
  have hsizeFits :
      UInt64.ofNat (high32Nat tagWord) ≤
        UInt64.ofNat total - UInt64.ofNat offset := by
    rw [UInt64.le_iff_toNat_le, UInt64.toNat_sub_of_le]
    · simp [UInt64.toNat_ofNat_of_lt' htotalLt,
        UInt64.toNat_ofNat_of_lt' (Nat.lt_trans hoffsetLtNat htotalLt),
        UInt64.toNat_ofNat_of_lt' hhighBound]
      omega
    · exact Nat.le_of_lt hoffsetLt
  have hsizeNoOverflow :
      UInt64.ofNat (high32Nat tagWord) ≤ 0xfffffffffffffff8 := by
    rw [UInt64.le_iff_toNat_le, UInt64.toNat_ofNat_of_lt' hhighBound]
    simp only [UInt64.toNat_ofNat]
    change high32Nat tagWord ≤ 18446744073709551608
    calc
      high32Nat tagWord ≤ offset + high32Nat tagWord :=
        Nat.le_add_left _ _
      _ ≤ total := hcontent
      _ ≤ maxTagBytes := htotalHigh
      _ ≤ 18446744073709551608 := by decide
  have hroundedNat :
      ((UInt64.ofNat (high32Nat tagWord) + 7) &&& 0xfffffffffffffff8) =
        UInt64.ofNat (aligned8 (high32Nat tagWord)) := by
    apply scalarAligned8_eq_richAligned8
    omega
  have hroundedFits :
      ((UInt64.ofNat (high32Nat tagWord) + 7) &&& 0xfffffffffffffff8) ≤
        UInt64.ofNat total - UInt64.ofNat offset := by
    rw [hroundedNat, UInt64.le_iff_toNat_le, UInt64.toNat_sub_of_le]
    · rw [UInt64.toNat_ofNat_of_lt' htotalLt,
        UInt64.toNat_ofNat_of_lt' (Nat.lt_trans hoffsetLtNat htotalLt)]
      have hr : aligned8 (high32Nat tagWord) < UInt64.size :=
        Nat.lt_of_le_of_lt (by omega) htotalLt
      rw [UInt64.toNat_ofNat_of_lt' hr]
      omega
    · exact Nat.le_of_lt hoffsetLt
  let header : ModelChunk :=
    { identity
      offset
      bytes := (bytes.drop offset).take 8
      terminal := false }
  have hheaderRead : readU64 header.bytes 0 = .ok tagWord := by
    rw [readU64_drop_take]
    exact hread
  have hheaderWord : chunkWord header.bytes = UInt64.ofNat tagWord :=
    chunkWord_readU64_agreement _ _ hheaderRead
  let afterHeader := scalarStep state header
  have hheaderStep :=
    BootMemoryMapStreamAuthority.memoryMapTagHeaderStepWords_of_admitted
      identity (UInt64.ofNat total) (UInt64.ofNat offset) state.word[6]!
      state.word[8]! state.word[9]! state.word[11]! state.word[12]!
      state.word[13]! state.word[14]! state.word[15]! (UInt64.ofNat target)
      state.word[17]! state.word[18]! (UInt64.ofNat tagWord)
      hidentityAligned hextentLow hextentHigh hextentAligned hoffsetLt
      hoffsetNotFinal husable hblocked htargetBound htagCount
      (by simp [hlow, htype])
      (by
        rw [hhigh, UInt64.le_iff_toNat_le]
        simpa [UInt64.toNat_ofNat_of_lt' hhighBound,
          memoryMapTagHeaderSize] using hsize)
      (by simpa [hhigh] using hsizeFits)
      (by simpa [hhigh] using hsizeNoOverflow)
      (by simpa [hhigh] using hroundedFits)
      (by
        rw [hhigh]
        apply UInt64.toNat.inj
        rw [UInt64.toNat_mod,
          UInt64.toNat_sub_of_le _ _ h16High,
          UInt64.toNat_ofNat_of_lt' hhighBound]
        simpa [memoryMapTagHeaderSize, memoryMapEntrySize] using
          halignedEntries)
      (by
        rw [hhigh, UInt64.le_iff_toNat_le, UInt64.toNat_div,
          UInt64.toNat_sub_of_le _ _ h16High]
        simpa [UInt64.toNat_ofNat_of_lt' hhighBound,
          memoryMapTagHeaderSize, memoryMapEntrySize,
          BootMemoryMapStreamAuthority.entryLimit, maxEntries]
          using hentryBound)
  have hafterHeader :
      afterHeader.word[0]! = BootMemoryMapStreamAuthority.abiVersion ∧
        afterHeader.word[1]! = BootMemoryMapStreamAuthority.active ∧
        afterHeader.word[2]! = BootMemoryMapStreamAuthority.noError ∧
        afterHeader.word[3]! = identity ∧
        afterHeader.word[4]! = UInt64.ofNat total ∧
        afterHeader.word[5]! = UInt64.ofNat (offset + 8) ∧
        afterHeader.word[7]! = BootMemoryMapStreamAuthority.phaseMapLayout ∧
        afterHeader.word[8]! =
          UInt64.ofNat (high32Nat tagWord) - 16 ∧
        afterHeader.word[9]! = 0 ∧
        afterHeader.word[10]! = 1 ∧
        afterHeader.word[11]! = 0 ∧
        afterHeader.word[14]! = state.word[14]! ∧
        afterHeader.word[15]! = state.word[15]! ∧
        afterHeader.word[16]! = UInt64.ofNat target ∧
        afterHeader.word[18]! = state.word[18]! + 1 := by
    rcases hheaderStep with ⟨haVersion, haStatus, haError, haIdentity,
      haExtent, haOffset, haPhase, haContent, haPadded, haSaw, haEntries,
      _haBase, _haLength, haUsable, haBlocked, haTarget, _haHighest,
      haTagCount⟩
    rw [hhigh] at haContent
    rw [hstateEntryZero] at haEntries
    simpa [afterHeader, scalarStep, header, hheaderWord, hversion, hstatus,
      herror, hidentity, hextent, hoffset, hphase, hsawMap, hstateEntryZero,
      htargetWord, hhigh] using
      ⟨haVersion, haStatus, haError, haIdentity, haExtent, haOffset,
        haPhase, haContent, haPadded, haSaw, haEntries, haUsable, haBlocked,
        haTarget, haTagCount⟩
  have hafterHeaderFields := hafterHeader
  rcases hafterHeaderFields with ⟨haVersion, haStatus, haError, haIdentity,
    haExtent, haOffset, haPhase, haContent, haPadded, haSaw, haEntries,
    haUsable, haBlocked, haTarget, haTagCount⟩
  let layout : ModelChunk :=
    { identity
      offset := offset + 8
      bytes := (bytes.drop (offset + 8)).take 8
      terminal := false }
  have hlayoutRead : readU64 layout.bytes 0 = .ok layoutWord := by
    rw [readU64_drop_take]
    exact hlayout
  have hlayoutWord : chunkWord layout.bytes = UInt64.ofNat layoutWord :=
    chunkWord_readU64_agreement _ _ hlayoutRead
  have hlayoutWordLt := readU64_lt_wordLimit bytes (offset + 8) layoutWord hlayout
  have hlayoutLow :
      BootMemoryMapStreamAuthority.low32 (UInt64.ofNat layoutWord) = 24 := by
    rw [BootMemoryMapStreamAuthority.low32,
      low32Word_ofNat layoutWord hlayoutWordLt, hentrySize]
    rfl
  have hlayoutHigh :
      BootMemoryMapStreamAuthority.high32 (UInt64.ofNat layoutWord) = 0 := by
    rw [BootMemoryMapStreamAuthority.high32,
      high32Word_ofNat layoutWord hlayoutWordLt, hentryVersion]
    rfl
  have hlayoutOffsetLtNat : offset + 8 < total := by
    have hnextBound := successfulTagDecodeTraversal_offset_lt_total
      bytes total (offset + aligned8 (high32Nat tagWord)) fuel true
      (.memoryMap (high32Nat tagWord) (low32Nat layoutWord)
        (high32Nat layoutWord) entries :: tagsRev) tags hrest
    simp only [memoryMapTagHeaderSize] at hsize
    unfold aligned8 at hnextBound
    omega
  have hlayoutOffsetLt :
      UInt64.ofNat (offset + 8) < UInt64.ofNat total := by
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat_of_lt' htotalLt,
      UInt64.toNat_ofNat_of_lt'
        (Nat.lt_trans hlayoutOffsetLtNat htotalLt)]
    exact hlayoutOffsetLtNat
  have hlayoutNotFinal :
      UInt64.ofNat (offset + 8) + 8 ≠ UInt64.ofNat total := by
    intro heq
    have hnextBound := successfulTagDecodeTraversal_offset_lt_total
      bytes total (offset + aligned8 (high32Nat tagWord)) fuel true
      (.memoryMap (high32Nat tagWord) (low32Nat layoutWord)
        (high32Nat layoutWord) entries :: tagsRev) tags hrest
    have h16Lt : offset + 16 < total := by
      simp only [memoryMapTagHeaderSize, aligned8] at hsize hnextBound
      omega
    have hoffset16 :
        UInt64.ofNat (offset + 8) + 8 =
          UInt64.ofNat (offset + 16) := by
      change UInt64.ofNat (offset + 8) + UInt64.ofNat 8 =
        UInt64.ofNat (offset + 16)
      rw [← UInt64.ofNat_add]
    have heqNat := congrArg UInt64.toNat heq
    rw [hoffset16,
      UInt64.toNat_ofNat_of_lt' (Nat.lt_trans h16Lt htotalLt),
      UInt64.toNat_ofNat_of_lt' htotalLt] at heqNat
    omega
  have hoffset16Word :
      UInt64.ofNat (offset + 8) + 8 =
        UInt64.ofNat (offset + memoryMapTagHeaderSize) := by
    change UInt64.ofNat (offset + 8) + UInt64.ofNat 8 =
      UInt64.ofNat (offset + 16)
    rw [← UInt64.ofNat_add]
  have hentryBytesNat :
      high32Nat tagWord - memoryMapTagHeaderSize =
        ((high32Nat tagWord - memoryMapTagHeaderSize) /
          memoryMapEntrySize) * memoryMapEntrySize := by
    have hdiv := Nat.mod_add_div
      (high32Nat tagWord - memoryMapTagHeaderSize) memoryMapEntrySize
    rw [halignedEntries, Nat.zero_add] at hdiv
    unfold memoryMapEntrySize at hdiv ⊢
    omega
  have hcontentWord :
      UInt64.ofNat (high32Nat tagWord) - 16 =
        UInt64.ofNat
          (((high32Nat tagWord - memoryMapTagHeaderSize) /
            memoryMapEntrySize) * memoryMapEntrySize) := by
    rw [← hentryBytesNat]
    rw [show (16 : UInt64) = UInt64.ofNat memoryMapTagHeaderSize by decide]
    rw [← UInt64.ofNat_sub hsize]
  have hentryBytesLt :
      ((high32Nat tagWord - memoryMapTagHeaderSize) /
          memoryMapEntrySize) * memoryMapEntrySize < UInt64.size := by
    rw [← hentryBytesNat]
    omega
  let afterLayout := scalarStep afterHeader layout
  have hlayoutStep :=
    BootMemoryMapStreamAuthority.memoryMapLayoutStepWords_of_admitted
      identity (UInt64.ofNat total) (UInt64.ofNat (offset + 8))
      afterHeader.word[6]! afterHeader.word[8]! afterHeader.word[11]!
      afterHeader.word[12]! afterHeader.word[13]! afterHeader.word[14]!
      afterHeader.word[15]! (UInt64.ofNat target) afterHeader.word[17]!
      afterHeader.word[18]! (UInt64.ofNat layoutWord)
      hidentityAligned hextentLow hextentHigh hextentAligned hlayoutOffsetLt
      hlayoutNotFinal
      (by rw [haUsable]; exact husable)
      (by rw [haBlocked]; exact hblocked)
      htargetBound
      (by
        rw [haTagCount]
        exact htagCountSucc)
      hlayoutLow hlayoutHigh
      (by
        rw [haContent, hcontentWord]
        apply UInt64.toNat.inj
        rw [UInt64.toNat_mod,
          UInt64.toNat_ofNat_of_lt' hentryBytesLt]
        simp [memoryMapEntrySize] at halignedEntries ⊢)
      (by
        rw [haContent, hcontentWord, UInt64.le_iff_toNat_le]
        rw [UInt64.toNat_div,
          UInt64.toNat_ofNat_of_lt' hentryBytesLt]
        simpa [memoryMapEntrySize,
          BootMemoryMapStreamAuthority.entryLimit, maxEntries]
          using hentryBound)
  rcases hlayoutStep with ⟨hlVersion, hlStatus, hlError, hlIdentity,
    hlExtent, hlOffset, hlPhase, hlContent, hlPadded, hlSaw, hlEntries,
    _hlBase, _hlLength, hlUsable, hlBlocked, hlTarget, _hlHighest,
    hlTagCount⟩
  rw [hoffset16Word] at hlOffset
  have hafterLayoutWord (query : Fin 19) :
      afterLayout.word[query.val]! =
        BootMemoryMapStreamAuthority.stepWord
          BootMemoryMapStreamAuthority.abiVersion
          BootMemoryMapStreamAuthority.active
          BootMemoryMapStreamAuthority.noError
          identity (UInt64.ofNat total) (UInt64.ofNat (offset + 8))
          afterHeader.word[6]!
          BootMemoryMapStreamAuthority.phaseMapLayout
          afterHeader.word[8]! 0 1 afterHeader.word[11]!
          afterHeader.word[12]! afterHeader.word[13]!
          afterHeader.word[14]! afterHeader.word[15]!
          (UInt64.ofNat target) afterHeader.word[17]!
          afterHeader.word[18]! identity (UInt64.ofNat (offset + 8))
          (UInt64.ofNat layoutWord) 0 (UInt64.ofNat query.val) := by
    apply scalarStep_word_of_stream_fields
    · exact haVersion
    · exact haStatus
    · exact haError
    · exact haIdentity
    · exact haExtent
    · exact haOffset
    · exact haPhase
    · exact haPadded
    · exact haSaw
    · exact haTarget
    · rfl
    · rfl
    · exact hlayoutWord
    · rfl
  have hafterLayoutTagCount :
      afterLayout.word[18]! = state.word[18]! + 1 := by
    exact ((hafterLayoutWord ⟨18, by decide⟩).trans hlTagCount).trans
      haTagCount
  have hafterLayout :
      CanonicalMemoryMapEntryState identity total
        (offset + memoryMapTagHeaderSize) target
        ((high32Nat tagWord - memoryMapTagHeaderSize) / memoryMapEntrySize)
        afterLayout := by
    let remaining :=
      (high32Nat tagWord - memoryMapTagHeaderSize) / memoryMapEntrySize
    have hcountBudget :
        afterHeader.word[11]!.toNat +
            remaining ≤ maxEntries := by
      rw [haEntries]
      unfold remaining
      simpa using hentryBound
    have hremainingBound : remaining ≤ maxEntries := by
      simpa [remaining] using hentryBound
    have hremainingBytesLt :
        remaining * memoryMapEntrySize < UInt64.size := by
      calc
        remaining * memoryMapEntrySize ≤ maxEntries * memoryMapEntrySize :=
          Nat.mul_le_mul_right memoryMapEntrySize hremainingBound
        _ < UInt64.size := by decide
    have hphaseBridge :
        (if afterHeader.word[8]! = 0
          then BootMemoryMapStreamAuthority.phaseTag
          else BootMemoryMapStreamAuthority.phaseEntryBase) =
        (if remaining = 0
          then BootMemoryMapStreamAuthority.phaseTag
          else BootMemoryMapStreamAuthority.phaseEntryBase) := by
      by_cases hzero : remaining = 0
      · have hcontentZero : afterHeader.word[8]! = 0 := by
          rw [haContent, hcontentWord]
          simp [remaining, hzero]
        simp [hzero, hcontentZero]
      · have hcontentNe : afterHeader.word[8]! ≠ 0 := by
          rw [haContent, hcontentWord]
          intro heq
          apply hzero
          have := congrArg UInt64.toNat heq
          rw [UInt64.toNat_ofNat_of_lt' hremainingBytesLt] at this
          have hmul : remaining * 24 = 0 := by
            simpa only [memoryMapEntrySize, UInt64.toNat_zero] using this
          rcases Nat.mul_eq_zero.mp hmul with hremaining | himpossible
          · exact hremaining
          · exact False.elim ((by decide : (24 : Nat) ≠ 0) himpossible)
        simp [hzero, hcontentNe]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      htarget, ?_⟩
    · exact (hafterLayoutWord ⟨0, by decide⟩).trans hlVersion
    · exact (hafterLayoutWord ⟨1, by decide⟩).trans hlStatus
    · exact (hafterLayoutWord ⟨2, by decide⟩).trans hlError
    · exact (hafterLayoutWord ⟨3, by decide⟩).trans hlIdentity
    · exact (hafterLayoutWord ⟨4, by decide⟩).trans hlExtent
    · simpa [memoryMapTagHeaderSize] using
        (hafterLayoutWord ⟨5, by decide⟩).trans hlOffset
    · have hphaseRaw :
          afterLayout.word[7]! =
            if afterHeader.word[8]! = 0
            then BootMemoryMapStreamAuthority.phaseTag
            else BootMemoryMapStreamAuthority.phaseEntryBase := by
        exact (hafterLayoutWord ⟨7, by decide⟩).trans hlPhase
      rw [hphaseRaw, hphaseBridge]
    · rw [(hafterLayoutWord ⟨8, by decide⟩).trans hlContent, haContent,
        hcontentWord]
    · exact (hafterLayoutWord ⟨9, by decide⟩).trans hlPadded
    · exact (hafterLayoutWord ⟨10, by decide⟩).trans hlSaw
    · rw [(hafterLayoutWord ⟨11, by decide⟩).trans hlEntries]
      exact hcountBudget
    · rw [(hafterLayoutWord ⟨14, by decide⟩).trans hlUsable, haUsable]
      exact husable
    · rw [(hafterLayoutWord ⟨15, by decide⟩).trans hlBlocked, haBlocked]
      exact hblocked
    · exact (hafterLayoutWord ⟨16, by decide⟩).trans hlTarget
    · rw [hafterLayoutTagCount]
      rw [UInt64.le_iff_toNat_le, UInt64.toNat_add]
      simp only [UInt64.toNat_ofNat]
      have hcountNat : state.word[18]!.toNat < 64 := by
        rw [UInt64.lt_iff_toNat_lt] at htagCount
        simpa using htagCount
      have hsumLt : state.word[18]!.toNat + 1 < UInt64.size :=
        Nat.lt_trans (by omega : state.word[18]!.toNat + 1 < 65) (by decide)
      rw [Nat.mod_eq_of_lt hsumLt]
      omega
  have hentryOffsetAligned :
      (offset + memoryMapTagHeaderSize) % 8 = 0 := by
    simp [memoryMapTagHeaderSize, Nat.add_mod, hoffsetAligned]
  have hroom :
      offset + memoryMapTagHeaderSize +
          ((high32Nat tagWord - memoryMapTagHeaderSize) / memoryMapEntrySize) *
            memoryMapEntrySize + 8 ≤ total := by
    rw [← hentryBytesNat]
    have hnextBound := successfulTagDecodeTraversal_offset_lt_total
      bytes total (offset + aligned8 (high32Nat tagWord)) fuel true
      (.memoryMap (high32Nat tagWord) (low32Nat layoutWord)
        (high32Nat layoutWord) entries :: tagsRev) tags hrest
    unfold aligned8 at hnextBound
    omega
  have hcontinuation :
      ∀ after,
        CanonicalMemoryMapEntryState identity total
            (offset + memoryMapTagHeaderSize +
              ((high32Nat tagWord - memoryMapTagHeaderSize) /
                memoryMapEntrySize) * memoryMapEntrySize)
            target 0 after →
          after.word[18]! = afterLayout.word[18]! →
          ∃ terminal,
            SuccessfulScalarRichTraversal target [] after
              ((canonicalChunks identity bytes).drop
                ((offset + memoryMapTagHeaderSize +
                  ((high32Nat tagWord - memoryMapTagHeaderSize) /
                    memoryMapEntrySize) * memoryMapEntrySize) / 8))
              terminal := by
    intro after hafter htagEq
    have hendOffset :
        offset + memoryMapTagHeaderSize +
            ((high32Nat tagWord - memoryMapTagHeaderSize) /
              memoryMapEntrySize) * memoryMapEntrySize =
          offset + aligned8 (high32Nat tagWord) := by
      have hhighDecomp :
          high32Nat tagWord =
            memoryMapTagHeaderSize +
              ((high32Nat tagWord - memoryMapTagHeaderSize) /
                memoryMapEntrySize) * memoryMapEntrySize := by
        omega
      rw [hhighDecomp]
      unfold memoryMapTagHeaderSize memoryMapEntrySize aligned8
      have hmultiple :
          16 + (high32Nat tagWord - 16) / 24 * 24 =
            (2 + 3 * ((high32Nat tagWord - 16) / 24)) * 8 := by
        omega
      rw [hmultiple]
      omega
    have hafterTagBudget :
        after.word[18]!.toNat + fuel ≤ maxTags := by
      rw [htagEq, hafterLayoutTagCount]
      rw [UInt64.toNat_add]
      simp only [UInt64.toNat_ofNat]
      have hcountNat : state.word[18]!.toNat < 64 := by
        rw [UInt64.lt_iff_toNat_lt] at htagCount
        simpa using htagCount
      have hsumLt : state.word[18]!.toNat + 1 < UInt64.size :=
        Nat.lt_trans (by omega : state.word[18]!.toNat + 1 < 65) (by decide)
      rw [Nat.mod_eq_of_lt hsumLt]
      have hbudget := htagBudget
      simp only [maxTags] at hbudget ⊢
      omega
    have htagState :
        CanonicalTagState identity total
          (offset + aligned8 (high32Nat tagWord)) target fuel true after := by
      exact canonicalTagState_of_completedMemoryMapEntries
        identity total
        (offset + memoryMapTagHeaderSize +
          ((high32Nat tagWord - memoryMapTagHeaderSize) /
            memoryMapEntrySize) * memoryMapEntrySize)
        (offset + aligned8 (high32Nat tagWord)) target fuel after
        hendOffset hafter hafterTagBudget
    simpa [hendOffset] using
      successfulScalarRichTraversal_afterMemoryMap identity bytes total
        (offset + aligned8 (high32Nat tagWord)) fuel target true
        (.memoryMap (high32Nat tagWord) (low32Nat layoutWord)
          (high32Nat layoutWord) entries :: tagsRev)
        tags after htotal hadmitted
        (by simp [Nat.add_mod, hoffsetAligned, aligned8])
        hrest htagState rfl
  obtain ⟨terminal, hentriesTraversal⟩ :=
    successfulScalarRichTraversal_canonicalMemoryMapEntries_exists
      identity bytes total
      (offset + memoryMapTagHeaderSize) target
      ((high32Nat tagWord - memoryMapTagHeaderSize) / memoryMapEntrySize)
      entries afterLayout
      htotal htotalLow htotalHigh htotalAligned hentryOffsetAligned hroom
      hidentityAligned hentries hafterLayout
      hcontinuation
  have hentryDrop :
      (offset + memoryMapTagHeaderSize) / 8 = offset / 8 + 2 := by
    have hdiv := Nat.mod_add_div offset 8
    rw [hoffsetAligned, Nat.zero_add] at hdiv
    unfold memoryMapTagHeaderSize
    omega
  have hentriesTraversal' :
      SuccessfulScalarRichTraversal target entries
        (scalarStep afterHeader layout)
        ((canonicalChunks identity bytes).drop (offset / 8 + 2))
        terminal := by
    simpa [afterLayout, hentryDrop] using hentriesTraversal
  have hlayoutTraversal :=
    successfulScalarRichTraversal_canonicalMemoryMapLayout identity bytes total
      offset fuel tagWord layoutWord target tagsRev tags entries afterHeader
      terminal htotal htotalAligned
      hoffsetAligned hsize hrest hlayout hidentityAligned hextentLow
      hextentHigh hextentAligned hlayoutOffsetLt hlayoutNotFinal
      haVersion haStatus haError haIdentity haExtent haOffset haPhase
      (by
        rw [haContent, hcontentWord]
        apply UInt64.toNat.inj
        rw [UInt64.toNat_mod,
          UInt64.toNat_ofNat_of_lt' hentryBytesLt]
        simp [memoryMapEntrySize] at halignedEntries ⊢)
      haPadded haSaw
      (by rw [haUsable]; exact husable)
      (by rw [haBlocked]; exact hblocked)
      haTarget htarget
      (by
        rw [haTagCount]
        exact htagCountSucc)
      hlayoutLow hlayoutHigh
      (by
        rw [haContent, hcontentWord,
          UInt64.le_iff_toNat_le]
        rw [UInt64.toNat_div,
          UInt64.toNat_ofNat_of_lt' hentryBytesLt]
        simpa [memoryMapEntrySize,
          BootMemoryMapStreamAuthority.entryLimit, maxEntries]
          using hentryBound)
      hentriesTraversal'
  have hoffsetWords : offset / 8 * 8 = offset := by
    have := Nat.mod_add_div offset 8
    rw [hoffsetAligned, Nat.zero_add] at this
    omega
  obtain ⟨_, _, hheaderGet, _⟩ :=
    canonicalTagStep_source_refines identity bytes total offset (fuel + 1)
      false tagsRev tags state htotal
      (by simpa [← htotal] using htotalAligned) hoffsetAligned
      (.memoryMapTag offset fuel tagWord layoutWord tagsRev tags entries
        hread hsize hcontent hadvance htype hlayout hentrySize hentryVersion
        halignedEntries hentryBound hentries hrest)
  have hdrop :=
    drop_eq_cons_drop_succ_of_get?_eq_some
      (canonicalChunks identity bytes) (offset / 8) header
      (by
        have hterminalFalse : (offset + 8 == total) = false := by
          apply beq_false_of_ne
          intro heq
          apply hoffsetNotFinal
          simpa [UInt64.ofNat_add] using
            congrArg UInt64.ofNat heq
        simpa [header, hoffsetWords, hterminalFalse] using hheaderGet)
  refine ⟨terminal, ?_⟩
  rw [hdrop]
  apply successfulScalarRichTraversal_memoryMapTagHeader
    identity (UInt64.ofNat total) (UInt64.ofNat offset)
      (UInt64.ofNat tagWord) target entries state
      terminal header
      ((canonicalChunks identity bytes).drop (offset / 8 + 1))
    rfl rfl rfl hheaderWord hversion hstatus herror hidentity
    hidentityAligned hextent hextentLow hextentHigh hextentAligned
    hoffset hoffsetLt hoffsetNotFinal hphase (by simpa using hsawMap)
    husable hblocked htargetWord htarget htagCount
    (by simp [hlow, htype])
    (by
      rw [hhigh, UInt64.le_iff_toNat_le]
      simpa [UInt64.toNat_ofNat_of_lt' hhighBound,
        memoryMapTagHeaderSize] using hsize)
    (by simpa [hhigh] using hsizeFits)
    (by simpa [hhigh] using hsizeNoOverflow)
    (by simpa [hhigh] using hroundedFits)
    (by
      rw [hhigh, hcontentWord]
      apply UInt64.toNat.inj
      rw [UInt64.toNat_mod,
        UInt64.toNat_ofNat_of_lt' hentryBytesLt]
      simp [memoryMapTagHeaderSize, memoryMapEntrySize] at halignedEntries ⊢)
    (by
      rw [hhigh, hcontentWord, UInt64.le_iff_toNat_le]
      rw [UInt64.toNat_div,
        UInt64.toNat_ofNat_of_lt' hentryBytesLt]
      simpa [
        memoryMapTagHeaderSize, memoryMapEntrySize,
        BootMemoryMapStreamAuthority.entryLimit, maxEntries]
        using hentryBound)
    (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      hlayoutTraversal)

set_option maxHeartbeats 800000 in
/-- Whole retained tag induction before the unique map.  Ignored spans are
composed on the way down, the map case consumes its exact entries and the
post-map suffix, and the extracted typed entry list is retained in the
result. -/
theorem successfulScalarRichTraversal_beforeMemoryMap
    (identity : UInt64) (bytes : List UInt8)
    (total offset fuel target : Nat) (sawMemoryMap : Bool)
    (tagsRev tags : List Tag) (state : ScalarState)
    (beforeSizes : List Nat)
    (htotal : total = bytes.length)
    (htotalWord : total < UInt64.size)
    (hoffsetAligned : offset % 8 = 0)
    (hinitialActive :
      (scalarInitialAt identity total target).word[1]! =
        BootMemoryMapStreamAuthority.active)
    (hprefix : tagsRev.reverse = beforeSizes.map Tag.ignored)
    (htraversal :
      SuccessfulTagDecodeTraversal bytes total offset fuel sawMemoryMap
        tagsRev tags)
    (hstate :
      CanonicalTagState identity total offset target fuel sawMemoryMap state)
    (hsaw : sawMemoryMap = false) :
    ∃ entries terminal,
      SuccessfulScalarRichTraversal target entries state
          ((canonicalChunks identity bytes).drop (offset / 8)) terminal ∧
        extractMemoryMap tags = .ok entries := by
  have hadmitted :=
    scalarInitialAt_active_implies_admitted
      identity total target htotalWord hinitialActive
  induction htraversal generalizing state beforeSizes with
  | endTag =>
      simp at hsaw
  | ignoredTag offset fuel tagWord sawMemoryMap tagsRev tags hread hsize
      hcontent hadvance htypeEnd htypeMap hrest ih =>
      subst sawMemoryMap
      have hnextAligned :
          (offset + aligned8 (high32Nat tagWord)) % 8 = 0 := by
        simp [Nat.add_mod, hoffsetAligned, aligned8]
      obtain ⟨after, hafter, hwrap⟩ :=
        canonicalIgnoredTag_successor identity bytes total offset fuel tagWord
          target false tagsRev tags state htotal hadmitted
          hoffsetAligned hread hsize hcontent
          hadvance htypeEnd htypeMap hrest hstate
      obtain ⟨entries, terminal, htail, hextract⟩ :=
        ih after (beforeSizes ++ [high32Nat tagWord]) hnextAligned
          (by simp [hprefix]) hafter rfl
      exact ⟨entries, terminal, hwrap entries terminal htail, hextract⟩
  | memoryMapTag offset fuel tagWord layoutWord tagsRev tags entries hread
      hsize hcontent hadvance htype hlayout hentrySize hentryVersion
      halignedEntries hentryBound hentries hrest =>
      obtain ⟨terminal, hwhole⟩ :=
        successfulScalarRichTraversal_memoryMapTag_complete identity bytes
          total offset fuel tagWord layoutWord target tagsRev tags entries
          state htotal hadmitted hoffsetAligned
          hread hsize hcontent hadvance htype hlayout
          hentrySize hentryVersion halignedEntries hentryBound hentries hrest
          hstate
      obtain ⟨afterSizes, hshape⟩ :=
        successfulTagDecodeTraversal_afterMap_shape bytes total
          (offset + aligned8 (high32Nat tagWord)) fuel true
          (.memoryMap (high32Nat tagWord) (low32Nat layoutWord)
            (high32Nat layoutWord) entries :: tagsRev)
          tags rfl hrest
      have hlength :=
        successfulEntryDecodeTraversal_length bytes
          (offset + memoryMapTagHeaderSize)
          ((high32Nat tagWord - memoryMapTagHeaderSize) /
            memoryMapEntrySize)
          entries hentries
      have htagSize :
          high32Nat tagWord =
            memoryMapTagHeaderSize + memoryMapEntrySize * entries.length := by
        have hdiv :=
          Nat.mod_add_div
            (high32Nat tagWord - memoryMapTagHeaderSize)
            memoryMapEntrySize
        rw [halignedEntries, Nat.zero_add, ← hlength] at hdiv
        omega
      refine ⟨entries, terminal, hwhole, ?_⟩
      rw [hshape]
      simp only [List.reverse_cons, List.append_assoc]
      rw [hprefix, hentrySize, hentryVersion]
      simpa only [List.append_assoc] using
        extractMemoryMap_ignored_around beforeSizes afterSizes
          (high32Nat tagWord) entries htagSize (by
            rw [hlength]
            exact hentryBound)

set_option maxHeartbeats 800000 in
/-- A successful decode establishes the canonical tag-boundary scalar state
after its independently certified information-header step.  Keeping this
initializer normalization out of tag induction prevents the generated
nineteen-query transition from being normalized again during final
composition. -/
theorem canonicalTagState_afterInfo_of_decode
    (input : Input) (decoded : Decoded) (target : Nat)
    (hdecode : decode input = .ok decoded)
    (htarget : target < frameLimit) :
    CanonicalTagState (UInt64.ofNat input.infoAddress) input.bytes.length
      8 target maxTags false
      (scalarStep
        (scalarInitialAt (UInt64.ofNat input.infoAddress)
          input.bytes.length target)
        { identity := UInt64.ofNat input.infoAddress
          offset := 0
          bytes := input.bytes.take 8
          terminal := false }) := by
  have hrich := successful_decode_constructs_traversal input decoded hdecode
  have hheader := accepted_input_scalar_header input decoded hdecode
  have hidentityAligned :
      UInt64.ofNat input.infoAddress % 8 = 0 := by
    have haddressLt : input.infoAddress < UInt64.size := by
      simpa [wordLimit] using hheader.2.1
    apply UInt64.toNat.inj
    simp [UInt64.toNat_ofNat_of_lt' haddressLt,
      hheader.2.2.2.2.1]
  obtain ⟨first, _rest, _hchunks, _hfirst, hnext⟩ :=
    canonicalInfoStep_of_richTraversal input decoded target hdecode hrich htarget
  let initial :=
    scalarInitialAt (UInt64.ofNat input.infoAddress)
      input.bytes.length target
  let afterInfo := scalarStep initial first
  rcases hnext with ⟨hiVersion, hiStatus, hiError, hiIdentity, hiExtent,
    hiOffset, hiPhase, hiContent, hiPadded, hiSaw, hiEntries, _hiBase,
    _hiLength, hiUsable, hiBlocked, hiTarget, _hiHighest, hiTagCount⟩
  subst first
  change CanonicalTagState (UInt64.ofNat input.infoAddress)
    input.bytes.length 8 target maxTags false afterInfo
  refine ⟨hiVersion, hiStatus, hiError, hiIdentity, hiExtent, hiOffset,
    hiPhase, hiContent, hiPadded, hiSaw, ?_, ?_, ?_, ?_, hiTarget, htarget,
    ?_⟩
  · rw [hiEntries]
    simp [maxEntries]
  · intro _
    exact hiEntries
  · rw [hiUsable]
    decide
  · rw [hiBlocked]
    decide
  · rw [hiTagCount]
    simp [maxTags]

set_option maxHeartbeats 800000 in
/-- The independently checked post-information-header composition for a
successful rich decode.  This packages tag induction, typed-map extraction,
and the exact canonical tail before the inexpensive information-header
prepend is elaborated. -/
theorem successfulScalarRichTraversal_decode_tail
    (input : Input) (decoded : Decoded) (target : Nat)
    (hdecode : decode input = .ok decoded)
    (htarget : target < frameLimit) :
    ∃ terminal,
      SuccessfulScalarRichTraversal target decoded.entries
        (scalarStep
          (scalarInitialAt (UInt64.ofNat input.infoAddress)
            input.bytes.length target)
          { identity := UInt64.ofNat input.infoAddress
            offset := 0
            bytes := input.bytes.take 8
            terminal := false })
        (canonicalChunks (UInt64.ofNat input.infoAddress) input.bytes).tail
        terminal := by
  have hrich := successful_decode_constructs_traversal input decoded hdecode
  obtain ⟨infoWord, tags, hinfo, htotal, hreserved, htags, htagTraversal,
    hhandoff, hvalid, hentries, hbounds⟩ := hrich.traversed
  have hheader := accepted_input_scalar_header input decoded hdecode
  have htotalEq : low32Nat infoWord = input.bytes.length := htotal
  let initial :=
    scalarInitialAt (UInt64.ofNat input.infoAddress)
      input.bytes.length target
  let first : ModelChunk :=
    { identity := UInt64.ofNat input.infoAddress
      offset := 0
      bytes := input.bytes.take 8
      terminal := false }
  let afterInfo := scalarStep initial first
  have htagStateInput :=
    canonicalTagState_afterInfo_of_decode input decoded target hdecode htarget
  have htagState :
      CanonicalTagState (UInt64.ofNat input.infoAddress)
        (low32Nat infoWord) 8 target maxTags false afterInfo := by
    simpa [htotalEq, afterInfo, initial, first] using htagStateInput
  obtain ⟨sourceEntries, terminal, htagWhole, hextract⟩ :=
    successfulScalarRichTraversal_beforeMemoryMap
      (UInt64.ofNat input.infoAddress) input.bytes (low32Nat infoWord) 8
      maxTags target false [] tags afterInfo [] htotalEq
      (by simpa [htotalEq, wordLimit] using hheader.2.2.1)
      (by decide)
      (by
        have hinitial :=
          scalarInitialAt_of_decode input decoded target hdecode htarget
        simpa [htotalEq, initial] using hinitial.1)
      rfl
      htagTraversal htagState rfl
  have hvalidExtract :
      extractMemoryMap tags = .ok decoded.entries := by
    have :=
      validateHandoff_extractMemoryMap decoded.handoff decoded.entries hvalid
    rw [hhandoff] at this
    exact this
  have hsourceEntries : sourceEntries = decoded.entries := by
    rw [hextract] at hvalidExtract
    exact Except.ok.inj hvalidExtract
  subst sourceEntries
  refine ⟨terminal, ?_⟩
  have htail :
      (canonicalChunks (UInt64.ofNat input.infoAddress) input.bytes).tail =
        (canonicalChunks (UInt64.ofNat input.infoAddress) input.bytes).drop 1 := by
    simp
  rw [htail]
  simpa [afterInfo, initial] using htagWhole

set_option maxHeartbeats 800000 in
/-- Universal whole-buffer structural refinement.  Every successful rich
decode induces a scalar/rich traversal over the immutable buffer's complete
canonical chunk list, with exactly the entries returned by rich handoff
validation. -/
theorem successfulScalarRichTraversal_of_decode
    (input : Input) (decoded : Decoded) (target : Nat)
    (hdecode : decode input = .ok decoded)
    (htarget : target < frameLimit) :
    ∃ terminal,
      SuccessfulScalarRichTraversal target decoded.entries
        (scalarInitialAt (UInt64.ofNat input.infoAddress)
          input.bytes.length target)
        (canonicalChunks (UInt64.ofNat input.infoAddress) input.bytes)
        terminal := by
  obtain ⟨terminal, htail⟩ :=
    successfulScalarRichTraversal_decode_tail
      input decoded target hdecode htarget
  refine ⟨terminal, ?_⟩
  exact successfulScalarRichTraversal_prepend_info
    input decoded target terminal hdecode
      (successful_decode_constructs_traversal input decoded hdecode)
      htarget htail

/-- Terminal scalar authority reconstructed from one successful immutable-byte
decode.  The witness retains the initializer-derived stream admission, the
exact decoded entry list used by the traversal, and the complete terminal
classification words.  In particular, callers cannot replace the decoded
entries or seed either classification accumulator independently. -/
def DecodedScalarTerminalAuthority
    (input : Input) (decoded : Decoded) (target : Nat)
    (terminal : ScalarState) : Prop :=
    AdmittedScalarStream (UInt64.ofNat input.infoAddress)
        input.bytes.length target ∧
      SuccessfulScalarRichTraversal target decoded.entries
        (scalarInitialAt (UInt64.ofNat input.infoAddress)
          input.bytes.length target)
        (canonicalChunks (UInt64.ofNat input.infoAddress) input.bytes)
        terminal ∧
      scalarReplay
          (canonicalChunks (UInt64.ofNat input.infoAddress) input.bytes)
          (scalarInitialAt (UInt64.ofNat input.infoAddress)
            input.bytes.length target) = terminal ∧
      terminal.word[1]! = BootMemoryMapStreamAuthority.complete ∧
      terminal.word[2]! = BootMemoryMapStreamAuthority.noError ∧
      terminal.word[14]! =
        decoded.entries.foldl (updateUsableClassification target)
          (scalarInitialAt (UInt64.ofNat input.infoAddress)
            input.bytes.length target).word[14]! ∧
      terminal.word[15]! =
        decoded.entries.foldl (updateBlockedClassification target)
          (scalarInitialAt (UInt64.ofNat input.infoAddress)
            input.bytes.length target).word[15]!

set_option maxHeartbeats 800000 in
/-- A successful rich decode produces one terminal scalar authority package
from the same bytes and decoded entries. -/
theorem decodedScalarTerminalAuthority_of_decode
    (input : Input) (decoded : Decoded) (target : Nat)
    (hdecode : decode input = .ok decoded)
    (htarget : target < frameLimit) :
    ∃ terminal, DecodedScalarTerminalAuthority input decoded target terminal := by
  have hinitial := scalarInitialAt_of_decode input decoded target hdecode htarget
  have hheader := accepted_input_scalar_header input decoded hdecode
  have hextentWord : input.bytes.length < UInt64.size := by
    simpa [wordLimit, UInt64.size] using hheader.2.2.1
  have hadmitted :
      AdmittedScalarStream (UInt64.ofNat input.infoAddress)
        input.bytes.length target := by
    apply scalarInitialAt_active_implies_admitted
      (UInt64.ofNat input.infoAddress) input.bytes.length target hextentWord
    exact hinitial.1
  obtain ⟨terminal, htraversal⟩ :=
    successfulScalarRichTraversal_of_decode input decoded target hdecode htarget
  have hterminal :=
    successfulScalarRichTraversal_terminal_words
      target decoded.entries
      (scalarInitialAt (UInt64.ofNat input.infoAddress)
        input.bytes.length target)
      terminal
      (canonicalChunks (UInt64.ofNat input.infoAddress) input.bytes)
      htraversal
  refine ⟨terminal, ?_⟩
  exact ⟨hadmitted, htraversal, hterminal.1, hterminal.2.1,
    hterminal.2.2.1, hterminal.2.2.2.1, hterminal.2.2.2.2⟩

/-- One accepted authority binds the terminal scalar replay to the exact rich
decode, typed handoff validation, canonical reservation initializer, and
allocator selection chain.  The classification folds and selected frame are
therefore carried by one witness rather than supplied as independent scalar
claims. -/
def ScalarAllocatorAuthority
    (authority : Authority) (terminal : ScalarState) : Prop :=
  DecodedScalarTerminalAuthority authority.input authority.decoded
      authority.allocation.frame terminal ∧
    decode authority.input = .ok authority.decoded ∧
    validateHandoff authority.decoded.handoff = .ok authority.decoded.entries ∧
    BootReservation.initializeAllocator authority.decoded.handoff
        authority.manifest = .ok authority.reserved ∧
    FrameAllocator.allocate authority.reserved.allocator authority.owner =
      .ok authority.allocation ∧
    usableFrameSound authority.decoded.entries authority.allocation.frame = true ∧
    authority.allocation.frame < frameLimit ∧
    BootReservation.reservedBy authority.reserved.intervals
        authority.allocation.frame = false

set_option maxHeartbeats 1200000 in
/-- Every accepted full authority produces the scalar/allocator authority
chain for its exact selected frame. -/
theorem scalarAllocatorAuthority_of_authority (authority : Authority) :
    ∃ terminal, ScalarAllocatorAuthority authority terminal := by
  obtain ⟨terminal, hterminal⟩ :=
    decodedScalarTerminalAuthority_of_decode authority.input authority.decoded
      authority.allocation.frame authority.decodedBy authority.selectedWithinBound
  refine ⟨terminal, hterminal, authority.decodedBy, ?_, authority.reservedBy,
    authority.allocatedBy, authority.selectedUsable,
    authority.selectedWithinBound, ?_⟩
  · exact accepted_handoff_valid authority.input authority.decoded authority.decodedBy
  · exact BootReservation.allocation_excludes_reservations
      authority.reserved authority.owner authority.allocation authority.allocatedBy

set_option maxHeartbeats 800000 in
/-- The frame selected by the canonical allocator is exactly the terminal
scalar candidate: it has decoded usable coverage and no decoded non-usable
overlap. -/
theorem scalarAllocatorAuthority_terminal_selection
    (authority : Authority) (terminal : ScalarState)
    (h : ScalarAllocatorAuthority authority terminal) :
    terminal.word[14]! = 1 ∧ terminal.word[15]! = 0 := by
  have hinitial :=
    scalarInitialAt_of_decode authority.input authority.decoded
      authority.allocation.frame authority.decodedBy authority.selectedWithinBound
  have husable := h.1.2.2.2.2.2.1
  have hblocked := h.1.2.2.2.2.2.2
  rw [hinitial.2.2.2.2.2.2.1,
    foldl_updateUsableClassification_zero] at husable
  rw [hinitial.2.2.2.2.2.2.2.1,
    foldl_updateBlockedClassification_zero] at hblocked
  have hsound := authority.selectedUsable
  simp only [usableFrameSound, Bool.and_eq_true] at hsound
  rw [if_pos hsound.1] at husable
  have hnoBlocked :
      authority.decoded.entries.any (fun entry =>
        entry.kind != MemoryKind.usable &&
          overlaps entry (authority.allocation.frame * pageBytes)
            (authority.allocation.frame * pageBytes + pageBytes)) = false := by
    simpa using hsound.2
  rw [if_neg (by simp [hnoBlocked])] at hblocked
  exact ⟨husable, hblocked⟩

/-- The exact rich decode/normalize/reserve/allocate chain determines the
allocation-free production result words for its selected frame.  The result
surface carries both the frame and the sole nonzero publication token; neither
is accepted as a caller-owned claim. -/
theorem scalarAllocatorAuthority_production_result
    (authority : Authority) (terminal : ScalarState)
    (h : ScalarAllocatorAuthority authority terminal) :
    let selected := UInt64.ofNat authority.allocation.frame
    BootMemoryMapStreamAuthority.authorityResultWord
          selected selected BootMemoryMapStreamAuthority.complete 1 0 1 1 0 = 1 ∧
      BootMemoryMapStreamAuthority.authorityResultWord
          selected selected BootMemoryMapStreamAuthority.complete 1 0 1 1 1 = 1 ∧
      BootMemoryMapStreamAuthority.authorityResultWord
          selected selected BootMemoryMapStreamAuthority.complete 1 0 1 1 2 = 0 ∧
      BootMemoryMapStreamAuthority.authorityResultWord
          selected selected BootMemoryMapStreamAuthority.complete 1 0 1 1 3 = selected ∧
      BootMemoryMapStreamAuthority.authorityResultWord
          selected selected BootMemoryMapStreamAuthority.complete 1 0 1 1 4 = selected + 1 := by
  have hselectedNat : authority.allocation.frame < 4096 := by
    have hbound := h.2.2.2.2.2.2.1
    have hframeLimit : frameLimit = 4096 := by native_decide
    rw [hframeLimit] at hbound
    exact hbound
  have hselectedWord : UInt64.ofNat authority.allocation.frame < 4096 := by
    rw [UInt64.lt_iff_toNat_lt]
    have hsize : authority.allocation.frame < UInt64.size := by
      exact Nat.lt_trans hselectedNat (by decide)
    simpa [UInt64.toNat_ofNat, Nat.mod_eq_of_lt hsize] using hselectedNat
  dsimp only
  exact BootMemoryMapStreamAuthority.authorityResultWord_accepted
    (UInt64.ofNat authority.allocation.frame) hselectedWord

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
