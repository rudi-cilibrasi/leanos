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

namespace Fixtures

open BootMemoryMapDecoder.Fixtures
open LeanOS.BootMemoryMapStreamAuthority

def identity : UInt64 := 0x1000

def allocationBytes : List UInt8 :=
  information
    (memoryMapTag [entry 0 (14 * pageBytes) 1] ++ endTag)

def chunkedAt (streamIdentity : UInt64) (bytes : List UInt8) : List ModelChunk :=
  (List.range ((bytes.length + 7) / 8)).map fun index =>
    let offset := index * 8
    let part := (bytes.drop offset).take 8
    { identity := streamIdentity
      offset
      bytes := part
      terminal := offset + part.length == bytes.length }

def chunked (bytes : List UInt8) : List ModelChunk :=
  chunkedAt identity bytes

def allocationChunks : List ModelChunk := chunked allocationBytes

structure ScalarState where
  word : Array UInt64

def scalarInitialAt (streamIdentity : UInt64) (extent target : Nat) : ScalarState :=
  { word := Array.ofFn fun query : Fin 19 =>
      BootMemoryMapStreamAuthority.initWord
        (UInt64.ofNat multiboot2Magic) streamIdentity (UInt64.ofNat extent)
        (UInt64.ofNat target) (UInt64.ofNat query.val) }

def scalarInitial (extent target : Nat) : ScalarState :=
  scalarInitialAt identity extent target

private def chunkWordAux : List UInt8 → UInt64 → UInt64 → UInt64
  | [], _, result => result
  | byte :: rest, factor, result =>
      chunkWordAux rest (factor * 256) (result + UInt64.ofNat byte.toNat * factor)

def chunkWord (bytes : List UInt8) : UInt64 :=
  chunkWordAux bytes 1 0

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

def scalarReplay : List ModelChunk → ScalarState → ScalarState
  | [], state => state
  | chunk :: rest, state =>
      let next := scalarStep state chunk
      if next.word[2]! != noError then next else scalarReplay rest next

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
