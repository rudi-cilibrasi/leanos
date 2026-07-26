import LeanOS.BootMemoryMapDecoder
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

def identity : UInt64 := 0x1000

def allocationBytes : List UInt8 :=
  information
    (memoryMapTag [entry 0 (14 * pageBytes) 1] ++ endTag)

def chunked (bytes : List UInt8) : List ModelChunk :=
  (List.range ((bytes.length + 7) / 8)).map fun index =>
    let offset := index * 8
    let part := (bytes.drop offset).take 8
    { identity
      offset
      bytes := part
      terminal := offset + part.length == bytes.length }

def allocationChunks : List ModelChunk := chunked allocationBytes

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
