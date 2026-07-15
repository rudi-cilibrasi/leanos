import LeanOS.FrameAllocator

/-!
# Bounded Multiboot2 memory-map normalization

This executable model starts after byte decoding.  It validates the fixed-width
fields used by a future adapter, then conservatively classifies a bounded set
of 4 KiB frames.  Firmware truthfulness and correspondence between bytes and
these typed values remain trusted assumptions.
-/
namespace LeanOS.BootMemoryMap

open LeanOS.FrameAllocator

def multiboot2Magic : Nat := 0x36d76289
def pageBytes : Nat := 4096
def wordLimit : Nat := 2 ^ 64
def physicalLimit : Nat := 2 ^ 24
def frameLimit : Nat := physicalLimit / pageBytes
def maxTagBytes : Nat := 65536
def maxTags : Nat := 64
def maxEntries : Nat := 256
def maxRegions : Nat := 512
def maxExpandedFrames : Nat := 4096
def memoryMapTagHeaderSize : Nat := 16
def memoryMapEntrySize : Nat := 24

inductive MemoryKind where
  | usable | reserved | acpiReclaimable | acpiNvs | badMemory
  deriving BEq, DecidableEq, Repr

structure RawEntry where
  base : Nat
  length : Nat
  kind : MemoryKind
  deriving BEq, DecidableEq, Repr

inductive Tag where
  | memoryMap (size entrySize entryVersion : Nat) (entries : List RawEntry)
  | ignored (size : Nat)
  | end (size : Nat)
  deriving BEq, DecidableEq, Repr

structure Handoff where
  magic : Nat
  infoAddress : Nat
  totalSize : Nat
  tags : List Tag
  deriving BEq, DecidableEq, Repr

inductive Error where
  | badMagic | unalignedInfo | malformedInfoSize | tooManyTags | tagBytesExceeded
  | malformedTagSize | missingEndTag | misplacedEndTag | missingMemoryMap
  | duplicateMemoryMap | badEntrySize | unsupportedEntryVersion | tooManyEntries
  | zeroLength | addressOverflow | expandedFramesExceeded
  | normalizedRegionsExceeded | normalizationInvariant | allocatorRejected
  deriving BEq, DecidableEq, Repr

def Tag.size : Tag → Nat
  | .memoryMap size _ _ _ | .ignored size | .end size => size

def aligned8 (n : Nat) : Nat := ((n + 7) / 8) * 8

def tagShapeValid : Tag → Bool
  | .memoryMap size entrySize _ entries =>
      size == memoryMapTagHeaderSize + entrySize * entries.length
  | .ignored size => 8 ≤ size
  | .end size => size == 8

def extractMemoryMap : List Tag → Except Error (List RawEntry)
  | [] => .error .missingEndTag
  | [.end size] => if size == 8 then .error .missingMemoryMap else .error .malformedTagSize
  | .end _ :: _ => .error .misplacedEndTag
  | .memoryMap size entrySize version entries :: rest =>
      if size != memoryMapTagHeaderSize + entrySize * entries.length then
        .error .malformedTagSize
      else if entrySize != memoryMapEntrySize then .error .badEntrySize
      else if version != 0 then .error .unsupportedEntryVersion
      else if entries.length > maxEntries then .error .tooManyEntries
      else match rest with
        | [.end endSize] => if endSize == 8 then .ok entries else .error .malformedTagSize
        | [] => .error .missingEndTag
        | _ =>
          if rest.any (fun tag => match tag with | .memoryMap .. => true | _ => false)
          then .error .duplicateMemoryMap
          else if rest.getLast? != some (.end 8) then .error .missingEndTag
          else if rest.dropLast.any (fun tag => match tag with | .end _ => true | _ => false)
          then .error .misplacedEndTag
          else .ok entries
  | _ :: rest => extractMemoryMap rest

def validateHandoff (handoff : Handoff) : Except Error (List RawEntry) := do
  if handoff.magic != multiboot2Magic then throw .badMagic
  if handoff.infoAddress ≥ wordLimit || handoff.totalSize ≥ wordLimit ||
      handoff.totalSize > wordLimit - handoff.infoAddress then throw .addressOverflow
  if handoff.infoAddress % 8 != 0 then throw .unalignedInfo
  if handoff.totalSize < 16 || handoff.totalSize % 8 != 0 then throw .malformedInfoSize
  if handoff.tags.length > maxTags then throw .tooManyTags
  if handoff.tags.any (fun tag => !tagShapeValid tag) then throw .malformedTagSize
  let bytes := 8 + (handoff.tags.map (aligned8 ∘ Tag.size)).foldl (· + ·) 0
  if bytes != handoff.totalSize then throw .malformedInfoSize
  if bytes > maxTagBytes then throw .tagBytesExceeded
  extractMemoryMap handoff.tags

def entryValid (entry : RawEntry) : Except Error Unit := do
  if entry.length == 0 then throw .zeroLength
  if entry.base ≥ wordLimit || entry.length ≥ wordLimit ||
      entry.length > wordLimit - entry.base then throw .addressOverflow

def overlaps (entry : RawEntry) (start stop : Nat) : Bool :=
  entry.base < stop && start < entry.base + entry.length

def covers (entry : RawEntry) (start stop : Nat) : Bool :=
  entry.base ≤ start && stop ≤ entry.base + entry.length

def classifyFrame (entries : List RawEntry) (frame : Nat) : Option RegionKind :=
  let start := frame * pageBytes
  let stop := start + pageBytes
  if entries.any (fun e => e.kind != .usable && overlaps e start stop) then some .reserved
  else if entries.any (fun e => e.kind == .usable && covers e start stop) then some .usable
  else if entries.any (fun e => overlaps e start stop) then some .reserved
  else none

def singletonRegions (entries : List RawEntry) : List Region :=
  (List.range frameLimit).filterMap fun frame =>
    (classifyFrame entries frame).map fun kind => { start := frame, count := 1, kind }

def appendRegion (regions : List Region) (next : Region) : List Region :=
  match regions.reverse with
  | [] => [next]
  | last :: revRest =>
      if last.kind == next.kind && last.start + last.count == next.start then
        (revRest.reverse ++ [{ last with count := last.count + next.count }])
      else regions ++ [next]

def mergeAdjacent (regions : List Region) : List Region :=
  regions.foldl appendRegion []

def regionShape (regions : List Region) : Bool :=
  regions.all fun r => r.count != 0 && r.start + r.count ≤ frameLimit

def pairwiseDisjoint (regions : List Region) : Bool :=
  (regions.zip regions.tail).all fun pair => pair.1.start + pair.1.count ≤ pair.2.start

def usableFrameSound (entries : List RawEntry) (frame : Nat) : Bool :=
  let start := frame * pageBytes
  let stop := start + pageBytes
  entries.any (fun e => e.kind == .usable && covers e start stop) &&
    !entries.any (fun e => e.kind != .usable && overlaps e start stop)

def usableSound (entries : List RawEntry) (regions : List Region) : Bool :=
  regions.all fun region =>
    region.kind != .usable || region.frames.all (usableFrameSound entries)

structure Normalized where
  entries : List RawEntry
  regions : List Region
  shape : regionShape regions = true
  disjoint : pairwiseDisjoint regions = true
  sound : usableSound entries regions = true
  allocatorAccepts : (FrameAllocator.init regions).isOk = true

def normalize (handoff : Handoff) : Except Error Normalized := do
  let entries ← validateHandoff handoff
  for entry in entries do entryValid entry
  let singletons := singletonRegions entries
  if singletons.length > maxExpandedFrames then throw .expandedFramesExceeded
  let regions := mergeAdjacent singletons
  if regions.length > maxRegions then throw .normalizedRegionsExceeded
  if hshape : regionShape regions then
    if hdisjoint : pairwiseDisjoint regions then
      if hsound : usableSound entries regions then
        match hinit : FrameAllocator.init regions with
        | .error _ => throw .allocatorRejected
        | .ok _ =>
          have haccepts : (FrameAllocator.init regions).isOk = true := by
            rw [hinit]
            rfl
          pure (Normalized.mk entries regions hshape hdisjoint hsound haccepts)
      else throw .normalizationInvariant
    else throw .normalizationInvariant
  else throw .normalizationInvariant

theorem normalize_functional handoff first second
    (hfirst : normalize handoff = first) (hsecond : normalize handoff = second) : first = second := by
  rw [hfirst] at hsecond
  exact hsecond

theorem accepted_shape (handoff : Handoff) (result : Normalized)
    (_h : normalize handoff = .ok result) : regionShape result.regions = true := by
  exact result.shape

theorem accepted_sorted_disjoint (handoff : Handoff) (result : Normalized)
    (_h : normalize handoff = .ok result) : pairwiseDisjoint result.regions = true := by
  exact result.disjoint

/-- Every frame emitted as usable is wholly covered by a usable input entry and
does not overlap any non-usable input entry. -/
theorem accepted_usable_sound (handoff : Handoff) (result : Normalized)
    (_h : normalize handoff = .ok result) : usableSound result.entries result.regions = true := by
  exact result.sound

theorem accepted_within_physical_limit (handoff : Handoff) (result : Normalized)
    (h : normalize handoff = .ok result) :
    result.regions.all (fun r => (r.start + r.count) * pageBytes ≤ physicalLimit) = true := by
  have hs := accepted_shape handoff result h
  simp only [regionShape, List.all_eq_true] at hs ⊢
  intro region hr
  have both := hs region hr
  have bounds : region.start + region.count ≤ frameLimit := by
    simp at both
    exact both.2
  apply decide_eq_true
  change region.start + region.count ≤ 4096 at bounds
  change (region.start + region.count) * 4096 ≤ 16777216
  calc
    (region.start + region.count) * 4096 ≤ 4096 * 4096 :=
      Nat.mul_le_mul_right 4096 bounds
    _ = 16777216 := by decide

theorem accepted_refines_allocator (handoff : Handoff) (result : Normalized)
    (_h : normalize handoff = .ok result) : (FrameAllocator.init result.regions).isOk = true := by
  exact result.allocatorAccepts

def mkHandoff (entries : List RawEntry) (entrySize := memoryMapEntrySize)
    (version := 0) : Handoff :=
  let mmapSize := memoryMapTagHeaderSize + entrySize * entries.length
  { magic := multiboot2Magic, infoAddress := 0x1000,
    totalSize := 8 + aligned8 mmapSize + 8,
    tags := [.memoryMap mmapSize entrySize version entries, .end 8] }

def normalizedRegions (handoff : Handoff) : Option (List Region) :=
  (normalize handoff).toOption.map (·.regions)

theorem rejected_has_no_regions (handoff : Handoff) (reason : Error)
    (h : normalize handoff = .error reason) : normalizedRegions handoff = none := by
  unfold normalizedRegions
  rw [h]
  rfl

def sample : List RawEntry :=
  [{ base := 0x3000, length := 0x3000, kind := .usable },
   { base := 0x4000, length := 0x1000, kind := .reserved },
   { base := 0x1000, length := 0x2000, kind := .usable }]

example : normalizedRegions (mkHandoff sample) = some
    [{ start := 1, count := 3, kind := .usable },
     { start := 4, count := 1, kind := .reserved },
     { start := 5, count := 1, kind := .usable }] := by native_decide

example : normalizedRegions
    (mkHandoff [{ base := 1, length := 4095, kind := .usable }]) =
      some [{ start := 0, count := 1, kind := .reserved }] := by native_decide

example : normalizedRegions
    (mkHandoff [{ base := 0x2000, length := pageBytes, kind := .usable }]) =
      some [{ start := 2, count := 1, kind := .usable }] := by native_decide

example : normalizedRegions
    (mkHandoff [{ base := 0, length := pageBytes, kind := .usable },
      { base := pageBytes, length := pageBytes, kind := .usable }]) =
      some [{ start := 0, count := 2, kind := .usable }] := by native_decide

def duplicatedEntry : RawEntry :=
  { base := 0x3000, length := 0x3000, kind := .usable }

example : normalizedRegions (mkHandoff [duplicatedEntry, duplicatedEntry]) =
    some [{ start := 3, count := 3, kind := .usable }] := by native_decide

example : normalizedRegions (mkHandoff sample.reverse) = normalizedRegions (mkHandoff sample) := by
  native_decide

def overflowingEntry : RawEntry :=
  { base := wordLimit - 1, length := 2, kind := .usable }

example : (normalize (mkHandoff [overflowingEntry])).isOk = false := by native_decide
example : normalizedRegions
    (mkHandoff [{ base := physicalLimit - pageBytes, length := (2 * pageBytes), kind := .usable }]) =
      some [{ start := frameLimit - 1, count := 1, kind := .usable }] := by native_decide
example : normalizedRegions
    (mkHandoff [{ base := physicalLimit, length := (128 * 1024 * 1024 - physicalLimit), kind := .usable }]) =
      some [] := by native_decide
example : (normalize (mkHandoff [{ base := 0, length := 0, kind := .usable }])).isOk = false := by
  native_decide
example : (normalize (mkHandoff sample (version := 1))).isOk = false := by native_decide
example : (normalize (mkHandoff sample (entrySize := 32))).isOk = false := by native_decide
example : (normalize { (mkHandoff sample) with tags :=
    [.memoryMap (memoryMapTagHeaderSize + memoryMapEntrySize * sample.length)
      memoryMapEntrySize 0 sample] }).isOk = false := by native_decide
example : (normalize { { (mkHandoff sample) with totalSize := 24 } with
    tags := [.memoryMap 15 memoryMapEntrySize 0 [], .end 8] }).isOk = false := by native_decide
example : (normalize { (mkHandoff sample) with infoAddress := wordLimit }).isOk = false := by
  native_decide
example : (normalize { (mkHandoff sample) with
    totalSize := (mkHandoff sample).totalSize + 16,
    tags := (mkHandoff sample).tags.dropLast ++ [.end 8, .ignored 8, .end 8] }).isOk = false := by
  native_decide

def tooMany : List RawEntry :=
  (List.range (maxEntries + 1)).map fun frame =>
    { base := frame * pageBytes, length := pageBytes, kind := .usable }

example : (normalize (mkHandoff tooMany)).isOk = false := by native_decide

/-- Rounding a partially covered frame upward would expose bytes not described
as usable. -/
example : covers { base := 1, length := 4095, kind := .usable } 0 pageBytes = false := by decide

/-- First-entry-wins is unsound: the later reservation overlaps frame four. -/
example : usableFrameSound sample 4 = false := by decide

end LeanOS.BootMemoryMap
