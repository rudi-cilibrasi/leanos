import LeanOS.BootMemoryMap

/-!
# Boot-owned physical-frame reservations

This bounded model overlays a checked manifest on the canonical firmware map
before allocator publication.  Linker and bootloader correspondence is an
explicit integration assumption checked by `scripts/check-image-policy.sh`;
it is not a theorem about ELF loading or assembly execution.
-/
namespace LeanOS.BootReservation

open LeanOS FrameAllocator BootMemoryMap

inductive Identity where
  | lowMemory | loadedImage | pageTables | descriptorTables | kernelStacks
  | ordinaryEntryGuard | ordinaryEntryStack | embeddedUsers | multibootInfo
  deriving BEq, DecidableEq, Repr

def requiredIdentities : List Identity :=
  [.lowMemory, .loadedImage, .pageTables, .descriptorTables, .kernelStacks,
   .ordinaryEntryGuard, .ordinaryEntryStack, .embeddedUsers, .multibootInfo]

inductive Lifetime where | permanent | bootstrap
  deriving BEq, DecidableEq, Repr

/-- Trusted byte boundaries use half-open `[start, start + length)` semantics. -/
structure Reservation where
  identity : Identity
  start : Nat
  length : Nat
  lifetime : Lifetime
  deriving BEq, DecidableEq, Repr

structure Interval where
  identity : Identity
  firstFrame : Nat
  frameCount : Nat
  lifetime : Lifetime
  deriving BEq, DecidableEq, Repr

inductive Error where
  | missingIdentity | duplicateIdentity | zeroLength | addressOverflow
  | outsidePhysicalLimit | tooManyReservations | inconsistentImage | ordinaryEntryOverlap
  | emptyOutput | normalizationInvariant | allocatorRejected
  deriving BEq, DecidableEq, Repr

def maxReservations : Nat := 32

def exactlyOnce (identity : Identity) (manifest : List Reservation) : Bool :=
  (manifest.filter (·.identity == identity)).length == 1

def roundInterval (reservation : Reservation) : Except Error Interval := do
  if reservation.length == 0 then throw .zeroLength
  if reservation.start ≥ wordLimit || reservation.length ≥ wordLimit ||
      reservation.length > wordLimit - reservation.start then throw .addressOverflow
  let stop := reservation.start + reservation.length
  let first := reservation.start / pageBytes
  let lastFrame := (stop + pageBytes - 1) / pageBytes
  if stop > physicalLimit || lastFrame > frameLimit then throw .outsidePhysicalLimit
  pure (Interval.mk reservation.identity first (lastFrame - first) reservation.lifetime)

def validateManifest (manifest : List Reservation) : Except Error (List Interval) := do
  if manifest.length > maxReservations then throw .tooManyReservations
  if !(requiredIdentities.all fun identity => exactlyOnce identity manifest) then
    throw .missingIdentity
  if !(manifest.all fun reservation => requiredIdentities.contains reservation.identity) then
    throw .duplicateIdentity
  let intervals ← manifest.mapM roundInterval
  let image := intervals.find? (·.identity == .loadedImage)
  if !(intervals.all fun interval =>
      interval.identity == .lowMemory || interval.identity == .multibootInfo ||
      match image with
      | none => false
      | some loaded => loaded.firstFrame ≤ interval.firstFrame &&
          interval.firstFrame + interval.frameCount ≤ loaded.firstFrame + loaded.frameCount)
  then throw .inconsistentImage
  pure intervals

def Interval.disjoint (left right : Interval) : Bool :=
  left.firstFrame + left.frameCount ≤ right.firstFrame ||
    right.firstFrame + right.frameCount ≤ left.firstFrame

def ordinaryEntryPeer : Identity → Bool
  | .pageTables | .descriptorTables | .kernelStacks | .embeddedUsers => true
  | _ => false

/-- The ordinary-entry identities are exact adjacent frame intervals. They may
overlap the enclosing loaded-image reservation, but not independently owned
page tables, descriptors, other kernel stacks, or embedded user images. -/
def ordinaryEntrySeparated (intervals : List Interval) : Bool :=
  match intervals.find? (·.identity == .ordinaryEntryGuard),
      intervals.find? (·.identity == .ordinaryEntryStack) with
  | some guard, some stack =>
      guard.firstFrame + guard.frameCount = stack.firstFrame &&
        guard.disjoint stack && intervals.all fun interval =>
          !ordinaryEntryPeer interval.identity ||
            (guard.disjoint interval && stack.disjoint interval)
  | _, _ => false

def Interval.contains (interval : Interval) (frame : Nat) : Bool :=
  interval.firstFrame ≤ frame && frame < interval.firstFrame + interval.frameCount

def reservedBy (intervals : List Interval) (frame : Nat) : Bool :=
  intervals.any (·.contains frame)

/-- Reservation wins unconditionally over firmware's classification. -/
def overlayRegion (intervals : List Interval) (region : Region) : List Region :=
  region.frames.map fun frame =>
    { start := frame, count := 1,
      kind := if reservedBy intervals frame then .reserved else region.kind }

def overlay (intervals : List Interval) (regions : List Region) : List Region :=
  mergeAdjacent (regions.flatMap (overlayRegion intervals))

def reservationPrecedence (intervals : List Interval) (regions : List Region) : Bool :=
  regions.all fun region => region.frames.all fun frame =>
    !reservedBy intervals frame || region.kind == .reserved

def preservesFirmwareUsable (before after : List Region) : Bool :=
  after.all fun region => region.kind != .usable || region.frames.all fun frame =>
    before.any fun original => original.kind == .usable && original.frames.contains frame

/-- Every frame covered by the manifest is unavailable in the allocator state.
This also requires reservations outside the firmware map to be rejected rather
than silently disappearing from the allocator domain. -/
def reservationsNonfree (intervals : List Interval) (state : State) : Bool :=
  intervals.all fun interval =>
    (List.range interval.frameCount).all fun offset =>
      state.status (interval.firstFrame + offset) != .free

structure Result where
  firmware : BootMemoryMap.Normalized
  intervals : List Interval
  regions : List Region
  nonempty : regions.isEmpty = false
  shape : regionShape regions = true
  disjoint : pairwiseDisjoint regions = true
  precedence : reservationPrecedence intervals regions = true
  firmwareSound : usableSound firmware.entries regions = true
  ordinaryEntrySeparation : ordinaryEntrySeparated intervals = true
  allocator : State
  allocatorInit : FrameAllocator.init regions = .ok allocator
  reservationsExcluded : reservationsNonfree intervals allocator = true

def initializeAllocator (handoff : Handoff) (manifest : List Reservation) : Except Error Result := do
  let firmware ← (normalize handoff).mapError fun _ => .normalizationInvariant
  let intervals ← validateManifest manifest
  let regions := overlay intervals firmware.regions
  if hnonempty : regions.isEmpty then throw .emptyOutput
  else if hshape : regionShape regions then
    if hdisjoint : pairwiseDisjoint regions then
      if hprecedence : reservationPrecedence intervals regions then
        if hsound : usableSound firmware.entries regions then
          if hentry : ordinaryEntrySeparated intervals then
            match hinit : FrameAllocator.init regions with
            | .error _ => throw .allocatorRejected
            | .ok allocator =>
              if hexcluded : reservationsNonfree intervals allocator then
                have hnonempty' : regions.isEmpty = false := Bool.eq_false_iff.mpr hnonempty
                pure ⟨firmware, intervals, regions, hnonempty', hshape, hdisjoint, hprecedence,
                  hsound, hentry, allocator, hinit, hexcluded⟩
              else throw .normalizationInvariant
          else throw .ordinaryEntryOverlap
        else throw .normalizationInvariant
      else throw .normalizationInvariant
    else throw .normalizationInvariant
  else throw .normalizationInvariant

theorem initialize_functional handoff manifest first second
    (hfirst : initializeAllocator handoff manifest = first)
    (hsecond : initializeAllocator handoff manifest = second) : first = second := by
  rw [hfirst] at hsecond
  exact hsecond

theorem accepted_normalized (handoff : Handoff) (manifest : List Reservation) (result : Result)
    (_h : initializeAllocator handoff manifest = .ok result) :
    result.regions.isEmpty = false ∧ regionShape result.regions = true ∧
      pairwiseDisjoint result.regions = true :=
  ⟨result.nonempty, result.shape, result.disjoint⟩

theorem accepted_reservation_precedence (handoff : Handoff) (manifest : List Reservation)
    (result : Result) (_h : initializeAllocator handoff manifest = .ok result) :
    reservationPrecedence result.intervals result.regions = true := result.precedence

theorem accepted_preserves_usable_soundness (handoff : Handoff) (manifest : List Reservation)
    (result : Result) (_h : initializeAllocator handoff manifest = .ok result) :
    usableSound result.firmware.entries result.regions = true := result.firmwareSound

theorem accepted_separates_ordinary_entry (handoff : Handoff)
    (manifest : List Reservation) (result : Result)
    (_h : initializeAllocator handoff manifest = .ok result) :
    ordinaryEntrySeparated result.intervals = true := result.ordinaryEntrySeparation

/-- Initialization makes every frame in every checked reservation non-free;
the state is published only after this executable invariant succeeds. -/
theorem accepted_reservations_nonfree (handoff : Handoff) (manifest : List Reservation)
    (result : Result) (_h : initializeAllocator handoff manifest = .ok result) :
    reservationsNonfree result.intervals result.allocator = true :=
  result.reservationsExcluded

/-- A successful allocation can only select an initially free frame.  Combined
with `accepted_reservation_precedence`, this excludes every live reservation. -/
theorem allocation_selects_initially_free (state : State) (owner : OwnerId)
    (allocation : Allocation) (h : allocate state owner = .ok allocation) :
    (state.status allocation.frame == .free) = true := by
  simp only [allocate] at h
  split at h
  · contradiction
  · rename_i frame hfind
    have hfree : (state.status frame == FrameState.free) = true :=
      @List.find?_some FrameId (fun candidate => state.status candidate == FrameState.free)
        frame state.frames hfind
    injection h with hallocation
    rw [← hallocation]
    exact hfree

/-- No successful first allocation from the published state can return a frame
covered by any live boot reservation. -/
theorem allocation_excludes_reservations (result : Result) (owner : OwnerId)
    (allocation : Allocation) (h : allocate result.allocator owner = .ok allocation) :
    reservedBy result.intervals allocation.frame = false := by
  have hfree := allocation_selects_initially_free result.allocator owner allocation h
  have hexcluded := result.reservationsExcluded
  simp only [reservationsNonfree, List.all_eq_true] at hexcluded
  apply Bool.eq_false_iff.mpr
  intro hreserved
  simp only [reservedBy, List.any_eq_true] at hreserved
  obtain ⟨interval, hinterval, hcontains⟩ := hreserved
  have hall := hexcluded interval hinterval
  simp [Interval.contains] at hcontains
  obtain ⟨hfirst, hstop⟩ := hcontains
  have hlt : allocation.frame - interval.firstFrame < interval.frameCount := by
    apply (Nat.sub_lt_iff_lt_add hfirst).mpr
    simpa [Nat.add_comm] using hstop
  have hoffset := hall (allocation.frame - interval.firstFrame)
    (List.mem_range.mpr hlt)
  have hadd : interval.firstFrame + (allocation.frame - interval.firstFrame) =
      allocation.frame := by
    omega
  rw [hadd] at hoffset
  cases hstatus : result.allocator.status allocation.frame with
  | reserved =>
      rw [hstatus] at hfree
      contradiction
  | free =>
      rw [hstatus] at hoffset
      contradiction
  | owned owner =>
      rw [hstatus] at hfree
      contradiction

def sampleManifest : List Reservation :=
  [{ identity := .lowMemory, start := 0, length := pageBytes, lifetime := .permanent },
   { identity := .loadedImage, start := 2 * pageBytes, length := 8 * pageBytes,
     lifetime := .permanent },
   { identity := .pageTables, start := 3 * pageBytes, length := pageBytes,
     lifetime := .permanent },
   { identity := .descriptorTables, start := 4 * pageBytes, length := pageBytes,
     lifetime := .permanent },
   { identity := .kernelStacks, start := 5 * pageBytes, length := pageBytes,
     lifetime := .permanent },
   { identity := .ordinaryEntryGuard, start := 8 * pageBytes, length := pageBytes,
     lifetime := .permanent },
   { identity := .ordinaryEntryStack, start := 9 * pageBytes, length := pageBytes,
     lifetime := .permanent },
   { identity := .embeddedUsers, start := 6 * pageBytes, length := 2 * pageBytes,
     lifetime := .permanent },
   { identity := .multibootInfo, start := pageBytes + 17, length := pageBytes,
     lifetime := .bootstrap }]

def layout : Handoff := mkHandoff
  [{ base := 0, length := 12 * pageBytes, kind := .usable }]

def crossingLayout : Handoff := mkHandoff
  [{ base := 0, length := 4 * pageBytes, kind := .usable },
   { base := 4 * pageBytes, length := 2 * pageBytes, kind := .reserved },
   { base := 6 * pageBytes, length := 6 * pageBytes, kind := .usable }]

def consumedLayout : Handoff := mkHandoff
  [{ base := 0, length := 10 * pageBytes, kind := .usable }]

def twoSidedManifest : List Reservation :=
  [{ identity := .lowMemory, start := 0, length := pageBytes, lifetime := .permanent },
   { identity := .loadedImage, start := 3 * pageBytes, length := 7 * pageBytes,
     lifetime := .permanent },
   { identity := .pageTables, start := 3 * pageBytes, length := pageBytes,
     lifetime := .permanent },
   { identity := .descriptorTables, start := 4 * pageBytes, length := pageBytes,
     lifetime := .permanent },
   { identity := .kernelStacks, start := 5 * pageBytes, length := pageBytes,
     lifetime := .permanent },
   { identity := .ordinaryEntryGuard, start := 8 * pageBytes, length := pageBytes,
     lifetime := .permanent },
   { identity := .ordinaryEntryStack, start := 9 * pageBytes, length := pageBytes,
     lifetime := .permanent },
   { identity := .embeddedUsers, start := 6 * pageBytes, length := 2 * pageBytes,
     lifetime := .permanent },
   { identity := .multibootInfo, start := 10 * pageBytes + 17, length := pageBytes,
     lifetime := .bootstrap }]

def twoSidedLayout : Handoff := mkHandoff
  [{ base := 0, length := 14 * pageBytes, kind := .usable }]

example : (initializeAllocator layout sampleManifest).isOk = true := by native_decide
example : ordinaryEntrySeparated (validateManifest sampleManifest).toOption.get! = true := by
  native_decide
example : (validateManifest (sampleManifest.drop 1)).isOk = false := by native_decide
example : (initializeAllocator layout (sampleManifest.map fun reservation =>
    if reservation.identity == .ordinaryEntryStack then
      { reservation with start := 7 * pageBytes }
    else reservation)).isOk = false := by native_decide
example : (validateManifest
    ({ identity := .lowMemory, start := 0, length := 0, lifetime := .permanent } ::
      sampleManifest.tail)).isOk = false := by native_decide
example : (validateManifest
    ({ identity := .lowMemory, start := wordLimit - 1, length := 2,
       lifetime := .permanent } :: sampleManifest.tail)).isOk = false := by native_decide
example : (initializeAllocator layout sampleManifest).toOption.map (·.regions) = some
    [{ start := 0, count := 10, kind := .reserved },
     { start := 10, count := 2, kind := .usable }] := by native_decide
example : (initializeAllocator crossingLayout sampleManifest).isOk = true := by native_decide
example : (initializeAllocator consumedLayout sampleManifest).toOption.map (·.regions) =
    some [{ start := 0, count := 10, kind := .reserved }] := by native_decide
example : (initializeAllocator twoSidedLayout twoSidedManifest).toOption.map (·.regions) =
    some [{ start := 0, count := 1, kind := .reserved },
      { start := 1, count := 2, kind := .usable },
      { start := 3, count := 9, kind := .reserved },
      { start := 12, count := 2, kind := .usable }] := by native_decide

def truncatedImageManifest : List Reservation :=
  sampleManifest.map fun reservation =>
    if reservation.identity == .loadedImage then
      { reservation with length := 7 * pageBytes }
    else reservation

/-- Omitting the final loaded-image page can no longer strand the separately
identified ordinary-entry stack outside its enclosing image reservation. -/
example : (initializeAllocator layout truncatedImageManifest).isOk = false := by native_decide

/-- Allowing firmware to win makes the first boot-owned low-memory frame allocatable. -/
example : ((FrameAllocator.init [{ start := 0, count := 12, kind := .usable }]).toOption.bind
    fun state => (allocate state 7).toOption.map (·.frame)) = some 0 := by native_decide

/-- Rounding an unaligned end down omits the second Multiboot2 frame. -/
example : ((pageBytes + 17 + pageBytes) / pageBytes) = 2 := by decide

end LeanOS.BootReservation
