import LeanOS.BootReservation
import LeanOS.FrameScrub

/-!
# First boot allocation refinement boundary

The byte parser and the write to physical memory remain trusted boot code.  This
module records the fixed-width evidence that code must present and composes the
already proved normalization, reservation, allocator, lifetime, and scrubbing
properties.  Acceptance is deliberately narrow: it is not a proof of GRUB,
the parser, generated C, or the machine write.
-/
namespace LeanOS.BootAllocation

open LeanOS

def multiboot2Magic : UInt64 := 0x36d76289
def maxInfoBytes : UInt64 := 65536
def memoryMapEntryBytes : UInt64 := 24
def bootAccessibleFrames : UInt64 := 4096

/-- `flags`: bit 0 normalized, bit 1 reservation excluded, bit 2 scrubbed,
bit 3 published. Publication is accepted only when all earlier stages exist. -/
@[export leanos_boot_allocation_check]
def check (magic infoBytes entryBytes selectedFrame flags : UInt64) : UInt64 :=
  if magic == multiboot2Magic && infoBytes ≥ 16 && infoBytes ≤ maxInfoBytes &&
      infoBytes % 8 == 0 && entryBytes == memoryMapEntryBytes &&
      selectedFrame < bootAccessibleFrames && flags == 15 then 1 else 0

theorem accepted_evidence (magic infoBytes entryBytes selectedFrame flags : UInt64)
    (h : check magic infoBytes entryBytes selectedFrame flags = 1) :
    magic = multiboot2Magic ∧ infoBytes ≥ 16 ∧ infoBytes ≤ maxInfoBytes ∧
      infoBytes % 8 = 0 ∧ entryBytes = memoryMapEntryBytes ∧
      selectedFrame < bootAccessibleFrames ∧ flags = 15 := by
  simp only [check] at h
  split at h
  next haccepted =>
    have hc := haccepted
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
    rcases hc with ⟨⟨⟨⟨⟨⟨hmagic, hmin⟩, hmax⟩, halign⟩, hentry⟩, hframe⟩, hflags⟩
    exact ⟨hmagic, hmin, hmax, halign, hentry, hframe, hflags⟩
  next => contradiction

/-- The model-level composition used by the boot adapter: a first allocator
selection is outside every checked reservation, and an accepted lifetime
allocation publishes an owned, completely scrubbed frame. -/
theorem allocation_refinement
    (reserved : BootReservation.Result) (owner : FrameAllocator.OwnerId)
    (allocation : FrameAllocator.Allocation)
    (ha : FrameAllocator.allocate reserved.allocator owner = .ok allocation)
    (scrub : FrameScrub.State) (object : FrameScrub.ObjectId)
    (subject : FrameScrub.SubjectId) (slot : FrameScrub.SlotId)
    (hs : (FrameScrub.allocate scrub object subject slot).result = .accepted) :
    BootReservation.reservedBy reserved.intervals allocation.frame = false ∧
      FrameScrub.Fresh (FrameScrub.allocate scrub object subject slot).state object ∧
      ∃ frame, (FrameScrub.allocate scrub object subject slot).state.memory.binding object =
        some frame ∧ FrameAllocator.IsOwnedBy
          (FrameScrub.allocate scrub object subject slot).state.memory.allocator frame object := by
  exact ⟨BootReservation.allocation_excludes_reservations reserved owner allocation ha,
    FrameScrub.allocation_publishes_scrubbed scrub object subject slot hs,
    FrameScrub.allocation_publishes_owned scrub object subject slot hs⟩

/-- Rejected scrub allocation is atomic: no allocator, object, capability, or
byte-memory prefix is published. -/
theorem rejected_publishes_nothing state object subject slot reason
    (h : (FrameScrub.allocate state object subject slot).result = .rejected reason) :
    (FrameScrub.allocate state object subject slot).state = state :=
  FrameScrub.allocate_rejected_unchanged state object subject slot reason h

example : check multiboot2Magic 128 24 512 15 = 1 := by native_decide
example : check 0 128 24 512 15 = 0 := by native_decide
example : check multiboot2Magic 15 24 512 15 = 0 := by native_decide
example : check multiboot2Magic 128 16 512 15 = 0 := by native_decide
example : check multiboot2Magic 128 24 4096 15 = 0 := by native_decide
example : check multiboot2Magic 128 24 512 7 = 0 := by native_decide

end LeanOS.BootAllocation
