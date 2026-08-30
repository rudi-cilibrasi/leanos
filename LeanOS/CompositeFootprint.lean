/-!
# Composite projection footprints

This dependency-free vocabulary names the authoritative projections currently
owned by `FailStop.CompositeState`.  It deliberately does not depend on that
state or on the operation dispatcher: later integration slices can declare
read/write footprints without changing either model's behavior.
-/
namespace LeanOS.CompositeFootprint

/-- Stable names for the projections currently owned by the composite gate. -/
inductive Projection where
  | execution
  | scheduler
  | preemption
  | virtualMemory
  | ipc
  | capabilities
  | lifecycle
  | resumable
  | transfers
  | blockingIPC
  | blockingContexts
  | deferredCancels
  | directPortIO
  | dmaAccepted
  | dmaObserved
  | invalidationPublication
  deriving DecidableEq, Repr

/-- The complete finite vocabulary, in `CompositeState` declaration order. -/
def Projection.all : List Projection :=
  [ .execution, .scheduler, .preemption, .virtualMemory, .ipc
  , .capabilities, .lifecycle, .resumable, .transfers, .blockingIPC
  , .blockingContexts, .deferredCancels, .directPortIO, .dmaAccepted
  , .dmaObserved, .invalidationPublication ]

/-- Every projection name occurs in the explicit finite vocabulary. -/
theorem Projection.mem_all (projection : Projection) :
    projection ∈ Projection.all := by
  cases projection <;> decide

/-- An operation footprint records everything it reads and writes.  Requiring
writes to be reads makes read-independence sufficient for the frame rule. -/
structure Footprint where
  reads : Projection → Bool
  writes : Projection → Bool
  writesAreRead : ∀ projection, writes projection = true → reads projection = true

/-- The footprint that observes and changes no composite projection. -/
def Footprint.empty : Footprint where
  reads := fun _ => false
  writes := fun _ => false
  writesAreRead := by simp

/-- A projection is unread when an operation does not inspect it. -/
def Unread (footprint : Footprint) (projection : Projection) : Prop :=
  footprint.reads projection = false

/-- A projection is untouched when an operation does not write it. -/
def Untouched (footprint : Footprint) (projection : Projection) : Prop :=
  footprint.writes projection = false

/-- A projection-specific frame obligation.  Callers supply the before/after
values, so this predicate stays independent of heterogeneous composite state. -/
def Frames (footprint : Footprint) (projection : Projection)
    (before after : α) : Prop :=
  Untouched footprint projection → after = before

/-- Read-independence implies that the projection is untouched. -/
theorem Footprint.unread_is_untouched (footprint : Footprint)
    (projection : Projection) (unread : Unread footprint projection) :
    Untouched footprint projection := by
  cases written : footprint.writes projection with
  | false => simpa [Untouched] using written
  | true =>
      have read := footprint.writesAreRead projection written
      simp [Unread, read] at unread

/-- Untouched projections are not written, by definition. -/
theorem Footprint.untouched_not_written (footprint : Footprint)
    (projection : Projection) (untouched : Untouched footprint projection) :
    footprint.writes projection = false := untouched

/-- Literal preservation always discharges the projection frame obligation. -/
theorem frames_of_eq (footprint : Footprint) (projection : Projection)
    {before after : α} (preserved : after = before) :
    Frames footprint projection before after := by
  intro _
  exact preserved

/-- Frame obligations compose across sequential operation steps. -/
theorem frames_trans (footprint : Footprint) (projection : Projection)
    {before middle after : α}
    (first : Frames footprint projection before middle)
    (second : Frames footprint projection middle after) :
    Frames footprint projection before after := by
  intro untouched
  exact (second untouched).trans (first untouched)

end LeanOS.CompositeFootprint
