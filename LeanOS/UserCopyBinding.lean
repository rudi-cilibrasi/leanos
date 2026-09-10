import LeanOS.UserCopyOperands

/-!
Bind policy-validated locations to an independently supplied subject page table.
Both observations must remain immutable through alias publication and transfer.
This is a fresh-walk model: it does not establish snapshot provenance, lifetime
stability, root installation or agreement with cached hardware translations.
-/
namespace LeanOS.UserCopyBinding

open LeanOS.UserCopy LeanOS.VirtualMapping LeanOS.X86PageTable

inductive Error where
  | validation (reason : CopyError)
  | hardwareMismatch
  deriving BEq, DecidableEq, Repr

/-- Check the subject's own read/write permission, not supervisor bypass rights. -/
def subjectContext (access : Access) : AccessContext :=
  { privilege := .user, kind := if access == .write then .write else .read
    writeProtect := true, nxEnable := true, smep := true, smap := false, ac := false }

def agrees (table : PageTable) (access : Access) (location : Location) : Bool :=
  (classify table location.virtualPage (subjectContext access)).toOption == some location.frame

/-- Whole-request policy validation precedes the independent page-table check.
No partial list is returned on rejection. A zero-length request needs no walk. -/
def bind (state : UserCopy.State) (context : TrustedContext) (start : UInt64)
    (length : Nat) (access : Access) (table : PageTable) : Except Error (List Location) :=
  match validate state context start length access with
  | .error reason => .error (.validation reason)
  | .ok locations =>
      if locations.all (agrees table access) then .ok locations else .error .hardwareMismatch

theorem bound_validated state context start length access table locations
    (h : bind state context start length access table = .ok locations) :
    validate state context start length access = .ok locations ∧
      locations.all (agrees table access) = true := by
  simp only [bind] at h
  split at h <;> try contradiction
  next accepted hv =>
    split at h <;> try contradiction
    next ha =>
      cases h
      exact ⟨hv, ha⟩

theorem bound_walk_exact state context start length access table locations location
    (h : bind state context start length access table = .ok locations)
    (hl : location ∈ locations) :
    classify table location.virtualPage (subjectContext access) = .ok location.frame := by
  have ha := (List.all_eq_true.mp (bound_validated _ _ _ _ _ _ _ h).2) location hl
  cases hc : classify table location.virtualPage (subjectContext access) with
  | error reason =>
    simp only [agrees, hc, beq_iff_eq] at ha
    change (none : Option PhysicalFrame) = some location.frame at ha
    contradiction
  | ok frame =>
    simp only [agrees, hc, beq_iff_eq] at ha
    change some frame = some location.frame at ha
    cases ha
    rfl

theorem bound_length state context start length access table locations
    (h : bind state context start length access table = .ok locations) :
    locations.length = length :=
  validate_length _ _ _ _ _ _ (bound_validated _ _ _ _ _ _ _ h).1

theorem validation_rejected state context start length access table reason
    (h : validate state context start length access = .error reason) :
    bind state context start length access table = .error (.validation reason) := by
  simp [bind, h]

end LeanOS.UserCopyBinding
