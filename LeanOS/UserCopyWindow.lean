import LeanOS.UserCopy

/-!
# Atomic SMAP user-copy window

This module composes whole-range `UserCopy.validate` with an explicit model of
the EFLAGS.AC override.  The public operations are atomic: validation happens
while AC is clear, the modeled byte transfer is the only action in the window,
and every return path clears AC.  The sequential model assumes that mappings
cannot change between validation and transfer.
-/
namespace LeanOS.UserCopyWindow

open LeanOS.UserCopy
open LeanOS.VirtualMapping

structure State where
  memory : UserCopy.State
  ac : Bool := false

inductive Error where
  | acAlreadySet
  | validation (reason : CopyError)
  deriving BEq, DecidableEq, Repr

inductive Result where
  | accepted
  | rejected (reason : Error)
  deriving BEq, DecidableEq, Repr

structure Outcome where
  state : State
  result : Result

private def reject (state : State) (reason : Error) : Outcome :=
  { state := { state with ac := false }, result := .rejected reason }

/-- The supervisor paging context used during a modeled byte transfer.  SMAP
is always enabled; only the explicit window state controls its AC override. -/
def accessContext (state : State) (kind : X86PageTable.AccessKind) :
    X86PageTable.AccessContext :=
  { privilege := .supervisor, kind, writeProtect := true, nxEnable := true,
    smep := true, smap := true, ac := state.ac }

/-- Validate the complete range while AC is clear, then produce the sole state
in which supervisor access to user leaves is permitted.  This transition is
internal to one atomic copy operation; callers never receive an open window. -/
def openWindow (state : State) (context : TrustedContext) (start : UInt64)
    (length : Nat) (access : Access) : Except Error (State × List Location) :=
  if state.ac then .error .acAlreadySet
  else match validate state.memory context start length access with
    | .error reason => .error (.validation reason)
    | .ok locations => .ok ({ state with ac := true }, locations)

theorem openWindow_validated state context start length access opened locations
    (h : openWindow state context start length access = .ok (opened, locations)) :
    state.ac = false ∧
      validate state.memory context start length access = .ok locations ∧
      opened = { state with ac := true } := by
  simp only [openWindow] at h
  split at h <;> try contradiction
  next hac =>
    split at h <;> try contradiction
    next accepted hvalidate =>
      simp at h
      rcases h with ⟨rfl, rfl⟩
      exact ⟨Bool.eq_false_iff.mpr hac, hvalidate, rfl⟩

theorem openWindow_sets_ac state context start length access opened locations
    (h : openWindow state context start length access = .ok (opened, locations)) :
    opened.ac = true := by
  obtain ⟨_, _, rfl⟩ := openWindow_validated state context start length access opened locations h
  rfl

/-- With the window closed, SMAP denies supervisor data access to every user
leaf emitted by the virtual-mapping encoder. -/
theorem closed_encoded_user_access_denied state addressSpace page leaf kind
    (hac : state.ac = false)
    (hkind : kind = X86PageTable.AccessKind.read ∨
      kind = X86PageTable.AccessKind.write)
    (hleaf : (X86PageTable.encode state.memory.virtual addressSpace).leaf page =
      some leaf) :
    X86PageTable.classify (X86PageTable.encode state.memory.virtual addressSpace) page
      (accessContext state kind) = .error .smap := by
  have hv := X86PageTable.encoded_structurally_valid state.memory.virtual addressSpace
  have hleafValid := hv.2.2.2 page leaf hleaf
  have hencoded : X86PageTable.encodedLeaf state.memory.virtual addressSpace page =
      some leaf := hleaf
  rcases hkind with rfl | rfl <;>
    simp [X86PageTable.classify, X86PageTable.encode, X86PageTable.userAncestor,
      X86PageTable.ancestorsUser,
      hleafValid.1, hencoded, hleafValid.2.1, hleafValid.2.2.1,
      hleafValid.2.2.2.1, hleafValid.2.2.2.2, accessContext, hac]

/-- A successfully opened, prevalidated window supplies exactly the AC state
needed for a supervisor read of an encoded user leaf. -/
theorem openWindow_encoded_read_allowed state context start length access opened locations
    addressSpace page leaf
    (hopen : openWindow state context start length access = .ok (opened, locations))
    (hleaf : (X86PageTable.encode opened.memory.virtual addressSpace).leaf page =
      some leaf) :
    X86PageTable.classify (X86PageTable.encode opened.memory.virtual addressSpace) page
      (accessContext opened .read) = .ok leaf.frame := by
  have hac := openWindow_sets_ac state context start length access opened locations hopen
  have hv := X86PageTable.encoded_structurally_valid opened.memory.virtual addressSpace
  have hleafValid := hv.2.2.2 page leaf hleaf
  have hencoded : X86PageTable.encodedLeaf opened.memory.virtual addressSpace page =
      some leaf := hleaf
  simp [X86PageTable.classify, X86PageTable.encode, X86PageTable.userAncestor,
    X86PageTable.ancestorsUser, hleafValid.1, hencoded, hleafValid.2.1,
    hleafValid.2.2.1, hleafValid.2.2.2.1, hleafValid.2.2.2.2,
    accessContext, hac]

/-- The AC override does not amplify write permission: an open, validated
window permits supervisor writes only to an encoded writable leaf. -/
theorem openWindow_encoded_write_allowed state context start length access opened locations
    addressSpace page leaf
    (hopen : openWindow state context start length access = .ok (opened, locations))
    (hleaf : (X86PageTable.encode opened.memory.virtual addressSpace).leaf page =
      some leaf) (hwritable : leaf.writable = true) :
    X86PageTable.classify (X86PageTable.encode opened.memory.virtual addressSpace) page
      (accessContext opened .write) = .ok leaf.frame := by
  have hac := openWindow_sets_ac state context start length access opened locations hopen
  have hv := X86PageTable.encoded_structurally_valid opened.memory.virtual addressSpace
  have hleafValid := hv.2.2.2 page leaf hleaf
  have hencoded : X86PageTable.encodedLeaf opened.memory.virtual addressSpace page =
      some leaf := hleaf
  simp [X86PageTable.classify, X86PageTable.encode, X86PageTable.userAncestor,
    X86PageTable.ancestorsUser, X86PageTable.ancestorsWritable,
    hleafValid.1, hencoded, hleafValid.2.1, hleafValid.2.2.1,
    hleafValid.2.2.2.1, hleafValid.2.2.2.2, accessContext, hac, hwritable]

/-- Validate with AC clear, perform exactly one bounded copy-from operation,
then close the override before returning. -/
def copyFrom (state : State) (context : TrustedContext) (start : UInt64)
    (length : Nat) (buffer : BufferId) : Outcome :=
  match openWindow state context start length .read with
  | .error reason => reject state reason
  | .ok (opened, _) =>
      let copied := copyFromUser opened.memory context start length buffer
      { state := { memory := copied.state, ac := false }, result := .accepted }

/-- Validate with AC clear, perform exactly one bounded copy-to operation,
then close the override before returning. -/
def copyTo (state : State) (context : TrustedContext) (start : UInt64)
    (length : Nat) (buffer : BufferId) : Outcome :=
  match openWindow state context start length .write with
  | .error reason => reject state reason
  | .ok (opened, _) =>
      let copied := copyToUser opened.memory context start length buffer
      { state := { memory := copied.state, ac := false }, result := .accepted }

theorem copyFrom_clears_ac state context start length buffer :
    (copyFrom state context start length buffer).state.ac = false := by
  unfold copyFrom
  split <;> rfl

theorem copyTo_clears_ac state context start length buffer :
    (copyTo state context start length buffer).state.ac = false := by
  unfold copyTo
  split <;> rfl

/-- An accepted copy window can only arise from successful whole-range
prevalidation with the requested read permission. -/
theorem copyFrom_accepted_validated state context start length buffer
    (h : (copyFrom state context start length buffer).result = .accepted) :
    ∃ locations, validate state.memory context start length .read = .ok locations := by
  simp only [copyFrom] at h
  split at h <;> try contradiction
  next opened locations hopen =>
    exact ⟨locations, (openWindow_validated state context start length .read
      opened locations hopen).2.1⟩

/-- An accepted copy-to window can only arise from successful whole-range
prevalidation with the requested write permission. -/
theorem copyTo_accepted_validated state context start length buffer
    (h : (copyTo state context start length buffer).result = .accepted) :
    ∃ locations, validate state.memory context start length .write = .ok locations := by
  simp only [copyTo] at h
  split at h <;> try contradiction
  next opened locations hopen =>
    exact ⟨locations, (openWindow_validated state context start length .write
      opened locations hopen).2.1⟩

/-- Rejection before opening the window cannot modify either memory domain. -/
theorem copyFrom_rejected_memory_unchanged state context start length buffer reason
    (h : (copyFrom state context start length buffer).result = .rejected reason) :
    (copyFrom state context start length buffer).state.memory = state.memory := by
  cases hw : openWindow state context start length .read with
  | error windowError => simp [copyFrom, hw, reject]
  | ok opened => simp [copyFrom, hw] at h

/-- Rejection before opening the window cannot modify either memory domain. -/
theorem copyTo_rejected_memory_unchanged state context start length buffer reason
    (h : (copyTo state context start length buffer).result = .rejected reason) :
    (copyTo state context start length buffer).state.memory = state.memory := by
  cases hw : openWindow state context start length .write with
  | error windowError => simp [copyTo, hw, reject]
  | ok opened => simp [copyTo, hw] at h

end LeanOS.UserCopyWindow
