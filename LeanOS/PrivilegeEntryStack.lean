import LeanOS.InterruptEntry

/-!
# Guarded privilege-entry stack budget

This module is the model-level contract for the ordinary x86-64 privilege-entry
stack.  It reuses the reviewed `InterruptEntry.ManifestEntry` vocabulary and
keeps concrete compiler stack-usage and linker/page-table correspondence as
checked integration evidence.  Byte intervals are half-open and stack growth
is downward from the exclusive `stackTop` bound.
-/
namespace LeanOS.PrivilegeEntryStack

open LeanOS InterruptEntry

def pageBytes : Nat := 4096
def abiAlignment : Nat := 16
def addressLimit : Nat := 2 ^ 64

/-- A half-open byte interval `[first, pastLast)`. -/
structure Interval where
  first : Nat
  pastLast : Nat
  deriving BEq, DecidableEq, Repr

def Interval.nonempty (interval : Interval) : Bool :=
  interval.first < interval.pastLast

def Interval.disjoint (left right : Interval) : Bool :=
  left.pastLast ≤ right.first || right.pastLast ≤ left.first

/-- The ordinary stack has one absent lower guard and one usable interval.
`stackTop` is the canonical exclusive upper bound installed in `TSS.rsp0`.
Permission facts describe the usable leaves, not the absent guard. -/
structure Layout where
  stackIdentity : UInt64
  guard : Interval
  usable : Interval
  stackTop : Nat
  guardAbsent : Bool
  supervisorWritable : Bool
  userAccessible : Bool
  executable : Bool
  deriving BEq, DecidableEq, Repr

def layoutValid (layout : Layout) (otherReserved : List Interval) : Bool :=
  layout.stackIdentity != 0 && layout.guard.nonempty && layout.usable.nonempty &&
    layout.guard.first % pageBytes = 0 &&
    layout.guard.pastLast = layout.usable.first &&
    layout.guard.pastLast - layout.guard.first = pageBytes &&
    layout.usable.first % pageBytes = 0 &&
    layout.usable.pastLast % pageBytes = 0 &&
    layout.stackTop = layout.usable.pastLast &&
    layout.stackTop % abiAlignment = 0 &&
    layout.stackTop < addressLimit &&
    layout.guardAbsent && layout.supervisorWritable &&
    !layout.userAccessible && !layout.executable &&
    otherReserved.all fun interval =>
      interval.nonempty && layout.guard.disjoint interval && layout.usable.disjoint interval

def usableBytes (layout : Layout) : Nat :=
  layout.usable.pastLast - layout.usable.first

/-- The fixed assembly contribution currently shared by every ordinary entry:
fifteen saved general-purpose registers. -/
def savedRegisterBytes : Nat := 15 * 8

/-- The raw x86 frame size already reviewed by `InterruptEntry`. -/
def hardwareFrameBytes : RawFrame → Nat
  | .privilegeChange .. => 5 * 8
  | .samePrivilege .. => 3 * 8

/-- Hardware contributes an error word only for the manifest's error-code
entries. -/
def hardwareErrorBytes (entry : ManifestEntry) : Nat :=
  if entry.hardwareError then 8 else 0

/-- The ordinary stubs reserve either one alignment word after the hardware
error or the dummy-error plus alignment pair before entering the normalizer. -/
def normalizationSlotBytes (entry : ManifestEntry) : Nat :=
  if entry.hardwareError then 8 else 16

/-- Machine-derived C/generated contributions remain explicit inputs until the
build gate supplies reviewed `.su` and call-graph evidence.  No purpose gets a
private stack policy: all entries use this one accounting record. -/
structure BudgetRequest where
  entry : ManifestEntry
  frame : RawFrame
  hardwareError : Bool
  trustedCallBytes : Nat
  returnValidationBytes : Nat
  safetyMarginBytes : Nat
  deriving BEq, DecidableEq, Repr

def fixedProtocolBytes (request : BudgetRequest) : Nat :=
  hardwareFrameBytes request.frame + hardwareErrorBytes request.entry + savedRegisterBytes +
    normalizationSlotBytes request.entry

def requiredBytes (request : BudgetRequest) : Nat :=
  fixedProtocolBytes request + request.trustedCallBytes +
    request.returnValidationBytes + request.safetyMarginBytes

/-- Checked subtraction is the only way to mint a remaining-budget fact. -/
def checkedRemaining (available required : Nat) : Option Nat :=
  if required ≤ available then some (available - required) else none

theorem checkedRemaining_sound available required remaining
    (hchecked : checkedRemaining available required = some remaining) :
    required ≤ available ∧ remaining + required = available := by
  unfold checkedRemaining at hchecked
  split at hchecked
  · rename_i hfits
    simp only [Option.some.injEq] at hchecked
    subst remaining
    exact ⟨hfits, Nat.sub_add_cancel hfits⟩
  · contradiction

theorem checkedRemaining_rejects_over_budget available required
    (hover : available < required) :
    checkedRemaining available required = none := by
  simp [checkedRemaining, Nat.not_le.mpr hover]

inductive RejectReason where
  | invalidLayout | unsupportedEntry | wrongErrorShape | insufficientBudget
  deriving BEq, DecidableEq, Repr

structure AcceptedBudget where
  stackIdentity : UInt64
  stackFirst : Nat
  stackPastLast : Nat
  stackTop : Nat
  requiredBytes : Nat
  remainingBytes : Nat
  purpose : Purpose
  deriving BEq, DecidableEq, Repr

/-- Both outcomes carry the exact inbound composite state.  Budget rejection
does not authorize an operation handler, a return epilogue, or any state edit. -/
inductive Result (State : Type) where
  | accepted (budget : AcceptedBudget) (state : State)
  | fatal (reason : RejectReason) (state : State)
  deriving DecidableEq, Repr

def resultState : Result State → State
  | .accepted _ state | .fatal _ state => state

def authorize (layout : Layout) (otherReserved : List Interval)
    (request : BudgetRequest) (state : State) : Result State :=
  if !layoutValid layout otherReserved then .fatal .invalidLayout state
  else if !entrySupported request.entry then .fatal .unsupportedEntry state
  else if request.hardwareError != request.entry.hardwareError then
    .fatal .wrongErrorShape state
  else match checkedRemaining (usableBytes layout) (requiredBytes request) with
  | none => .fatal .insufficientBudget state
  | some remaining =>
      .accepted
        { stackIdentity := layout.stackIdentity
          stackFirst := layout.usable.first
          stackPastLast := layout.usable.pastLast
          stackTop := layout.stackTop
          requiredBytes := requiredBytes request
          remainingBytes := remaining
          purpose := purposeFor request.entry (frameOrigin request.frame) }
        state

theorem authorize_preserves_state (State : Type) layout reserved request (state : State) :
    resultState (authorize layout reserved request state) = state := by
  unfold authorize
  split <;> try rfl
  split <;> try rfl
  split <;> try rfl
  split <;> rfl

theorem fatal_preserves_composite_state (State : Type) layout reserved request
    (before : State) reason (after : State)
    (hfatal : authorize layout reserved request before = .fatal reason after) :
    after = before := by
  have hstate := authorize_preserves_state State layout reserved request before
  rw [hfatal] at hstate
  exact hstate

theorem accepted_budget_sound (State : Type) layout reserved request (state : State)
    budget (acceptedState : State)
    (haccepted : authorize layout reserved request state = .accepted budget acceptedState) :
    acceptedState = state ∧
      budget.stackIdentity = layout.stackIdentity ∧
      budget.stackFirst = layout.usable.first ∧
      budget.stackPastLast = layout.usable.pastLast ∧
      budget.stackTop = layout.stackTop ∧
      budget.requiredBytes = requiredBytes request ∧
      budget.remainingBytes + budget.requiredBytes = usableBytes layout := by
  unfold authorize at haccepted
  split at haccepted <;> try contradiction
  split at haccepted <;> try contradiction
  split at haccepted <;> try contradiction
  split at haccepted <;> try contradiction
  rename_i remaining hremaining
  cases haccepted
  have hsound := checkedRemaining_sound _ _ _ hremaining
  simp_all

theorem accepted_contract_conditions (State : Type) layout reserved request (state : State)
    budget (acceptedState : State)
    (haccepted : authorize layout reserved request state = .accepted budget acceptedState) :
    layoutValid layout reserved = true ∧
      entrySupported request.entry = true ∧
      request.hardwareError = request.entry.hardwareError := by
  have hlayout : layoutValid layout reserved = true := by
    cases hvalue : layoutValid layout reserved
    · simp [authorize, hvalue] at haccepted
    · rfl
  have hentry : entrySupported request.entry = true := by
    cases hvalue : entrySupported request.entry
    · simp [authorize, hlayout, hvalue] at haccepted
    · rfl
  have herror : request.hardwareError = request.entry.hardwareError := by
    cases hleft : request.hardwareError <;> cases hright : request.entry.hardwareError
    · rfl
    · simp [authorize, hlayout, hentry, hleft, hright] at haccepted
    · simp [authorize, hlayout, hentry, hleft, hright] at haccepted
    · rfl
  exact ⟨hlayout, hentry, herror⟩

theorem insufficient_budget_is_atomic (State : Type) layout reserved request (state : State)
    (hlayout : layoutValid layout reserved = true)
    (hentry : entrySupported request.entry = true)
    (herror : request.hardwareError = request.entry.hardwareError)
    (hover : usableBytes layout < requiredBytes request) :
    authorize layout reserved request state = .fatal .insufficientBudget state := by
  simp [authorize, hlayout, hentry, herror,
    checkedRemaining_rejects_over_budget _ _ hover]

/-! Small executable witnesses exercise the shared syscall, timer, user-fault,
and diagnostic-recovery vocabulary without assigning any operation a separate
budget. -/

private def sampleLayout : Layout :=
  { stackIdentity := 1
    guard := ⟨0x7ff000, 0x800000⟩
    usable := ⟨0x800000, 0x804000⟩
    stackTop := 0x804000
    guardAbsent := true
    supervisorWritable := true
    userAccessible := false
    executable := false }

private def requestFor (entry : ManifestEntry) (frame : RawFrame) : BudgetRequest :=
  { entry, frame, hardwareError := entry.hardwareError
    trustedCallBytes := 0
    returnValidationBytes := 0
    safetyMarginBytes := 0 }

example : layoutValid sampleLayout [] = true := by native_decide

example : ∀ entry ∈ manifest,
    ∃ frame, authorize sampleLayout [] (requestFor entry frame) () =
      .accepted
        { stackIdentity := 1, stackFirst := 0x800000, stackPastLast := 0x804000,
          stackTop := 0x804000,
          requiredBytes := requiredBytes (requestFor entry frame),
          remainingBytes := usableBytes sampleLayout - requiredBytes (requestFor entry frame),
          purpose := purposeFor entry (frameOrigin frame) }
        () := by
  intro entry hentry
  simp [manifest] at hentry
  rcases hentry with rfl | rfl | rfl
  · exact ⟨.privilegeChange 0 0x23 0 0 0, by native_decide⟩
  · exact ⟨.privilegeChange 0 0x23 0 0 0, by native_decide⟩
  · exact ⟨.privilegeChange 0 0x23 0 0 0, by native_decide⟩

example :
    ∃ budget, authorize sampleLayout []
      (requestFor pageFaultEntry (.samePrivilege 0 0x08 0)) () =
        .accepted budget () ∧ budget.purpose = .diagnosticRecovery := by
  refine ⟨
    { stackIdentity := 1, stackFirst := 0x800000, stackPastLast := 0x804000,
      stackTop := 0x804000,
      requiredBytes := requiredBytes (requestFor pageFaultEntry (.samePrivilege 0 0x08 0)),
      remainingBytes := usableBytes sampleLayout -
        requiredBytes (requestFor pageFaultEntry (.samePrivilege 0 0x08 0)),
      purpose := .diagnosticRecovery }, ?_⟩
  native_decide

example :
    authorize sampleLayout []
      { requestFor syscallEntry (.privilegeChange 0 0x23 0 0 0) with
        trustedCallBytes := usableBytes sampleLayout }
      () = .fatal .insufficientBudget () := by
  native_decide

end LeanOS.PrivilegeEntryStack
