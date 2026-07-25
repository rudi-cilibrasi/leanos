import LeanOS.DirectPortContainment

/-!
# Shared user-fault containment vocabulary

Issue #150 requires that the real CPL3 divide-error (`#DE`, vector 0) and
breakpoint (`#BP`, vector 3) machine scenarios share **one**
subject-termination/peer-survival implementation and evidence vocabulary with
the page-fault (`#PF`, vector 14) survivor scenario and the denied-port (`#GP`)
scenario of issue #130.  The generalized cleanup/survivor transition and its
reason-independence are already proved in `LeanOS.FaultDispatch`
(`success_state_reason_independent`, `successful_nonresumption`,
`success_reason_vector_binding`) and merged as `SC-USER-FAULT-CLASS-CONTAINMENT`.

This module supplies the concrete executable vocabulary that binds those
abstract results to one shared two-subject pre-state: real normalized `#DE` and
`#BP` entries, the `#PF` entry, and the `#GP` port-denial composition all drive
`FaultDispatch.dispatch` to retire subject A (1) and dispatch survivor B (2)
through the identical post-state.  Only the typed reason differs; no reason
selects a distinct cleanup, survivor, or address-space variant, and no raw
saved-RIP restart class rewrites A's continuation.  x86 `#DE`/`#BP`/`#PF`
delivery, gate loads, the normalizer-to-machine refinement, generated code, and
the final binary remain trusted boundaries rather than theorem claims.
-/
namespace LeanOS.UserFaultContainmentVocabulary

open LeanOS
open LeanOS.DirectPortContainment

/-- Kernel-owned entry context matching the shared two-subject pre-state:
subject A (1) current in address space 1. -/
def sharedContext : InterruptEntry.KernelContext :=
  { currentSubject := 1
    activeAddressSpace := 1
    activeCr3 := 0
    stackIdentity := 1
    stackFirst := 0x800000
    stackPastLast := 0x804000
    entryActive := false }

/-- Raw CPL3 divide-error snapshot: vector 0, no architectural error word, and
faulting-instruction saved-RIP evidence for the reviewed `DIV`/`IDIV` boundary. -/
def divideErrorRaw : InterruptEntry.RawEntry :=
  { boundVector := 0
    boundStub := 0
    errorCode := none
    restartClass := .faultingInstruction
    frame := .privilegeChange 0x400200 0x23 0x202 0x500ff8 0x1b
    frameBytes := 40
    frameAddress := 0x800000
    acCleared := true
    dfCleared := true }

/-- Raw CPL3 breakpoint snapshot: vector 3, no error word, and following-boundary
saved-RIP evidence for the reviewed post-`INT3` boundary. -/
def breakpointRaw : InterruptEntry.RawEntry :=
  { divideErrorRaw with
    boundVector := 3
    boundStub := 3
    restartClass := .followingBoundary }

/-- Normalized real divide-error entry over the shared kernel context. -/
def divideErrorEntry : InterruptEntry.Result :=
  InterruptEntry.normalize divideErrorRaw sharedContext

/-- Normalized real breakpoint entry over the shared kernel context. -/
def breakpointEntry : InterruptEntry.Result :=
  InterruptEntry.normalize breakpointRaw sharedContext

/-- The normalized entries are exactly the reviewed user-fault records: vector,
purpose, origin, and error convention are bound by the manifest, never by any
raw payload word. -/
theorem contained_entries_normalized :
    divideErrorEntry = .accepted
      { vector := 0, purpose := .userFault, origin := .user, errorCode := none
        rip := 0x400200, cs := 0x23, flags := 0x202
        userRsp := some 0x500ff8, userSs := some 0x1b
        currentSubject := 1, activeAddressSpace := 1, activeCr3 := 0
        stackIdentity := 1 } ∧
      breakpointEntry = .accepted
      { vector := 3, purpose := .userFault, origin := .user, errorCode := none
        rip := 0x400200, cs := 0x23, flags := 0x202
        userRsp := some 0x500ff8, userSs := some 0x1b
        currentSubject := 1, activeAddressSpace := 1, activeCr3 := 0
        stackIdentity := 1 } := by
  native_decide

/-- The four reviewed contained CPL3 entry shapes drive **one** shared
transition over the two-subject pre-state: the real `#DE`, real `#BP`, and `#PF`
entries all dispatch survivor B (subject 2) with the typed reason bound to the
manifest vector, the `#GP` port-denial composition reuses the identical
vector-14 dispatch, and every successful post-state is byte-for-byte the
page-fault post-state. -/
theorem shared_contained_classes_one_transition :
    (FaultDispatch.dispatch witnessSchedule divideErrorEntry).action =
        .dispatch .divideError witnessSurvivorContext ∧
      (FaultDispatch.dispatch witnessSchedule breakpointEntry).action =
        .dispatch .breakpoint witnessSurvivorContext ∧
      (FaultDispatch.dispatch witnessSchedule witnessEntry).action =
        .dispatch .pageFault witnessSurvivorContext ∧
      (containDeniedPort witnessDevices DirectPortIO.selectedControls serialProbe
          witnessSchedule witnessEntry).fault.state =
        (FaultDispatch.dispatch witnessSchedule witnessEntry).state ∧
      (FaultDispatch.dispatch witnessSchedule divideErrorEntry).state =
        (FaultDispatch.dispatch witnessSchedule witnessEntry).state ∧
      (FaultDispatch.dispatch witnessSchedule breakpointEntry).state =
        (FaultDispatch.dispatch witnessSchedule witnessEntry).state := by
  refine ⟨by native_decide, by native_decide, by native_decide, rfl, ?_, ?_⟩
  · exact FaultDispatch.success_state_reason_independent witnessSchedule _ _
      (Or.inr ⟨.divideError, witnessSurvivorContext, by native_decide⟩)
      (Or.inr ⟨.pageFault, witnessSurvivorContext, by native_decide⟩)
  · exact FaultDispatch.success_state_reason_independent witnessSchedule _ _
      (Or.inr ⟨.breakpoint, witnessSurvivorContext, by native_decide⟩)
      (Or.inr ⟨.pageFault, witnessSurvivorContext, by native_decide⟩)

/-- Kernel-origin (same-privilege) raw divide-error snapshot. -/
def divideErrorKernelRaw : InterruptEntry.RawEntry :=
  { divideErrorRaw with
    frame := .samePrivilege 0x100000 0x08 0x202
    frameBytes := 24 }

/-- Kernel-origin (same-privilege) raw breakpoint snapshot. -/
def breakpointKernelRaw : InterruptEntry.RawEntry :=
  { breakpointRaw with
    frame := .samePrivilege 0x100000 0x08 0x202
    frameBytes := 24 }

/-- Kernel-origin (same-privilege) real `#DE` and `#BP` snapshots are terminal
normalizer rejections, never containment: the user-only origin policy of the
reviewed vector-0/3 gates rejects a CPL0 occurrence with `wrongOrigin`. -/
theorem kernel_origin_contained_entries_rejected :
    InterruptEntry.normalize divideErrorKernelRaw sharedContext = .fatal .wrongOrigin ∧
      InterruptEntry.normalize breakpointKernelRaw sharedContext = .fatal .wrongOrigin := by
  native_decide

/-- Both real contained classes retire subject A (1) from live/runnable
identity, the ready queue, the current slot, and the resumable context bank,
and select survivor B (2) — the shared non-resumption boundary. -/
theorem contained_classes_retire_faulting_select_survivor :
    (FaultDispatch.dispatch witnessSchedule divideErrorEntry).state.scheduler.lifecycle.capabilities.subjects 1 = false ∧
      (FaultDispatch.dispatch witnessSchedule divideErrorEntry).state.scheduler.lifecycle.current = some 2 ∧
      ResumablePreemption.contextFor
        (FaultDispatch.dispatch witnessSchedule divideErrorEntry).state.contexts 1 = none ∧
      (FaultDispatch.dispatch witnessSchedule breakpointEntry).state.scheduler.lifecycle.capabilities.subjects 1 = false ∧
      (FaultDispatch.dispatch witnessSchedule breakpointEntry).state.scheduler.lifecycle.current = some 2 ∧
      ResumablePreemption.contextFor
        (FaultDispatch.dispatch witnessSchedule breakpointEntry).state.contexts 1 = none := by
  native_decide

end LeanOS.UserFaultContainmentVocabulary
