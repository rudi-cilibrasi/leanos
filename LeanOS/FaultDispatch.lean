import LeanOS.InterruptEntry
import LeanOS.ResumablePreemption
import LeanOS.BootPageTablePlan

/-!
# Atomic user-fault cleanup and survivor dispatch

This is the first composition slice between the normalized inbound interrupt
contract and the authoritative scheduler/context-bank state.  A valid CPL3
page fault, divide error, or breakpoint terminates the kernel-selected current
subject and selects the next context in one total transition; the typed
contained reason is carried in the outcome but never selects a cleanup or
survivor variant. Kernel faults and every inbound `.fatal` result halt; stale
authoritative bindings reject without exposing cleanup.
-/
namespace LeanOS.FaultDispatch

open LeanOS
set_option linter.unusedSimpArgs false

inductive RejectReason where
  | wrongPurpose | staleCurrent | staleAddressSpace
  | scheduler (reason : Scheduler.Error) | missingContext | staleContext
  deriving DecidableEq, Repr

inductive PageFaultDenial where
  | notPresent | supervisor | readOnly | noExecute
  deriving BEq, DecidableEq, Repr

inductive PageFaultIntegrityReason where
  | malformedSnapshot | provenanceMismatch | unsupportedAddressSpace
  | wrongRoot | staleMapping | incoherentTlb | accessAllowed
  | liveTableReport (cause : BootPageTablePlan.ReportError)
  | walkIntegrity (cause : X86PageTable.WalkError) | walkMismatch
  deriving BEq, DecidableEq, Repr

inductive FatalReason where
  | entry (reason : InterruptEntry.RejectReason)
  | kernelOrigin
  | pageFaultIntegrity (reason : PageFaultIntegrityReason)
  | alreadyHalted
  deriving DecidableEq, Repr

inductive Action where
  | idle (reason : InterruptEntry.ContainedReason)
  | dispatch (reason : InterruptEntry.ContainedReason)
      (context : ResumablePreemption.Context)
  | rejected (reason : RejectReason)
  | fatal (reason : FatalReason)
  deriving DecidableEq, Repr

structure Outcome where
  state : ResumablePreemption.State
  action : Action

def reject (state : ResumablePreemption.State) (reason : RejectReason) : Outcome :=
  { state, action := .rejected reason }

def halt (state : ResumablePreemption.State) (reason : FatalReason) : Outcome :=
  { state := { state with halted := true }, action := .fatal reason }

/-- The per-class shape gate: the manifest-bound vector, the shared user-fault
purpose, CPL3 origin, and the reviewed per-reason error convention. -/
def validUserFaultFor (reason : InterruptEntry.ContainedReason)
    (frame : InterruptEntry.NormalizedFrame) : Bool :=
  frame.vector = reason.vector && frame.purpose = .userFault && frame.origin = .user &&
    frame.errorCode.isSome = reason.hasErrorWord && frame.cs % 4 = 3 &&
    frame.userRsp.isSome && frame.userSs.isSome

/-- The generalized containment gate over every reviewed contained class. -/
def validUserFault (frame : InterruptEntry.NormalizedFrame) : Bool :=
  match InterruptEntry.containedReason? frame.vector with
  | some reason => validUserFaultFor reason frame
  | none => false

/-- The generalized gate is exactly the per-class gate under the
manifest-bound reason decode; `dispatch` evaluates the right-hand side. -/
theorem validUserFault_iff frame :
    validUserFault frame = true ↔
      ∃ reason, InterruptEntry.containedReason? frame.vector = some reason ∧
        validUserFaultFor reason frame = true := by
  unfold validUserFault
  split <;> simp_all

/-- Atomically consume one normalized contained user fault (page fault, divide
error, or breakpoint).  Destination identity comes only from
`Scheduler.selectNext`; the selected kernel-owned context is consumed from the
existing resumable bank and its address space is installed through the
existing TLB transition.  The typed reason is decoded from the manifest-bound
vector alone and never chooses a different cleanup or survivor rule. -/
def dispatch (state : ResumablePreemption.State)
    (entry : InterruptEntry.Result) : Outcome :=
  if state.halted then halt state .alreadyHalted
  else match entry with
  | .fatal reason => halt state (.entry reason)
  | .accepted frame =>
      if frame.origin = .kernel then halt state .kernelOrigin
      else match InterruptEntry.containedReason? frame.vector with
      | none => reject state .wrongPurpose
      | some reason =>
      if !validUserFaultFor reason frame then reject state .wrongPurpose
      else match state.scheduler.lifecycle.current with
      | none => reject state .staleCurrent
      | some current =>
          if frame.currentSubject != current ||
              state.scheduler.lifecycle.capabilities.subjects current != true ||
              state.scheduler.lifecycle.runnable current != true then
            reject state .staleCurrent
          else if frame.activeAddressSpace != current ||
              state.scheduler.lifecycle.addressOwner current != some current ||
              state.translations.active != some current ||
              state.translations.virtual.owner current != some current then
            reject state .staleAddressSpace
          else
            let cleaned := ResumablePreemption.cleanupSubject state current
            let selected := Scheduler.selectNext cleaned.scheduler
            match selected.result with
            | .rejected reason => reject state (.scheduler reason)
            | .accepted none =>
                { state := { cleaned with scheduler := selected.state }, action := .idle reason }
            | .accepted (some trusted) =>
                match ResumablePreemption.contextFor cleaned.contexts
                    trusted.currentSubject with
                | none => reject state .missingContext
                | some context =>
                    if context.owner != trusted.currentSubject ||
                        context.addressSpace != trusted.activeAddressSpace ||
                        Interrupt.validSavedUserFrame context.frame != true ||
                        selected.state.lifecycle.capabilities.subjects context.owner != true ||
                        selected.state.lifecycle.runnable context.owner != true ||
                        selected.state.lifecycle.addressOwner context.addressSpace !=
                          some context.owner ||
                        state.translations.virtual.owner context.addressSpace !=
                          some context.owner ||
                        cleaned.translations.virtual.owner context.addressSpace !=
                          some context.owner then
                      reject state .staleContext
                    else
                      { state := { cleaned with
                          scheduler := selected.state
                          contexts := ResumablePreemption.eraseContext cleaned.contexts context.owner
                          translations := TLB.switch cleaned.translations context.addressSpace }
                        action := .dispatch reason context }

/-! ## Canonical page-fault/page-table agreement gate

The stronger vector-14 boundary consumes issue #168's exact codec and action
authorizer.  The proof-carrying boot plan and bounded decoded live-root report
are read-only views retained by the global runtime; no second CR3 map,
page-table store, scheduler, or lifecycle projection is introduced here.
Successful agreement delegates to `dispatch`, so cleanup and survivor
selection remain the single transition above. -/

def selectedBootSpace : VirtualMapping.AddressSpaceId →
    Option BootPageTablePlan.Space
  | 1 => some .subjectA
  | 2 => some .subjectB
  | _ => none

def expectedCr3 (plan : BootPageTablePlan.Plan)
    (space : BootPageTablePlan.Space) : UInt64 :=
  UInt64.ofNat (plan.rootFrame space * X86PageTable.pageBytes)

def decodedAncestorAt (entries : List BootPageTablePlan.DecodedAncestor)
    (index : Nat) : X86PageTable.Ancestor :=
  match entries[index]? with
  | none => { present := false, writable := false, user := false }
  | some entry =>
      { present := entry.present, writable := entry.writable, user := entry.user }

/-- The page-local x86 view decoded from the bounded report rooted at the CR3
selected by the kernel.  The report retains all slots for whole-root
validation; classification projects only the ancestor path and leaf selected
by CR2. -/
def livePageTableAt (report : BootPageTablePlan.DecodedRoot)
    (page : Nat) : X86PageTable.PageTable :=
  { pml4 := decodedAncestorAt report.pml4Entries 0
    pdpt := decodedAncestorAt report.pdptEntries 0
    pd := decodedAncestorAt report.pdEntries (page / X86PageTable.entriesPerTable)
    leaf := BootPageTablePlan.actualAt report }

def pageFaultAccessContext (snapshot : InterruptEntry.CanonicalPageFault) :
    X86PageTable.AccessContext :=
  { privilege := .user
    kind :=
      if snapshot.accessCode = 2 then .execute
      else if snapshot.accessCode = 1 then .write
      else .read
    writeProtect := snapshot.controlsCode % 2 = 1
    nxEnable := snapshot.controlsCode / 2 % 2 = 1
    smep := snapshot.controlsCode / 4 % 2 = 1
    smap := snapshot.controlsCode / 8 % 2 = 1
    ac := false }

/-- The active boot-plan leaf and the live virtual/lifetime projection agree
at the checked CR2 page.  Supervisor leaves are plan-owned and must not be
shadowed by a user mapping.  User leaves must name the exact current live
object/frame binding and permissions in both lifecycle projections. -/
def livePlanAgreement (state : ResumablePreemption.State)
    (plan : BootPageTablePlan.Plan) (space : BootPageTablePlan.Space)
    (addressSpace : VirtualMapping.AddressSpaceId)
    (page : VirtualMapping.VirtualPage) : Bool :=
  let virtual := state.translations.virtual
  let lifecycle := state.scheduler.lifecycle
  match BootPageTablePlan.expectedAt plan space page,
      virtual.mappings addressSpace page with
  | none, none => lifecycle.mapping addressSpace page = none
  | none, some _ => false
  | some leaf, none =>
      !leaf.user && lifecycle.mapping addressSpace page = none
  | some leaf, some mapping =>
      if !leaf.user then false
      else
        match virtual.memory.binding mapping.object with
        | none => false
        | some frame =>
            virtual.memory.issued mapping.object &&
              virtual.memory.capabilities.objects mapping.object &&
              virtual.memory.capabilities.kinds mapping.object = some .memory &&
              lifecycle.capabilities.objects mapping.object &&
              lifecycle.capabilities.kinds mapping.object = some .memory &&
              virtual.memory.allocator.status frame = .owned mapping.object &&
              lifecycle.ownedMemory mapping.object = some (addressSpace, frame) &&
              lifecycle.frameOwner frame = some addressSpace &&
              !lifecycle.freeFrame frame &&
              leaf.frame = frame && mapping.permissions.read &&
              leaf.writable = mapping.permissions.write &&
              lifecycle.mapping addressSpace page = some mapping.object

def pageFaultTlbCoherent (state : ResumablePreemption.State)
    (addressSpace : VirtualMapping.AddressSpaceId)
    (page : VirtualMapping.VirtualPage)
    (context : X86PageTable.AccessContext) : Bool :=
  state.translations.entries.length ≤ TLB.capacity &&
    TLB.lookup state.translations.entries { addressSpace, page } context = none

def activeFaultAddressSpace (state : ResumablePreemption.State) :
    VirtualMapping.AddressSpaceId :=
  state.translations.active.getD 0

def denialAgreement (decoded : InterruptEntry.DecodedPageFaultError)
    (cause : X86PageTable.WalkError) : Option PageFaultDenial :=
  if !decoded.protection then
    if cause = .notPresent then some .notPresent else none
  else
    match cause, decoded.accessKind with
    | .supervisor, _ => some .supervisor
    | .notWritable, .write => some .readOnly
    | .noExecute, .execute => some .noExecute
    | _, _ => none

def pageFaultClassificationAgreement (plan : BootPageTablePlan.Plan)
    (_space : BootPageTablePlan.Space)
    (report : BootPageTablePlan.DecodedRoot)
    (snapshot : InterruptEntry.CanonicalPageFault)
    (decoded : InterruptEntry.DecodedPageFaultError) :
    Except PageFaultIntegrityReason PageFaultDenial :=
  let context := pageFaultAccessContext snapshot
  match X86PageTable.classify (livePageTableAt report snapshot.faultPage.toNat)
      snapshot.faultPage.toNat context with
  | .ok _ => throw .accessAllowed
  | .error cause =>
      if cause = .reservedBits || cause = .frameOutOfRange then
        throw (.walkIntegrity cause)
      else
        match BootPageTablePlan.validateDecodedRoot plan report with
        | .error reportCause => throw (.liveTableReport reportCause)
        | .ok _ =>
          match denialAgreement decoded cause with
          | some denial => pure denial
          | none => throw .walkMismatch

/-- Finite agreement between the canonical architectural error class and the
decoded live table rooted at the kernel-selected active CR3. Integrity walk
failures are classified before whole-report validation; every ordinary denial
requires the complete report to match the proof-carrying plan. -/
def pageFaultAgreement (state : ResumablePreemption.State)
    (plan : BootPageTablePlan.Plan)
    (report : BootPageTablePlan.DecodedRoot)
    (snapshot : InterruptEntry.CanonicalPageFault) :
    Except PageFaultIntegrityReason PageFaultDenial :=
  if !InterruptEntry.validCanonicalPageFault snapshot then
    .error .malformedSnapshot
  else
    let addressSpace := activeFaultAddressSpace state
    match selectedBootSpace addressSpace with
    | none => .error .unsupportedAddressSpace
    | some space =>
        if report.space ≠ space then
          .error (.liveTableReport .wrongRoot)
        else if report.selectedRoot ≠ plan.rootFrame space then
          .error (.liveTableReport .wrongRoot)
        else if snapshot.activeCr3 != expectedCr3 plan space then .error .wrongRoot
        else if snapshot.controlsCode != 15 then .error .provenanceMismatch
        else if !livePlanAgreement state plan space addressSpace
            snapshot.faultPage.toNat then .error .staleMapping
        else
          let context := pageFaultAccessContext snapshot
          if !pageFaultTlbCoherent state addressSpace snapshot.faultPage.toNat
              context then .error .incoherentTlb
          else
            match InterruptEntry.decodePageFaultError snapshot.errorWord with
            | .error _ => .error .malformedSnapshot
            | .ok decoded =>
                if decoded.write && decoded.instructionFetch then
                  .error .malformedSnapshot
                else
                  pageFaultClassificationAgreement plan space report snapshot decoded

def canonicalPageFaultFrame
    (snapshot : InterruptEntry.CanonicalPageFault) :
    InterruptEntry.NormalizedFrame :=
  { vector := snapshot.vector
    purpose := .userFault
    origin := .user
    errorCode := some snapshot.errorWord
    rip := snapshot.rip
    cs := snapshot.cs
    flags := snapshot.flags
    userRsp := some snapshot.userRsp
    userSs := some snapshot.userSs
    currentSubject := snapshot.currentSubject.toNat
    activeAddressSpace := snapshot.activeAddressSpace.toNat
    activeCr3 := snapshot.activeCr3
    stackIdentity := snapshot.stackIdentity }

/-- Strengthened page-fault entry point.  Stale nonfatal scheduler bindings
reject atomically before cleanup.  Once the canonical snapshot has an
integrity-class failure, the existing fatal latch is set and every
authoritative store is frozen.  Only a matching ordinary denial reaches the
shared cleanup/survivor transition. -/
def dispatchPageFault (state : ResumablePreemption.State)
    (plan : BootPageTablePlan.Plan) (report : BootPageTablePlan.DecodedRoot)
    (words : List UInt64)
    (trusted : InterruptEntry.PageFaultContext) : Outcome :=
  if state.halted then halt state .alreadyHalted
  else match InterruptEntry.decodeCanonicalPageFault words with
  | none => halt state (.pageFaultIntegrity .malformedSnapshot)
  | some snapshot =>
      if snapshot.privilegeCode != 1 then halt state .kernelOrigin
      else match state.scheduler.lifecycle.current with
      | none => reject state .staleCurrent
      | some current =>
          if trusted.entry.currentSubject != current ||
              state.scheduler.lifecycle.capabilities.subjects current != true ||
              state.scheduler.lifecycle.runnable current != true then
            reject state .staleCurrent
          else if trusted.entry.activeAddressSpace != current ||
              state.scheduler.lifecycle.addressOwner current != some current ||
              state.translations.active != some current ||
              state.translations.virtual.owner current != some current then
            reject state .staleAddressSpace
          else
            let authorized :=
              InterruptEntry.authorizeCanonicalPageFault words trusted state
            match authorized.authorized with
            | none => halt state (.pageFaultIntegrity .provenanceMismatch)
            | some checked =>
                match pageFaultAgreement state plan report checked with
                | .error reason => halt state (.pageFaultIntegrity reason)
                | .ok _ =>
                    dispatch state (.accepted (canonicalPageFaultFrame checked))

theorem dispatchPageFault_total state plan report words trusted :
    ∃ outcome, dispatchPageFault state plan report words trusted = outcome :=
  ⟨_, rfl⟩

theorem dispatchPageFault_deterministic state plan report words trusted first second
    (hfirst : dispatchPageFault state plan report words trusted = first)
    (hsecond : dispatchPageFault state plan report words trusted = second) :
    first = second := by
  rw [← hfirst, hsecond]

/-- Once the stronger page-fault boundary sets the halt latch, every later
page-fault input is absorbed before decoding or consulting trusted context. -/
theorem dispatchPageFault_already_halted_absorbing state plan report words trusted
    (hhalted : state.halted = true) :
    dispatchPageFault state plan report words trusted = halt state .alreadyHalted := by
  simp [dispatchPageFault, hhalted]

theorem denialAgreement_sound decoded cause denial
    (h : denialAgreement decoded cause = some denial) :
    (decoded.protection = false ∧ cause = .notPresent ∧
        denial = .notPresent) ∨
      (decoded.protection = true ∧ cause = .supervisor ∧
        denial = .supervisor) ∨
      (decoded.protection = true ∧ decoded.accessKind = .write ∧
        cause = .notWritable ∧ denial = .readOnly) ∨
      (decoded.protection = true ∧ decoded.accessKind = .execute ∧
        cause = .noExecute ∧ denial = .noExecute) := by
  unfold denialAgreement at h
  split at h <;> simp_all
  all_goals split at h <;> simp_all
  all_goals split at h <;> simp_all


/-- Explicit attacker data is not consulted by fault cleanup or survivor
selection. -/
def dispatchWithPayload {Payload : Type} (state : ResumablePreemption.State)
    (entry : InterruptEntry.Result) (_payload : Payload) : Outcome :=
  dispatch state entry

theorem attacker_payload_independent {Payload : Type} state entry
    (left right : Payload) :
    dispatchWithPayload state entry left = dispatchWithPayload state entry right := by
  rfl

theorem total state entry : ∃ outcome, dispatch state entry = outcome :=
  ⟨_, rfl⟩

theorem deterministic state entry first second
    (hfirst : dispatch state entry = first)
    (hsecond : dispatch state entry = second) : first = second := by
  rw [← hfirst, hsecond]

/-- Every typed nonfatal rejection is atomic: lifecycle, scheduler queue,
context bank, mappings, translations, and the halt latch are all unchanged. -/
theorem rejected_unchanged state entry reason
    (h : (dispatch state entry).action = .rejected reason) :
    (dispatch state entry).state = state := by
  simp only [dispatch] at h ⊢
  split <;> simp_all [halt, reject]
  split <;> simp_all [halt, reject]
  all_goals split <;> simp_all [halt, reject]
  all_goals split <;> simp_all [halt, reject]
  all_goals split <;> simp_all [halt, reject]
  all_goals split <;> simp_all [halt, reject]
  all_goals split <;> simp_all [halt, reject]
  all_goals split <;> simp_all [halt, reject]
  all_goals split <;> simp_all [halt, reject]
  all_goals split <;> simp_all [halt, reject]
  all_goals split <;> simp_all [halt, reject]
  all_goals split <;> simp_all [halt, reject]
  all_goals split <;> simp_all [halt, reject]
  all_goals split <;> simp_all [halt, reject]

/-- The authoritative fatal primitive changes only the absorbing latch. -/
theorem halt_preserves_authoritative_stores state reason :
    (halt state reason).state.halted = true ∧
      (halt state reason).state.scheduler = state.scheduler ∧
      (halt state reason).state.contexts = state.contexts ∧
      (halt state reason).state.translations = state.translations := by
  simp [halt]

theorem kernel_origin_is_fatal state frame
    (hrunning : state.halted = false)
    (horigin : frame.origin = .kernel) :
    dispatch state (.accepted frame) = halt state .kernelOrigin := by
  simp [dispatch, hrunning, horigin]

theorem nested_is_fatal state (hrunning : state.halted = false) :
    dispatch state (.fatal .nested) = halt state (.entry .nested) := by
  simp [dispatch, hrunning]

/-- Every failure emitted by the inbound normalizer is terminal.  This keeps
the composite consumer aligned with the normalizer's fail-stop contract. -/
theorem entry_failure_is_fatal state reason
    (hrunning : state.halted = false) :
    dispatch state (.fatal reason) = halt state (.entry reason) := by
  simp [dispatch, hrunning]

/-- Once the resumable layer projects the repository fail-stop latch, no later
fault-dispatch input can resume, reject back to a caller, or expose cleanup. -/
theorem already_halted_absorbing state entry (hhalted : state.halted = true) :
    dispatch state entry = halt state .alreadyHalted := by
  simp [dispatch, hhalted]

/-- A dispatched context is exactly the deterministic scheduler selection and
is live, runnable, and address-space-owned in the post-state. -/
theorem dispatched_context_safe state entry reason context
    (h : (dispatch state entry).action = .dispatch reason context) :
    let next := (dispatch state entry).state
    next.scheduler.lifecycle.capabilities.subjects context.owner = true ∧
      next.scheduler.lifecycle.runnable context.owner = true ∧
      next.scheduler.lifecycle.addressOwner context.addressSpace = some context.owner ∧
      next.translations.virtual.owner context.addressSpace = some context.owner := by
  generalize hd : dispatch state entry = outcome at h ⊢
  cases outcome with
  | mk next action =>
    simp only at h ⊢
    subst action
    simp only [dispatch] at hd
    split at hd <;> try simp_all [halt, reject]
    split at hd <;> try simp_all [halt, reject]
    all_goals split at hd <;> try simp_all [halt, reject]
    all_goals split at hd <;> try simp_all [halt, reject]
    all_goals split at hd <;> try simp_all [halt, reject]
    all_goals split at hd <;> try simp_all [halt, reject]
    all_goals split at hd <;> try simp_all [halt, reject]
    all_goals split at hd <;> try simp_all [halt, reject]
    all_goals split at hd <;> try simp_all [halt, reject]
    all_goals split at hd <;> try simp_all [halt, reject]
    all_goals split at hd <;> try simp_all [halt, reject]
    all_goals rcases hd with ⟨rfl, rfl, rfl⟩
    all_goals simp_all [TLB.switch]
    all_goals grind

/-- The cleanup primitive used by every successful branch removes both live
identity and the authoritative resumable slot for the faulting subject. -/
theorem cleanup_nonresumption state subject :
    ResumablePreemption.contextFor
        (ResumablePreemption.cleanupSubject state subject).contexts subject = none ∧
      (ResumablePreemption.cleanupSubject state subject).scheduler.lifecycle.capabilities.subjects
        subject = false :=
  ⟨ResumablePreemption.cleanup_removes_context state subject,
    ResumablePreemption.cleanup_terminates_subject state subject⟩

/-- A survivor-dispatch outcome carries the cleanup boundary into the returned
state: the faulting subject is dead, absent from the ready queue and current
slot, and has no resumable context. -/
theorem dispatched_nonresumption state entry reason context
    (hdispatch : (dispatch state entry).action = .dispatch reason context) :
    ∃ faulting,
      state.scheduler.lifecycle.current = some faulting ∧
        (dispatch state entry).state.scheduler.lifecycle.capabilities.subjects
          faulting = false ∧
        faulting ∉ (dispatch state entry).state.scheduler.ready ∧
        (dispatch state entry).state.scheduler.lifecycle.current ≠ some faulting ∧
        ResumablePreemption.contextFor
          (dispatch state entry).state.contexts faulting = none := by
  generalize hd : dispatch state entry = outcome at hdispatch ⊢
  cases outcome with
  | mk next action =>
    simp only at hdispatch ⊢
    subst action
    simp only [dispatch] at hd
    split at hd <;> try simp_all [halt, reject]
    split at hd <;> try simp_all [halt, reject]
    all_goals split at hd <;> try simp_all [halt, reject]
    all_goals split at hd <;> try simp_all [halt, reject]
    all_goals split at hd <;> try simp_all [halt, reject]
    all_goals split at hd <;> try simp_all [halt, reject]
    all_goals split at hd <;> try simp_all [halt, reject]
    all_goals split at hd <;> try simp_all [halt, reject]
    all_goals split at hd <;> try simp_all [halt, reject]
    all_goals split at hd <;> try simp_all [halt, reject]
    all_goals split at hd <;> try simp_all [halt, reject]
    all_goals rcases hd with ⟨rfl, rfl, rfl⟩
    all_goals
      let faulting := state.scheduler.lifecycle.current.getD 0
      have hdead := ResumablePreemption.cleanup_terminates_subject state faulting
      have habsent := ResumablePreemption.cleanup_removes_scheduler_membership state faulting
      have hcontext := ResumablePreemption.cleanup_removes_context state faulting
      simp_all only [Option.getD_some]
      grind [Scheduler.selectNext, Scheduler.reject,
        ResumablePreemption.eraseContext, ResumablePreemption.contextFor,
        List.find?_eq_none]

private theorem cleanupCurrent_preserves_coreWellFormed state subject
    (hstate : ResumablePreemption.WellFormed state) :
    ResumablePreemption.CleanupCoreWellFormed
      (ResumablePreemption.cleanupSubject state subject) := by
  exact ResumablePreemption.cleanupSubject_preserves_coreWellFormed
    state subject hstate

/-- Fault dispatch preserves the scheduler/lifecycle invariant and the bounded
no-PCID translation-cache invariant as one composite transition. -/
theorem dispatch_preserves_scheduler_and_tlb state entry
    (hstate : ResumablePreemption.WellFormed state) :
    Scheduler.WellFormed (dispatch state entry).state.scheduler ∧
      TLB.Coherent (dispatch state entry).state.translations := by
  have hparts := hstate
  rcases hparts with ⟨hscheduler, _, _, _, _, _, _, _, _, htlb⟩
  simp only [dispatch]
  all_goals (try split) <;> try simp_all [halt, reject]
  all_goals (try split) <;> try simp_all [halt, reject]
  all_goals (try split) <;> try simp_all [halt, reject]
  all_goals (try split) <;> try simp_all [halt, reject]
  all_goals (try split) <;> try simp_all [halt, reject]
  all_goals (try split) <;> try simp_all [halt, reject]
  all_goals (try split) <;> try simp_all [halt, reject]
  all_goals (try split) <;> try simp_all [halt, reject]
  all_goals (try split) <;> try simp_all [halt, reject]
  all_goals (try split) <;> try simp_all [halt, reject]
  all_goals (try split) <;> try simp_all [halt, reject]
  all_goals (try split) <;> try simp_all [halt, reject]
  all_goals
    have hcore := cleanupCurrent_preserves_coreWellFormed state
      (state.scheduler.lifecycle.current.getD 0) hstate
    simp_all
    rcases hcore with ⟨hcleanScheduler, _, _, _, _, _, _, hcleanTlb⟩
    constructor
    · exact Scheduler.selectNext_preserves_wellFormed _ hcleanScheduler
    · first | exact hcleanTlb | exact TLB.switch_coherent _ _

private theorem consumeSelected_preserves_wellFormed state trusted context
    (hstate : ResumablePreemption.WellFormed state)
    (hselected : (Scheduler.selectNext state.scheduler).result =
      .accepted (some trusted))
    (hcontext : ResumablePreemption.contextFor state.contexts
      trusted.currentSubject = some context) :
    ResumablePreemption.WellFormed
      { state with
        scheduler := (Scheduler.selectNext state.scheduler).state
        contexts := ResumablePreemption.eraseContext state.contexts context.owner
        translations := TLB.switch state.translations context.addressSpace } := by
  rcases hstate with
    ⟨hscheduler, hcapacity, hunique, hvalid, habsent, hagreement,
      htranslations, hvirtual, hkinds, htlb⟩
  have hcontextOwner := ResumablePreemption.contextFor_owner _ _ _ hcontext
  simp only [Scheduler.selectNext] at hselected
  split at hselected <;> try simp_all [Scheduler.reject]
  split at hselected <;> try simp_all [Scheduler.reject]
  all_goals
    have hcontextMem := List.mem_of_find?_eq_some hcontext
    have hcontextValid := hvalid context hcontextMem
    have hcontextSpace : context.addressSpace = trusted.activeAddressSpace := by
      simp only [ResumablePreemption.validContext] at hcontextValid
      grind [Scheduler.ownsAddressSpace]
    have hpostScheduler := Scheduler.selectNext_preserves_wellFormed
      state.scheduler hscheduler
    have hpostCurrent :
        (Scheduler.selectNext state.scheduler).state.lifecycle.current =
          some trusted.currentSubject := by
      grind [Scheduler.selectNext, Scheduler.reject]
    have hcapabilityProjection :
        (Scheduler.selectNext state.scheduler).state.lifecycle.capabilities =
          state.scheduler.lifecycle.capabilities := by
      grind [Scheduler.selectNext, Scheduler.reject]
    have hrunnable :
        (Scheduler.selectNext state.scheduler).state.lifecycle.runnable =
          state.scheduler.lifecycle.runnable := by
      grind [Scheduler.selectNext, Scheduler.reject]
    have haddressOwner :
        (Scheduler.selectNext state.scheduler).state.lifecycle.addressOwner =
          state.scheduler.lifecycle.addressOwner := by
      grind [Scheduler.selectNext, Scheduler.reject]
    have hownedMemory :
        (Scheduler.selectNext state.scheduler).state.lifecycle.ownedMemory =
          state.scheduler.lifecycle.ownedMemory := by
      grind [Scheduler.selectNext, Scheduler.reject]
    have hendpointOwner :
        (Scheduler.selectNext state.scheduler).state.lifecycle.endpointOwner =
          state.scheduler.lifecycle.endpointOwner := by
      grind [Scheduler.selectNext, Scheduler.reject]
    have hselectedSpace : trusted.activeAddressSpace = trusted.currentSubject := by
      grind [Scheduler.ownsAddressSpace]
    refine ⟨hpostScheduler, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, TLB.switch_coherent _ _⟩
    · exact Nat.le_trans (List.length_filter_le _ _) hcapacity
    · exact hunique.filter _
    · intro retained hretained
      have hold := hvalid retained (List.mem_filter.mp hretained).1
      simpa [ResumablePreemption.validContext, TLB.switch, hcapabilityProjection,
        hrunnable, haddressOwner] using hold
    · intro candidate hcurrent
      have hc : candidate = trusted.currentSubject := by grind
      subst candidate
      exact ResumablePreemption.contextFor_erase_self _ _
    · refine ⟨?_, ?_⟩
      · intro queued hqueued
        have hqueuedOld : queued ∈ state.scheduler.ready := by
          simp [Scheduler.selectNext] at hqueued
          simp_all
        obtain ⟨saved, hsaved, howner⟩ := hagreement.1 queued hqueuedOld
        have hne : saved.owner ≠ trusted.currentSubject := by
          intro heq
          have hnotReady := hpostScheduler.2.2.2.2 trusted.currentSubject
            hpostCurrent |>.2.2.2
          apply hnotReady
          have hqueuedEq : queued = trusted.currentSubject := by
            rw [← howner, heq]
          simpa [hqueuedEq] using hqueued
        exact ⟨saved, by
          simp [ResumablePreemption.eraseContext, hsaved, hne], howner⟩
      · intro retained hretained hsuspended
        have holdMem := (List.mem_filter.mp hretained).1
        have holdReady := hagreement.2 retained holdMem hsuspended
        have hne : retained.owner ≠ trusted.currentSubject := by
          simpa using (List.mem_filter.mp hretained).2
        grind [Scheduler.selectNext, Scheduler.reject]
    · rcases htranslations with ⟨howner, hactive⟩
      constructor
      · simpa [TLB.switch, haddressOwner] using howner
      · simp [TLB.switch, hpostCurrent, hcontextSpace, hselectedSpace]
    · rcases hvirtual with ⟨hvirtualCapabilities, hvirtualWellFormed⟩
      exact ⟨by simpa [TLB.switch, hcapabilityProjection] using hvirtualCapabilities,
        by simpa [TLB.switch] using hvirtualWellFormed⟩
    · simpa [ResumablePreemption.ResourceKindAgreement, TLB.switch,
        hcapabilityProjection, hownedMemory, hendpointOwner] using hkinds

private theorem fatal_state_eq_halt state entry reason
    (h : (dispatch state entry).action = .fatal reason) :
    (dispatch state entry).state = (halt state reason).state := by
  simp only [dispatch] at h ⊢
  split <;> try simp_all [halt, reject]
  split <;> try simp_all [halt, reject]
  all_goals split <;> try simp_all [halt, reject]
  all_goals split <;> try simp_all [halt, reject]
  all_goals split <;> try simp_all [halt, reject]
  all_goals split <;> try simp_all [halt, reject]
  all_goals split <;> try simp_all [halt, reject]
  all_goals split <;> try simp_all [halt, reject]
  all_goals split <;> try simp_all [halt, reject]
  all_goals split <;> try simp_all [halt, reject]
  all_goals split <;> try simp_all [halt, reject]
  all_goals split <;> simp_all [halt, reject]

/-- Every fatal composite result changes only the irreversible latch.  In
particular, it cannot publish partial subject cleanup or a return context. -/
theorem fatal_atomicity state entry reason
    (h : (dispatch state entry).action = .fatal reason) :
    (dispatch state entry).state.halted = true ∧
      (dispatch state entry).state.scheduler = state.scheduler ∧
      (dispatch state entry).state.contexts = state.contexts ∧
      (dispatch state entry).state.translations = state.translations := by
  rw [fatal_state_eq_halt state entry reason h]
  exact halt_preserves_authoritative_stores state reason

private theorem dispatched_is_authoritative_transition state entry reason context
    (h : (dispatch state entry).action = .dispatch reason context) :
    ∃ faulting trusted,
      state.scheduler.lifecycle.current = some faulting ∧
      (Scheduler.selectNext
          (ResumablePreemption.cleanupSubject state faulting).scheduler).result =
        .accepted (some trusted) ∧
      ResumablePreemption.contextFor
          (ResumablePreemption.cleanupSubject state faulting).contexts
          trusted.currentSubject = some context ∧
      (dispatch state entry).state =
        { ResumablePreemption.cleanupSubject state faulting with
          scheduler := (Scheduler.selectNext
            (ResumablePreemption.cleanupSubject state faulting).scheduler).state
          contexts := ResumablePreemption.eraseContext
            (ResumablePreemption.cleanupSubject state faulting).contexts context.owner
          translations := TLB.switch
            (ResumablePreemption.cleanupSubject state faulting).translations
            context.addressSpace } := by
  simp only [dispatch] at h ⊢
  split at h <;> try simp_all [halt, reject]
  split at h <;> try simp_all [halt, reject]
  all_goals split at h <;> try simp_all [halt, reject]
  all_goals split at h <;> try simp_all [halt, reject]
  all_goals split at h <;> try simp_all [halt, reject]
  all_goals split at h <;> try simp_all [halt, reject]
  all_goals split at h <;> try simp_all [halt, reject]
  all_goals split at h <;> try simp_all [halt, reject]
  all_goals split at h <;> try simp_all [halt, reject]
  all_goals split at h <;> try simp_all [halt, reject]
  all_goals split at h <;> try simp_all [halt, reject]
  all_goals rcases h with ⟨rfl⟩
  all_goals grind

/-- A successful dispatch consumes exactly the post-cleanup FIFO head. -/
theorem dispatch_uses_survivor_head state entry reason context
    (h : (dispatch state entry).action = .dispatch reason context) :
    ∃ faulting rest,
      (ResumablePreemption.cleanupSubject state faulting).scheduler.ready =
        context.owner :: rest := by
  simp only [dispatch] at h
  split at h <;> try simp_all [halt, reject]
  split at h <;> try simp_all [halt, reject]
  all_goals split at h <;> try simp_all [halt, reject]
  all_goals split at h <;> try simp_all [halt, reject]
  all_goals split at h <;> try simp_all [halt, reject]
  all_goals split at h <;> try simp_all [halt, reject]
  all_goals split at h <;> try simp_all [halt, reject]
  all_goals split at h <;> try simp_all [halt, reject]
  all_goals split at h <;> try simp_all [halt, reject]
  all_goals split at h <;> try simp_all [halt, reject]
  all_goals split at h <;> try simp_all [halt, reject]
  all_goals grind [Scheduler.selectNext, Scheduler.ownsAddressSpace, Scheduler.reject]

/-- Dispatch consumes the selected survivor's context but leaves every third
subject's suspended context byte-for-byte unchanged.  The two inequalities
name the only context-bank slots removed by the composite transition: the
faulting current subject and the scheduler-selected survivor. -/
theorem dispatch_preserves_unselected_context state entry reason selected faulting other saved
    (hdispatch : (dispatch state entry).action = .dispatch reason selected)
    (hcurrent : state.scheduler.lifecycle.current = some faulting)
    (hsaved : ResumablePreemption.contextFor state.contexts other = some saved)
    (hotherFaulting : other ≠ faulting)
    (hotherSelected : other ≠ selected.owner) :
    ResumablePreemption.contextFor
      (dispatch state entry).state.contexts other = some saved := by
  obtain ⟨actualFaulting, trusted, hactualCurrent, _, hselected, hstate⟩ :=
    dispatched_is_authoritative_transition state entry reason selected hdispatch
  have hfaulting : actualFaulting = faulting := by grind
  subst actualFaulting
  rw [hstate]
  rw [ResumablePreemption.contextFor_erase_other _ _ _ hotherSelected]
  rw [show (ResumablePreemption.cleanupSubject state faulting).contexts =
      ResumablePreemption.eraseContext state.contexts faulting by
    rfl]
  rw [ResumablePreemption.contextFor_erase_other _ _ _ hotherFaulting]
  exact hsaved

/-- Cleanup and scheduler selection leave lifecycle resources owned by a third
subject unchanged.  These hypotheses cover the ownership branches that may be
removed by `SubjectLifecycle.terminateState`; selection itself changes only
the current subject and ready queue. -/
theorem dispatch_preserves_unrelated_resources state entry reason selected faulting owner
    memoryObject frame addressSpace page endpoint
    (hdispatch : (dispatch state entry).action = .dispatch reason selected)
    (hcurrent : state.scheduler.lifecycle.current = some faulting)
    (hmemory : state.scheduler.lifecycle.ownedMemory memoryObject = some (owner, frame))
    (haddress : state.scheduler.lifecycle.addressOwner addressSpace = some owner)
    (hendpoint : state.scheduler.lifecycle.endpointOwner endpoint = some owner)
    (hframe : state.scheduler.lifecycle.frameOwner frame = some owner)
    (howner : owner ≠ faulting) :
    let next := (dispatch state entry).state.scheduler.lifecycle
    next.ownedMemory memoryObject = some (owner, frame) ∧
      next.addressOwner addressSpace = some owner ∧
      next.mapping addressSpace page = state.scheduler.lifecycle.mapping addressSpace page ∧
      next.endpointOwner endpoint = some owner ∧
      next.frameOwner frame = some owner := by
  obtain ⟨actualFaulting, trusted, hactualCurrent, hselected, hcontext, hstate⟩ :=
    dispatched_is_authoritative_transition state entry reason selected hdispatch
  have hfaulting : actualFaulting = faulting := by grind
  subst actualFaulting
  rw [hstate]
  simp [ResumablePreemption.cleanupSubject, Scheduler.selectNext,
    Scheduler.reject, SubjectLifecycle.terminateState, hmemory, haddress,
    hendpoint, hframe, howner] at hselected ⊢
  grind

/-- Idle is exposed only after cleanup and an actually empty survivor queue. -/
private theorem selectNext_none_eq scheduler
    (h : (Scheduler.selectNext scheduler).result = .accepted none) :
    Scheduler.selectNext scheduler = { state := scheduler, result := .accepted none } := by
  grind [Scheduler.selectNext, Scheduler.reject]

theorem idle_is_clean_empty state entry reason
    (h : (dispatch state entry).action = .idle reason) :
    ∃ faulting,
      state.scheduler.lifecycle.current = some faulting ∧
      (dispatch state entry).state = ResumablePreemption.cleanupSubject state faulting ∧
      (dispatch state entry).state.scheduler.ready = [] ∧
      (dispatch state entry).state.scheduler.lifecycle.current = none := by
  simp only [dispatch] at h ⊢
  split at h <;> try simp_all [halt, reject]
  split at h <;> try simp_all [halt, reject]
  all_goals split at h <;> try simp_all [halt, reject]
  all_goals split at h <;> try simp_all [halt, reject]
  all_goals split at h <;> try simp_all [halt, reject]
  all_goals split at h <;> try simp_all [halt, reject]
  all_goals split at h <;> try simp_all [halt, reject]
  all_goals split at h <;> try simp_all [halt, reject]
  all_goals (try split at h) <;> try simp_all [halt, reject]
  all_goals (try split at h) <;> try simp_all [halt, reject]
  all_goals (try split at h) <;> try simp_all [halt, reject]
  all_goals
    have hselected := selectNext_none_eq _ (by assumption)
    simp_all [hselected]
    grind [Scheduler.selectNext, Scheduler.reject]

/-- The idle success branch has the same non-resumption boundary as survivor
dispatch; an empty queue never turns the terminated subject into a fallback. -/
theorem idle_nonresumption state entry reason
    (hidle : (dispatch state entry).action = .idle reason) :
    ∃ faulting,
      state.scheduler.lifecycle.current = some faulting ∧
        (dispatch state entry).state.scheduler.lifecycle.capabilities.subjects
          faulting = false ∧
        faulting ∉ (dispatch state entry).state.scheduler.ready ∧
        (dispatch state entry).state.scheduler.lifecycle.current ≠ some faulting ∧
        ResumablePreemption.contextFor
          (dispatch state entry).state.contexts faulting = none := by
  rcases idle_is_clean_empty state entry reason hidle with
    ⟨faulting, hcurrent, hstate, _, _⟩
  rw [hstate]
  exact ⟨faulting, hcurrent,
    ResumablePreemption.cleanup_terminates_subject state faulting,
    (ResumablePreemption.cleanup_removes_scheduler_membership state faulting).1,
    (ResumablePreemption.cleanup_removes_scheduler_membership state faulting).2,
    ResumablePreemption.cleanup_removes_context state faulting⟩

/-- A successful branch can only start from the authoritative current subject
being live and runnable.  Exposing these facts keeps the stable termination
claim non-vacuous even if the entry gate is later refactored. -/
theorem successful_faulting_live_runnable state entry
    (hsuccess : (∃ reason, (dispatch state entry).action = .idle reason) ∨
      ∃ reason context, (dispatch state entry).action = .dispatch reason context) :
    ∃ faulting,
      state.scheduler.lifecycle.current = some faulting ∧
        state.scheduler.lifecycle.capabilities.subjects faulting = true ∧
        state.scheduler.lifecycle.runnable faulting = true := by
  simp only [dispatch] at hsuccess ⊢
  split at hsuccess <;> try simp_all [halt, reject]
  split at hsuccess <;> try simp_all [halt, reject]
  all_goals split at hsuccess <;> try simp_all [halt, reject]
  all_goals split at hsuccess <;> try simp_all [halt, reject]
  all_goals split at hsuccess <;> try simp_all [halt, reject]
  all_goals split at hsuccess <;> try simp_all [halt, reject]
  all_goals split at hsuccess <;> try simp_all [halt, reject]
  all_goals split at hsuccess <;> try simp_all [halt, reject]
  all_goals (try split at hsuccess) <;> try simp_all [halt, reject]
  all_goals (try split at hsuccess) <;> try simp_all [halt, reject]
  all_goals (try split at hsuccess) <;> try simp_all [halt, reject]
  all_goals grind

/-- Both successful branches expose the complete lifecycle and virtual-mapping
cleanup boundary. Every address space owned by the faulting subject in the
pre-state loses its owner and every mapping in that space. -/
theorem successful_cleanup_complete state entry
    (hsuccess : (∃ reason, (dispatch state entry).action = .idle reason) ∨
      ∃ reason context, (dispatch state entry).action = .dispatch reason context) :
    ∃ faulting,
      state.scheduler.lifecycle.current = some faulting ∧
        (dispatch state entry).state.scheduler.lifecycle.runnable faulting = false ∧
        ∀ addressSpace,
          state.scheduler.lifecycle.addressOwner addressSpace = some faulting →
            (dispatch state entry).state.scheduler.lifecycle.addressOwner addressSpace = none ∧
            ∀ page,
              (dispatch state entry).state.translations.virtual.mappings
                addressSpace page = none := by
  rcases hsuccess with ⟨reason, hidle⟩ | ⟨reason, context, hdispatch⟩
  · rcases idle_is_clean_empty state entry reason hidle with
      ⟨faulting, hcurrent, hstate, _, _⟩
    refine ⟨faulting, hcurrent, ?_, ?_⟩
    · rw [hstate]
      exact ResumablePreemption.cleanup_marks_subject_not_runnable state faulting
    · intro addressSpace howner
      rw [hstate]
      exact ⟨ResumablePreemption.cleanup_removes_owned_address_space
          state faulting addressSpace howner,
        fun page => ResumablePreemption.cleanup_removes_owned_space_mappings
          state faulting addressSpace page howner⟩
  · obtain ⟨faulting, trusted, hcurrent, hselected, _, hstate⟩ :=
      dispatched_is_authoritative_transition state entry reason context hdispatch
    let cleaned := ResumablePreemption.cleanupSubject state faulting
    have hrunnable :
        (Scheduler.selectNext cleaned.scheduler).state.lifecycle.runnable =
          cleaned.scheduler.lifecycle.runnable := by
      grind [Scheduler.selectNext, Scheduler.reject]
    have haddressOwner :
        (Scheduler.selectNext cleaned.scheduler).state.lifecycle.addressOwner =
          cleaned.scheduler.lifecycle.addressOwner := by
      grind [Scheduler.selectNext, Scheduler.reject]
    refine ⟨faulting, hcurrent, ?_, ?_⟩
    · rw [hstate]
      change (Scheduler.selectNext cleaned.scheduler).state.lifecycle.runnable faulting = false
      rw [hrunnable]
      exact ResumablePreemption.cleanup_marks_subject_not_runnable state faulting
    · intro addressSpace howner
      rw [hstate]
      constructor
      · change (Scheduler.selectNext cleaned.scheduler).state.lifecycle.addressOwner
          addressSpace = none
        rw [haddressOwner]
        exact ResumablePreemption.cleanup_removes_owned_address_space
          state faulting addressSpace howner
      · intro page
        change (TLB.switch cleaned.translations context.addressSpace).virtual.mappings
          addressSpace page = none
        simpa [TLB.switch] using
          ResumablePreemption.cleanup_removes_owned_space_mappings
            state faulting addressSpace page howner

/-- Every successful composite result excludes resumption of the live,
runnable subject that faulted, regardless of whether the deterministic
scheduler finds a survivor. It also exposes removal of the runnable bit and
every pre-fault-owned address space and mapping. -/
theorem successful_nonresumption state entry
    (hsuccess : (∃ reason, (dispatch state entry).action = .idle reason) ∨
      ∃ reason context, (dispatch state entry).action = .dispatch reason context) :
    ∃ faulting,
      state.scheduler.lifecycle.current = some faulting ∧
        state.scheduler.lifecycle.capabilities.subjects faulting = true ∧
        state.scheduler.lifecycle.runnable faulting = true ∧
        (dispatch state entry).state.scheduler.lifecycle.capabilities.subjects
          faulting = false ∧
        (dispatch state entry).state.scheduler.lifecycle.runnable faulting = false ∧
        faulting ∉ (dispatch state entry).state.scheduler.ready ∧
        (dispatch state entry).state.scheduler.lifecycle.current ≠ some faulting ∧
        ResumablePreemption.contextFor
          (dispatch state entry).state.contexts faulting = none ∧
        ∀ addressSpace,
          state.scheduler.lifecycle.addressOwner addressSpace = some faulting →
            (dispatch state entry).state.scheduler.lifecycle.addressOwner addressSpace = none ∧
            ∀ page,
              (dispatch state entry).state.translations.virtual.mappings
                addressSpace page = none := by
  rcases successful_faulting_live_runnable state entry hsuccess with
    ⟨liveFaulting, hliveCurrent, hlive, hrunnable⟩
  rcases successful_cleanup_complete state entry hsuccess with
    ⟨cleanedFaulting, hcleanedCurrent, hnotRunnable, hspaces⟩
  rcases hsuccess with ⟨reason, hidle⟩ | ⟨reason, context, hdispatch⟩
  · rcases idle_nonresumption state entry reason hidle with
      ⟨faulting, hfaulting, hdead, habsent, hcurrent, hcontext⟩
    have : liveFaulting = faulting := by simp_all
    subst liveFaulting
    have : cleanedFaulting = faulting := by simp_all
    subst cleanedFaulting
    exact ⟨faulting, hfaulting, hlive, hrunnable, hdead, hnotRunnable,
      habsent, hcurrent, hcontext, hspaces⟩
  · rcases dispatched_nonresumption state entry reason context hdispatch with
      ⟨faulting, hfaulting, hdead, habsent, hcurrent, hcontext⟩
    have : liveFaulting = faulting := by simp_all
    subst liveFaulting
    have : cleanedFaulting = faulting := by simp_all
    subst cleanedFaulting
    exact ⟨faulting, hfaulting, hlive, hrunnable, hdead, hnotRunnable,
      habsent, hcurrent, hcontext, hspaces⟩

/-- Reason/vector agreement at the composite boundary: a successful action's
typed reason is exactly the manifest-bound decode of the accepted frame's
vector with the reviewed per-class error convention, so no untrusted word can
relabel one contained class as another. -/
theorem success_reason_vector_binding state frame reason
    (hsuccess : (dispatch state (.accepted frame)).action = .idle reason ∨
      ∃ context, (dispatch state (.accepted frame)).action = .dispatch reason context) :
    InterruptEntry.containedReason? frame.vector = some reason ∧
      frame.vector = reason.vector ∧
      frame.purpose = .userFault ∧
      frame.origin = .user ∧
      frame.errorCode.isSome = reason.hasErrorWord ∧
      frame.cs % 4 = 3 := by
  simp only [dispatch] at hsuccess
  split at hsuccess <;> try simp_all [halt, reject]
  all_goals split at hsuccess <;> try simp_all [halt, reject]
  all_goals split at hsuccess <;> try simp_all [halt, reject]
  all_goals split at hsuccess <;> try simp_all [halt, reject]
  all_goals split at hsuccess <;> try simp_all [halt, reject]
  all_goals split at hsuccess <;> try simp_all [halt, reject]
  all_goals (try split at hsuccess) <;> try simp_all [halt, reject]
  all_goals (try split at hsuccess) <;> try simp_all [halt, reject]
  all_goals (try split at hsuccess) <;> try simp_all [halt, reject]
  all_goals grind [validUserFaultFor]

/-- Reason-independent cleanup: any two successful composite results from the
same authoritative pre-state publish exactly the same post-state.  The typed
reason names the contained class in the outcome but never selects a cleanup,
survivor, or address-space variant, so issue-#104 composition can treat the
three contained classes as one transition. -/
theorem success_state_reason_independent state first second
    (hfirst : (∃ reason, (dispatch state first).action = .idle reason) ∨
      ∃ reason context, (dispatch state first).action = .dispatch reason context)
    (hsecond : (∃ reason, (dispatch state second).action = .idle reason) ∨
      ∃ reason context, (dispatch state second).action = .dispatch reason context) :
    (dispatch state first).state = (dispatch state second).state := by
  rcases hfirst with ⟨reasonFirst, hfirstIdle⟩ | ⟨reasonFirst, contextFirst, hfirstDispatch⟩ <;>
    rcases hsecond with ⟨reasonSecond, hsecondIdle⟩ |
      ⟨reasonSecond, contextSecond, hsecondDispatch⟩
  · obtain ⟨faultingFirst, hcurrentFirst, hstateFirst, _, _⟩ :=
      idle_is_clean_empty state first reasonFirst hfirstIdle
    obtain ⟨faultingSecond, hcurrentSecond, hstateSecond, _, _⟩ :=
      idle_is_clean_empty state second reasonSecond hsecondIdle
    have : faultingFirst = faultingSecond := by grind
    subst this
    rw [hstateFirst, hstateSecond]
  · obtain ⟨faultingFirst, hcurrentFirst, hstateFirst, hreadyFirst, _⟩ :=
      idle_is_clean_empty state first reasonFirst hfirstIdle
    obtain ⟨faultingSecond, trusted, hcurrentSecond, hselected, _, _⟩ :=
      dispatched_is_authoritative_transition state second reasonSecond contextSecond
        hsecondDispatch
    have : faultingFirst = faultingSecond := by grind
    subst this
    rw [hstateFirst] at hreadyFirst
    exact absurd hselected (by grind [Scheduler.selectNext, Scheduler.reject])
  · obtain ⟨faultingSecond, hcurrentSecond, hstateSecond, hreadySecond, _⟩ :=
      idle_is_clean_empty state second reasonSecond hsecondIdle
    obtain ⟨faultingFirst, trusted, hcurrentFirst, hselected, _, _⟩ :=
      dispatched_is_authoritative_transition state first reasonFirst contextFirst
        hfirstDispatch
    have : faultingSecond = faultingFirst := by grind
    subst this
    rw [hstateSecond] at hreadySecond
    exact absurd hselected (by grind [Scheduler.selectNext, Scheduler.reject])
  · obtain ⟨faultingFirst, trustedFirst, hcurrentFirst, hselectedFirst,
      hcontextFirst, hstateFirst⟩ :=
      dispatched_is_authoritative_transition state first reasonFirst contextFirst
        hfirstDispatch
    obtain ⟨faultingSecond, trustedSecond, hcurrentSecond, hselectedSecond,
      hcontextSecond, hstateSecond⟩ :=
      dispatched_is_authoritative_transition state second reasonSecond contextSecond
        hsecondDispatch
    have hfaulting : faultingFirst = faultingSecond := by grind
    subst hfaulting
    have htrusted : trustedFirst = trustedSecond := by grind
    subst htrusted
    have hcontext : contextFirst = contextSecond := by grind
    subst hcontext
    rw [hstateFirst, hstateSecond]

/-- Attacker payload words cannot select or relabel the typed contained
reason: the observable action is a function of the kernel-owned state and the
normalized entry alone. -/
theorem attacker_payload_cannot_relabel {Payload : Type} state entry
    (left right : Payload) :
    (dispatchWithPayload state entry left).action =
      (dispatchWithPayload state entry right).action := by
  rfl

/-! Executable regressions for the invariant boundary closed by this slice:
one queued survivor becomes the sole current subject, while no survivor yields
idle.  Neither result retains the faulting subject's resumable slot. -/

private def traceCapabilities (survivor : Bool) : Capability.State :=
  { subjects := fun subject => subject = 1 || (survivor && subject = 2)
    objects := fun object => object = 1 ||
      (survivor && (object = 2 || object = 20 || object = 30))
    kinds := fun object =>
      if object = 1 || (survivor && object = 2) then some .addressSpace
      else if survivor && object = 20 then some .memory
      else if survivor && object = 30 then some .endpoint
      else none
    slots := fun holder slot =>
      if survivor && holder = 2 && slot = 7 then
        some { object := 20, kind := .memory, rights := { read := true } }
      else none }

private def traceLifecycle (survivor : Bool) : SubjectLifecycle.State :=
  { capabilities := traceCapabilities survivor
    issuedSubjects := fun subject => subject = 1 || (survivor && subject = 2)
    ownedMemory := fun object => if survivor && object = 20 then some (2, 40) else none
    addressOwner := fun space =>
      if space = 1 || (survivor && space = 2) then some space else none
    mapping := fun space page => if survivor && space = 2 && page = 9 then some 20 else none
    endpointOwner := fun endpoint => if survivor && endpoint = 30 then some 2 else none
    mailbox := fun _ => none
    frameOwner := fun frame => if survivor && frame = 40 then some 2 else none
    freeFrame := fun frame => !(survivor && frame = 40)
    runnable := fun subject => subject = 1 || (survivor && subject = 2)
    current := some 1 }

private def traceHardwareFrame : Interrupt.HardwareFrame :=
  { vector := 14
    errorCode := 0
    savedPrivilege := .user
    instructionPointer := 0x400200
    stackPointer := 0x500ff8
    codeSelector := 0x23
    stackSelector := 0x1b
    flags := 0x202
    canonicalInstructionPointer := true
    canonicalStackPointer := true
    flagsAllowed := true }

private def traceRegisters : ResumablePreemption.Registers :=
  { accumulator := 0
    base := 0xb2b2cafe51a7e55e
    count := 0x030201
    data := 0x51a7
    source := 0
    destination := 0
    basePointer := 0
    r8 := 0
    r9 := 0
    r10 := 0
    r11 := 0
    r12 := 0
    r13 := 0
    r14 := 0
    r15 := 0 }

private def traceSurvivorContext : ResumablePreemption.Context :=
  { owner := 2
    addressSpace := 2
    frame := traceHardwareFrame
    registers := traceRegisters
    kind := .suspended }

private def traceState (survivor : Bool) : ResumablePreemption.State :=
  let lifecycle := traceLifecycle survivor
  let capabilities := traceCapabilities survivor
  { scheduler := {
      lifecycle
      ready := if survivor then [2] else []
      capacity := 2 }
    contexts := if survivor then [traceSurvivorContext] else []
    capacity := 2
    translations := {
      virtual := {
        memory := {
          capabilities
          allocator := {
            frames := if survivor then [40] else []
            status := fun frame => if survivor && frame = 40 then .owned 20 else .free }
          binding := fun object => if survivor && object = 20 then some 40 else none
          issued := fun object => object = 1 ||
            (survivor && (object = 2 || object = 20 || object = 30)) }
        owner := lifecycle.addressOwner
        mappings := fun space page => if survivor && space = 2 && page = 9 then
          some { object := 20, permissions := { read := true } } else none
        issuedAddressSpace := fun space => space = 1 || (survivor && space = 2) }
      active := some 1
      entries := [] } }

private def traceEntry : InterruptEntry.Result :=
  .accepted {
    vector := 14
    purpose := .userFault
    origin := .user
    errorCode := some 0
    rip := 0x400100
    cs := 0x23
    flags := 0x202
    userRsp := some 0x500ff8
    userSs := some 0x1b
    currentSubject := 1
    activeAddressSpace := 1
    activeCr3 := 0
    stackIdentity := 1 }

example : (dispatch (traceState true) traceEntry).action =
    .dispatch .pageFault traceSurvivorContext := by native_decide

/-- The selected peer fixture owns resources in every lifecycle cleanup class,
and dispatch preserves them independently of its complete saved context. -/
example :
    let next := (dispatch (traceState true) traceEntry).state
    ResumablePreemption.contextFor (traceState true).contexts 2 =
        some traceSurvivorContext ∧
      (traceState true).scheduler.lifecycle.capabilities.slots 2 7 =
        some { object := 20, kind := .memory, rights := { read := true } } ∧
      next.scheduler.lifecycle.capabilities.slots 2 7 =
        (traceState true).scheduler.lifecycle.capabilities.slots 2 7 ∧
      next.scheduler.lifecycle.ownedMemory 20 = some (2, 40) ∧
      next.scheduler.lifecycle.mapping 2 9 = some 20 ∧
      next.scheduler.lifecycle.endpointOwner 30 = some 2 ∧
      next.scheduler.lifecycle.frameOwner 40 = some 2 ∧
      next.translations.virtual.mappings 2 9 =
        some { object := 20, permissions := { read := true } } := by
  native_decide

example :
    (dispatch (traceState true) traceEntry).state.scheduler.lifecycle.current = some 2 ∧
      (dispatch (traceState true) traceEntry).state.scheduler.ready = [] ∧
      (dispatch (traceState true) traceEntry).state.scheduler.lifecycle.capabilities.subjects 1 =
        false ∧
      ResumablePreemption.contextFor
        (dispatch (traceState true) traceEntry).state.contexts 1 = none := by
  native_decide

example : (dispatch (traceState false) traceEntry).action = .idle .pageFault ∧
    (dispatch (traceState false) traceEntry).state.scheduler.lifecycle.current = none ∧
    (dispatch (traceState false) traceEntry).state.scheduler.ready = [] ∧
    ResumablePreemption.contextFor
      (dispatch (traceState false) traceEntry).state.contexts 1 = none := by
  native_decide

/-! Mixed adversarial traces exercise the rejection/fatal boundary without
sharing partially cleaned state with the successful traces above. -/

private def traceThirdContext : ResumablePreemption.Context :=
  { traceSurvivorContext with owner := 3, addressSpace := 3 }

private def traceMultiCapabilities : Capability.State :=
  { subjects := fun subject => subject = 1 || subject = 2 || subject = 3
    objects := fun object => object = 1 || object = 2 || object = 3
    kinds := fun object =>
      if object = 1 || object = 2 || object = 3 then some .addressSpace else none
    slots := fun holder slot =>
      if holder = 3 && slot = 7 then
        some { object := 3, kind := .addressSpace, rights := { grant := true } }
      else none }

private def traceMultiLifecycle : SubjectLifecycle.State :=
  { capabilities := traceMultiCapabilities
    issuedSubjects := fun subject => subject = 1 || subject = 2 || subject = 3
    ownedMemory := fun object => if object = 30 then some (3, 50) else none
    addressOwner := fun space =>
      if space = 1 || space = 2 || space = 3 then some space else none
    mapping := fun space page => if space = 3 && page = 9 then some 30 else none
    endpointOwner := fun endpoint => if endpoint = 40 then some 3 else none
    mailbox := fun _ => none
    frameOwner := fun frame => if frame = 50 then some 3 else none
    freeFrame := fun frame => frame != 50
    runnable := fun subject => subject = 1 || subject = 2 || subject = 3
    current := some 1 }

private def traceMultiState : ResumablePreemption.State :=
  let lifecycle := traceMultiLifecycle
  { scheduler := { lifecycle, ready := [2, 3], capacity := 3 }
    contexts := [traceSurvivorContext, traceThirdContext]
    capacity := 3
    translations := {
      virtual := {
        memory := {
          capabilities := traceMultiCapabilities
          allocator := { frames := [50], status := fun frame =>
            if frame = 50 then .owned 30 else .free }
          binding := fun object => if object = 30 then some 50 else none
          issued := fun object => object = 1 || object = 2 || object = 3 || object = 30 }
        owner := lifecycle.addressOwner
        mappings := fun space page => if space = 3 && page = 9 then
          some { object := 30, permissions := { read := true } } else none
        issuedAddressSpace := fun space => space = 1 || space = 2 || space = 3 }
      active := some 1
      entries := [] } }

/-- A non-vacuous fault-owned mapping fixture: address space 1 and its page-4
mapping belong to the current subject before dispatch. -/
private def traceFaultOwnedMapping : ResumablePreemption.State :=
  { traceMultiState with
    scheduler := { traceMultiState.scheduler with
      lifecycle := { traceMultiState.scheduler.lifecycle with
        mapping := fun space page =>
          if space = 1 && page = 4 then some 1
          else traceMultiState.scheduler.lifecycle.mapping space page } }
    translations := { traceMultiState.translations with
      virtual := { traceMultiState.translations.virtual with
        mappings := fun space page =>
          if space = 1 && page = 4 then
            some { object := 1, permissions := { read := true } }
          else traceMultiState.translations.virtual.mappings space page } } }

private def traceStaleCurrent : InterruptEntry.Result :=
  match traceEntry with
  | .accepted frame => .accepted { frame with currentSubject := 3 }
  | other => other

private def traceWrongAddressSpace : InterruptEntry.Result :=
  match traceEntry with
  | .accepted frame => .accepted { frame with activeAddressSpace := 3 }
  | other => other

private def traceWrongPurpose : InterruptEntry.Result :=
  match traceEntry with
  | .accepted frame => .accepted { frame with purpose := .timer }
  | other => other

private def traceKernelContext : InterruptEntry.KernelContext :=
  { currentSubject := 1
    activeAddressSpace := 1
    activeCr3 := 0
    stackIdentity := 1
    stackFirst := 0x800000
    stackPastLast := 0x804000
    entryActive := false }

private def traceRawUserFault : InterruptEntry.RawEntry :=
  { boundVector := 14
    boundStub := 14
    errorCode := some 0
    restartClass := .faultingInstruction
    frame := .privilegeChange 0x400100 0x23 0x202 0x500ff8 0x1b
    frameBytes := 40
    frameAddress := 0x800000
    acCleared := true
    dfCleared := true }

private def traceMalformedUserFault : InterruptEntry.RawEntry :=
  { traceRawUserFault with frameBytes := 32 }

private def traceRawKernelFault : InterruptEntry.RawEntry :=
  { traceRawUserFault with
    frame := .samePrivilege 0x100000 0x08 0x202
    frameBytes := 24 }

private def traceUnsupportedEntry : InterruptEntry.RawEntry :=
  { traceRawKernelFault with boundVector := 15, boundStub := 15, errorCode := none }

/-- Raw CPL3 divide-error snapshot: vector 0, no architectural error word, and
faulting-instruction saved-RIP evidence. -/
private def traceRawDivideError : InterruptEntry.RawEntry :=
  { traceRawUserFault with boundVector := 0, boundStub := 0, errorCode := none }

/-- Raw CPL3 breakpoint snapshot: vector 3, no error word, and
following-boundary saved-RIP evidence for the `int3` trap class. -/
private def traceRawBreakpoint : InterruptEntry.RawEntry :=
  { traceRawUserFault with
    boundVector := 3
    boundStub := 3
    errorCode := none
    restartClass := .followingBoundary }

/-- Kernel-origin (same-privilege) divide error: the user-only origin policy
makes this a terminal normalizer rejection, never containment. -/
private def traceRawKernelDivideError : InterruptEntry.RawEntry :=
  { traceRawDivideError with
    frame := .samePrivilege 0x100000 0x08 0x202
    frameBytes := 24 }

private def traceRawKernelBreakpoint : InterruptEntry.RawEntry :=
  { traceRawBreakpoint with
    frame := .samePrivilege 0x100000 0x08 0x202
    frameBytes := 24 }

/-- Spurious synthesized error word on a #BP entry. -/
private def traceRawBreakpointSpuriousError : InterruptEntry.RawEntry :=
  { traceRawBreakpoint with errorCode := some 0 }

/-- Wrong restart-class evidence: a #BP snapshot claiming the saved RIP names
the faulting instruction contradicts the reviewed AMD64 trap table. -/
private def traceRawBreakpointWrongRestart : InterruptEntry.RawEntry :=
  { traceRawBreakpoint with restartClass := .faultingInstruction }

private def traceDivideEntry : InterruptEntry.Result :=
  match traceEntry with
  | .accepted frame => .accepted { frame with vector := 0, errorCode := none }
  | other => other

private def traceBreakpointEntry : InterruptEntry.Result :=
  match traceEntry with
  | .accepted frame => .accepted { frame with vector := 3, errorCode := none }
  | other => other

/-- Swapped reason/vector shape: a divide-error vector carrying a page-fault
error word must stay a typed rejection. -/
private def traceSwappedDivideShape : InterruptEntry.Result :=
  match traceEntry with
  | .accepted frame => .accepted { frame with vector := 0 }
  | other => other

private def traceNestedContext : InterruptEntry.KernelContext :=
  { traceKernelContext with entryActive := true }

private def traceAlreadyTerminated : ResumablePreemption.State :=
  { traceState false with scheduler := { (traceState false).scheduler with
      lifecycle := { (traceState false).scheduler.lifecycle with
        capabilities := { (traceState false).scheduler.lifecycle.capabilities with
          subjects := fun _ => false }
        -- Retain an adversarial stale owner binding: liveness, rather than
        -- address ownership alone, must reject the dead current subject.
        addressOwner := fun subject => if subject = 1 then some 1 else none
        runnable := fun _ => false } } }

/-- Keep lifecycle ownership coherent while corrupting only the survivor's
authoritative virtual owner projection.  Dispatch must reject before exposing
the cleaned state. -/
private def traceStaleSurvivorVirtualOwner : ResumablePreemption.State :=
  { traceMultiState with
    translations := { traceMultiState.translations with
      virtual := { traceMultiState.translations.virtual with
        owner := fun addressSpace =>
          if addressSpace = 2 then some 3
          else traceMultiState.translations.virtual.owner addressSpace } } }

example : (dispatch traceMultiState traceEntry).action =
    .dispatch .pageFault traceSurvivorContext := by
  native_decide

/-! The two new contained classes reuse the identical cleanup and survivor
path: same survivor context, same post-cleanup state, distinct typed reason.
Kernel-origin, spurious-error, wrong-restart, swapped-shape, and stale-binding
forms stay fatal or state-preserving rejections. -/

example : (dispatch traceMultiState
      (InterruptEntry.normalize traceRawDivideError traceKernelContext)).action =
    .dispatch .divideError traceSurvivorContext := by
  native_decide

example : (dispatch traceMultiState
      (InterruptEntry.normalize traceRawBreakpoint traceKernelContext)).action =
    .dispatch .breakpoint traceSurvivorContext := by
  native_decide

/-- Reason-independent cleanup, executably: the divide-error class publishes
exactly the page-fault post-state over the multi-survivor fixture. -/
example :
    (dispatch traceMultiState
        (InterruptEntry.normalize traceRawDivideError traceKernelContext)).state =
      (dispatch traceMultiState traceEntry).state :=
  success_state_reason_independent traceMultiState _ _
    (Or.inr ⟨.divideError, traceSurvivorContext, by native_decide⟩)
    (Or.inr ⟨.pageFault, traceSurvivorContext, by native_decide⟩)

/-- The breakpoint class also publishes exactly the page-fault post-state. -/
example :
    (dispatch traceMultiState
        (InterruptEntry.normalize traceRawBreakpoint traceKernelContext)).state =
      (dispatch traceMultiState traceEntry).state :=
  success_state_reason_independent traceMultiState _ _
    (Or.inr ⟨.breakpoint, traceSurvivorContext, by native_decide⟩)
    (Or.inr ⟨.pageFault, traceSurvivorContext, by native_decide⟩)

/-- No-survivor #DE and #BP entries produce the typed idle result and retire
the faulting subject's resumable slot, exactly like the page-fault path. -/
example :
    (dispatch (traceState false) traceDivideEntry).action = .idle .divideError ∧
      (dispatch (traceState false) traceBreakpointEntry).action = .idle .breakpoint ∧
      ResumablePreemption.contextFor
        (dispatch (traceState false) traceDivideEntry).state.contexts 1 = none ∧
      (dispatch (traceState false) traceDivideEntry).state.scheduler.lifecycle.current =
        none := by
  native_decide

/-- The idle #DE cleanup equals the idle page-fault cleanup byte for byte. -/
example :
    (dispatch (traceState false) traceDivideEntry).state =
      (dispatch (traceState false) traceEntry).state :=
  success_state_reason_independent (traceState false) _ _
    (Or.inl ⟨.divideError, by native_decide⟩)
    (Or.inl ⟨.pageFault, by native_decide⟩)

/-- Kernel-origin #DE/#BP are absorbed by the terminal wrong-origin latch and
preserve authoritative stores; they are never relabeled as containment. -/
example :
    InterruptEntry.normalize traceRawKernelDivideError traceKernelContext =
        .fatal .wrongOrigin ∧
      InterruptEntry.normalize traceRawKernelBreakpoint traceKernelContext =
        .fatal .wrongOrigin ∧
      (dispatch traceMultiState
        (InterruptEntry.normalize traceRawKernelDivideError traceKernelContext)).action =
        .fatal (.entry .wrongOrigin) ∧
      (dispatch traceMultiState
        (InterruptEntry.normalize traceRawKernelDivideError traceKernelContext)).state.halted =
        true := by
  native_decide

/-- The kernel-origin #DE latch preserves the complete scheduler store. -/
example :
    (dispatch traceMultiState
      (InterruptEntry.normalize traceRawKernelDivideError traceKernelContext)).state.scheduler =
      traceMultiState.scheduler :=
  (fatal_atomicity _ _ (.entry .wrongOrigin) (by native_decide)).2.1

/-- A spurious error word on #BP and wrong restart-class evidence both reject
at the normalizer with their exact typed reasons. -/
example :
    InterruptEntry.normalize traceRawBreakpointSpuriousError traceKernelContext =
        .fatal .wrongErrorShape ∧
      InterruptEntry.normalize traceRawBreakpointWrongRestart traceKernelContext =
        .fatal .wrongRestartClass ∧
      (dispatch traceMultiState
        (InterruptEntry.normalize traceRawBreakpointWrongRestart traceKernelContext)).action =
        .fatal (.entry .wrongRestartClass) := by
  native_decide

/-- Swapped reason/vector records reject without exposing cleanup, and stale
current/address bindings reject the new classes exactly like vector 14. -/
example :
    (dispatch traceMultiState traceSwappedDivideShape).action = .rejected .wrongPurpose ∧
      (dispatch traceAlreadyTerminated traceDivideEntry).action = .rejected .staleCurrent ∧
      (dispatch traceStaleSurvivorVirtualOwner traceBreakpointEntry).action =
        .rejected .staleContext := by
  native_decide

/-- Each of those rejections retains the complete pre-state. -/
example :
    (dispatch traceMultiState traceSwappedDivideShape).state = traceMultiState ∧
      (dispatch traceAlreadyTerminated traceDivideEntry).state = traceAlreadyTerminated ∧
      (dispatch traceStaleSurvivorVirtualOwner traceBreakpointEntry).state =
        traceStaleSurvivorVirtualOwner :=
  ⟨rejected_unchanged _ _ .wrongPurpose (by native_decide),
    rejected_unchanged _ _ .staleCurrent (by native_decide),
    rejected_unchanged _ _ .staleContext (by native_decide)⟩

/-- Successful dispatch clears both the runnable projection and a real
pre-fault mapping in every address space owned by the terminated subject. -/
example :
    traceFaultOwnedMapping.translations.virtual.mappings 1 4 =
        some { object := 1, permissions := { read := true } } ∧
      (dispatch traceFaultOwnedMapping traceEntry).action =
        .dispatch .pageFault traceSurvivorContext ∧
      (dispatch traceFaultOwnedMapping traceEntry).state.scheduler.lifecycle.runnable 1 = false ∧
      (dispatch traceFaultOwnedMapping traceEntry).state.scheduler.lifecycle.addressOwner 1 = none ∧
      (dispatch traceFaultOwnedMapping traceEntry).state.translations.virtual.mappings 1 4 = none := by
  native_decide

/-- The FIFO survivor at position two and its unrelated authority, mapping,
frame, endpoint, and suspended context survive dispatch of the head. -/
example :
    (dispatch traceMultiState traceEntry).state.scheduler.ready = [3] ∧
      ResumablePreemption.contextFor
        (dispatch traceMultiState traceEntry).state.contexts 3 = some traceThirdContext ∧
      (dispatch traceMultiState traceEntry).state.scheduler.lifecycle.capabilities.slots 3 7 =
        traceMultiState.scheduler.lifecycle.capabilities.slots 3 7 ∧
      (dispatch traceMultiState traceEntry).state.scheduler.lifecycle.ownedMemory 30 = some (3, 50) ∧
      (dispatch traceMultiState traceEntry).state.scheduler.lifecycle.mapping 3 9 = some 30 ∧
      (dispatch traceMultiState traceEntry).state.scheduler.lifecycle.endpointOwner 40 = some 3 ∧
      (dispatch traceMultiState traceEntry).state.scheduler.lifecycle.frameOwner 50 = some 3 := by
  native_decide

example : (dispatch traceMultiState traceStaleCurrent).action = .rejected .staleCurrent ∧
    (dispatch traceMultiState traceStaleCurrent).state = traceMultiState := by
  constructor
  · native_decide
  · exact rejected_unchanged _ _ .staleCurrent (by native_decide)

example : (dispatch traceMultiState traceWrongAddressSpace).action =
    .rejected .staleAddressSpace ∧
    (dispatch traceMultiState traceWrongAddressSpace).state = traceMultiState := by
  constructor
  · native_decide
  · exact rejected_unchanged _ _ .staleAddressSpace (by native_decide)

example : (dispatch traceMultiState traceWrongPurpose).action = .rejected .wrongPurpose ∧
    (dispatch traceMultiState traceWrongPurpose).state = traceMultiState := by
  constructor
  · native_decide
  · exact rejected_unchanged _ _ .wrongPurpose (by native_decide)

example : (dispatch traceMultiState (.fatal .wrongFrameShape)).action =
    .fatal (.entry .wrongFrameShape) ∧
    (dispatch traceMultiState (.fatal .wrongFrameShape)).state.halted = true ∧
    (dispatch traceMultiState (.fatal .wrongFrameShape)).state.scheduler =
      traceMultiState.scheduler := by
  have haction : (dispatch traceMultiState (.fatal .wrongFrameShape)).action =
      .fatal (.entry .wrongFrameShape) := by
    native_decide
  exact ⟨haction, (fatal_atomicity _ _ _ haction).1,
    (fatal_atomicity _ _ _ haction).2.1⟩

/-- A truncated user frame is fatal at the inbound normalizer boundary; the
composite consumer sets the halt latch while preserving authoritative stores. -/
example : InterruptEntry.normalize traceMalformedUserFault traceKernelContext =
      .fatal .truncated ∧
    dispatch traceMultiState
        (InterruptEntry.normalize traceMalformedUserFault traceKernelContext) =
      halt traceMultiState (.entry .truncated) := by
  have hnormalized : InterruptEntry.normalize traceMalformedUserFault traceKernelContext =
      .fatal .truncated := by native_decide
  refine ⟨hnormalized, ?_⟩
  rw [hnormalized]
  exact entry_failure_is_fatal _ _ (by native_decide)

/-- A normalized same-privilege page fault is terminal and cannot publish
cleanup before the halt latch is set. -/
example : (dispatch traceMultiState
      (InterruptEntry.normalize traceRawKernelFault traceKernelContext)).action =
        .fatal .kernelOrigin ∧
    (dispatch traceMultiState
      (InterruptEntry.normalize traceRawKernelFault traceKernelContext)).state.halted = true ∧
    (dispatch traceMultiState
      (InterruptEntry.normalize traceRawKernelFault traceKernelContext)).state.scheduler =
        traceMultiState.scheduler := by
  have haction : (dispatch traceMultiState
      (InterruptEntry.normalize traceRawKernelFault traceKernelContext)).action =
        .fatal .kernelOrigin := by
    native_decide
  refine ⟨haction, ?_⟩
  exact ⟨(fatal_atomicity _ _ _ haction).1, (fatal_atomicity _ _ _ haction).2.1⟩

/-- Nested normalization is terminal and preserves the pre-fault scheduler. -/
example : (dispatch traceMultiState
      (InterruptEntry.normalize traceRawUserFault traceNestedContext)).action =
        .fatal (.entry .nested) ∧
    (dispatch traceMultiState
      (InterruptEntry.normalize traceRawUserFault traceNestedContext)).state.halted = true ∧
    (dispatch traceMultiState
      (InterruptEntry.normalize traceRawUserFault traceNestedContext)).state.scheduler =
        traceMultiState.scheduler := by
  have haction : (dispatch traceMultiState
      (InterruptEntry.normalize traceRawUserFault traceNestedContext)).action =
        .fatal (.entry .nested) := by
    native_decide
  refine ⟨haction, ?_⟩
  exact ⟨(fatal_atomicity _ _ _ haction).1, (fatal_atomicity _ _ _ haction).2.1⟩

/-- An unsupported vector follows the distinct terminal entry class. -/
example : (dispatch traceMultiState
    (InterruptEntry.normalize traceUnsupportedEntry traceKernelContext)).action =
      .fatal (.entry .unsupportedVector) := by
  native_decide

/-- An already-halted state absorbs an otherwise valid user-fault entry without
changing scheduler, lifecycle, context-bank, or translation state. -/
example :
    let halted := { traceMultiState with halted := true }
    (dispatch halted traceEntry).action = .fatal .alreadyHalted ∧
      (dispatch halted traceEntry).state.halted = true ∧
      (dispatch halted traceEntry).state.scheduler = halted.scheduler ∧
      (dispatch halted traceEntry).state.contexts = halted.contexts ∧
      (dispatch halted traceEntry).state.translations = halted.translations := by
  simp [dispatch, halt]

/-- A dead current subject is rejected even if an attacker preserves a stale
address-owner binding that would pass the address-space checks by itself. -/
example : (dispatch traceAlreadyTerminated traceEntry).action = .rejected .staleCurrent ∧
    (dispatch traceAlreadyTerminated traceEntry).state = traceAlreadyTerminated := by
  constructor
  · native_decide
  · exact rejected_unchanged _ _ .staleCurrent (by native_decide)

/-- A survivor whose lifecycle owner is valid but whose virtual owner
projection names another subject is not eligible for dispatch. -/
example : (dispatch traceStaleSurvivorVirtualOwner traceEntry).action =
      .rejected .staleContext ∧
    (dispatch traceStaleSurvivorVirtualOwner traceEntry).state =
      traceStaleSurvivorVirtualOwner := by
  constructor
  · native_decide
  · exact rejected_unchanged _ _ .staleContext (by native_decide)

/-- Regression witness: after cleanup an attacker-chosen context lookup can
name subject 3 even though the deterministic ready head is subject 2.  The
composite transition cannot exhibit that substitution. -/
example :
    ResumablePreemption.contextFor
        (ResumablePreemption.cleanupSubject traceMultiState 1).contexts 3 =
      some traceThirdContext ∧
      (dispatch traceMultiState traceEntry).action =
        .dispatch .pageFault traceSurvivorContext ∧
      (dispatch traceMultiState traceEntry).action ≠
        .dispatch .pageFault traceThirdContext := by
  native_decide

/-- The atomic fault transition preserves the complete authoritative runtime
invariant on every result.  In the survivor branch, selecting the ready head
makes it current while consuming exactly its saved context; every unrelated
context and all cleanup-preserved lifecycle/virtual projections remain
unchanged. -/
theorem dispatch_preserves_wellFormed state entry
    (hstate : ResumablePreemption.WellFormed state) :
    ResumablePreemption.WellFormed (dispatch state entry).state := by
  cases haction : (dispatch state entry).action with
  | idle reason =>
      obtain ⟨faulting, _, hnext, _, _⟩ := idle_is_clean_empty state entry reason haction
      rw [hnext]
      exact ResumablePreemption.cleanupSubject_preserves_wellFormed state faulting hstate
  | dispatch reason context =>
      obtain ⟨faulting, trusted, _, hselected, hcontext, hnext⟩ :=
        dispatched_is_authoritative_transition state entry reason context haction
      rw [hnext]
      exact consumeSelected_preserves_wellFormed _ trusted context
        (ResumablePreemption.cleanupSubject_preserves_wellFormed state faulting hstate)
        hselected hcontext
  | rejected reason =>
      rw [rejected_unchanged state entry reason haction]
      exact hstate
  | fatal reason =>
      rw [fatal_state_eq_halt state entry reason haction]
      simpa [halt, ResumablePreemption.wellFormed_set_halted] using hstate

/-! A fixed-width boundary for the first boot containment scenario.  The
machine passes only values already bound by the normalized entry record and
the kernel-owned bounded scheduler/context bank.  The result packs action in
  the low byte, selected subject/address space in the next two bytes, the five
  cleanup witnesses (live, runnable, current, queued, resumable) in bits
  24--28, preserved survivor frame/register context in bit 29, preserved
  capability authority in bit 30, and preserved memory/mapping/endpoint/frame
  resources in bit 31, and the typed contained-reason code in bits 40--47
  (zero for the legacy page-fault class, so version-one words are unchanged).
  Bit 63 distinguishes typed fail-stop from nonfatal rejection.  Entry class
  4 is the bounded malformed-frame fixture emitted by the normalizer, class 5
  the wrong restart-class evidence fixture, and class 6 the swapped
  reason/vector error-shape fixture. -/

def faultDispatchDemo (vector entryClass current active ready contextOwner : UInt64) : UInt64 :=
  let reasonCode : UInt64 :=
    if vector = 14 then 0 else if vector = 0 then 1 else if vector = 3 then 2 else 3
  if reasonCode = 3 then 0x8000000000000002
  else if entryClass = 4 then 0x8000000000000002
  else if entryClass = 5 then 0x8000000000000002
  else if entryClass = 6 then 0
  else if entryClass != 3 then
    if vector = 14 then 0x8000000000000001 else 0x8000000000000002
  else if current != 1 || active != 1 then 0
  else if ready = 0 then 1 + reasonCode * 0x10000000000
  else if ready = 2 && contextOwner = 2 then
    0x00000000ff020202 + reasonCode * 0x10000000000
  else if ready = 3 && contextOwner = 2 then
    0x000000003f020202 + reasonCode * 0x10000000000
  else 0

@[export leanos_fault_dispatch_demo]
def faultDispatchDemoExport (vector origin current active ready contextOwner : UInt64) : UInt64 :=
  faultDispatchDemo vector origin current active ready contextOwner

private def bootCleanupWitness (before : ResumablePreemption.State)
    (outcome : Outcome) : UInt64 :=
  match before.scheduler.lifecycle.current with
  | none => 0
  | some faulting =>
      (if outcome.state.scheduler.lifecycle.capabilities.subjects faulting = false then
        0x01000000 else 0) +
      (if outcome.state.scheduler.lifecycle.runnable faulting = false then 0x02000000 else 0) +
      (if outcome.state.scheduler.lifecycle.current != some faulting then 0x04000000 else 0) +
      (if outcome.state.scheduler.ready.contains faulting = false then 0x08000000 else 0) +
      (if ResumablePreemption.contextFor outcome.state.contexts faulting = none then
        0x10000000 else 0)

private def bootPeerContextWitness (before : ResumablePreemption.State)
    (outcome : Outcome) : UInt64 :=
  match outcome.action with
  | .dispatch _ context =>
      if ResumablePreemption.contextFor before.contexts context.owner = some context ∧
          outcome.state.scheduler.lifecycle.capabilities.subjects context.owner = true ∧
          outcome.state.scheduler.lifecycle.runnable context.owner = true ∧
          outcome.state.scheduler.lifecycle.addressOwner context.addressSpace =
            some context.owner then 0x20000000 else 0
  | _ => 0

private def bootPeerCapabilityWitness (before : ResumablePreemption.State)
    (outcome : Outcome) : UInt64 :=
  match outcome.action with
  | .dispatch _ context =>
      if before.scheduler.lifecycle.capabilities.slots context.owner 7 =
            some { object := 20, kind := .memory, rights := { read := true } } ∧
          outcome.state.scheduler.lifecycle.capabilities.slots context.owner 7 =
            before.scheduler.lifecycle.capabilities.slots context.owner 7 then
        0x40000000 else 0
  | _ => 0

private def bootPeerResourceWitness (before : ResumablePreemption.State)
    (outcome : Outcome) : UInt64 :=
  match outcome.action with
  | .dispatch _ context =>
      if before.scheduler.lifecycle.ownedMemory 20 = some (context.owner, 40) ∧
          outcome.state.scheduler.lifecycle.ownedMemory 20 = some (context.owner, 40) ∧
          before.scheduler.lifecycle.mapping context.addressSpace 9 = some 20 ∧
          outcome.state.scheduler.lifecycle.mapping context.addressSpace 9 = some 20 ∧
          before.scheduler.lifecycle.endpointOwner 30 = some context.owner ∧
          outcome.state.scheduler.lifecycle.endpointOwner 30 = some context.owner ∧
          before.scheduler.lifecycle.frameOwner 40 = some context.owner ∧
          outcome.state.scheduler.lifecycle.frameOwner 40 = some context.owner ∧
          before.translations.virtual.mappings context.addressSpace 9 =
            some { object := 20, permissions := { read := true } } ∧
          outcome.state.translations.virtual.mappings context.addressSpace 9 =
            before.translations.virtual.mappings context.addressSpace 9 then
        0x80000000 else 0
  | _ => 0

def encodeBootOutcome (before : ResumablePreemption.State) (outcome : Outcome) : UInt64 :=
  match outcome.action with
  | .idle reason => 1 + reason.code * 0x10000000000
  | .dispatch reason context =>
      2 + UInt64.ofNat context.owner * 0x100 +
        UInt64.ofNat context.addressSpace * 0x10000 +
        bootCleanupWitness before outcome + bootPeerContextWitness before outcome +
        bootPeerCapabilityWitness before outcome + bootPeerResourceWitness before outcome +
        reason.code * 0x10000000000
  | .rejected _ => 0
  | .fatal .kernelOrigin => 0x8000000000000001
  | .fatal _ => 0x8000000000000002

/-- Independently evaluated expectation for the shared oracle.  Each scalar
fixture selects a concrete input to the authoritative composite transition;
the exported adapter is not used to compute this expected word. -/
def faultDispatchModelExpected (vector entryClass current active ready contextOwner : UInt64) : UInt64 :=
  let state :=
    if current = 0 then traceAlreadyTerminated
    else if ready = 0 then traceState false
    else if ready = 3 then traceMultiState
    else if contextOwner = 2 then traceState true
    else traceStaleSurvivorVirtualOwner
  let rawUser :=
    if vector = 0 then traceRawDivideError
    else if vector = 3 then traceRawBreakpoint
    else traceRawUserFault
  let rawKernel :=
    if vector = 0 then traceRawKernelDivideError
    else if vector = 3 then traceRawKernelBreakpoint
    else traceRawKernelFault
  let entry :=
    if vector != 0 && vector != 3 && vector != 14 then
      (.fatal .unsupportedVector : InterruptEntry.Result)
    else if entryClass = 4 then
      InterruptEntry.normalize { rawUser with frameBytes := 32 } traceKernelContext
    else if entryClass = 5 then
      InterruptEntry.normalize
        { rawUser with restartClass := rawUser.restartClass.other } traceKernelContext
    else if entryClass = 6 then
      match traceEntry with
      | .accepted frame => .accepted { frame with
          vector := vector
          errorCode := if vector = 14 then none else some 0
          currentSubject := current.toNat, activeAddressSpace := active.toNat }
      | other => other
    else if entryClass != 3 then InterruptEntry.normalize rawKernel traceKernelContext
    else match traceEntry with
      | .accepted frame => .accepted { frame with
          vector := vector
          errorCode := if vector = 14 then some 0 else none
          currentSubject := current.toNat, activeAddressSpace := active.toNat }
      | other => other
  encodeBootOutcome state (dispatch state entry)

theorem faultDispatchDemo_accepts_composite :
    faultDispatchDemo 14 3 1 1 2 2 =
      encodeBootOutcome (traceState true) (dispatch (traceState true) traceEntry) := by
  native_decide

theorem faultDispatchDemo_kernel_origin_fail_stop :
    faultDispatchDemo 14 0 1 1 2 2 =
      encodeBootOutcome (traceState true) (dispatch (traceState true)
        (InterruptEntry.normalize traceRawKernelFault traceKernelContext)) := by
  native_decide

theorem faultDispatchDemo_malformed_frame_fail_stop :
    faultDispatchDemo 14 4 1 1 2 2 =
      encodeBootOutcome (traceState true) (dispatch (traceState true)
        (InterruptEntry.normalize traceMalformedUserFault traceKernelContext)) := by
  native_decide

theorem faultDispatchDemo_accepts_divide_error :
    faultDispatchDemo 0 3 1 1 2 2 =
      encodeBootOutcome (traceState true)
        (dispatch (traceState true) traceDivideEntry) := by
  native_decide

theorem faultDispatchDemo_accepts_breakpoint_multi_survivor :
    faultDispatchDemo 3 3 1 1 3 2 =
      encodeBootOutcome traceMultiState
        (dispatch traceMultiState traceBreakpointEntry) := by
  native_decide

theorem faultDispatchDemo_kernel_divide_error_fail_stop :
    faultDispatchDemo 0 0 1 1 2 2 =
      encodeBootOutcome (traceState true) (dispatch (traceState true)
        (InterruptEntry.normalize traceRawKernelDivideError traceKernelContext)) := by
  native_decide

theorem faultDispatchDemo_wrong_restart_fail_stop :
    faultDispatchDemo 3 5 1 1 2 2 =
      encodeBootOutcome (traceState true) (dispatch (traceState true)
        (InterruptEntry.normalize traceRawBreakpointWrongRestart traceKernelContext)) := by
  native_decide

/-! Executable agreement traces use the repository's proof-carrying sample
boot plan.  The checked page is always selected inside active address space A;
the encoded CR2 field never selects a root or cleanup target. -/

private def pageFaultAgreementContext : InterruptEntry.PageFaultContext :=
  { entry :=
      { currentSubject := 1
        activeAddressSpace := 1
        activeCr3 := 0xa000
        stackIdentity := 1
        stackFirst := 0x800000
        stackPastLast := 0x804000
        entryActive := false }
    controls :=
      { writeProtect := true
        nxEnable := true
        smep := true
        smap := true } }

private def pageFaultRecord (errorWord faultPage : UInt64) :
    InterruptEntry.CanonicalPageFault :=
  let decoded :=
    match InterruptEntry.decodePageFaultError errorWord with
    | .ok decoded => decoded
    | .error _ =>
        { protection := false, write := false, user := true,
          instructionFetch := false }
  { vector := 14
    errorWord
    faultAddress := faultPage * UInt64.ofNat X86PageTable.pageBytes
    faultPage
    accessCode := InterruptEntry.pageFaultAccessCode decoded.accessKind
    protectionCode := if decoded.protection then 1 else 0
    privilegeCode := if decoded.user then 1 else 0
    currentSubject := 1
    activeAddressSpace := 1
    activeCr3 := 0xa000
    controlsCode := 15
    rip := 0x400100
    cs := 0x23
    flags := 0x202
    userRsp := 0x500ff8
    userSs := 0x1b
    stackIdentity := 1
    reserved := 0 }

private def samplePlanDispatch (state : ResumablePreemption.State)
    (record : InterruptEntry.CanonicalPageFault) : Outcome :=
  match BootPageTablePlan.compile BootPageTablePlan.sampleInput with
  | .error _ => halt state (.pageFaultIntegrity .malformedSnapshot)
  | .ok plan =>
      dispatchPageFault state plan (BootPageTablePlan.decodedReport plan .subjectA)
        (InterruptEntry.encodeCanonicalPageFault record)
        pageFaultAgreementContext

private def samplePlanDispatchWithReport (state : ResumablePreemption.State)
    (record : InterruptEntry.CanonicalPageFault)
    (mutate : BootPageTablePlan.DecodedRoot →
      BootPageTablePlan.DecodedRoot) : Outcome :=
  match BootPageTablePlan.compile BootPageTablePlan.sampleInput with
  | .error _ => halt state (.pageFaultIntegrity .malformedSnapshot)
  | .ok plan =>
      let report := mutate (BootPageTablePlan.decodedReport plan .subjectA)
      dispatchPageFault state plan report
        (InterruptEntry.encodeCanonicalPageFault record)
        pageFaultAgreementContext

/-- Public concrete fixtures used only by proof-integrity regressions. -/
def pageFaultAgreementWitnessState : ResumablePreemption.State :=
  traceState true

def pageFaultAgreementWitnessRecord (errorWord faultPage : UInt64) :
    InterruptEntry.CanonicalPageFault :=
  pageFaultRecord errorWord faultPage

def pageFaultAgreementWitnessOutcome
    (record : InterruptEntry.CanonicalPageFault) : Outcome :=
  samplePlanDispatch pageFaultAgreementWitnessState record

def pageFaultAgreementWitnessOutcomeFromState
    (state : ResumablePreemption.State)
    (record : InterruptEntry.CanonicalPageFault) : Outcome :=
  samplePlanDispatch state record

def pageFaultAgreementWitnessContained
    (record : InterruptEntry.CanonicalPageFault) : Bool :=
  match (pageFaultAgreementWitnessOutcome record).action with
  | .idle .pageFault | .dispatch .pageFault _ => true
  | _ => false

def mutatePageFaultLiveLeaf (page : Nat)
    (mutate : X86PageTable.Leaf → X86PageTable.Leaf)
    (report : BootPageTablePlan.DecodedRoot) :
    BootPageTablePlan.DecodedRoot :=
  { report with
    leaves := report.leaves.map fun entry =>
      if entry.page = page then { entry with leaf := mutate entry.leaf }
      else entry }

/-- Concrete stale cross-projection counterexample: the plan and virtual
mapping both omit page 50, but the lifecycle still names object 999 there. -/
def pageFaultAgreementStaleLifecycleState : ResumablePreemption.State :=
  let base := pageFaultAgreementWitnessState
  { base with
    scheduler :=
      { base.scheduler with
        lifecycle :=
          { base.scheduler.lifecycle with
            mapping := fun space page =>
              if space = 1 && page = 50 then some 999
              else base.scheduler.lifecycle.mapping space page } } }

def pageFaultAgreementStaleLifecycleContained : Bool :=
  match (pageFaultAgreementWitnessOutcomeFromState
      pageFaultAgreementStaleLifecycleState
      (pageFaultAgreementWitnessRecord 4 50)).action with
  | .idle .pageFault | .dispatch .pageFault _ => true
  | _ => false

private def pageFaultMappedState (page : Nat) (writable : Bool) :
    ResumablePreemption.State :=
  let base := traceState true
  let object := page
  let frame := page
  let capabilities :=
    { base.scheduler.lifecycle.capabilities with
      objects := fun candidate =>
        candidate = object ||
          base.scheduler.lifecycle.capabilities.objects candidate
      kinds := fun candidate =>
        if candidate = object then some .memory
        else base.scheduler.lifecycle.capabilities.kinds candidate }
  let lifecycle :=
    { base.scheduler.lifecycle with
      capabilities
      ownedMemory := fun candidate =>
        if candidate = object then some (1, frame)
        else base.scheduler.lifecycle.ownedMemory candidate
      mapping := fun space candidatePage =>
        if space = 1 && candidatePage = page then some object
        else base.scheduler.lifecycle.mapping space candidatePage
      frameOwner := fun candidate =>
        if candidate = frame then some 1
        else base.scheduler.lifecycle.frameOwner candidate
      freeFrame := fun candidate =>
        if candidate = frame then false
        else base.scheduler.lifecycle.freeFrame candidate }
  { base with
    scheduler := { base.scheduler with lifecycle }
    translations :=
      { base.translations with
        virtual :=
          { base.translations.virtual with
            memory :=
              { base.translations.virtual.memory with
                capabilities
                allocator :=
                  { frames := frame :: base.translations.virtual.memory.allocator.frames
                    status := fun candidate =>
                      if candidate = frame then .owned object
                      else base.translations.virtual.memory.allocator.status candidate }
                binding := fun candidate =>
                  if candidate = object then some frame
                  else base.translations.virtual.memory.binding candidate
                issued := fun candidate =>
                  candidate = object ||
                    base.translations.virtual.memory.issued candidate }
            mappings := fun space candidatePage =>
              if space = 1 && candidatePage = page then
                some { object, permissions := { read := true, write := writable } }
              else base.translations.virtual.mappings space candidatePage } } }

/-- Concrete stale-generation counterexample: every mapped-object projection
still names object 100, but its monotonic issuance bit has been cleared. -/
def pageFaultAgreementUnissuedObjectState : ResumablePreemption.State :=
  let base := pageFaultMappedState 100 false
  { base with
    translations :=
      { base.translations with
        virtual :=
          { base.translations.virtual with
            memory :=
              { base.translations.virtual.memory with
                issued := fun candidate =>
                  if candidate = 100 then false
                  else base.translations.virtual.memory.issued candidate } } } }

def pageFaultAgreementUnissuedObjectOutcome : Outcome :=
  samplePlanDispatch pageFaultAgreementUnissuedObjectState
    (pageFaultRecord 7 100)

def pageFaultAgreementUnissuedObjectContained : Bool :=
  match pageFaultAgreementUnissuedObjectOutcome.action with
  | .idle .pageFault | .dispatch .pageFault _ => true
  | _ => false

def pageFaultReservedLiveTableOutcome : Outcome :=
  samplePlanDispatchWithReport (pageFaultMappedState 100 false)
    (pageFaultRecord 7 100)
    (mutatePageFaultLiveLeaf 100 fun leaf =>
      { leaf with reservedBitsClear := false })

def pageFaultOutOfRangeLiveTableOutcome : Outcome :=
  samplePlanDispatchWithReport (pageFaultMappedState 100 false)
    (pageFaultRecord 7 100)
    (mutatePageFaultLiveLeaf 100 fun leaf =>
      { leaf with frame := X86PageTable.physicalFrameLimit })

def pageFaultMalformedAncestorOutcome : Outcome :=
  samplePlanDispatchWithReport (traceState true) (pageFaultRecord 4 50)
    (fun report =>
      { report with
        pdEntries := report.pdEntries.modify 0 fun entry =>
          { entry with present := false } })

def pageFaultReservedLiveTableContained : Bool :=
  match pageFaultReservedLiveTableOutcome.action with
  | .idle .pageFault | .dispatch .pageFault _ => true
  | _ => false

/-- Concrete witness for the architecturally impossible simultaneous
write/instruction-fetch error encoding (P/W/U/I = 1). -/
def pageFaultImpossibleWriteInstructionOutcome : Outcome :=
  samplePlanDispatch (pageFaultMappedState 101 true) (pageFaultRecord 23 101)

def pageFaultImpossibleWriteInstructionContained : Bool :=
  match pageFaultImpossibleWriteInstructionOutcome.action with
  | .idle .pageFault | .dispatch .pageFault _ => true
  | _ => false

theorem page_fault_nonpresent_read_contained_nonvacuous :
    (samplePlanDispatch (traceState true) (pageFaultRecord 4 50)).action =
      .dispatch .pageFault traceSurvivorContext := by
  native_decide

theorem page_fault_supervisor_read_contained_nonvacuous :
    (samplePlanDispatch (traceState true) (pageFaultRecord 5 1)).action =
      .dispatch .pageFault traceSurvivorContext := by
  native_decide

theorem page_fault_readonly_write_contained_nonvacuous :
    (samplePlanDispatch (pageFaultMappedState 100 false)
      (pageFaultRecord 7 100)).action =
        .dispatch .pageFault traceSurvivorContext := by
  native_decide

theorem page_fault_nx_execute_contained_nonvacuous :
    (samplePlanDispatch (pageFaultMappedState 101 true)
      (pageFaultRecord 21 101)).action =
        .dispatch .pageFault traceSurvivorContext := by
  native_decide

theorem page_fault_validated_live_report_contained_nonvacuous :
    (samplePlanDispatch (traceState true) (pageFaultRecord 4 50)).action =
      .dispatch .pageFault traceSurvivorContext := by
  native_decide

theorem page_fault_reserved_live_table_is_fatal_nonvacuous :
    pageFaultReservedLiveTableOutcome.action =
      .fatal (.pageFaultIntegrity (.walkIntegrity .reservedBits)) := by
  native_decide

theorem page_fault_out_of_range_live_table_is_fatal_nonvacuous :
    pageFaultOutOfRangeLiveTableOutcome.action =
      .fatal (.pageFaultIntegrity (.walkIntegrity .frameOutOfRange)) := by
  native_decide

theorem page_fault_malformed_ancestor_is_fatal_nonvacuous :
    pageFaultMalformedAncestorOutcome.action =
      .fatal (.pageFaultIntegrity (.liveTableReport .wrongAncestor)) := by
  native_decide

theorem page_fault_write_instruction_is_absorbing_fatal :
    pageFaultImpossibleWriteInstructionOutcome.action =
        .fatal (.pageFaultIntegrity .malformedSnapshot) ∧
      pageFaultImpossibleWriteInstructionOutcome.state.halted = true ∧
      ∀ plan report words trusted,
        dispatchPageFault pageFaultImpossibleWriteInstructionOutcome.state
            plan report words trusted =
          halt pageFaultImpossibleWriteInstructionOutcome.state .alreadyHalted := by
  have hfatal :
      pageFaultImpossibleWriteInstructionOutcome.action =
        .fatal (.pageFaultIntegrity .malformedSnapshot) := by
    native_decide
  have hhalted : pageFaultImpossibleWriteInstructionOutcome.state.halted = true := by
    native_decide
  refine ⟨hfatal, hhalted, ?_⟩
  intro plan report words trusted
  exact dispatchPageFault_already_halted_absorbing _ _ _ _ _ hhalted

theorem page_fault_no_survivor_contained_nonvacuous :
    (samplePlanDispatch (traceState false) (pageFaultRecord 4 50)).action =
      .idle .pageFault := by
  native_decide

theorem page_fault_multiple_survivors_contained_nonvacuous :
    (samplePlanDispatch traceMultiState (pageFaultRecord 4 50)).action =
      .dispatch .pageFault traceSurvivorContext := by
  native_decide

theorem page_fault_mismatched_error_is_fatal :
    (samplePlanDispatch (traceState true) (pageFaultRecord 5 50)).action =
      .fatal (.pageFaultIntegrity .walkMismatch) := by
  native_decide

theorem page_fault_readonly_mismatched_error_is_fatal :
    (samplePlanDispatch (pageFaultMappedState 100 false)
      (pageFaultRecord 5 100)).action =
        .fatal (.pageFaultIntegrity .accessAllowed) := by
  native_decide

theorem page_fault_nx_mismatched_error_is_fatal :
    (samplePlanDispatch (pageFaultMappedState 101 true)
      (pageFaultRecord 5 101)).action =
        .fatal (.pageFaultIntegrity .accessAllowed) := by
  native_decide

theorem page_fault_reserved_error_is_fatal :
    (samplePlanDispatch (traceState true) (pageFaultRecord 12 50)).action =
      .fatal (.pageFaultIntegrity .malformedSnapshot) := by
  native_decide

theorem page_fault_wrong_root_is_fatal :
    let record := { pageFaultRecord 4 50 with activeCr3 := 0xb000 }
    let trusted :=
      { pageFaultAgreementContext with
        entry :=
          { pageFaultAgreementContext.entry with
            activeCr3 := 0xb000 } }
    let outcome :=
      match BootPageTablePlan.compile BootPageTablePlan.sampleInput with
      | .error _ =>
          halt (traceState true) (.pageFaultIntegrity .malformedSnapshot)
      | .ok plan =>
          dispatchPageFault (traceState true) plan
            (BootPageTablePlan.decodedReport plan .subjectA)
            (InterruptEntry.encodeCanonicalPageFault record) trusted
    outcome.action = .fatal (.pageFaultIntegrity .wrongRoot) := by
  native_decide

theorem page_fault_forged_address_space_is_fatal :
    let record :=
      { pageFaultRecord 4 50 with activeAddressSpace := 2 }
    (samplePlanDispatch (traceState true) record).action =
      .fatal (.pageFaultIntegrity .provenanceMismatch) := by
  native_decide

theorem page_fault_kernel_origin_is_fatal :
    let record :=
      { pageFaultRecord 0 50 with
        cs := 0x08
        userRsp := 0
        userSs := 0 }
    (samplePlanDispatch (traceState true) record).action =
      .fatal .kernelOrigin := by
  native_decide

theorem page_fault_stale_mapping_is_fatal :
    (samplePlanDispatch (traceState true) (pageFaultRecord 4 100)).action =
      .fatal (.pageFaultIntegrity .staleMapping) := by
  native_decide

theorem page_fault_stale_lifecycle_mapping_is_fatal :
    (pageFaultAgreementWitnessOutcomeFromState
      pageFaultAgreementStaleLifecycleState
      (pageFaultAgreementWitnessRecord 4 50)).action =
        .fatal (.pageFaultIntegrity .staleMapping) := by
  native_decide

theorem page_fault_unissued_object_mapping_is_fatal :
    pageFaultAgreementUnissuedObjectOutcome.action =
      .fatal (.pageFaultIntegrity .staleMapping) := by
  native_decide

private def incoherentPageFaultState : ResumablePreemption.State :=
  let record := pageFaultRecord 4 50
  let context := pageFaultAccessContext record
  { traceState true with
    translations :=
      { (traceState true).translations with
        entries :=
          [{ key := { addressSpace := 1, page := 50 },
             frame := 999, context }] } }

def pageFaultAgreementIncoherentOutcome : Outcome :=
  samplePlanDispatch incoherentPageFaultState (pageFaultRecord 4 50)

theorem page_fault_incoherent_tlb_is_fatal :
    pageFaultAgreementIncoherentOutcome.action =
      .fatal (.pageFaultIntegrity .incoherentTlb) := by
  native_decide

/-- Authorization cannot substitute a different decoded record. -/
theorem authorized_page_fault_is_decoded (State : Type) words trusted
    (state : State) record
    (hauthorized :
      (InterruptEntry.authorizeCanonicalPageFault words trusted state).authorized =
        some record) :
    InterruptEntry.decodeCanonicalPageFault words = some record := by
  unfold InterruptEntry.authorizeCanonicalPageFault at hauthorized
  split at hauthorized <;> try simp_all
  split at hauthorized <;> try simp_all
  split at hauthorized <;> try simp_all
  split at hauthorized <;> simp_all

/-- Small projection lemma for #104: under the already checked authoritative
bindings, the stronger page-fault gate is definitionally the existing cleanup
and survivor transition. -/
theorem dispatchPageFault_checked_transition state plan report words trusted record denial
    (hrunning : state.halted = false)
    (hdecoded : InterruptEntry.decodeCanonicalPageFault words = some record)
    (huser : record.privilegeCode = 1)
    (hcurrent : state.scheduler.lifecycle.current =
      some trusted.entry.currentSubject)
    (hlive :
      state.scheduler.lifecycle.capabilities.subjects
        trusted.entry.currentSubject = true)
    (hrunnable :
      state.scheduler.lifecycle.runnable trusted.entry.currentSubject = true)
    (hspace : trusted.entry.activeAddressSpace =
      trusted.entry.currentSubject)
    (howner : state.scheduler.lifecycle.addressOwner
      trusted.entry.currentSubject = some trusted.entry.currentSubject)
    (hactive : state.translations.active =
      some trusted.entry.currentSubject)
    (hvirtualOwner : state.translations.virtual.owner
      trusted.entry.currentSubject = some trusted.entry.currentSubject)
    (hauthorized :
      (InterruptEntry.authorizeCanonicalPageFault words trusted state).authorized =
        some record)
    (hagreement : pageFaultAgreement state plan report record = .ok denial) :
    dispatchPageFault state plan report words trusted =
      dispatch state (.accepted (canonicalPageFaultFrame record)) := by
  unfold dispatchPageFault
  simp only [hrunning, hdecoded, huser, hcurrent, hlive, hrunnable,
    hspace, howner, hactive, hvirtualOwner, hauthorized, hagreement]
  simp

/-- Every admitted ordinary denial exposes the active root, live
mapping/lifetime check, cache-coherence precondition, exact architectural
decoder, and matching page-table classification. -/
theorem pageFaultClassificationAgreement_sound plan space report record decoded denial
    (hagreement :
      pageFaultClassificationAgreement plan space report record decoded = .ok denial) :
    ∃ cause,
      BootPageTablePlan.validateDecodedRoot plan report = .ok () ∧
      X86PageTable.classify (livePageTableAt report record.faultPage.toNat)
          record.faultPage.toNat (pageFaultAccessContext record) = .error cause ∧
        denialAgreement decoded cause = some denial := by
  simp only [pageFaultClassificationAgreement] at hagreement
  split at hagreement <;> try contradiction
  split at hagreement <;> try contradiction
  split at hagreement <;> try contradiction
  all_goals split at hagreement <;> try contradiction
  all_goals
    change Except.ok _ = Except.ok _ at hagreement
    injection hagreement with hdenial
    subst denial
    simp_all

set_option maxRecDepth 8192 in
theorem pageFaultAgreement_sound state plan report record denial
    (hagreement : pageFaultAgreement state plan report record = .ok denial) :
    ∃ space decoded cause,
      selectedBootSpace (activeFaultAddressSpace state) = some space ∧
        report.space = space ∧
        report.selectedRoot = plan.rootFrame space ∧
        record.activeCr3 = expectedCr3 plan space ∧
        BootPageTablePlan.validateDecodedRoot plan report = .ok () ∧
        livePlanAgreement state plan space
          (activeFaultAddressSpace state) record.faultPage.toNat = true ∧
        pageFaultTlbCoherent state (activeFaultAddressSpace state)
          record.faultPage.toNat (pageFaultAccessContext record) = true ∧
        InterruptEntry.decodePageFaultError record.errorWord = .ok decoded ∧
        X86PageTable.classify (livePageTableAt report record.faultPage.toNat)
          record.faultPage.toNat (pageFaultAccessContext record) = .error cause ∧
        denialAgreement decoded cause = some denial := by
  simp only [pageFaultAgreement] at hagreement
  split at hagreement <;> try contradiction
  split at hagreement <;> try contradiction
  split at hagreement <;> try contradiction
  split at hagreement <;> try contradiction
  split at hagreement <;> try contradiction
  split at hagreement <;> try contradiction
  split at hagreement <;> try contradiction
  split at hagreement <;> try contradiction
  split at hagreement <;> try contradiction
  split at hagreement <;> try contradiction
  all_goals
    rename_i hvalid selected space hspace hreportSpaceNeg hreportRootNeg
      hrootNeg hcontrols hliveNeg htlbNeg decodedResult decoded hdecoded
      himpossible
    obtain ⟨cause, hreport, hclassify, hdenial⟩ :=
      pageFaultClassificationAgreement_sound _ _ _ _ _ _ hagreement
    have hreportSpace : report.space = space :=
      Classical.byContradiction (fun hne => hreportSpaceNeg hne)
    have hreportRoot : report.selectedRoot = plan.rootFrame space :=
      Classical.byContradiction (fun hne => hreportRootNeg hne)
    have hroot : record.activeCr3 = expectedCr3 plan space := by
      apply Classical.byContradiction
      intro hne
      exact hrootNeg (by simp [hne])
    have hlive : livePlanAgreement state plan space
        (activeFaultAddressSpace state) record.faultPage.toNat = true := by
      cases hlive : livePlanAgreement state plan space
        (activeFaultAddressSpace state) record.faultPage.toNat <;> simp_all
    have htlb : pageFaultTlbCoherent state (activeFaultAddressSpace state)
        record.faultPage.toNat (pageFaultAccessContext record) = true := by
      cases hcoherent : pageFaultTlbCoherent state (activeFaultAddressSpace state)
        record.faultPage.toNat (pageFaultAccessContext record) <;> simp_all
    exact ⟨space, decoded, cause, hspace, hreportSpace, hreportRoot, hroot,
      hreport, hlive, htlb, hdecoded, hclassify, hdenial⟩

set_option maxRecDepth 8192 in
/-- Containment soundness stated from the observable successful result:
every successful strengthened page-fault cleanup has one exact codec-decoded,
independently authorized record and one active-root agreement witness. -/
theorem dispatchPageFault_success_sound state plan report words trusted
    (hsuccess :
      (dispatchPageFault state plan report words trusted).action =
          .idle .pageFault ∨
        ∃ context,
          (dispatchPageFault state plan report words trusted).action =
            .dispatch .pageFault context) :
    ∃ record denial,
      InterruptEntry.decodeCanonicalPageFault words = some record ∧
        (InterruptEntry.authorizeCanonicalPageFault words trusted state).authorized =
          some record ∧
        pageFaultAgreement state plan report record = .ok denial ∧
        ∃ space decoded cause,
          selectedBootSpace (activeFaultAddressSpace state) = some space ∧
            report.space = space ∧
            report.selectedRoot = plan.rootFrame space ∧
            record.activeCr3 = expectedCr3 plan space ∧
            BootPageTablePlan.validateDecodedRoot plan report = .ok () ∧
            livePlanAgreement state plan space
              (activeFaultAddressSpace state) record.faultPage.toNat = true ∧
            pageFaultTlbCoherent state (activeFaultAddressSpace state)
              record.faultPage.toNat (pageFaultAccessContext record) = true ∧
            InterruptEntry.decodePageFaultError record.errorWord = .ok decoded ∧
            X86PageTable.classify (livePageTableAt report record.faultPage.toNat)
              record.faultPage.toNat (pageFaultAccessContext record) =
                .error cause ∧
            denialAgreement decoded cause = some denial := by
  simp only [dispatchPageFault] at hsuccess
  split at hsuccess <;> try simp_all [halt, reject]
  split at hsuccess <;> try simp_all [halt, reject]
  all_goals split at hsuccess <;> try simp_all [halt, reject]
  all_goals split at hsuccess <;> try simp_all [halt, reject]
  all_goals split at hsuccess <;> try simp_all [halt, reject]
  all_goals split at hsuccess <;> try simp_all [halt, reject]
  all_goals split at hsuccess <;> try simp_all [halt, reject]
  all_goals split at hsuccess <;> try simp_all [halt, reject]
  all_goals
    have hdecodedAuthorized :=
      authorized_page_fault_is_decoded ResumablePreemption.State
        words trusted state _ (by assumption)
    simp_all only [Option.some.injEq]
    constructor
    · trivial
    · refine ⟨_, rfl, ?_⟩
      obtain ⟨space, decoded, cause, hspace, hreportSpace, hreportRoot,
          hroot, hreport, hlive, htlb,
          hdecoded, hclassify, hdenial⟩ :=
        pageFaultAgreement_sound _ _ _ _ _ (by assumption)
      exact ⟨space, hspace, hreportSpace, hreportRoot, hroot, hreport,
        hlive, htlb, decoded, hdecoded, cause, hclassify, hdenial⟩

/-- Integrity-fatal outcomes freeze every authoritative store while setting
the absorbing latch. -/
theorem dispatchPageFault_integrity_fatal_atomicity state plan report words trusted reason
    (hfatal : (dispatchPageFault state plan report words trusted).action =
      .fatal (.pageFaultIntegrity reason)) :
    (dispatchPageFault state plan report words trusted).state.halted = true ∧
      (dispatchPageFault state plan report words trusted).state.scheduler =
        state.scheduler ∧
      (dispatchPageFault state plan report words trusted).state.contexts =
        state.contexts ∧
      (dispatchPageFault state plan report words trusted).state.translations =
        state.translations := by
  simp only [dispatchPageFault] at hfatal ⊢
  split at hfatal <;> try simp_all [halt, reject]
  split at hfatal <;> try simp_all [halt, reject]
  all_goals split at hfatal <;> try simp_all [halt, reject]
  all_goals split at hfatal <;> try simp_all [halt, reject]
  all_goals split at hfatal <;> try simp_all [halt, reject]
  all_goals split at hfatal <;> try simp_all [halt, reject]
  all_goals split at hfatal <;> try simp_all [halt, reject]
  all_goals split at hfatal <;> try simp_all [halt, reject]
  all_goals
    exact fatal_atomicity state _ (.pageFaultIntegrity reason) hfatal

/-- Every fatal result of the strengthened page-fault boundary, including
kernel-origin and already-halted outcomes, freezes the authoritative stores. -/
theorem dispatchPageFault_fatal_atomicity state plan report words trusted reason
    (hfatal : (dispatchPageFault state plan report words trusted).action =
      .fatal reason) :
    (dispatchPageFault state plan report words trusted).state.halted = true ∧
      (dispatchPageFault state plan report words trusted).state.scheduler =
        state.scheduler ∧
      (dispatchPageFault state plan report words trusted).state.contexts =
        state.contexts ∧
      (dispatchPageFault state plan report words trusted).state.translations =
        state.translations := by
  simp only [dispatchPageFault] at hfatal ⊢
  split at hfatal <;> try simp_all [halt, reject]
  split at hfatal <;> try simp_all [halt, reject]
  all_goals split at hfatal <;> try simp_all [halt, reject]
  all_goals split at hfatal <;> try simp_all [halt, reject]
  all_goals split at hfatal <;> try simp_all [halt, reject]
  all_goals split at hfatal <;> try simp_all [halt, reject]
  all_goals split at hfatal <;> try simp_all [halt, reject]
  all_goals split at hfatal <;> try simp_all [halt, reject]
  all_goals exact fatal_atomicity state _ reason hfatal

/-- Stale nonfatal bindings reject before cleanup and retain the exact input
state. -/
theorem dispatchPageFault_rejected_unchanged state plan report words trusted reason
    (hrejected : (dispatchPageFault state plan report words trusted).action =
      .rejected reason) :
    (dispatchPageFault state plan report words trusted).state = state := by
  simp only [dispatchPageFault] at hrejected ⊢
  split at hrejected <;> try simp_all [halt, reject]
  split at hrejected <;> try simp_all [halt, reject]
  all_goals split at hrejected <;> try simp_all [halt, reject]
  all_goals split at hrejected <;> try simp_all [halt, reject]
  all_goals split at hrejected <;> try simp_all [halt, reject]
  all_goals split at hrejected <;> try simp_all [halt, reject]
  all_goals split at hrejected <;> try simp_all [halt, reject]
  all_goals split at hrejected <;> try simp_all [halt, reject]
  all_goals exact rejected_unchanged state _ reason hrejected

/-- The stronger page-fault gate preserves the complete resumable-preemption
invariant for every nonfatal result and for every fatal latch update. -/
theorem dispatchPageFault_preserves_wellFormed state plan report words trusted
    (hstate : ResumablePreemption.WellFormed state) :
    ResumablePreemption.WellFormed
      (dispatchPageFault state plan report words trusted).state := by
  simp only [dispatchPageFault]
  split <;> try simpa [halt, ResumablePreemption.wellFormed_set_halted] using hstate
  split <;> try simpa [halt, ResumablePreemption.wellFormed_set_halted] using hstate
  all_goals split <;> try simpa [halt, reject,
    ResumablePreemption.wellFormed_set_halted] using hstate
  all_goals split <;> try simpa [halt, reject,
    ResumablePreemption.wellFormed_set_halted] using hstate
  all_goals split <;> try simpa [halt, reject,
    ResumablePreemption.wellFormed_set_halted] using hstate
  all_goals split <;> try simpa [halt, reject,
    ResumablePreemption.wellFormed_set_halted] using hstate
  all_goals split <;> try simpa [halt, reject,
    ResumablePreemption.wellFormed_set_halted] using hstate
  all_goals split <;> try simpa [halt, reject,
    ResumablePreemption.wellFormed_set_halted] using hstate
  all_goals exact dispatch_preserves_wellFormed _ _ hstate

end LeanOS.FaultDispatch
