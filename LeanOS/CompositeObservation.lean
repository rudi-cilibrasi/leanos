import LeanOS.FailStop
import LeanOS.ReplayUnwinding

/-!
# Observer confidentiality over the authoritative composite state

This module lifts the replay unwinding of `LeanOS.ScheduledObservation` from
its separate scheduler/observation model to the authoritative
`FailStop.CompositeState`, executed through `FailStop.authoritativeGate`.

**Low equivalence.**  For an observing subject `S`, `observe S` collects:

* the public scheduler choice (`lifecycle.current`);
* S's authority: its liveness, slot capacity, complete finite capability row
  (`Capability.capabilitySpace`), and for every capability in that row the
  object it names (liveness, kind, endpoint mailbox, pending sealed transfer,
  blocking mailbox, blocking waiter queue, and frame backing);
* S's IPC observations: the messages queued on endpoints S names (above), the
  endpoint S waits on, and its blocking completion (delivered reply words);
* which address spaces S owns, and their mappings.

The frame backing of a named object and the set of spaces S owns are exactly
what S's own `map` reads beyond its capability; they are part of the view so
that step and output consistency for S's own memory operations hold
(`LeanOS.CompositeUnwinding`).

**Unwinding.**  `isSilent` is a decidable classification of authoritative
operations.  It is true only for an operation that another subject performs
and whose effects provably stay outside S's view.  Local respect
(`authoritativeGate_silent_observe`) is proved per operation family, using the
declared footprints and frame rule of `FailStop.Footprint` for the families
that write no projection S observes.  Every other operation is visible: its
event carries S's resulting view and, when S is the actor, S's reply.

**Scope.**  Silent families: `nmi`, `selectUserReturn`, `userReturn`, and
`restart` (frame rule); `capabilityCopy` whose destination is not S;
`capabilityRevoke` whose victim is not S; `map`, `unmap`, and memory
`syscall`s; and data-only `ipc` whose resolved endpoint is not named by S's
row.  All other ordinary operations, every blocking operation, and every
deferred drain are always visible to S here; `LeanOS.CompositeUnwinding`
extends the silent families under a trace invariant.  The scheduler's choice
is a public input: it is part of every view and scheduler operations are
always visible.

**Exclusions.**  Timing, caches, device reads, the termination channel, and
refinement to generated C or hardware are not modeled.  The theorem is
termination-insensitive and, as in the scheduler model, assumes equal observer
event projections.
-/
namespace LeanOS.CompositeObservation

open LeanOS
open LeanOS.FailStop
open LeanOS.CompositeFootprint (Projection)
set_option linter.unusedSimpArgs false

abbrev SubjectId := Capability.SubjectId
abbrev ObjectId := Capability.ObjectId

/-! ## The observer view -/

/-- What an observer sees of one object named by its capability row. -/
structure ObjectView where
  live : Bool
  kind : Option Capability.ObjectKind
  mailbox : Option EndpointIPC.Envelope
  sealed : Option CapabilityTransfer.Sealed
  blockingMailbox : Option BlockingIPC.Envelope
  waiters : List SubjectId
  /-- Whether a memory object is bound to a frame (`none`), and if so whether
  the allocator still records that frame as owned by the object.  This is
  exactly what `VirtualMapping.map` consults beyond the capability itself. -/
  backing : Option Bool
  deriving DecidableEq

/-- The frame-binding status `VirtualMapping.map` reads for one object. -/
def backing (state : CompositeState) (object : ObjectId) : Option Bool :=
  (state.virtualMemory.memory.binding object).map fun frame =>
    decide (state.virtualMemory.memory.allocator.status frame = .owned object)

def objectView (state : CompositeState) (object : ObjectId) : ObjectView :=
  { live := state.capabilities.objects object
    kind := state.capabilities.kinds object
    mailbox := state.ipc.endpoints.mailbox object
    sealed := state.transfers.pending object
    blockingMailbox := state.blockingIPC.mailbox object
    waiters := state.blockingIPC.waiters object
    backing := backing state object }

/-- The observer's complete, finite capability row. -/
def row (state : CompositeState) (observer : SubjectId) :
    List (Option Capability.Capability) :=
  Capability.capabilitySpace state.capabilities observer

/-- Whether some capability in the observer's row names `object`. -/
def Names (state : CompositeState) (observer : SubjectId) (object : ObjectId) : Bool :=
  (row state observer).any fun slot => slot.any (·.object == object)

structure View where
  /-- The scheduler's choice: a public input. -/
  scheduled : Option SubjectId
  live : Bool
  capacity : Nat
  row : List (Option Capability.Capability)
  named : List (Option ObjectView)
  /-- The address spaces the observer owns. -/
  owns : VirtualMapping.AddressSpaceId → Bool
  mappings : VirtualMapping.AddressSpaceId → VirtualMapping.VirtualPage →
    Option VirtualMapping.Mapping
  waitingOn : Option ObjectId
  completion : Option BlockingIPC.Completion

def observe (observer : SubjectId) (state : CompositeState) : View :=
  { scheduled := state.lifecycle.current
    live := state.capabilities.subjects observer
    capacity := state.capabilities.slotCapacity observer
    row := row state observer
    named := (row state observer).map (Option.map fun cap => objectView state cap.object)
    owns := fun space => decide (state.virtualMemory.owner space = some observer)
    mappings := fun space page =>
      if state.virtualMemory.owner space = some observer then
        state.virtualMemory.mappings space page
      else none
    waitingOn := state.blockingIPC.waiterEndpoint observer
    completion := state.blockingIPC.completion observer }

/-- Observer low equivalence on the authoritative composite state. -/
def LowEquiv (observer : SubjectId) (left right : CompositeState) : Prop :=
  observe observer left = observe observer right

/-- The projections the observer view reads. -/
def viewProjections : List Projection :=
  [.lifecycle, .capabilities, .virtualMemory, .ipc, .transfers, .blockingIPC]

/-- The view depends only on `viewProjections`. -/
theorem observe_eq_of_projections (observer : SubjectId) (before after : CompositeState)
    (same : ∀ projection, projection ∈ viewProjections →
      after.project projection = before.project projection) :
    observe observer after = observe observer before := by
  have hlifecycle : after.lifecycle = before.lifecycle := same .lifecycle (by decide)
  have hcapabilities : after.capabilities = before.capabilities := same .capabilities (by decide)
  have hvirtual : after.virtualMemory = before.virtualMemory := same .virtualMemory (by decide)
  have hipc : after.ipc = before.ipc := same .ipc (by decide)
  have htransfers : after.transfers = before.transfers := same .transfers (by decide)
  have hblocking : after.blockingIPC = before.blockingIPC := same .blockingIPC (by decide)
  simp [observe, row, objectView, backing, hlifecycle, hcapabilities, hvirtual, hipc,
    htransfers, hblocking]

/-- Field-wise sufficient condition for an unchanged view.  Objects outside the
observer's row and address spaces it does not own may change arbitrarily. -/
theorem observe_eq_of (observer : SubjectId) (before after : CompositeState)
    (hcurrent : after.lifecycle.current = before.lifecycle.current)
    (hlive : after.capabilities.subjects observer = before.capabilities.subjects observer)
    (hcapacity : after.capabilities.slotCapacity observer =
      before.capabilities.slotCapacity observer)
    (hslots : after.capabilities.slots observer = before.capabilities.slots observer)
    (hnamed : ∀ object, Names before observer object = true →
      objectView after object = objectView before object)
    (howner : after.virtualMemory.owner = before.virtualMemory.owner)
    (hmappings : ∀ space, before.virtualMemory.owner space = some observer →
      after.virtualMemory.mappings space = before.virtualMemory.mappings space)
    (hwaiting : after.blockingIPC.waiterEndpoint observer =
      before.blockingIPC.waiterEndpoint observer)
    (hcompletion : after.blockingIPC.completion observer =
      before.blockingIPC.completion observer) :
    observe observer after = observe observer before := by
  have hrow : row after observer = row before observer := by
    simp [row, Capability.capabilitySpace, hcapacity, hslots]
  have hnamedList :
      (row before observer).map (Option.map fun cap => objectView after cap.object) =
        (row before observer).map (Option.map fun cap => objectView before cap.object) := by
    apply List.map_congr_left
    intro slot hmem
    cases slot with
    | none => rfl
    | some cap =>
        have hnames : Names before observer cap.object = true := by
          simp only [Names, List.any_eq_true]
          exact ⟨some cap, hmem, by simp⟩
        simp [hnamed cap.object hnames]
  have hmap : (fun space page =>
        if after.virtualMemory.owner space = some observer then
          after.virtualMemory.mappings space page else none) =
      (fun space page =>
        if before.virtualMemory.owner space = some observer then
          before.virtualMemory.mappings space page else none) := by
    funext space page
    rw [howner]
    by_cases hown : before.virtualMemory.owner space = some observer
    · simp [hown, hmappings space hown]
    · simp [hown]
  have hown : (fun space => decide (after.virtualMemory.owner space = some observer)) =
      (fun space => decide (before.virtualMemory.owner space = some observer)) := by
    rw [howner]
  simp only [observe, hcurrent, hlive, hcapacity, hrow, hnamedList, hmap, hwaiting,
    hcompletion, hown]

/-! ## Silent operations -/

/-- The subject on whose behalf the composite executes an operation. -/
def actor (state : CompositeState) : SubjectId :=
  state.execution.core.context.currentSubject

/-- The endpoint a data-only IPC call would touch, resolved exactly as
`IPCSyscall.dispatch` resolves it. -/
def ipcTarget (state : CompositeState) (call : IPCSyscall.Call) : Option ObjectId :=
  let handleWord := match call with
    | .send handleWord _ _ => handleWord
    | .receive handleWord => handleWord
  match CapabilityHandle.resolveCurrent state.ipc.endpoints.capabilities
      { caller := actor state } handleWord .endpoint with
  | .ok resolution => some resolution.capability.object
  | .error _ => none

/-- Decidable silence classification for ordinary operations.  Every case that
returns `true` is justified by `applyOperation_silent_observe`. -/
def isSilentOrdinary (observer : SubjectId) (state : CompositeState) :
    Operation → Bool
  | .nmi _ _ | .selectUserReturn _ | .userReturn _ | .restart => actor state != observer
  | .capabilityCopy _ destination _ _ => actor state != observer && destination != observer
  | .capabilityRevoke _ victim _ => actor state != observer && victim != observer
  | .map _ _ _ | .unmap _ | .syscall _ => actor state != observer
  | .ipc call =>
      actor state != observer &&
        match ipcTarget state call with
        | none => true
        | some object => !Names state observer object
  | _ => false

/-- Blocking operations and deferred drains are always visible. -/
def isSilent (observer : SubjectId) (state : CompositeState) :
    AuthoritativeOperation → Bool
  | .ordinary operation => isSilentOrdinary observer state operation
  | .blocking _ | .drainDeferred _ => false

theorem isSilent_actor {observer state operation}
    (hsilent : isSilent observer state operation = true) : actor state ≠ observer := by
  cases operation with
  | ordinary operation =>
      cases operation <;> simp_all [isSilent, isSilentOrdinary] <;>
        (try split at hsilent) <;> simp_all
  | blocking _ => simp [isSilent] at hsilent
  | drainDeferred _ => simp [isSilent] at hsilent

/-! ### Subsystem frame facts -/

theorem copy_frame (capabilities : Capability.State) actor source destination
    destinationSlot rights (observer : SubjectId) (hne : destination ≠ observer) :
    let next := (Capability.copy capabilities actor source destination destinationSlot
      rights).state
    next.subjects = capabilities.subjects ∧ next.slotCapacity = capabilities.slotCapacity ∧
      next.slots observer = capabilities.slots observer ∧
      next.objects = capabilities.objects ∧ next.kinds = capabilities.kinds := by
  simp only [Capability.copy]
  repeat' split
  all_goals simp [Capability.reject, Capability.install]
  all_goals (funext slot; simp [Ne.symm hne])

theorem revokeRuntimeSafe_frame (capabilities : Capability.State) actor authoritySlot
    victim victimSlot (observer : SubjectId) (hne : victim ≠ observer) :
    let next := (Capability.revokeRuntimeSafe capabilities actor authoritySlot victim
      victimSlot).state
    next.subjects = capabilities.subjects ∧ next.slotCapacity = capabilities.slotCapacity ∧
      next.slots observer = capabilities.slots observer ∧
      next.objects = capabilities.objects ∧ next.kinds = capabilities.kinds := by
  simp only [Capability.revokeRuntimeSafe, Capability.revoke]
  repeat' split
  all_goals simp_all [Capability.reject, Capability.clear]
  all_goals (funext slot; simp [Ne.symm hne])

theorem map_frame (virtualMemory : VirtualMapping.State) actor slot space page permissions
    (observer : SubjectId) (hne : actor ≠ observer) :
    let next := (VirtualMapping.map virtualMemory actor slot space page permissions).state
    next.owner = virtualMemory.owner ∧ next.memory = virtualMemory.memory ∧
      ∀ candidate, virtualMemory.owner candidate = some observer →
        next.mappings candidate = virtualMemory.mappings candidate := by
  simp only [VirtualMapping.map]
  repeat' split
  all_goals simp_all [VirtualMapping.reject, VirtualMapping.setMapping]
  all_goals
    intro candidate hown
    funext candidatePage
    have hspace : candidate ≠ space := by
      intro hsame
      subst hsame
      simp_all
    simp [hspace]

theorem unmap_frame (virtualMemory : VirtualMapping.State) actor space page
    (observer : SubjectId) (hne : actor ≠ observer) :
    let next := (VirtualMapping.unmap virtualMemory actor space page).state
    next.owner = virtualMemory.owner ∧ next.memory = virtualMemory.memory ∧
      ∀ candidate, virtualMemory.owner candidate = some observer →
        next.mappings candidate = virtualMemory.mappings candidate := by
  simp only [VirtualMapping.unmap]
  repeat' split
  all_goals simp_all [VirtualMapping.reject, VirtualMapping.setMapping]
  all_goals
    intro candidate hown
    funext candidatePage
    have hspace : candidate ≠ space := by
      intro hsame
      subst hsame
      simp_all
    simp [hspace]

/-- A memory syscall (map, unmap, or access check) by another subject changes
only address spaces that subject owns. -/
theorem syscallDispatch_frame (virtualMemory : VirtualMapping.State)
    (context : Syscall.TrustedContext) (call : Syscall.UntrustedCall)
    (observer : SubjectId) (hne : context.caller ≠ observer) :
    let next := (Syscall.dispatch virtualMemory context call).state
    next.owner = virtualMemory.owner ∧ next.memory = virtualMemory.memory ∧
      ∀ candidate, virtualMemory.owner candidate = some observer →
        next.mappings candidate = virtualMemory.mappings candidate := by
  simp only [Syscall.dispatch]
  split
  · exact ⟨rfl, rfl, fun _ _ => rfl⟩
  · rename_i decoded _
    cases decoded with
    | map handleWord page permissions =>
        simp only [Syscall.dispatchDecoded]
        split
        · exact ⟨rfl, rfl, fun _ _ => rfl⟩
        · exact map_frame virtualMemory context.caller _ context.activeAddressSpace page
            permissions observer hne
    | unmap page =>
        exact unmap_frame virtualMemory context.caller context.activeAddressSpace page
          observer hne
    | access page access =>
        simp only [Syscall.dispatchDecoded]
        split <;> exact ⟨rfl, rfl, fun _ _ => rfl⟩

theorem resolveCurrent_ok_lookup (capabilities : Capability.State) caller word expected
    resolution
    (hresolve : CapabilityHandle.resolveCurrent capabilities { caller } word expected =
      .ok resolution) :
    Capability.lookup capabilities caller resolution.handle.slot =
      .found resolution.capability := by
  simp only [CapabilityHandle.resolveCurrent] at hresolve
  split at hresolve
  · simp at hresolve
  · rename_i handle _
    split at hresolve
    · simp at hresolve
    · rename_i capability hcap
      simp only [Except.ok.injEq] at hresolve
      subst hresolve
      simp only [CapabilityHandle.resolve] at hcap
      repeat' split at hcap
      all_goals simp_all [Capability.lookup, Capability.slotInRange]

theorem endpointSend_mailbox_other (endpoints : EndpointIPC.State) caller slot payload
    (cap : Capability.Capability) (object : ObjectId)
    (hlookup : Capability.lookup endpoints.capabilities caller slot = .found cap)
    (hne : cap.object ≠ object) :
    (EndpointIPC.send endpoints caller slot payload).state.mailbox object =
      endpoints.mailbox object := by
  simp only [EndpointIPC.send, hlookup]
  repeat' split
  all_goals simp [EndpointIPC.reject, EndpointIPC.setOption, Ne.symm hne]

theorem endpointReceive_mailbox_other (endpoints : EndpointIPC.State) caller slot
    (cap : Capability.Capability) (object : ObjectId)
    (hlookup : Capability.lookup endpoints.capabilities caller slot = .found cap)
    (hne : cap.object ≠ object) :
    (EndpointIPC.receive endpoints caller slot).state.mailbox object =
      endpoints.mailbox object := by
  simp only [EndpointIPC.receive, hlookup]
  repeat' split
  all_goals simp [EndpointIPC.rejectReceive, EndpointIPC.setOption, Ne.symm hne]

/-- Data-only IPC changes exactly the mailbox of its resolved endpoint. -/
theorem ipcDispatch_mailbox_other (state : CompositeState) (call : IPCSyscall.Call)
    (object : ObjectId) (hne : ipcTarget state call ≠ some object) :
    (IPCSyscall.dispatch state.ipc state.ipcContext call).state.endpoints.mailbox object =
      state.ipc.endpoints.mailbox object := by
  cases call with
  | send handleWord word0 word1 =>
      simp only [IPCSyscall.dispatch]
      split
      · rfl
      · rename_i resolution hresolve
        have htarget : ipcTarget state (.send handleWord word0 word1) =
            some resolution.capability.object := by
          simp only [ipcTarget, actor]
          rw [show state.ipcContext.caller = state.execution.core.context.currentSubject
            from rfl] at hresolve
          rw [hresolve]
        exact endpointSend_mailbox_other _ _ _ _ resolution.capability object
          (resolveCurrent_ok_lookup _ _ _ _ _ hresolve)
          (fun heq => hne (by rw [htarget, heq]))
  | receive handleWord =>
      simp only [IPCSyscall.dispatch]
      split
      · rfl
      · rename_i resolution hresolve
        have htarget : ipcTarget state (.receive handleWord) =
            some resolution.capability.object := by
          simp only [ipcTarget, actor]
          rw [show state.ipcContext.caller = state.execution.core.context.currentSubject
            from rfl] at hresolve
          rw [hresolve]
        exact endpointReceive_mailbox_other _ _ _ resolution.capability object
          (resolveCurrent_ok_lookup _ _ _ _ _ hresolve)
          (fun heq => hne (by rw [htarget, heq]))

/-! ### Local respect per operation family -/

/-- Families whose declared write set misses every projection the view reads
are invisible by the composite frame rule alone. -/
theorem applyOperation_observe_of_untouched (observer : SubjectId) (state : CompositeState)
    (operation : Operation)
    (untouched : ∀ projection, projection ∈ viewProjections →
      CompositeFootprint.Untouched operation.footprint projection) :
    observe observer (applyOperation state operation) = observe observer state :=
  observe_eq_of_projections observer state _ fun projection hmem =>
    applyOperation_project_untouched state operation projection (untouched projection hmem)

theorem observe_installCopiedCapabilities (observer : SubjectId) (state : CompositeState)
    (capabilities : Capability.State)
    (hsubjects : capabilities.subjects = state.capabilities.subjects)
    (hcapacity : capabilities.slotCapacity = state.capabilities.slotCapacity)
    (hslots : capabilities.slots observer = state.capabilities.slots observer)
    (hobjects : capabilities.objects = state.capabilities.objects)
    (hkinds : capabilities.kinds = state.capabilities.kinds) :
    observe observer (installCopiedCapabilities state capabilities) = observe observer state := by
  apply observe_eq_of <;> simp [installCopiedCapabilities, objectView, hsubjects, hcapacity,
    hslots, hobjects, hkinds]
  intro _ _
  rfl

theorem observe_installVirtualMemory (observer : SubjectId) (state : CompositeState)
    (virtualMemory : VirtualMapping.State) (translations : TLB.State)
    (howner : virtualMemory.owner = state.virtualMemory.owner)
    (hmemory : virtualMemory.memory = state.virtualMemory.memory)
    (hmappings : ∀ space, state.virtualMemory.owner space = some observer →
      virtualMemory.mappings space = state.virtualMemory.mappings space) :
    observe observer (installVirtualMemory state virtualMemory translations) =
      observe observer state := by
  apply observe_eq_of <;> simp [installVirtualMemory, objectView, backing, howner, hmemory]
  exact hmappings

theorem observe_installIPC (observer : SubjectId) (state : CompositeState)
    (ipc : IPCSyscall.State)
    (hmailbox : ∀ object, Names state observer object = true →
      ipc.endpoints.mailbox object = state.ipc.endpoints.mailbox object) :
    observe observer (installIPC state ipc) = observe observer state := by
  apply observe_eq_of <;> simp [installIPC, objectView]
  intro object hnames
  exact ⟨hmailbox object hnames, rfl⟩

theorem observe_dispatchIPC (observer : SubjectId) (state : CompositeState)
    (call : IPCSyscall.Call)
    (hdisjoint : ∀ object, Names state observer object = true →
      ipcTarget state call ≠ some object) :
    observe observer (dispatchIPC state call).state = observe observer state := by
  have hinstall : observe observer
      (installIPC state (IPCSyscall.dispatch state.ipc state.ipcContext call).state) =
        observe observer state :=
    observe_installIPC observer state _ fun object hnames =>
      ipcDispatch_mailbox_other state call object (hdisjoint object hnames)
  cases call with
  | send handleWord word0 word1 => exact hinstall
  | receive handleWord =>
      simp only [dispatchIPC]
      repeat' split
      all_goals first | rfl | exact hinstall

/-- Arming or disarming the return authority writes only `execution`. -/
theorem observe_selectLiveReturnAuthority (observer : SubjectId) (state : CompositeState)
    (purpose : Interrupt.ReturnPurpose) :
    observe observer (selectLiveReturnAuthority state purpose) = observe observer state :=
  observe_eq_of_projections observer state _ fun projection hmem =>
    selectLiveReturnAuthority_frames state purpose projection (by
      simp only [viewProjections, List.mem_cons, List.mem_nil_iff, or_false] at hmem
      rcases hmem with h | h | h | h | h | h <;> subst h <;> untouched_decide)

/-- **Local respect** for ordinary operations: every operation classified as
silent leaves the observer's view literally unchanged. -/
theorem applyOperation_silent_observe (observer : SubjectId) (state : CompositeState)
    (operation : Operation) (hsilent : isSilentOrdinary observer state operation = true) :
    observe observer (applyOperation state operation) = observe observer state := by
  cases operation with
  | nmi raw context =>
      exact applyOperation_observe_of_untouched observer state _
        (by simp only [CompositeFootprint.Untouched, Operation.footprint]; decide)
  | selectUserReturn purpose =>
      exact applyOperation_observe_of_untouched observer state _
        (by simp only [CompositeFootprint.Untouched, Operation.footprint]; decide)
  | userReturn request =>
      exact applyOperation_observe_of_untouched observer state _
        (by simp only [CompositeFootprint.Untouched, Operation.footprint]; decide)
  | restart =>
      exact applyOperation_observe_of_untouched observer state _
        (by simp only [CompositeFootprint.Untouched, Operation.footprint]; decide)
  | capabilityCopy source destination destinationSlot rights =>
      simp only [isSilentOrdinary, Bool.and_eq_true, bne_iff_ne, ne_eq] at hsilent
      obtain ⟨hsubjects, hcapacity, hslots, hobjects, hkinds⟩ :=
        copy_frame state.capabilities state.execution.core.context.currentSubject source
          destination destinationSlot rights observer hsilent.2
      simp only [applyOperation]
      split
      · rfl
      · exact observe_installCopiedCapabilities observer state _ hsubjects hcapacity hslots
          hobjects hkinds
  | capabilityRevoke authoritySlot victim victimSlot =>
      simp only [isSilentOrdinary, Bool.and_eq_true, bne_iff_ne, ne_eq] at hsilent
      obtain ⟨hsubjects, hcapacity, hslots, hobjects, hkinds⟩ :=
        revokeRuntimeSafe_frame state.capabilities state.execution.core.context.currentSubject
          authoritySlot victim victimSlot observer hsilent.2
      simp only [applyOperation]
      split
      · rfl
      · exact observe_installCopiedCapabilities observer state _ hsubjects hcapacity hslots
          hobjects hkinds
  | map slot page permissions =>
      simp only [isSilentOrdinary, bne_iff_ne, ne_eq, actor] at hsilent
      obtain ⟨howner, hmemory, hmappings⟩ := map_frame state.virtualMemory
        state.execution.core.context.currentSubject slot
        state.execution.core.context.activeAddressSpace page permissions observer hsilent
      simp only [applyOperation]
      split
      · rfl
      · exact observe_installVirtualMemory observer state _ _ howner hmemory hmappings
  | unmap page =>
      simp only [isSilentOrdinary, bne_iff_ne, ne_eq, actor] at hsilent
      obtain ⟨howner, hmemory, hmappings⟩ := unmap_frame state.virtualMemory
        state.execution.core.context.currentSubject
        state.execution.core.context.activeAddressSpace page observer hsilent
      simp only [applyOperation]
      split
      · rfl
      · exact observe_installVirtualMemory observer state _ _ howner hmemory hmappings
  | syscall call =>
      simp only [isSilentOrdinary, bne_iff_ne, ne_eq, actor] at hsilent
      obtain ⟨howner, hmemory, hmappings⟩ := syscallDispatch_frame state.virtualMemory
        state.syscallContext call observer hsilent
      simp only [applyOperation]
      split
      · rfl
      · split
        · exact observe_selectLiveReturnAuthority observer state _
        · rw [observe_selectLiveReturnAuthority]
          exact observe_installVirtualMemory observer state _ _ howner hmemory hmappings
        · rw [observe_selectLiveReturnAuthority]
          exact observe_installVirtualMemory observer state _ _ howner hmemory hmappings
  | ipc call =>
      simp only [isSilentOrdinary, Bool.and_eq_true] at hsilent
      have hdisjoint : ∀ object, Names state observer object = true →
          ipcTarget state call ≠ some object := by
        intro object hnames htarget
        have h := hsilent.2
        rw [htarget] at h
        simp [hnames] at h
      simp only [applyOperation]
      split <;> first | rfl | exact observe_dispatchIPC observer state call hdisjoint
  | _ => simp [isSilentOrdinary] at hsilent

theorem gate_state_cases (state : CompositeState) (operation : Operation) :
    (gate state operation).state = state ∨
      (gate state operation).state = applyOperation state operation := by
  cases operation <;> cases hmode : state.execution.mode <;> simp [gate, hmode]

/-- **Local respect** on the authoritative gate, including busy and halted
stutters. -/
theorem authoritativeGate_silent_observe (observer : SubjectId) (state : CompositeState)
    (operation : AuthoritativeOperation) (hsilent : isSilent observer state operation = true) :
    observe observer (authoritativeGate state operation).state = observe observer state := by
  cases operation with
  | ordinary operation =>
      rw [authoritativeGate_ordinary_state]
      rcases gate_state_cases state operation with hsame | happly
      · rw [hsame]
      · rw [happly]
        exact applyOperation_silent_observe observer state operation hsilent
  | blocking _ => simp [isSilent] at hsilent
  | drainDeferred _ => simp [isSilent] at hsilent

/-! ## Step consistency -/

/-- **Step consistency by the frame rule.**  An operation whose declared write
set misses the view's projections preserves low equivalence whoever performs
it, including the observer itself. -/
theorem step_consistent_of_untouched (observer : SubjectId) (left right : CompositeState)
    (operation : Operation)
    (untouched : ∀ projection, projection ∈ viewProjections →
      CompositeFootprint.Untouched operation.footprint projection)
    (hlow : LowEquiv observer left right) :
    LowEquiv observer (authoritativeGate left (.ordinary operation)).state
      (authoritativeGate right (.ordinary operation)).state := by
  have hframe : ∀ state : CompositeState,
      observe observer (authoritativeGate state (.ordinary operation)).state =
        observe observer state := fun state => by
    rw [authoritativeGate_ordinary_state]
    exact observe_eq_of_projections observer state _ fun projection hmem =>
      gate_frames state operation projection (untouched projection hmem)
  unfold LowEquiv at *
  rw [hframe left, hframe right, hlow]

/-- **Step consistency for silent steps.**  Independently chosen operations
that are silent for the observer preserve low equivalence. -/
theorem silent_steps_lowEquiv (observer : SubjectId) (left right : CompositeState)
    (leftOperation rightOperation : AuthoritativeOperation)
    (hlow : LowEquiv observer left right)
    (hleft : isSilent observer left leftOperation = true)
    (hright : isSilent observer right rightOperation = true) :
    LowEquiv observer (authoritativeGate left leftOperation).state
      (authoritativeGate right rightOperation).state := by
  unfold LowEquiv at *
  rw [authoritativeGate_silent_observe observer left leftOperation hleft,
    authoritativeGate_silent_observe observer right rightOperation hright, hlow]

/-! ## Output consistency for the observer's own IPC

The observer's replies to its own data-only IPC calls (including delivered
sender and reply words) are a function of its view: low-equivalent states give
equal replies.  The only extra premise is that the IPC and transfer
capability copies are the published `capabilities` projection, which
`CompositeState.Coherent` provides. -/

theorem row_getElem? (state : CompositeState) (observer : SubjectId) (slot : Nat)
    (hslot : slot < state.capabilities.slotCapacity observer) :
    (row state observer)[slot]? = some (state.capabilities.slots observer slot) := by
  simp [row, Capability.capabilitySpace, hslot]

theorem LowEquiv.live {observer left right} (hlow : LowEquiv observer left right) :
    left.capabilities.subjects observer = right.capabilities.subjects observer :=
  congrArg View.live hlow

theorem LowEquiv.capacity {observer left right} (hlow : LowEquiv observer left right) :
    left.capabilities.slotCapacity observer = right.capabilities.slotCapacity observer :=
  congrArg View.capacity hlow

/-- Low-equivalent states agree on every in-range slot of the observer's row
and on every object such a slot names. -/
theorem LowEquiv.slot {observer left right} (hlow : LowEquiv observer left right)
    (slot : Nat) (hslot : slot < left.capabilities.slotCapacity observer) :
    left.capabilities.slots observer slot = right.capabilities.slots observer slot ∧
      ∀ cap, left.capabilities.slots observer slot = some cap →
        objectView left cap.object = objectView right cap.object := by
  have hslot' : slot < right.capabilities.slotCapacity observer := hlow.capacity ▸ hslot
  have hrow := congrArg (fun view => view.row[slot]?) hlow
  have hnamed := congrArg (fun view => view.named[slot]?) hlow
  simp only [observe, List.getElem?_map, row_getElem? left observer slot hslot,
    row_getElem? right observer slot hslot', Option.map_some, Option.some.injEq] at hrow hnamed
  refine ⟨hrow, ?_⟩
  intro cap hcap
  rw [← hrow, hcap] at hnamed
  simpa using hnamed

theorem lookup_found_inRange (capabilities : Capability.State) subject slot cap
    (hfound : Capability.lookup capabilities subject slot = .found cap) :
    slot < capabilities.slotCapacity subject ∧ capabilities.slots subject slot = some cap := by
  simp only [Capability.lookup, Capability.slotInRange] at hfound
  by_cases hsubject : capabilities.subjects subject = true
  · by_cases hin : slot < capabilities.slotCapacity subject
    · cases hslot : capabilities.slots subject slot <;> simp_all
    · simp [hsubject, hin] at hfound
  · simp [hsubject] at hfound

theorem LowEquiv.lookup {observer left right} (hlow : LowEquiv observer left right)
    (slot : Nat) :
    Capability.lookup left.capabilities observer slot =
      Capability.lookup right.capabilities observer slot := by
  simp only [Capability.lookup, Capability.slotInRange, hlow.live, hlow.capacity]
  by_cases hin : slot < right.capabilities.slotCapacity observer
  · rw [(hlow.slot slot (hlow.capacity ▸ hin)).1]
    rfl
  · simp [hin]

theorem LowEquiv.resolve {observer left right} (hlow : LowEquiv observer left right)
    (handle : CapabilityHandle.Handle) (expected : Capability.ObjectKind) :
    CapabilityHandle.resolve left.capabilities observer handle expected =
      CapabilityHandle.resolve right.capabilities observer handle expected := by
  simp only [CapabilityHandle.resolve, Capability.slotInRange, hlow.live, hlow.capacity]
  by_cases hin : handle.slot < right.capabilities.slotCapacity observer
  · obtain ⟨hslot, hobject⟩ := hlow.slot handle.slot (hlow.capacity ▸ hin)
    rw [hslot]
    cases hcase : right.capabilities.slots observer handle.slot with
    | none => rfl
    | some cap =>
        have hview := hobject cap (hslot.trans hcase)
        have hlive := congrArg ObjectView.live hview
        have hkind := congrArg ObjectView.kind hview
        simp only [objectView] at hlive hkind
        simp [hlive, hkind]
  · simp [hin]

theorem LowEquiv.resolveCurrent {observer left right} (hlow : LowEquiv observer left right)
    (word : UInt64) (expected : Capability.ObjectKind) :
    CapabilityHandle.resolveCurrent left.capabilities { caller := observer } word expected =
      CapabilityHandle.resolveCurrent right.capabilities { caller := observer } word expected := by
  simp only [CapabilityHandle.resolveCurrent, hlow.resolve]

/-- The endpoint view of an object the observer can look up is shared. -/
theorem LowEquiv.lookupObject {observer left right} (hlow : LowEquiv observer left right)
    (slot : Nat) (cap : Capability.Capability)
    (hfound : Capability.lookup right.capabilities observer slot = .found cap) :
    objectView left cap.object = objectView right cap.object := by
  obtain ⟨hin, hslot⟩ := lookup_found_inRange _ _ _ _ hfound
  obtain ⟨hsame, hobject⟩ := hlow.slot slot (hlow.capacity ▸ hin)
  exact hobject cap (hsame.trans hslot)

theorem LowEquiv.scheduled {observer left right} (hlow : LowEquiv observer left right) :
    left.lifecycle.current = right.lifecycle.current :=
  congrArg View.scheduled hlow

theorem LowEquiv.rowEq {observer left right} (hlow : LowEquiv observer left right) :
    row left observer = row right observer :=
  congrArg View.row hlow

theorem LowEquiv.namesEq {observer left right} (hlow : LowEquiv observer left right)
    (object : ObjectId) : Names left observer object = Names right observer object := by
  simp only [Names, hlow.rowEq]

theorem LowEquiv.ownsIff {observer left right} (hlow : LowEquiv observer left right)
    (space : VirtualMapping.AddressSpaceId) :
    left.virtualMemory.owner space = some observer ↔
      right.virtualMemory.owner space = some observer := by
  have h := congrFun (congrArg View.owns hlow) space
  simp only [observe, decide_eq_decide] at h
  exact h

theorem LowEquiv.ownedMappings {observer left right} (hlow : LowEquiv observer left right)
    (space : VirtualMapping.AddressSpaceId)
    (hown : left.virtualMemory.owner space = some observer) :
    left.virtualMemory.mappings space = right.virtualMemory.mappings space := by
  funext page
  have h := congrFun (congrFun (congrArg View.mappings hlow) space) page
  simp only [observe, hown, (hlow.ownsIff space).1 hown, ↓reduceIte] at h
  exact h

/-- Low-equivalent states agree on the view of every object the observer
names. -/
theorem LowEquiv.namedView {observer left right} (hlow : LowEquiv observer left right)
    (object : ObjectId) (hnames : Names left observer object = true) :
    objectView left object = objectView right object := by
  have hnamed := congrArg View.named hlow
  simp only [observe] at hnamed
  rw [← hlow.rowEq] at hnamed
  have hpointwise := List.map_inj_left.mp hnamed
  simp only [Names, List.any_eq_true] at hnames
  obtain ⟨slot, hmem, hslot⟩ := hnames
  cases slot with
  | none => simp at hslot
  | some cap =>
      simp only [Option.any_some, beq_iff_eq] at hslot
      have h := hpointwise (some cap) hmem
      simp only [Option.map_some, Option.some.injEq] at h
      rw [← hslot]
      exact h

theorem LowEquiv.endpointSend {observer left right} (hlow : LowEquiv observer left right)
    (hleft : left.ipc.endpoints.capabilities = left.capabilities)
    (hright : right.ipc.endpoints.capabilities = right.capabilities)
    (slot : Nat) (payload : EndpointIPC.Payload) :
    (EndpointIPC.send left.ipc.endpoints observer slot payload).result =
      (EndpointIPC.send right.ipc.endpoints observer slot payload).result := by
  simp only [EndpointIPC.send, hleft, hright, hlow.lookup slot]
  cases hfound : Capability.lookup right.capabilities observer slot with
  | invalidSubject => rfl
  | staleSlot => rfl
  | found cap =>
      have hview := hlow.lookupObject slot cap hfound
      have hlive := congrArg ObjectView.live hview
      have hkind := congrArg ObjectView.kind hview
      have hmailbox := congrArg ObjectView.mailbox hview
      simp only [objectView] at hlive hkind hmailbox
      simp only [hlive, hkind, hmailbox]
      repeat' split
      all_goals rfl

theorem LowEquiv.endpointReceive {observer left right} (hlow : LowEquiv observer left right)
    (hleft : left.ipc.endpoints.capabilities = left.capabilities)
    (hright : right.ipc.endpoints.capabilities = right.capabilities)
    (slot : Nat) :
    (EndpointIPC.receive left.ipc.endpoints observer slot).result =
      (EndpointIPC.receive right.ipc.endpoints observer slot).result := by
  simp only [EndpointIPC.receive, hleft, hright, hlow.lookup slot]
  cases hfound : Capability.lookup right.capabilities observer slot with
  | invalidSubject => rfl
  | staleSlot => rfl
  | found cap =>
      have hview := hlow.lookupObject slot cap hfound
      have hlive := congrArg ObjectView.live hview
      have hkind := congrArg ObjectView.kind hview
      have hmailbox := congrArg ObjectView.mailbox hview
      simp only [objectView] at hlive hkind hmailbox
      simp only [hlive, hkind, hmailbox]
      repeat' split
      all_goals rfl

/-- The capability copies consumed by data-only IPC are the published
`capabilities` projection (a consequence of `CompositeState.Coherent`). -/
def IPCCapabilitiesPublished (state : CompositeState) : Prop :=
  state.ipc.endpoints.capabilities = state.capabilities ∧
    state.transfers.capabilities = state.capabilities

theorem ipcCapabilitiesPublished_of_coherent {state : CompositeState}
    (hcoherent : state.Coherent) : IPCCapabilitiesPublished state := by
  rcases hcoherent with
    ⟨_, _, _, hcapabilities, _, _, hipc, _, _, htransfers, _, _, _⟩
  refine ⟨hipc.trans hcapabilities.symm, ?_⟩
  have : state.transfers.capabilities = state.ipc.endpoints.capabilities := by
    rw [← htransfers]
  rw [this, hipc, hcapabilities]

/-- **Output consistency (IPC).**  When the observer performs the same
data-only IPC call in two low-equivalent states, it receives the same reply,
including the delivered sender and reply words. -/
theorem ipc_output_consistent (observer : SubjectId) (left right : CompositeState)
    (call : IPCSyscall.Call) (hlow : LowEquiv observer left right)
    (hleftActor : actor left = observer) (hrightActor : actor right = observer)
    (hleft : IPCCapabilitiesPublished left) (hright : IPCCapabilitiesPublished right) :
    operationReply left (.ipc call) = operationReply right (.ipc call) := by
  simp only [actor] at hleftActor hrightActor
  simp only [operationReply]
  cases call with
  | send handleWord word0 word1 =>
      simp only [dispatchIPC, IPCSyscall.dispatch, CompositeState.ipcContext, hleftActor,
        hrightActor, hleft.1, hright.1, hlow.resolveCurrent]
      split
      · rfl
      · rw [hlow.endpointSend hleft.1 hright.1]
  | receive handleWord =>
      have hinner : (IPCSyscall.dispatch left.ipc left.ipcContext (.receive handleWord)).reply =
          (IPCSyscall.dispatch right.ipc right.ipcContext (.receive handleWord)).reply := by
        simp only [IPCSyscall.dispatch, CompositeState.ipcContext, hleftActor, hrightActor,
          hleft.1, hright.1, hlow.resolveCurrent]
        split
        · rfl
        · rw [hlow.endpointReceive hleft.1 hright.1]
      simp only [dispatchIPC, hleftActor, hrightActor, hleft.2, hright.2,
        hlow.resolveCurrent]
      split
      · rename_i endpoint hresolve
        have hview := hlow.lookupObject _ _
          (resolveCurrent_ok_lookup _ _ _ _ _ hresolve)
        have hsealed := congrArg ObjectView.sealed hview
        simp only [objectView] at hsealed
        rw [hsealed]
        split
        · rfl
        · simp only [CompositeIPCOutcome.mk.injEq] at hinner ⊢
          rw [hinner]
      · simp only [CompositeIPCOutcome.mk.injEq] at hinner ⊢
        rw [hinner]

/-! ## Observer events and finite traces -/

/-- One observer event: the observer's resulting view, plus the gate result
when the observer is the actor. -/
structure Event where
  view : View
  reply : Option AuthoritativeGateResult

/-- Execute one authoritative operation through `authoritativeGate`; silent
operations emit nothing. -/
def execute (observer : SubjectId) (state : CompositeState)
    (operation : AuthoritativeOperation) : CompositeState × Option Event :=
  let outcome := authoritativeGate state operation
  (outcome.state,
    if isSilent observer state operation then none
    else some
      { view := observe observer outcome.state
        reply := if actor state = observer then some outcome.result else none })

/-- The composite observer model as an instance of the shared replay unwinding
structure. -/
def system (observer : SubjectId) :
    ReplayUnwinding.System CompositeState AuthoritativeOperation Event View where
  observe := observe observer
  execute := execute observer
  applyEvent _ event := event.view

def run (observer : SubjectId) (state : CompositeState)
    (operations : List AuthoritativeOperation) : CompositeState × List Event :=
  ReplayUnwinding.run (system observer) state operations

def projection (observer : SubjectId) (state : CompositeState)
    (operations : List AuthoritativeOperation) : List Event :=
  ReplayUnwinding.projection (system observer) state operations

/-- The run's state component is exactly the authoritative gate trace. -/
theorem run_state (observer : SubjectId) (state : CompositeState)
    (operations : List AuthoritativeOperation) :
    (run observer state operations).1 =
      operations.foldl (fun current operation => (authoritativeGate current operation).state)
        state := by
  induction operations generalizing state with
  | nil => rfl
  | cons operation rest ih =>
      simp only [run, ReplayUnwinding.run, List.foldl] at ih ⊢
      exact ih _

theorem system_replays (observer : SubjectId) :
    ReplayUnwinding.Replays (system observer) := by
  apply ReplayUnwinding.replays_of_unwinding
  · intro state operation hnone
    simp only [system, execute] at hnone ⊢
    split at hnone
    · rename_i hsilent
      exact authoritativeGate_silent_observe observer state operation hsilent
    · simp at hnone
  · intro state operation event hsome
    simp only [system, execute] at hsome ⊢
    split at hsome
    · simp at hsome
    · simp only [Option.some.injEq] at hsome
      rw [← hsome]

/-- **Composite finite-trace noninterference.**  For an observer `S`, two
finite runs of `authoritativeGate` from S-low-equivalent composite states that
emit equal S-event projections end in S-low-equivalent states.  Silent steps
(another subject's operation that provably stays outside S's view) emit no
event, so the runs may differ in their number and choice. -/
theorem finite_trace_lowEquiv (observer : SubjectId) (left right : CompositeState)
    (leftOperations rightOperations : List AuthoritativeOperation)
    (hlow : LowEquiv observer left right)
    (hevents : projection observer left leftOperations =
      projection observer right rightOperations) :
    LowEquiv observer (run observer left leftOperations).1
      (run observer right rightOperations).1 :=
  ReplayUnwinding.finite_trace_lowEquiv (system observer) (system_replays observer)
    left right leftOperations rightOperations hlow hevents

/-! ## Executable evidence

Subject 0 observes.  Subject 1 holds endpoint 10 and endpoint 20.  The
observer holds a send-only descendant of subject 1's endpoint-10 capability, so
endpoint 10 is shared with the observer; endpoint 20 is shared only with
subject 2.  The paired states differ only in a message queued on endpoint 20.
Every other field comes from an arbitrary `base` composite state. -/
namespace Evidence

def endpointCap (object identity : Nat) (rights : Capability.Rights)
    (parent : Option Nat := none) : Capability.Capability :=
  { object, kind := .endpoint, rights, identity, parent }

def capabilities : Capability.State :=
  { nextIdentity := 5
    derivations := fun identity =>
      if identity = 4 then some (some 1, 10, .endpoint, { send := true }) else none
    subjects := fun subject => subject < 3
    objects := fun object => object = 10 || object = 20
    kinds := fun object => if object = 10 || object = 20 then some .endpoint else none
    slots := fun subject slot =>
      match subject, slot with
      | 0, 0 => some (endpointCap 10 4 { send := true } (some 1))
      | 1, 0 => some (endpointCap 10 1 { send := true, grant := true, revoke := true })
      | 1, 1 => some (endpointCap 20 2 { send := true, receive := true, grant := true })
      | 2, 0 => some (endpointCap 20 3 { receive := true })
      | _, _ => none }

/-- Subject 1 is executing; endpoint 20 carries `secret`. -/
def composite (base : CompositeState) (secret : UInt64) : CompositeState :=
  let endpoints := { base.ipc.endpoints with
    capabilities
    mailbox := fun object =>
      if object = 20 then
        some { endpoint := 20, sender := 1, payload := { word0 := secret, word1 := 0 } }
      else none }
  { base with
    execution := { base.execution with
      mode := .running
      core := { base.execution.core with
        context := { base.execution.core.context with currentSubject := 1 } } }
    capabilities
    ipc := { base.ipc with endpoints }
    transfers := { base.transfers with toEndpointState := endpoints, pending := fun _ => none } }

/-- Subject 1's handle for endpoint 20 (slot 1, generation 2). -/
def privateWord : UInt64 := 131073
/-- Subject 1's handle for the shared endpoint 10 (slot 0, generation 1). -/
def sharedWord : UInt64 := 65536

/-- Subject 1 revokes the subtree of its endpoint-10 capability, which contains
the observer's derived capability. -/
def sharedRevoke : AuthoritativeOperation := .ordinary (.capabilityRevokeSubtree 0 1 0)

def privateTrace : List AuthoritativeOperation :=
  [.ordinary (.ipc (.receive privateWord)),
   .ordinary (.capabilityCopy 1 2 2 { send := true }),
   .ordinary .restart]

example (base : CompositeState) : LowEquiv 0 (composite base 7) (composite base 99) := rfl

/-- Unrelated IPC, delegation to a third subject, and a frame-rule operation are
silent; IPC on the shared endpoint and subtree revocation are not. -/
example (base : CompositeState) :
    isSilent 0 (composite base 7) (.ordinary (.ipc (.receive privateWord))) = true ∧
      isSilent 0 (composite base 7) (.ordinary (.capabilityCopy 1 2 2 { send := true })) =
        true ∧
      isSilent 0 (composite base 7) (.ordinary .restart) = true ∧
      isSilent 0 (composite base 7) (.ordinary (.ipc (.send sharedWord 1 2))) = false ∧
      isSilent 0 (composite base 7) sharedRevoke = false := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- A three-step run that consumes the secret message is invisible to the
observer, so it ends low-equivalent to the untouched paired state. -/
example (base : CompositeState) :
    projection 0 (composite base 7) privateTrace = [] := by
  rfl

example (base : CompositeState) :
    LowEquiv 0 (run 0 (composite base 7) privateTrace).1 (composite base 99) :=
  finite_trace_lowEquiv 0 (composite base 7) (composite base 99) privateTrace []
    rfl rfl

/-- The capability-identity counter is a declared visible channel, not a
claimed absence: a silent delegation between other subjects advances
`nextIdentity`, so a later delegation to the observer carries a different
generation.  The theorem stays sound because that delegation's event carries
the observer's resulting row, but the event projections of the two runs
differ. -/
def handleIdentities (event : Event) : List Nat :=
  (event.view.row.filterMap id).map (·.identity)

def counterTrace : List AuthoritativeOperation :=
  [.ordinary (.capabilityCopy 1 2 2 { send := true }),
   .ordinary (.capabilityCopy 1 0 1 { send := true })]

/-- **Identity-counter channel, executable witness.**  Prefixing the
observer's delegation with a silent delegation between subjects 1 and 2
changes the identity of the capability the observer receives from 5 to 6.
`CompositeUnwinding.identity_counter_step_inconsistent` proves the same
channel breaks step consistency between runtime-well-formed states. -/
theorem identity_counter_projection_witness (base : CompositeState) :
    (projection 0 (composite base 7) counterTrace).map handleIdentities = [[4, 6]] ∧
      (projection 0 (composite base 7) counterTrace.tail).map handleIdentities =
        [[4, 5]] := by
  exact ⟨rfl, rfl⟩

/-- The shared-capability channel is real: revoking a subtree that reaches the
observer's capability changes the observer's row, although the operation names
neither the observer nor any of its slots. -/
theorem shared_capability_revocation_visible (base : CompositeState) :
    actor (composite base 7) ≠ 0 ∧
      ¬ LowEquiv 0 (composite base 7)
        (authoritativeGate (composite base 7) sharedRevoke).state := by
  refine ⟨show (1 : Nat) ≠ 0 by decide, ?_⟩
  intro hlow
  have hrow := congrArg View.row hlow
  have hbefore : (observe 0 (composite base 7)).row =
      [some (endpointCap 10 4 { send := true } (some 1)), none, none, none] := rfl
  have hafter : (observe 0 (authoritativeGate (composite base 7) sharedRevoke).state).row =
      [none, none, none, none] := rfl
  rw [hbefore, hafter] at hrow
  simp at hrow

/-- Consequently, classifying an operation as silent from the subjects it
names is unsound: such a classification must also exclude capabilities the
operation reaches through derivation, which `isSilent` does by never calling
subtree revocation silent. -/
theorem naive_named_subject_silence_unsound (base : CompositeState) :
    ¬ ∀ (state : CompositeState) (authoritySlot victim victimSlot : Nat),
      actor state ≠ 0 → victim ≠ 0 →
        LowEquiv 0 state (authoritativeGate state
          (.ordinary (.capabilityRevokeSubtree authoritySlot victim victimSlot))).state := by
  intro hnaive
  exact (shared_capability_revocation_visible base).2
    (hnaive (composite base 7) 0 1 0 (shared_capability_revocation_visible base).1
      (by decide))

end Evidence

end LeanOS.CompositeObservation
