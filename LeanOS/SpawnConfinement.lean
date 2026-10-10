import LeanOS.CompositeLocalRespect

/-!
# Confinement of a spawned child (ADR 0010 gate item 4)

The ADR 0010 proof plan asks for confinement: the child can affect only
what its capabilities reach.  This module states that over the authoritative
composite state, using the observer view (`CompositeObservation.observe`) and
the local-respect results of `CompositeObservation`, `CompositeUnwinding` and
`CompositeLocalRespect`.  It adds no transition and changes no existing model.

**Reach.**  An operation the child invokes resolves its handle words only in
the child's own capability row.  So every object such an operation targets
is an object the child names (`ipcTarget_named`, `transferTarget_named`,
`blockingTarget_named`).  A subject queued as a waiter on an endpoint names
that endpoint (`waiter_names`).

**Confinement for one step** (`child_step_confined`).  Let the child be the
acting subject and let `observer` be any other subject such that no object
the child names is named by the observer (`ReachDisjoint`).  Then every
operation of the child's syscall surface (`ChildInvocable`) that does not
designate the observer as the destination of a delegation or the victim of a
revocation (`Designates`) leaves the observer's entire view unchanged:
liveness, capability row, every object the row names (liveness, kind,
mailboxes, pending sealed transfer, waiters, frame backing), owned address
spaces and their mappings, waiter index and completion, and the public
scheduler choice.

**Confinement along a run** (`child_run_confined`).  The same holds for every
finite run of such operations by the child, with the premises checked in the
state each operation runs in.

**At spawn** (`spawn_child_names`, `spawned_child_confined`).  Right after an
accepted spawn the child names exactly the granted endpoint and its own new
address space.  So once the child acts with that capability space, it can
affect a subject's view only through one of those two objects, or by naming
that subject as a delegation destination or revocation victim.

## Exclusions

These are stated, not hidden:

- **The public scheduler choice.**  A blocking receive that actually blocks
  changes `lifecycle.current`, which every view contains.  Blocking receive is
  covered only when it completes (`ReceiveCompletes`).
- **`capabilityRevokeSubtree`** is always visible in the existing
  classification, so it is not in `ChildInvocable`.
- **Designation.**  `Capability.copy` may install into an empty slot of any
  live subject, and `capabilityRevoke` names its victim subject.  A child
  that designates the observer this way is excluded by `Designates`; the
  installed or revoked capability is still one derived from a capability the
  child holds.
- **Kernel and scheduler events** (interrupts, preemption, scheduler steps,
  subject creation and termination, deferred drains, blocking cancellation)
  are not invoked by the child and are not in `ChildInvocable`.
- Timing, caches, devices, and refinement to generated C or hardware are not
  modeled, as in `CompositeObservation`.
-/
namespace LeanOS.SpawnConfinement

open LeanOS
open LeanOS.FailStop
open LeanOS.CompositeObservation
open LeanOS.CompositeUnwinding
open LeanOS.CompositeLocalRespect
set_option linter.unusedSimpArgs false

abbrev SubjectId := Capability.SubjectId
abbrev ObjectId := Capability.ObjectId

/-! ## Naming -/

/-- A subject names an object exactly when an in-range slot of its row holds
a capability over it. -/
theorem names_iff (state : CompositeState) (subject : SubjectId) (object : ObjectId) :
    Names state subject object = true ↔
      ∃ slot cap, slot < state.capabilities.slotCapacity subject ∧
        state.capabilities.slots subject slot = some cap ∧ cap.object = object := by
  simp only [Names, row, Capability.capabilitySpace, List.any_map, List.any_eq_true,
    List.mem_range, Function.comp_apply]
  constructor
  · rintro ⟨slot, inRange, held⟩
    cases found : state.capabilities.slots subject slot with
    | none => simp [found] at held
    | some cap =>
        simp only [found, Option.any_some, beq_iff_eq] at held
        exact ⟨slot, cap, inRange, found, held⟩
  · rintro ⟨slot, cap, inRange, found, same⟩
    exact ⟨slot, inRange, by simp [found, same]⟩

/-- A slot holding a capability in a well-formed registry is in range, so its
holder names the capability's object. -/
theorem names_of_slot {state : CompositeState} (wellFormed : Capability.WellFormed state.capabilities)
    {subject slot : Nat} {cap : Capability.Capability}
    (held : state.capabilities.slots subject slot = some cap) :
    Names state subject cap.object = true := by
  refine (names_iff state subject cap.object).2 ⟨slot, cap, ?_, held, rfl⟩
  by_cases inRange : slot < state.capabilities.slotCapacity subject
  · exact inRange
  · have := wellFormed.2.2.2 subject slot (Nat.le_of_not_lt inRange)
    rw [held] at this
    cases this

/-- A handle word resolved in the published registry for `caller` names an
object `caller` names. -/
theorem names_of_resolve {state : CompositeState} {capabilities : Capability.State}
    (same : capabilities = state.capabilities) {caller : SubjectId} {word : UInt64}
    {kind : Capability.ObjectKind} {resolution : CapabilityHandle.Resolution}
    (resolved : CapabilityHandle.resolveCurrent capabilities { caller } word kind =
      .ok resolution) :
    Names state caller resolution.capability.object = true := by
  subst same
  obtain ⟨_, _, inRange, held, _⟩ :=
    CapabilityHandle.resolveCurrent_sound _ _ _ _ _ resolved
  refine (names_iff state caller _).2 ⟨resolution.handle.slot, resolution.capability, ?_,
    held, rfl⟩
  simpa [Capability.slotInRange] using inRange

/-! ## Every target is reached through the actor's own row -/

/-- The endpoint a data-only IPC call targets is named by the actor. -/
theorem ipcTarget_named {state : CompositeState} (coherent : state.Coherent)
    {call : IPCSyscall.Call} {object : ObjectId} (target : ipcTarget state call = some object) :
    Names state (actor state) object = true := by
  have same : state.ipc.endpoints.capabilities = state.capabilities :=
    coherent.2.2.2.2.2.2.1.trans coherent.2.2.2.1.symm
  cases call <;> simp only [ipcTarget] at target <;> split at target
  all_goals first
    | (next resolution resolved =>
        cases target
        exact names_of_resolve same resolved)
    | cases target

/-- The endpoint a transfer offer or receipt targets is named by the actor. -/
theorem transferTarget_named {state : CompositeState} (coherent : state.Coherent)
    {word : UInt64} {object : ObjectId} (target : transferTarget state word = some object) :
    Names state (actor state) object = true := by
  have same : state.transfers.capabilities = state.capabilities := by
    have := coherent.2.2.2.2.2.2.2.2.2.1
    change state.transfers.toEndpointState.capabilities = state.capabilities
    rw [this]
    exact coherent.2.2.2.2.2.2.1.trans coherent.2.2.2.1.symm
  unfold transferTarget at target
  split at target
  · next resolution resolved =>
    cases target
    exact names_of_resolve same resolved
  · cases target

/-- The endpoint a blocking send or receive targets is named by the actor. -/
theorem blockingTarget_named {state : CompositeState} (holds : AuthoritativeRuntimeWellFormed state)
    {word : UInt64} {object : ObjectId} (target : blockingTarget state word = some object) :
    Names state (actor state) object = true := by
  have same : state.blockingIPC.scheduler.lifecycle.capabilities = state.capabilities := by
    rw [holds.left.blockingLifecycle]; exact holds.left.1.2.2.2.1.symm
  unfold blockingTarget at target
  split at target
  · next resolution resolved =>
    cases target
    exact names_of_resolve same resolved
  · cases target

/-- A subject waiting on an endpoint holds a receive capability over it, so
it names the endpoint. -/
theorem waiter_names {state : CompositeState} (holds : AuthoritativeRuntimeWellFormed state)
    {endpoint : ObjectId} {subject : SubjectId}
    (waiting : subject ∈ state.blockingIPC.waiters endpoint) :
    Names state subject endpoint = true := by
  have ipc : BlockingIPC.WellFormed state.blockingIPC := holds.blocking.2.1
  obtain ⟨_, ⟨slot, cap, held, sameObject, _⟩, _⟩ := ipc.2.2.1 endpoint subject waiting
  have same : state.blockingIPC.scheduler.lifecycle.capabilities = state.capabilities := by
    rw [holds.left.blockingLifecycle]; exact holds.left.1.2.2.2.1.symm
  rw [same] at held
  rw [← sameObject]
  exact names_of_slot holds.left.2.2.2.1 held

/-! ## The child's syscall surface -/

/-- The operations a subject invokes itself through its syscall surface and
whose effects the existing classification can keep away from another
subject: memory syscalls, map, unmap, protect, data-only IPC, sealed transfer
offer and receipt, capability delegation and single-slot revocation, and
blocking send and receive. -/
def ChildInvocable : AuthoritativeOperation → Bool
  | .ordinary (.syscall _) | .ordinary (.ipc _) | .ordinary (.transferOffer ..)
  | .ordinary (.transferAccept ..) | .ordinary (.capabilityCopy ..)
  | .ordinary (.capabilityRevoke ..) | .ordinary (.map ..) | .ordinary (.unmap _)
  | .ordinary (.protect ..) => true
  | .blocking (.send ..) | .blocking (.receive ..) => true
  | _ => false

/-- The operation names `observer` as the destination of a delegation or the
victim of a revocation. -/
def Designates (observer : SubjectId) : AuthoritativeOperation → Bool
  | .ordinary (.capabilityCopy _ destination _ _) => destination == observer
  | .ordinary (.capabilityRevoke _ victim _) => victim == observer
  | _ => false

/-- A blocking receive completes without blocking: the actor already holds a
reserved completion or the target mailbox holds a message.  Every other
operation satisfies this trivially. -/
def ReceiveCompletes (state : CompositeState) : AuthoritativeOperation → Bool
  | .blocking (.receive handleWord _ _) =>
      match blockingTarget state handleWord with
      | none => true
      | some endpoint =>
          (state.blockingIPC.completion (actor state)).isSome ||
            (state.blockingIPC.mailbox endpoint).isSome
  | _ => true

/-- No object the child names is named by the observer. -/
def ReachDisjoint (state : CompositeState) (child observer : SubjectId) : Prop :=
  ∀ object, Names state child object = true → Names state observer object = false

/-- **The silence classification holds.**  Every non-designating invocable
operation of the child, whose reach is disjoint from the observer's row, is
silent for the observer under `isSilentExtended`. -/
theorem child_step_silent (state : CompositeState) (child observer : SubjectId)
    (operation : AuthoritativeOperation) (holds : AuthoritativeRuntimeWellFormed state)
    (acting : actor state = child) (other : observer ≠ child)
    (invocable : ChildInvocable operation = true)
    (notDesignated : Designates observer operation = false)
    (completes : ReceiveCompletes state operation = true)
    (disjoint : ReachDisjoint state child observer) :
    isSilentExtended observer state operation = true := by
  have coherent := holds.left.1
  have actorNe : (actor state != observer) = true := by
    rw [acting]; simp [Ne.symm other]
  cases operation with
  | ordinary operation =>
      cases operation <;> simp [ChildInvocable] at invocable
      all_goals simp only [isSilentExtended, isSilentExtendedOrdinary, isSilentCoherentOrdinary,
        isSilentOrdinary, Bool.and_eq_true, actorNe, true_and]
      case ipc call =>
        cases target : ipcTarget state call with
        | none => rfl
        | some object =>
            have named := ipcTarget_named coherent target
            rw [acting] at named
            simp [disjoint object named]
      case transferOffer endpointWord _ _ _ _ =>
        cases target : transferTarget state endpointWord with
        | none => rfl
        | some object =>
            have named := transferTarget_named coherent target
            rw [acting] at named
            simp [disjoint object named]
      case transferAccept endpointWord _ =>
        cases target : transferTarget state endpointWord with
        | none => rfl
        | some object =>
            have named := transferTarget_named coherent target
            rw [acting] at named
            simp [disjoint object named]
      case capabilityCopy _ destination _ _ =>
        simpa [Designates] using notDesignated
      case capabilityRevoke _ victim _ =>
        simpa [Designates] using notDesignated
  | blocking operation =>
      cases operation <;> simp [ChildInvocable] at invocable
      case send handleWord _ _ =>
        simp only [isSilentExtended, isSilentBlocking, Bool.and_eq_true, actorNe, true_and]
        cases target : blockingTarget state handleWord with
        | none => rfl
        | some endpoint =>
            have named := blockingTarget_named holds target
            rw [acting] at named
            have notNamed := disjoint endpoint named
            have notWaiting : (state.blockingIPC.waiters endpoint).contains observer = false := by
              cases waiting : (state.blockingIPC.waiters endpoint).contains observer with
              | false => rfl
              | true =>
                  have := waiter_names holds (List.contains_iff_mem.1 waiting)
                  rw [notNamed] at this
                  cases this
            simp only [notNamed, Bool.not_false, Bool.true_and]
            rw [notWaiting]; rfl
      case receive handleWord _ _ =>
        simp only [isSilentExtended, isSilentBlocking, Bool.and_eq_true, actorNe, true_and]
        simp only [ReceiveCompletes] at completes
        cases target : blockingTarget state handleWord with
        | none => rfl
        | some endpoint =>
            rw [target] at completes
            have named := blockingTarget_named holds target
            rw [acting] at named
            simp only [disjoint endpoint named, Bool.not_false, Bool.true_and]
            exact completes
  | drainDeferred _ => simp [ChildInvocable] at invocable

/-- **Confinement of one step.**  When the child is the acting subject, every
operation of its syscall surface that does not designate `observer`, and
that (for a blocking receive) does not block, leaves the view of every other
subject whose row names nothing the child names exactly unchanged. -/
theorem child_step_confined (state : CompositeState) (child observer : SubjectId)
    (operation : AuthoritativeOperation) (holds : AuthoritativeRuntimeWellFormed state)
    (acting : actor state = child) (other : observer ≠ child)
    (invocable : ChildInvocable operation = true)
    (notDesignated : Designates observer operation = false)
    (completes : ReceiveCompletes state operation = true)
    (disjoint : ReachDisjoint state child observer) :
    observe observer (authoritativeGate state operation).state = observe observer state :=
  authoritativeGate_silentExtended_observe observer state operation holds
    (child_step_silent state child observer operation holds acting other invocable
      notDesignated completes disjoint)

/-! ## Runs of the child -/

/-- Run authoritative operations in sequence. -/
def runGate : CompositeState → List AuthoritativeOperation → CompositeState
  | state, [] => state
  | state, operation :: rest => runGate (authoritativeGate state operation).state rest

/-- Every operation of a run is a non-designating, non-blocking invocable
operation of the child, performed while the child is the acting subject and
its reach is disjoint from the observer's row, each checked in the state the
operation runs in. -/
def ConfinedRun (child observer : SubjectId) :
    CompositeState → List AuthoritativeOperation → Prop
  | _, [] => True
  | state, operation :: rest =>
      actor state = child ∧ ChildInvocable operation = true ∧
        Designates observer operation = false ∧ ReceiveCompletes state operation = true ∧
        ReachDisjoint state child observer ∧
        ConfinedRun child observer (authoritativeGate state operation).state rest

/-- **Confinement along a run.**  A finite run of the child's own invocable
operations, each meeting the step premises in the state it runs in, ends
with the observer's view exactly as it started, and keeps the authoritative
runtime invariant. -/
theorem child_run_confined (state : CompositeState) (child observer : SubjectId)
    (operations : List AuthoritativeOperation) (holds : AuthoritativeRuntimeWellFormed state)
    (other : observer ≠ child) (run : ConfinedRun child observer state operations) :
    observe observer (runGate state operations) = observe observer state ∧
      AuthoritativeRuntimeWellFormed (runGate state operations) := by
  induction operations generalizing state with
  | nil => exact ⟨rfl, holds⟩
  | cons operation rest ih =>
      obtain ⟨acting, invocable, notDesignated, completes, disjoint, later⟩ := run
      have step := child_step_confined state child observer operation holds acting other
        invocable notDesignated completes disjoint
      obtain ⟨final, finalHolds⟩ := ih (authoritativeGate state operation).state
        (authoritativeGate_preserves_authoritativeRuntimeWellFormed state operation holds) later
      exact ⟨final.trans step, finalHolds⟩

/-! ## The child's reach at spawn -/

/-- Reach disjointness from a bound on the child's names: if every object the
child names is in `reach` and the observer names nothing in `reach`, the two
are disjoint. -/
theorem reachDisjoint_of_bound (state : CompositeState) (child observer : SubjectId)
    (reach : ObjectId → Prop)
    (bound : ∀ object, Names state child object = true → reach object)
    (outside : ∀ object, reach object → Names state observer object = false) :
    ReachDisjoint state child observer :=
  fun object named => outside object (bound object named)

/-- **What a spawned child names.**  Right after an accepted spawn the child
names exactly two objects: the endpoint of the parent capability it was
granted, and its own new address space. -/
theorem spawn_child_names (state : CompositeState) (request : SpawnRequest)
    (child addressSpace : Nat) (running : state.execution.mode = .running)
    (holds : ResourceRuntimeWellFormed state)
    (spawned : (spawn state request).result = .spawned child addressSpace) :
    ∃ slot endpoint,
      state.capabilities.slots (spawnParent state) slot = some endpoint ∧
      endpoint.kind = .endpoint ∧ endpoint.rights.grant = true ∧
      ∀ object, Names (spawn state request).state child object = true ↔
        object = endpoint.object ∨ object = addressSpace := by
  obtain ⟨slot, endpoint, held, kind, grant, _, slots⟩ :=
    spawn_child_capabilities state request child addressSpace holds.1.left spawned
  have post := spawn_preserves_resourceRuntimeWellFormed state request running holds
  have wellFormed : Capability.WellFormed (spawn state request).state.capabilities :=
    post.1.left.2.2.2.1
  refine ⟨slot, endpoint, held, kind, grant, fun object => ⟨fun named => ?_, fun which => ?_⟩⟩
  · obtain ⟨candidate, cap, _, found, same⟩ := (names_iff _ child object).1 named
    rw [slots] at found
    split at found
    · cases found; exact Or.inl same.symm
    · split at found
      · cases found; exact Or.inr same.symm
      · cases found
  · rcases which with same | same <;> rw [same]
    · have found := slots childEndpointSlot
      simp only [↓reduceIte] at found
      have := names_of_slot wellFormed found
      simpa using this
    · have found := slots childAddressSpaceSlot
      simp only [childAddressSpaceSlot, childEndpointSlot] at found
      have := names_of_slot wellFormed found
      simpa [addressSpaceRoot] using this

/-- **A spawned child is confined to what it was given.**  After an accepted
spawn, take any other subject whose row names neither the granted endpoint
nor the child's new address space.  If the child acts with the capability
space spawn gave it, every operation of its syscall surface that does not
designate that subject, and does not block, leaves that subject's whole view
unchanged. -/
theorem spawned_child_confined (state : CompositeState) (request : SpawnRequest)
    (child addressSpace : Nat) (running : state.execution.mode = .running)
    (holds : ResourceRuntimeWellFormed state)
    (spawned : (spawn state request).result = .spawned child addressSpace) :
    ∃ slot endpoint,
      state.capabilities.slots (spawnParent state) slot = some endpoint ∧
      endpoint.kind = .endpoint ∧
      ∀ observer, observer ≠ child →
        Names (spawn state request).state observer endpoint.object = false →
        Names (spawn state request).state observer addressSpace = false →
        ∀ operation, actor (spawn state request).state = child →
          ChildInvocable operation = true → Designates observer operation = false →
          ReceiveCompletes (spawn state request).state operation = true →
          observe observer (authoritativeGate (spawn state request).state operation).state =
            observe observer (spawn state request).state := by
  obtain ⟨slot, endpoint, held, kind, _, names⟩ :=
    spawn_child_names state request child addressSpace running holds spawned
  have post := (spawn_preserves_resourceRuntimeWellFormed state request running holds).1
  refine ⟨slot, endpoint, held, kind, fun observer other notEndpoint notSpace operation
    acting invocable notDesignated completes => ?_⟩
  apply child_step_confined _ child observer operation post acting other invocable
    notDesignated completes
  refine reachDisjoint_of_bound _ child observer
    (fun object => object = endpoint.object ∨ object = addressSpace)
    (fun object named => (names object).1 named) ?_
  rintro object (rfl | rfl)
  · exact notEndpoint
  · exact notSpace

end LeanOS.SpawnConfinement
