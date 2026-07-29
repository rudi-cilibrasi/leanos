import LeanOS.FrameBudget
import LeanOS.FrameScrub

/-!
# Canonical boot frame-budget scenario

This module is the bounded state family used by the issue-112 generated
dispatcher and machine scenario.  It composes the authoritative
`FrameBudget.State` with the kernel-selected current subject/address space.
Commands never carry a charging subject, frame, budget, object identity, or
expected result.

The finite trace admits one frame to A and two frames to B.  A allocates and
then receives a state-preserving `budgetExhausted`; the kernel selects B, which
allocates while A remains full; checked termination retires A; and B publishes
its second fresh lifetime.  A two-frame scrub state is composed with the
admitted budget: after both subjects hold a physical frame, A's cleanup
releases its canary-bearing frame and B's second publication must reuse and
completely scrub that frame before installing a fresh capability identity.
-/
namespace LeanOS.FrameBudgetScenario

open LeanOS

def abiVersion : UInt64 := 1

structure Runtime where
  budget : FrameBudget.State
  scrub : FrameScrub.State
  currentSubject : FrameBudget.SubjectId
  activeAddressSpace : FrameBudget.SubjectId
  userMapping : Option (FrameBudget.SubjectId × FrameScrub.ObjectId ×
    CapabilityHandle.Handle × FrameScrub.FrameId × UInt64)

inductive Command where
  | allocateA | retryA | selectB | allocateB | terminateA
  | publishFreshB | denyStaleA | complete
  | releaseA | repeatReleaseA | completeReleased
  deriving DecidableEq, Repr

inductive Reply where
  | allocatedA | budgetExhaustedUnchanged | selectedB | allocatedB
  | terminatedA | freshB | staleDenied | passed
  | releasedA | repeatedReleaseDenied
  deriving DecidableEq, Repr

structure Outcome where
  state : Runtime
  reply : Reply

private def capabilities : Capability.State :=
  { subjects := fun subject => subject < 2
    objects := fun _ => false
    kinds := fun _ => none
    slotCapacity := fun _ => 4
    slots := fun _ _ => none }

def initialBudget : FrameBudget.State :=
  { memory :=
      { capabilities
        allocator :=
          { frames := [0, 1, 2]
            status := fun frame => if frame < 3 then .free else .reserved }
        binding := fun _ => none
        issued := fun _ => false }
    issuedSubjects := fun subject => subject < 2
    commitment := fun frame =>
      if frame = 0 then some 0
      else if frame = 1 || frame = 2 then some 1 else none }

def initialScrub : FrameScrub.State :=
  { memory :=
      { capabilities
        allocator :=
          { frames := [100, 101]
            status := fun frame => if frame = 100 || frame = 101 then .free else .reserved }
        binding := fun _ => none
        issued := fun _ => false }
    bytes := fun _ _ => 0xcc
    written := fun _ => false }

def initial : Runtime :=
  { budget := initialBudget
    scrub := initialScrub
    currentSubject := 0
    activeAddressSpace := 0
    userMapping := none }

/-- The sole machine-scenario virtual page.  It is generated policy rather
than a C-selected address or a ring-3 request word. -/
def machineUserPage : UInt64 := 4095

def reject (state : Runtime) (reply : Reply) : Outcome := { state, reply }

/-- The exact scenario transition.  Object identities and slots are
kernel-selected constants.  The only context switch is likewise generated. -/
def step (state : Runtime) : Command → Option Outcome
  | .allocateA =>
      if state.currentSubject != 0 || state.activeAddressSpace != 0 then none
      else
        let allocation := FrameBudget.allocate state.budget state.currentSubject 10 0
        let publication := FrameScrub.allocate state.scrub 10 state.currentSubject 0
        if allocation.result != .accepted || publication.result != .accepted then none
        else
          match FrameScrub.writeByte publication.state state.currentSubject 0 0 0xa5 with
          | .error _ => none
          | .ok written =>
              some {
                state := {
                  state with
                    budget := allocation.state
                    scrub := written
                    userMapping := some (0, 10, { slot := 0, identity := 1 },
                      100, machineUserPage) }
                reply := .allocatedA }
  | .retryA =>
      if state.currentSubject != 0 || state.activeAddressSpace != 0 then none
      else
        let allocation := FrameBudget.allocate state.budget state.currentSubject 11 1
        if allocation.result = .rejected .budgetExhausted then
          some (reject state .budgetExhaustedUnchanged)
        else none
  | .selectB =>
      if state.currentSubject != 0 || state.activeAddressSpace != 0 then none
      else
        some {
          state := { state with currentSubject := 1, activeAddressSpace := 1 }
          reply := .selectedB }
  | .allocateB =>
      if state.currentSubject != 1 || state.activeAddressSpace != 1 then none
      else
        let allocation := FrameBudget.allocate state.budget state.currentSubject 20 0
        let publication := FrameScrub.allocate state.scrub 20 state.currentSubject 0
        if allocation.result = .accepted && publication.result = .accepted then
          some {
            state := {
              state with budget := allocation.state, scrub := publication.state }
            reply := .allocatedB }
        else none
  | .terminateA =>
      if state.currentSubject != 1 || state.activeAddressSpace != 1 then none
      else
        let cleanup := FrameBudget.terminate state.budget 0
        let reclamation := FrameScrub.release state.scrub 0 0
        if cleanup.result = .accepted && reclamation.result = .accepted then
          some {
            state := {
              state with
                budget := cleanup.state
                scrub := reclamation.state
                userMapping := none }
            reply := .terminatedA }
        else none
  | .publishFreshB =>
      if state.currentSubject != 1 || state.activeAddressSpace != 1 then none
      else
        let allocation := FrameBudget.allocate state.budget state.currentSubject 21 1
        let publication := FrameScrub.allocate state.scrub 21 state.currentSubject 1
        if allocation.result = .accepted && publication.result = .accepted then
          some {
            state := {
              state with
                budget := allocation.state
                scrub := publication.state
                userMapping := some (1, 21, { slot := 1, identity := 3 },
                  100, machineUserPage) }
            reply := .freshB }
        else none
  | .denyStaleA =>
      if state.currentSubject != 1 || state.activeAddressSpace != 1 then none
      else
        match CapabilityHandle.resolveCurrent state.scrub.memory.capabilities
            { caller := state.currentSubject } 0x10000 .memory with
        | .error (.denied .staleHandle) => some (reject state .staleDenied)
        | _ => none
  | .complete =>
      if state.currentSubject = 1 && state.activeAddressSpace = 1 then
        some (reject state .passed)
      else none
  | .releaseA =>
      if state.currentSubject != 0 || state.activeAddressSpace != 0 then none
      else
        let release := FrameBudget.release state.budget state.currentSubject 0
        let reclamation := FrameScrub.release state.scrub state.currentSubject 0
        if release.result = .accepted && reclamation.result = .accepted then
          some {
            state := {
              state with budget := release.state, scrub := reclamation.state }
            reply := .releasedA }
        else none
  | .repeatReleaseA =>
      if state.currentSubject != 0 || state.activeAddressSpace != 0 then none
      else
        let release := FrameBudget.release state.budget state.currentSubject 0
        let reclamation := FrameScrub.release state.scrub state.currentSubject 0
        if release.result = .rejected .staleSlot &&
            reclamation.result = .rejected .staleSlot then
          some (reject state .repeatedReleaseDenied)
        else none
  | .completeReleased =>
      if state.currentSubject = 0 && state.activeAddressSpace = 0 then
        some (reject state .passed)
      else none

inductive StateId where
  | initial | aAllocated | aExhausted | bSelected | bAllocated
  | aTerminated | bFresh | staleDenied | complete
  | aReleased | releaseDenied | releaseComplete
  deriving DecidableEq, Repr

def encodeState : StateId → UInt64
  | .initial => 0x4001
  | .aAllocated => 0x4101
  | .aExhausted => 0x4201
  | .bSelected => 0x4301
  | .bAllocated => 0x4401
  | .aTerminated => 0x4501
  | .bFresh => 0x4601
  | .staleDenied => 0x4701
  | .complete => 0x4801
  | .aReleased => 0x4901
  | .releaseDenied => 0x4a01
  | .releaseComplete => 0x4b01

def encodeCommand : Command → UInt64
  | .allocateA => 0x4001
  | .retryA => 0x4101
  | .selectB => 0x4201
  | .allocateB => 0x4301
  | .terminateA => 0x4401
  | .publishFreshB => 0x4501
  | .denyStaleA => 0x4601
  | .complete => 0x4701
  | .releaseA => 0x4801
  | .repeatReleaseA => 0x4901
  | .completeReleased => 0x4a01

def encodeReply : Reply → UInt64
  | .allocatedA => 0x40
  | .budgetExhaustedUnchanged => 0x41
  | .selectedB => 0x42
  | .allocatedB => 0x43
  | .terminatedA => 0x44
  | .freshB => 0x45
  | .staleDenied => 0x46
  | .passed => 0x47
  | .releasedA => 0x48
  | .repeatedReleaseDenied => 0x49

def next : StateId → Command → Option StateId
  | .initial, .allocateA => some .aAllocated
  | .aAllocated, .retryA => some .aExhausted
  | .aExhausted, .selectB => some .bSelected
  | .bSelected, .allocateB => some .bAllocated
  | .bAllocated, .terminateA => some .aTerminated
  | .aTerminated, .publishFreshB => some .bFresh
  | .bFresh, .denyStaleA => some .staleDenied
  | .staleDenied, .complete => some .complete
  | .aAllocated, .releaseA => some .aReleased
  | .aReleased, .repeatReleaseA => some .releaseDenied
  | .releaseDenied, .completeReleased => some .releaseComplete
  | _, _ => none

def aAllocatedRuntime : Runtime :=
  match step initial .allocateA with | some outcome => outcome.state | none => initial
def aExhaustedRuntime : Runtime :=
  match step aAllocatedRuntime .retryA with
  | some outcome => outcome.state | none => aAllocatedRuntime
def bSelectedRuntime : Runtime :=
  match step aExhaustedRuntime .selectB with
  | some outcome => outcome.state | none => aExhaustedRuntime
def bAllocatedRuntime : Runtime :=
  match step bSelectedRuntime .allocateB with
  | some outcome => outcome.state | none => bSelectedRuntime
def aTerminatedRuntime : Runtime :=
  match step bAllocatedRuntime .terminateA with
  | some outcome => outcome.state | none => bAllocatedRuntime
def bFreshRuntime : Runtime :=
  match step aTerminatedRuntime .publishFreshB with
  | some outcome => outcome.state | none => aTerminatedRuntime
def staleDeniedRuntime : Runtime :=
  match step bFreshRuntime .denyStaleA with
  | some outcome => outcome.state | none => bFreshRuntime
def completeRuntime : Runtime :=
  match step staleDeniedRuntime .complete with
  | some outcome => outcome.state | none => staleDeniedRuntime
def aReleasedRuntime : Runtime :=
  match step aAllocatedRuntime .releaseA with
  | some outcome => outcome.state | none => aAllocatedRuntime
def releaseDeniedRuntime : Runtime :=
  match step aReleasedRuntime .repeatReleaseA with
  | some outcome => outcome.state | none => aReleasedRuntime
def releaseCompleteRuntime : Runtime :=
  match step releaseDeniedRuntime .completeReleased with
  | some outcome => outcome.state | none => releaseDeniedRuntime

def materialize : StateId → Runtime
  | .initial => initial
  | .aAllocated => aAllocatedRuntime
  | .aExhausted => aExhaustedRuntime
  | .bSelected => bSelectedRuntime
  | .bAllocated => bAllocatedRuntime
  | .aTerminated => aTerminatedRuntime
  | .bFresh => bFreshRuntime
  | .staleDenied => staleDeniedRuntime
  | .complete => completeRuntime
  | .aReleased => aReleasedRuntime
  | .releaseDenied => releaseDeniedRuntime
  | .releaseComplete => releaseCompleteRuntime

def commandArgs : Command → UInt64 × UInt64 × UInt64 × UInt64
  | .allocateA => (10, 0, 0, 0)
  | .retryA => (11, 1, 0, 0)
  | .selectB => (0, 0, 0, 0)
  | .allocateB => (20, 0, 0, 0)
  | .terminateA => (0, 0, 0, 0)
  | .publishFreshB => (21, 1, 0, 0)
  | .denyStaleA => (0x10000, 0, 0, 0)
  | .complete => (0, 0, 0, 0)
  | .releaseA => (0, 0, 0, 0)
  | .repeatReleaseA => (0, 0, 0, 0)
  | .completeReleased => (0, 0, 0, 0)

def replyFor : StateId → Command → Option Reply
  | .initial, .allocateA => some .allocatedA
  | .aAllocated, .retryA => some .budgetExhaustedUnchanged
  | .aExhausted, .selectB => some .selectedB
  | .bSelected, .allocateB => some .allocatedB
  | .bAllocated, .terminateA => some .terminatedA
  | .aTerminated, .publishFreshB => some .freshB
  | .bFresh, .denyStaleA => some .staleDenied
  | .staleDenied, .complete => some .passed
  | .aAllocated, .releaseA => some .releasedA
  | .aReleased, .repeatReleaseA => some .repeatedReleaseDenied
  | .releaseDenied, .completeReleased => some .passed
  | _, _ => none

def replyWord (nextState : StateId) (reply : Reply) : UInt64 :=
  abiVersion + ((encodeState nextState / 256) * 256) + encodeReply reply * 65536

/-- Generated machine-publication query.  C supplies only the accepted
pre-state token and command tag; all other pairs are denied. -/
@[export leanos_frame_budget_mapping_page]
def machineMappingPage (stateWord command : UInt64) : UInt64 :=
  if stateWord = 0x4001 && command = 0x4001 then 4095
  else if stateWord = 0x4501 && command = 0x4501 then 4095
  else 0xffffffffffffffff

/-- Allocation-free table reached through `CompositeDispatcher.dispatch`.
`0xff05` is noncanonical input and `0xff06` is a continuity failure. -/
@[inline] def dispatch (stateWord tag arg0 arg1 arg2 arg3 : UInt64) : UInt64 :=
  let canonical expectedState expectedArg0 expectedArg1 result :=
    if arg0 != expectedArg0 || arg1 != expectedArg1 || arg2 != 0 ||
        arg3 != 0 then 0xff05
    else if stateWord = expectedState then result else 0xff06
  if tag = 0x4001 then canonical 0x4001 10 0 0x404101
  else if tag = 0x4101 then canonical 0x4101 11 1 0x414201
  else if tag = 0x4201 then canonical 0x4201 0 0 0x424301
  else if tag = 0x4301 then canonical 0x4301 20 0 0x434401
  else if tag = 0x4401 then canonical 0x4401 0 0 0x444501
  else if tag = 0x4501 then canonical 0x4501 21 1 0x454601
  else if tag = 0x4601 then canonical 0x4601 0x10000 0 0x464701
  else if tag = 0x4701 then canonical 0x4701 0 0 0x474801
  else if tag = 0x4801 then canonical 0x4101 0 0 0x484901
  else if tag = 0x4901 then canonical 0x4901 0 0 0x494a01
  else if tag = 0x4a01 then canonical 0x4a01 0 0 0x474b01
  else if tag % 256 != abiVersion then 0xff01
  else if 0x4b01 ≤ tag then 0xff02
  else 0xff04

theorem canonical_dispatch state command post reply
    (hnext : next state command = some post)
    (hreply : replyFor state command = some reply) :
    let args := commandArgs command
    dispatch (encodeState state) (encodeCommand command)
      args.1 args.2.1 args.2.2.1 args.2.2.2 = replyWord post reply := by
  cases state <;> cases command <;> simp [next] at hnext
  all_goals subst post
  all_goals simp [replyFor] at hreply
  all_goals subst reply
  all_goals rfl

/-- Every corpus edge is the exact scenario transition over the materialized
authoritative budget state. -/
theorem step_refinement state command post reply
    (hnext : next state command = some post)
    (hreply : replyFor state command = some reply) :
    step (materialize state) command =
      some { state := materialize post, reply } := by
  cases state <;> cases command <;> simp [next] at hnext
  all_goals subst post
  all_goals simp [replyFor] at hreply
  all_goals subst reply
  all_goals rfl

theorem a_retry_is_budgetExhausted_and_unchanged :
    let before := materialize .aAllocated
    (FrameBudget.allocate before.budget before.currentSubject 11 1).result =
        .rejected .budgetExhausted ∧
      (FrameBudget.allocate before.budget before.currentSubject 11 1).state =
        before.budget ∧
      (materialize .aExhausted).scrub = before.scrub := by
  have hresult :
      (FrameBudget.allocate (materialize .aAllocated).budget
        (materialize .aAllocated).currentSubject 11 1).result =
        .rejected .budgetExhausted := by native_decide
  exact ⟨hresult, FrameBudget.allocate_rejected_unchanged _ _ _ _ _ hresult, rfl⟩

theorem peer_allocation_remains_available :
    let before := materialize .bSelected
    (FrameBudget.allocate before.budget before.currentSubject 20 0).result =
      .accepted := by
  native_decide

theorem termination_restores_exactly_one_a_frame :
    let before := materialize .bAllocated
    let after := materialize .aTerminated
    FrameBudget.usage before.budget 0 = 1 ∧
      FrameBudget.usage after.budget 0 = 0 ∧
      after.budget.memory.allocator.status 0 = .free ∧
      before.scrub.memory.allocator.status 100 = .owned 10 ∧
      before.scrub.memory.allocator.status 101 = .owned 20 ∧
      after.scrub.memory.allocator.status 100 = .free ∧
      after.scrub.memory.allocator.status 101 = .owned 20 ∧
      after.scrub.bytes 100 0 = 0xa5 := by
  native_decide

theorem fresh_b_lifetime_and_stale_a_denial :
    let fresh := materialize .bFresh
    fresh.budget.memory.issued 10 = true ∧
      fresh.budget.memory.issued 21 = true ∧
      fresh.budget.memory.binding 21 = some 2 ∧
      fresh.scrub.memory.binding 21 = some 100 ∧
      (fresh.scrub.memory.capabilities.slots 0 0).map (·.identity) = none ∧
      (fresh.scrub.memory.capabilities.slots 1 0).map (·.identity) = some 2 ∧
      (fresh.scrub.memory.capabilities.slots 1 1).map (·.identity) = some 3 ∧
      fresh.scrub.bytes 100 0 = FrameScrub.initialByte ∧
      fresh.scrub.bytes 100 (FrameScrub.frameBytes - 1) = FrameScrub.initialByte ∧
      CapabilityHandle.encode { slot := 0, identity := 2 } = some 0x20000 ∧
      CapabilityHandle.encode { slot := 1, identity := 3 } = some 0x30001 ∧
      CapabilityHandle.resolveCurrent fresh.scrub.memory.capabilities
          { caller := 1 } 0x10000 .memory =
        .error (.denied .staleHandle) := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem machine_mapping_is_authoritative_and_reuses_frame :
    (materialize .aAllocated).userMapping =
        some (0, 10, { slot := 0, identity := 1 }, 100, machineUserPage) ∧
      (materialize .aTerminated).userMapping = none ∧
      (materialize .bFresh).userMapping =
        some (1, 21, { slot := 1, identity := 3 }, 100, machineUserPage) ∧
      machineMappingPage (encodeState .initial) (encodeCommand .allocateA) =
        machineUserPage ∧
      machineMappingPage (encodeState .aTerminated)
          (encodeCommand .publishFreshB) = machineUserPage := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The reclaimed physical frame is scrubbed in its entirety before object 21
and its fresh capability generation become observable. -/
theorem fresh_b_publication_is_completely_scrubbed :
    FrameScrub.Fresh (materialize .bFresh).scrub 21 := by
  have haccepted :
      (FrameScrub.allocate (materialize .aTerminated).scrub 21 1 1).result =
        .accepted := by native_decide
  change FrameScrub.Fresh
    (FrameScrub.allocate (materialize .aTerminated).scrub 21 1 1).state 21
  exact FrameScrub.allocation_publishes_scrubbed _ _ _ _ haccepted

/-- The concrete scrub model follows the exact physical frame across
reclamation and reuse. The retired bytes remain observable inside the model
until allocation atomically scrubs frame 100 and publishes object 21 with a
never-reused capability identity. -/
theorem exact_reclaimed_frame_scrubbed_before_fresh_generation :
    let before := materialize .bAllocated
    let reclaimed := materialize .aTerminated
    let fresh := materialize .bFresh
    before.scrub.memory.binding 10 = some 100 ∧
      before.scrub.bytes 100 0 = 0xa5 ∧
      reclaimed.scrub.memory.binding 10 = none ∧
      reclaimed.scrub.memory.allocator.status 100 = .free ∧
      reclaimed.scrub.bytes 100 0 = 0xa5 ∧
      fresh.scrub.memory.binding 21 = some 100 ∧
      fresh.scrub.memory.allocator.status 100 = .owned 21 ∧
      (fresh.scrub.memory.capabilities.slots 1 1).map (·.identity) = some 3 ∧
      ∀ offset, offset < FrameScrub.frameBytes →
        fresh.scrub.bytes 100 offset = FrameScrub.initialByte := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  have hfresh := fresh_b_publication_is_completely_scrubbed
  rcases hfresh.2 with ⟨frame, hbinding, hbytes⟩
  have hframe : frame = 100 := by
    rw [show (materialize .bFresh).scrub.memory.binding 21 = some 100 by rfl] at hbinding
    exact Option.some.inj hbinding.symm
  simpa [hframe] using hbytes

theorem release_and_repeated_release_are_checked :
    let released := materialize .aReleased
    FrameBudget.usage released.budget 0 = 0 ∧
      released.budget.memory.allocator.status 0 = .free ∧
      released.scrub.memory.allocator.status 100 = .free ∧
      (FrameBudget.release released.budget 0 0).result =
        .rejected .staleSlot ∧
      (materialize .releaseDenied).budget = released.budget ∧
      (materialize .releaseDenied).scrub = released.scrub := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

def canonicalCommands : List Command :=
  [.allocateA, .retryA, .selectB, .allocateB, .terminateA,
    .publishFreshB, .denyStaleA, .complete]

def run : StateId → List Command → Option StateId
  | state, [] => some state
  | state, command :: rest => do
      let following ← next state command
      run following rest

theorem canonical_sequence_complete :
    run .initial canonicalCommands = some .complete := by native_decide

def releaseCommands : List Command :=
  [.allocateA, .releaseA, .repeatReleaseA, .completeReleased]

theorem release_sequence_complete :
    run .initial releaseCommands = some .releaseComplete := by native_decide

theorem canonical_sequence_adjacent state command rest finish
    (h : run state (command :: rest) = some finish) :
    ∃ following, next state command = some following ∧
      run following rest = some finish := by
  unfold run at h
  cases hnext : next state command with
  | none => simp [hnext] at h
  | some following =>
      simp only [hnext] at h
      exact ⟨following, rfl, h⟩

end LeanOS.FrameBudgetScenario
