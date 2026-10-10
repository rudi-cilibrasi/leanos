import LeanOS.FailStop.Spawn
import LeanOS.FailStop.ResourceSteps

/-!
# Fail-stop composite: spawn keeps every invariant

Every spawn step keeps the combined invariant `ResourceRuntimeWellFormed`
(`spawnGate_preserves_resourceRuntimeWellFormed`).  An accepted spawn is the
composition of three transitions already shown to keep it, plus a record the
invariant does not read:

1. issued subject creation (`issueSubject`, from `Resources`);
2. address-space creation (`installCreatedAddressSpace`, from
   `SpawnAddressSpace`), with the object issuer advanced past the new
   identity (`spaced_resourceWellFormed`);
3. the composite `capabilityCopy` publication, through the authoritative
   gate (`authoritativeGate_capabilityCopy_preserves_authoritativeRuntimeWellFormed`
   and the history-keeping resource lemma);
4. `recordSpawn`, which writes only the `spawn` projection.

A rejected spawn returns the pre-state (`spawn_rejected_unchanged`).
-/
namespace LeanOS.FailStop

open LeanOS
set_option linter.unusedSimpArgs false

/-! ## Facts about each stage -/

/-- Issued creation keeps the execution mode and the trusted context. -/
theorem issueSubject_execution (state : CompositeState) (child : Nat)
    (issued : (issueSubject state).result = .issued child) :
    (issueSubject state).state.execution.mode = state.execution.mode ∧
      (issueSubject state).state.execution.core.context = state.execution.core.context ∧
      (issueSubject state).state.issuers.object = state.issuers.object := by
  obtain ⟨_, _, created, eq⟩ := issueSubject_issued state child issued
  rw [eq]
  simp [applyOperation, created, installCreatedSubject]

/-- The record of a spawn is invisible to every invariant: it writes only the
`spawn` projection, which no invariant reads. -/
theorem spawn_unsupported :
    (authoritativeInvariants ++ resourceInvariants).all
      (fun invariant => !invariant.support.contains .spawn) = true := by
  decide

theorem withSpawn_resourceRuntimeWellFormed {state : CompositeState}
    (holds : ResourceRuntimeWellFormed state) (registry : SpawnRegistry) :
    ResourceRuntimeWellFormed { state with spawn := registry } := by
  rw [resourceRuntimeWellFormed_iff_all] at holds ⊢
  intro invariant member
  apply invariant.dependsOn state _ _ (holds invariant member)
  intro projection supported
  cases projection <;> try rfl
  have := List.all_eq_true.1 spawn_unsupported invariant member
  simp only [decide_eq_true_eq] at supported
  simp [supported] at this

theorem recordSpawn_resourceRuntimeWellFormed {state : CompositeState}
    (holds : ResourceRuntimeWellFormed state) (parent child addressSpace : Nat) :
    ResourceRuntimeWellFormed (recordSpawn state parent child addressSpace) :=
  withSpawn_resourceRuntimeWellFormed holds _

/-- The address-space stage with the object issuer advanced past the new
identity keeps every resource conjunct: the new identity is the old object
counter, which the advanced counter now bounds, and the frame allocator,
bindings, commitment, contents, and subject history are untouched. -/
theorem spaced_resourceWellFormed (state : CompositeState) (addressSpace owner slot : Nat)
    (issued : LifetimeIssuer.issue state.issuers.object =
      .issued addressSpace { next := addressSpace + 1 })
    (holds : ResourceWellFormed state) :
    ResourceWellFormed
      { installCreatedAddressSpace state addressSpace owner slot with
        issuers := { state.issuers with object := { next := addressSpace + 1 } } } := by
  obtain ⟨same, follow, positive, bounded⟩ := LifetimeIssuer.issued_facts issued
  dsimp only at follow
  rw [resourceWellFormed_iff] at holds ⊢
  obtain ⟨issuersHold, agreementHold, budgetHold, scrubHold⟩ := holds
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [issuersInvariant] at issuersHold ⊢
    exact ⟨issuersHold.1, show addressSpace + 1 ≤ LifetimeIssuer.identityReserved by omega⟩
  · simp only [issuerAgreementInvariant, CompositeState.lifecycleRuntime,
      BoundedLifecycle.issuedObject] at agreementHold ⊢
    refine ⟨agreementHold.1, ?_⟩
    intro object issuedNow
    simp only [installCreatedAddressSpace, createdVirtualMemory,
      VirtualMapping.clearAddressSpaceMappings, MemoryLifecycle.setIssued,
      VirtualMapping.setIssuedAddressSpace] at issuedNow
    show 0 < object ∧ object < addressSpace + 1
    by_cases hobject : object = addressSpace
    · subst hobject; exact ⟨same ▸ positive, Nat.lt_succ_self _⟩
    · simp only [hobject, ↓reduceIte] at issuedNow
      have := agreementHold.2 object issuedNow
      exact ⟨this.1, by rw [same]; exact Nat.lt_succ_of_lt this.2⟩
  · simpa [budgetAgreementInvariant, installCreatedAddressSpace, createdVirtualMemory,
      VirtualMapping.clearAddressSpaceMappings] using budgetHold
  · simpa [scrubInvariant, CompositeState.scrubState, FrameScrub.ScrubInvariant,
      installCreatedAddressSpace, createdVirtualMemory,
      VirtualMapping.clearAddressSpaceMappings] using scrubHold

/-- The address-space stage is admissible on the created state. -/
theorem spawn_creatable (state : CompositeState) (request : SpawnRequest) (built : SpawnBuilt)
    (trace : SpawnTrace state request built)
    (holds : RuntimeWellFormed (issueSubject state).state) :
    AddressSpaceCreatable (issueSubject state).state built.addressSpace built.child
      childAddressSpaceSlot := by
  have vmCaps : (issueSubject state).state.virtualMemory.memory.capabilities =
      (issueSubject state).state.capabilities :=
    holds.1.2.2.2.2.1.trans holds.1.2.2.2.1.symm
  obtain ⟨live, bounded, inRange, generation, empty, unissued, dead, _⟩ :=
    VirtualMapping.createAddressSpace_accepted_state _ _ _ _ trace.spaceAccepted
  rw [vmCaps] at live inRange generation empty dead
  have free := trace.free
  simp only [addressSpaceFree, Bool.and_eq_true, beq_iff_eq] at free
  exact ⟨live, bounded, inRange, generation, empty, unissued, dead, free⟩

/-! ## Preservation -/

/-- **Spawn keeps the combined invariant** from any running state that
satisfies it, on every outcome. -/
theorem spawn_preserves_resourceRuntimeWellFormed (state : CompositeState)
    (request : SpawnRequest) (running : state.execution.mode = .running)
    (holds : ResourceRuntimeWellFormed state) :
    ResourceRuntimeWellFormed (spawn state request).state := by
  cases result : (spawn state request).result with
  | rejected reason => rw [spawn_rejected_unchanged state request reason result]; exact holds
  | spawned child addressSpace =>
      obtain ⟨built, ok, _, _, eq⟩ := spawn_spawned_build state request child addressSpace result
      rw [eq]
      have trace := spawnBuild_ok state request built ok
      obtain ⟨resolution, _, _, _, _, _, stateEq⟩ := trace.granted
      rw [stateEq]
      have created : ResourceRuntimeWellFormed (issueSubject state).state :=
        ⟨issueSubject_preserves_authoritativeRuntimeWellFormed state running holds.1,
          issueSubject_preserves_resourceWellFormed state holds.2⟩
      have createdRunning : (issueSubject state).state.execution.mode = .running := by
        rw [(issueSubject_execution state built.child trace.issued).1, running]
      have creatable := spawn_creatable state request built trace created.1.left
      have spaced : ResourceRuntimeWellFormed
          (spawnSpaced (issueSubject state).state built.child built.addressSpace) :=
        ⟨(installCreatedAddressSpace_preserves_authoritativeRuntimeWellFormed _ _ _ _
            created.1 creatable).withIssuers _,
          spaced_resourceWellFormed _ _ _ _ trace.objectIssued created.2⟩
      have spacedRunning :
          (spawnSpaced (issueSubject state).state built.child built.addressSpace).execution.mode =
            .running := createdRunning
      apply recordSpawn_resourceRuntimeWellFormed
      have authoritative := authoritativeGate_capabilityCopy_preserves_authoritativeRuntimeWellFormed
        (spawnSpaced (issueSubject state).state built.child built.addressSpace)
        resolution.handle.slot built.child childEndpointSlot request.rights spaced.1
      have resource := authoritativeGate_preserves_resourceWellFormed_of_keepsHistory
        (spawnSpaced (issueSubject state).state built.child built.addressSpace)
        (.capabilityCopy resolution.handle.slot built.child childEndpointSlot request.rights)
        rfl spaced.2
      rw [authoritativeGate_ordinary_state] at authoritative resource
      simp only [gate, spacedRunning] at authoritative resource
      exact ⟨authoritative, resource⟩

/-- Kernel grant and revocation of spawn authority write only the `spawn`
projection. -/
theorem SpawnOperation.apply_preserves_resourceRuntimeWellFormed (state : CompositeState)
    (operation : SpawnOperation) (running : state.execution.mode = .running)
    (holds : ResourceRuntimeWellFormed state) :
    ResourceRuntimeWellFormed (operation.apply state).1 := by
  cases operation with
  | spawn request => exact spawn_preserves_resourceRuntimeWellFormed state request running holds
  | grantAuthority subject =>
      simp only [SpawnOperation.apply, grantSpawnAuthority]
      split
      · exact withSpawn_resourceRuntimeWellFormed holds _
      · exact holds
  | revokeAuthority subject =>
      exact withSpawn_resourceRuntimeWellFormed holds _

/-- **Every spawn-family step keeps the combined invariant**, including busy
and halted rejections. -/
theorem spawnGate_preserves_resourceRuntimeWellFormed (state : CompositeState)
    (operation : SpawnOperation) (holds : ResourceRuntimeWellFormed state) :
    ResourceRuntimeWellFormed (spawnGate state operation).state := by
  cases hmode : state.execution.mode <;> simp only [spawnGate, hmode]
  · exact SpawnOperation.apply_preserves_resourceRuntimeWellFormed state operation hmode holds
  · exact holds
  · exact holds

end LeanOS.FailStop
