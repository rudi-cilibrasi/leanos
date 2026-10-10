import LeanOS.FailStop.SpawnAddressSpace

/-!
# Fail-stop composite: explicit spawn with an empty inheritance set

Issue #489 under ADR 0010 (amendments of 2026-10-07 and 2026-10-10).  Spawn
is one composite transition on `FailStop.CompositeState`.  It is a separate
operation family (`SpawnOperation`), like `LifecycleOperation`; it does not
change `Operation`, `applyOperation`, or caller-identity `createSubject`.

`spawn state request` runs for the current subject (the parent).  In order:

1. **Spawn authority.**  The parent must be live and hold a spawn capability
   (`CompositeState.spawn.authority`) whose generation is the presented word
   (`missingSpawnRight`, `staleSpawnCapability`).
2. **Fresh identity.**  `issueSubject` draws the subject issuer's next
   identity and creates the child (`identityExhausted`, `identityRejected`).
3. **Slot table.**  The child's slot space must hold its inheritance set,
   slots `0` and `1` (`slotTableFull`).
4. **Empty address space.**  The object issuer's next identity becomes a new
   address space owned by the child, with its root capability in slot `1`
   and no mappings (`addressSpaceIdentityExhausted`, `addressSpaceRejected`,
   `addressSpaceUnavailable`).
5. **The granted endpoint.**  The parent's endpoint handle word is resolved
   in the parent's live capability space; that capability must carry
   `grant`, and the requested rights must be valid endpoint rights and a
   subset of it (`endpointHandle`, `endpointNotGrantable`, `invalidRights`,
   `rightsNotSubset`).  `Capability.copy` installs the attenuated copy in the
   child's slot `0` through the composite `capabilityCopy` publication
   (`endpointCopyRejected`).
6. **The record.**  `spawn.parent child` and `spawn.addressSpace child` are
   set.  They are records, never authority.

Every stage before the last runs on a candidate state.  Any failure returns
the typed error and **the pre-state itself** (`spawn_rejected_unchanged`), so a
partly built child (an issued identity, a created address space) never
survives a failure.
-/
namespace LeanOS.FailStop

open LeanOS
set_option linter.unusedSimpArgs false

/-! ## The operation -/

/-- The child's endpoint slot. -/
def childEndpointSlot : Nat := 0

/-- The child's address-space root slot. -/
def childAddressSpaceSlot : Nat := 1

/-- One typed error per spawn failure point. -/
inductive SpawnError where
  | missingSpawnRight
  | staleSpawnCapability
  | identityExhausted
  | identityRejected (reason : SubjectLifecycle.CreateError)
  | slotTableFull
  | addressSpaceIdentityExhausted
  | addressSpaceRejected (reason : VirtualMapping.CreateError)
  | addressSpaceUnavailable
  | endpointHandle (reason : CapabilityHandle.WordResolveDenial)
  | endpointNotGrantable
  | invalidRights
  | rightsNotSubset
  | endpointCopyRejected (reason : Capability.Denial)
  deriving DecidableEq, Repr

inductive SpawnResult where
  | spawned (child addressSpace : Nat)
  | rejected (reason : SpawnError)
  deriving DecidableEq, Repr

/-- The words a parent presents: its spawn-capability generation, a handle to
the endpoint it grants, and the rights the child receives. -/
structure SpawnRequest where
  spawnWord : UInt64
  endpointWord : UInt64
  rights : Capability.Rights
  deriving DecidableEq, Repr

structure SpawnOutcome where
  state : CompositeState
  result : SpawnResult

/-- The parent is the current subject of the execution latch. -/
def spawnParent (state : CompositeState) : Nat :=
  state.execution.core.context.currentSubject

/-- Stage 1: the parent is live and presents its current spawn capability. -/
def spawnAuthorize (state : CompositeState) (spawnWord : UInt64) : Option SpawnError :=
  if state.capabilities.subjects (spawnParent state) = true then
    match state.spawn.authority (spawnParent state) with
    | none => some .missingSpawnRight
    | some capability =>
        if capability.generation = spawnWord.toNat then none else some .staleSpawnCapability
  else some .missingSpawnRight

/-- No lifecycle record of owned memory or of an owned endpoint names the
candidate address-space identifier. -/
def addressSpaceFree (state : CompositeState) (addressSpace : Nat) : Bool :=
  state.lifecycle.ownedMemory addressSpace == none &&
    state.lifecycle.endpointOwner addressSpace == none

/-- A successfully built child: the post-state, the child, and its address
space. -/
structure SpawnBuilt where
  state : CompositeState
  child : Nat
  addressSpace : Nat

/-- Record the parent/child relation and the child's address space. -/
def recordSpawn (state : CompositeState) (parent child addressSpace : Nat) : CompositeState :=
  { state with spawn := { state.spawn with
      parent := fun candidate => if candidate = child then some parent
        else state.spawn.parent candidate
      addressSpace := fun candidate => if candidate = child then some addressSpace
        else state.spawn.addressSpace candidate } }

/-- Stage 5: grant the named endpoint to the child, on the state with the
child and its address space already built. -/
def spawnGrant (built : CompositeState) (request : SpawnRequest) (child addressSpace : Nat) :
    Except SpawnError SpawnBuilt :=
  match CapabilityHandle.resolveCurrent built.capabilities { caller := spawnParent built }
      request.endpointWord .endpoint with
  | .error reason => .error (.endpointHandle reason)
  | .ok resolution =>
      if resolution.capability.rights.grant = false then .error .endpointNotGrantable
      else if Capability.rightsValid .endpoint request.rights = false then .error .invalidRights
      else if Capability.rightsSubset request.rights resolution.capability.rights = false then
        .error .rightsNotSubset
      else
        match (Capability.copy built.capabilities (spawnParent built) resolution.handle.slot
            child childEndpointSlot request.rights).result with
        | .rejected reason => .error (.endpointCopyRejected reason)
        | .accepted =>
            .ok { state := recordSpawn
                    (applyOperation built
                      (.capabilityCopy resolution.handle.slot child childEndpointSlot
                        request.rights))
                    (spawnParent built) child addressSpace
                  child, addressSpace }

/-- The candidate state after the address-space stage: the created address
space published, and the object issuer advanced past it. -/
def spawnSpaced (created : CompositeState) (child addressSpace : Nat) : CompositeState :=
  { installCreatedAddressSpace created addressSpace child childAddressSpaceSlot with
    issuers := { created.issuers with object := { next := addressSpace + 1 } } }

/-- Stage 4: create the child's empty address space from the object issuer. -/
def spawnAddressSpace (created : CompositeState) (request : SpawnRequest) (child : Nat) :
    Except SpawnError SpawnBuilt :=
  match LifetimeIssuer.issue created.issuers.object with
  | .exhausted => .error .addressSpaceIdentityExhausted
  | .issued addressSpace _ =>
      if addressSpaceFree created addressSpace = false then .error .addressSpaceUnavailable
      else
        match (VirtualMapping.createAddressSpace created.virtualMemory addressSpace child
            childAddressSpaceSlot).result with
        | .rejected reason => .error (.addressSpaceRejected reason)
        | .accepted =>
            spawnGrant (spawnSpaced created child addressSpace) request child addressSpace

/-- Stages 1 to 6 on candidate states. -/
def spawnBuild (state : CompositeState) (request : SpawnRequest) :
    Except SpawnError SpawnBuilt :=
  match spawnAuthorize state request.spawnWord with
  | some reason => .error reason
  | none =>
      match (issueSubject state).result with
      | .exhausted => .error .identityExhausted
      | .rejected reason => .error (.identityRejected reason)
      | .issued child =>
          if (issueSubject state).state.capabilities.slotCapacity child < 2 then
            .error .slotTableFull
          else spawnAddressSpace (issueSubject state).state request child

/-- **Explicit spawn.**  Either every component of the child is built, or the
pre-state is returned with the typed error. -/
def spawn (state : CompositeState) (request : SpawnRequest) : SpawnOutcome :=
  match spawnBuild state request with
  | .error reason => { state, result := .rejected reason }
  | .ok built => { state := built.state, result := .spawned built.child built.addressSpace }

/-! ## Kernel grant and revocation of spawn authority -/

/-- The spawn family.  `grantAuthority` and `revokeAuthority` are trusted
kernel operations, like `DeviceCapability.grant`; no subject word reaches
them.  This is the unaccounted core: the public spawn family is
`ChildOperation` (`SpawnAccounting`, issues #490 and #491), which charges
spawn against the parent's subject budget and records the child in the
parent's child table. -/
inductive SpawnOperation where
  | spawn (request : SpawnRequest)
  | grantAuthority (subject : Nat)
  | revokeAuthority (subject : Nat)
  deriving DecidableEq, Repr

inductive SpawnOperationResult where
  | spawn (result : SpawnResult)
  | granted (generation : Nat)
  | grantRejected
  | revoked
  deriving DecidableEq, Repr

/-- Grant a fresh-generation spawn capability to a live subject. -/
def grantSpawnAuthority (state : CompositeState) (subject : Nat) :
    CompositeState × SpawnOperationResult :=
  if state.capabilities.subjects subject = true then
    ({ state with spawn := { state.spawn with
        authority := fun candidate => if candidate = subject then
          some { generation := state.spawn.nextGeneration } else state.spawn.authority candidate
        nextGeneration := state.spawn.nextGeneration + 1 } },
      .granted state.spawn.nextGeneration)
  else (state, .grantRejected)

/-- Revoke a subject's spawn capability. -/
def revokeSpawnAuthority (state : CompositeState) (subject : Nat) : CompositeState :=
  { state with spawn := { state.spawn with
      authority := fun candidate => if candidate = subject then none
        else state.spawn.authority candidate } }

def SpawnOperation.apply (state : CompositeState) : SpawnOperation →
    CompositeState × SpawnOperationResult
  | .spawn request =>
      ((FailStop.spawn state request).state, .spawn (FailStop.spawn state request).result)
  | .grantAuthority subject => grantSpawnAuthority state subject
  | .revokeAuthority subject => (revokeSpawnAuthority state subject, .revoked)

inductive SpawnGateResult where
  | completed (result : SpawnOperationResult)
  | rejectedBusy
  | rejectedHalted (record : HaltRecord)
  deriving DecidableEq, Repr

structure SpawnGateOutcome where
  state : CompositeState
  result : SpawnGateResult

/-- The spawn family runs only under the running latch. -/
def spawnGate (state : CompositeState) (operation : SpawnOperation) : SpawnGateOutcome :=
  match state.execution.mode with
  | .running =>
      { state := (operation.apply state).1, result := .completed (operation.apply state).2 }
  | .handling _ => { state, result := .rejectedBusy }
  | .halted record => { state, result := .rejectedHalted record }

/-! ## Rollback -/

/-- **Rollback.**  Every rejected spawn, at every failure point, returns the
pre-state exactly. -/
theorem spawn_rejected_unchanged (state : CompositeState) (request : SpawnRequest)
    (reason : SpawnError) (rejected : (spawn state request).result = .rejected reason) :
    (spawn state request).state = state := by
  unfold spawn at rejected ⊢
  split at rejected
  · rfl
  · simp at rejected

/-- The typed error of a rejected spawn is exactly the error of the first
failing stage. -/
theorem spawn_rejected_iff (state : CompositeState) (request : SpawnRequest)
    (reason : SpawnError) :
    (spawn state request).result = .rejected reason ↔ spawnBuild state request = .error reason := by
  unfold spawn
  split <;> simp_all

/-- Missing spawn authority is rejected with the pre-state. -/
theorem spawn_missing_right (state : CompositeState) (request : SpawnRequest)
    (missing : state.spawn.authority (spawnParent state) = none) :
    (spawn state request).result = .rejected .missingSpawnRight ∧
      (spawn state request).state = state := by
  have stage : spawnAuthorize state request.spawnWord = some .missingSpawnRight := by
    unfold spawnAuthorize; split <;> simp_all
  have result : (spawn state request).result = .rejected .missingSpawnRight := by
    rw [spawn_rejected_iff]; simp [spawnBuild, stage]
  exact ⟨result, spawn_rejected_unchanged state request _ result⟩

/-- A stale spawn-capability word is rejected with the pre-state. -/
theorem spawn_stale_spawn_capability (state : CompositeState) (request : SpawnRequest)
    (capability : SpawnCapability)
    (live : state.capabilities.subjects (spawnParent state) = true)
    (held : state.spawn.authority (spawnParent state) = some capability)
    (stale : capability.generation ≠ request.spawnWord.toNat) :
    (spawn state request).result = .rejected .staleSpawnCapability ∧
      (spawn state request).state = state := by
  have stage : spawnAuthorize state request.spawnWord = some .staleSpawnCapability := by
    simp [spawnAuthorize, live, held, stale]
  have result : (spawn state request).result = .rejected .staleSpawnCapability := by
    rw [spawn_rejected_iff]; simp [spawnBuild, stage]
  exact ⟨result, spawn_rejected_unchanged state request _ result⟩

/-- An exhausted subject issuer is rejected with the pre-state, both issuers
included. -/
theorem spawn_identity_exhausted (state : CompositeState) (request : SpawnRequest)
    (authorized : spawnAuthorize state request.spawnWord = none)
    (exhausted : LifetimeIssuer.exhausted state.issuers.subject = true) :
    (spawn state request).result = .rejected .identityExhausted ∧
      (spawn state request).state = state := by
  have issued : (issueSubject state).result = .exhausted :=
    (issueSubject_exhausted_iff state).2 exhausted
  have result : (spawn state request).result = .rejected .identityExhausted := by
    rw [spawn_rejected_iff]; simp [spawnBuild, authorized, issued]
  exact ⟨result, spawn_rejected_unchanged state request _ result⟩

/-- A child slot space too small for the inheritance set is rejected with the
pre-state: the identity just drawn is not consumed. -/
theorem spawn_slot_table_full (state : CompositeState) (request : SpawnRequest) (child : Nat)
    (authorized : spawnAuthorize state request.spawnWord = none)
    (issued : (issueSubject state).result = .issued child)
    (full : (issueSubject state).state.capabilities.slotCapacity child < 2) :
    (spawn state request).result = .rejected .slotTableFull ∧
      (spawn state request).state = state := by
  have result : (spawn state request).result = .rejected .slotTableFull := by
    rw [spawn_rejected_iff]; simp [spawnBuild, authorized, issued, full]
  exact ⟨result, spawn_rejected_unchanged state request _ result⟩

/-- An exhausted object issuer is rejected with the pre-state: the subject
identity and slot check already passed are rolled back. -/
theorem spawn_address_space_exhausted (state : CompositeState) (request : SpawnRequest)
    (child : Nat)
    (authorized : spawnAuthorize state request.spawnWord = none)
    (issued : (issueSubject state).result = .issued child)
    (room : ¬(issueSubject state).state.capabilities.slotCapacity child < 2)
    (exhausted : LifetimeIssuer.exhausted state.issuers.object = true) :
    (spawn state request).result = .rejected .addressSpaceIdentityExhausted ∧
      (spawn state request).state = state := by
  have object : (issueSubject state).state.issuers.object = state.issuers.object := by
    obtain ⟨_, _, _, eq⟩ := issueSubject_issued state child issued
    rw [eq]
  have issue : LifetimeIssuer.issue (issueSubject state).state.issuers.object = .exhausted := by
    rw [object]; simp [LifetimeIssuer.issue, exhausted]
  have result : (spawn state request).result = .rejected .addressSpaceIdentityExhausted := by
    rw [spawn_rejected_iff]
    simp [spawnBuild, authorized, issued, room, spawnAddressSpace, issue]
  exact ⟨result, spawn_rejected_unchanged state request _ result⟩

/-! ## The accepted path -/

/-- What an accepted endpoint grant did on the built state `spaced`. -/
inductive SpawnGranted (spaced : CompositeState) (request : SpawnRequest) (built : SpawnBuilt) :
    Prop where
  | intro (resolution : CapabilityHandle.Resolution)
      (resolved : CapabilityHandle.resolveCurrent spaced.capabilities
        { caller := spawnParent spaced } request.endpointWord .endpoint = .ok resolution)
      (grant : resolution.capability.rights.grant = true)
      (valid : Capability.rightsValid .endpoint request.rights = true)
      (subset : Capability.rightsSubset request.rights resolution.capability.rights = true)
      (copied : (Capability.copy spaced.capabilities (spawnParent spaced) resolution.handle.slot
        built.child childEndpointSlot request.rights).result = .accepted)
      (state : built.state = recordSpawn
        (applyOperation spaced
          (.capabilityCopy resolution.handle.slot built.child childEndpointSlot request.rights))
        (spawnParent spaced) built.child built.addressSpace)

theorem spawnGrant_ok (spaced : CompositeState) (request : SpawnRequest) (child addressSpace : Nat)
    (built : SpawnBuilt) (ok : spawnGrant spaced request child addressSpace = .ok built) :
    built.child = child ∧ built.addressSpace = addressSpace ∧ SpawnGranted spaced request built := by
  unfold spawnGrant at ok
  cases resolved : CapabilityHandle.resolveCurrent spaced.capabilities
      { caller := spawnParent spaced } request.endpointWord .endpoint with
  | error reason => simp [resolved] at ok
  | ok resolution =>
      simp only [resolved] at ok
      cases grant : resolution.capability.rights.grant
      · simp [grant] at ok
      cases valid : Capability.rightsValid .endpoint request.rights
      · simp [grant, valid] at ok
      cases subset : Capability.rightsSubset request.rights resolution.capability.rights
      · simp [grant, valid, subset] at ok
      cases copied : (Capability.copy spaced.capabilities (spawnParent spaced)
          resolution.handle.slot child childEndpointSlot request.rights).result with
      | rejected reason => simp [grant, valid, subset, copied] at ok
      | accepted =>
          simp only [grant, valid, subset, copied, Bool.true_eq_false, ↓reduceIte,
            Except.ok.injEq] at ok
          subst ok
          exact ⟨rfl, rfl, ⟨resolution, resolved, grant, valid, subset, copied, rfl⟩⟩

/-- Everything an accepted spawn did, stage by stage.  `created` is the state
after the identity, `spaced` after the address space. -/
structure SpawnTrace (state : CompositeState) (request : SpawnRequest) (built : SpawnBuilt) :
    Prop where
  authorized : spawnAuthorize state request.spawnWord = none
  issued : (issueSubject state).result = .issued built.child
  room : ¬(issueSubject state).state.capabilities.slotCapacity built.child < 2
  objectIssued : LifetimeIssuer.issue (issueSubject state).state.issuers.object =
    .issued built.addressSpace { next := built.addressSpace + 1 }
  free : addressSpaceFree (issueSubject state).state built.addressSpace = true
  spaceAccepted : (VirtualMapping.createAddressSpace (issueSubject state).state.virtualMemory
    built.addressSpace built.child childAddressSpaceSlot).result = .accepted
  granted : SpawnGranted (spawnSpaced (issueSubject state).state built.child built.addressSpace)
    request built

/-- Inversion of an accepted spawn into its stages. -/
theorem spawnBuild_ok (state : CompositeState) (request : SpawnRequest) (built : SpawnBuilt)
    (ok : spawnBuild state request = .ok built) : SpawnTrace state request built := by
  unfold spawnBuild at ok
  split at ok
  · contradiction
  next authorized =>
  split at ok
  · contradiction
  · contradiction
  next child issued =>
  split at ok
  · contradiction
  next room =>
  unfold spawnAddressSpace at ok
  split at ok
  · contradiction
  next addressSpace objectIssuer objectIssued =>
  have objectIssuer_eq : objectIssuer = { next := addressSpace + 1 } := by
    obtain ⟨_, hfollow, _, _⟩ := LifetimeIssuer.issued_facts objectIssued
    cases objectIssuer; simp_all
  subst objectIssuer_eq
  split at ok
  · contradiction
  next free =>
  split at ok
  · contradiction
  next spaceAccepted =>
  obtain ⟨hchild, haddress, granted⟩ := spawnGrant_ok _ _ _ _ _ ok
  subst hchild haddress
  exact ⟨authorized, issued, room, objectIssued, by simpa using free, spaceAccepted, granted⟩

theorem spawn_spawned_build (state : CompositeState) (request : SpawnRequest)
    (child addressSpace : Nat)
    (spawned : (spawn state request).result = .spawned child addressSpace) :
    ∃ built, spawnBuild state request = .ok built ∧ built.child = child ∧
      built.addressSpace = addressSpace ∧ (spawn state request).state = built.state := by
  unfold spawn at spawned ⊢
  split at spawned
  · contradiction
  next built ok =>
    cases spawned
    exact ⟨built, ok, rfl, rfl, by simp [ok]⟩

end LeanOS.FailStop
