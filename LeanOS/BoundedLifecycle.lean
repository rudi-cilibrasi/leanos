import LeanOS.SubjectLifecycle
import LeanOS.LifetimeIssuer

/-!
# Bounded lifecycle-identity issuance runtime

This module makes the two `LifetimeIssuer` issuers the authoritative creation
path for subject and object lifetimes.  Public creation operations accept no
identity word: every accepted creation receives exactly the issuer's next
representable identity and the composite result returns it.  The low-level
lifecycle creations (`SubjectLifecycle.create`, `MemoryLifecycle.allocate`,
`EndpointIPC.create`, `VirtualMapping.createAddressSpace`) remain internal
transitions invoked only with the identity the issuer just produced.

One object issuer covers the memory, endpoint, and address-space kinds, so an
identifier retired under one kind can never be rebound under another kind.
The existing distributed `issued`/`issuedAddressSpace` histories are preserved
as derived views bounded by the counter, never as independent allocators.
Issuance is atomic with creation: every rejected or exhausted creation
preserves the complete runtime including both counters, and cleanup,
revocation, termination, and failed allocation never advance or recycle a
counter.

The subject-domain lifecycle state and the object-domain capability store are
kept as the existing separate authoritative shapes; unifying them into one
coherent runtime is issue #104, which composes through the projection and
monotonicity lemmas proved here.
-/
namespace LeanOS.BoundedLifecycle

set_option linter.unusedSimpArgs false

open LeanOS
open LeanOS.LifetimeIssuer (Issuer IssueResult)

abbrev SubjectId := Capability.SubjectId
abbrev ObjectId := Capability.ObjectId
abbrev SlotId := Capability.SlotId

/-- Composite runtime: both kernel-owned issuers next to the subject-domain
lifecycle and the object-domain state.  The endpoint view shares the one
object-domain memory state instead of duplicating it. -/
structure Runtime where
  subjectIssuer : Issuer .subject
  objectIssuer : Issuer .object
  lifecycle : SubjectLifecycle.State
  virtualMemory : VirtualMapping.State
  mailbox : ObjectId → Option EndpointIPC.Envelope
  sendHistory : ObjectId → List EndpointIPC.Envelope

/-- The derived endpoint state over the shared object-domain memory. -/
def Runtime.endpoints (runtime : Runtime) : EndpointIPC.State :=
  { toState := runtime.virtualMemory.memory
    issuedAddressSpace := runtime.virtualMemory.issuedAddressSpace
    mailbox := runtime.mailbox
    sendHistory := runtime.sendHistory }

/-- Reinstall an endpoint-transition result into the shared runtime fields. -/
def installEndpoints (runtime : Runtime) (endpoints : EndpointIPC.State) : Runtime :=
  { runtime with
    virtualMemory := { runtime.virtualMemory with
      memory := endpoints.toState
      issuedAddressSpace := endpoints.issuedAddressSpace }
    mailbox := endpoints.mailbox
    sendHistory := endpoints.sendHistory }

theorem installEndpoints_endpoints (runtime : Runtime) (endpoints : EndpointIPC.State) :
    (installEndpoints runtime endpoints).endpoints = endpoints := rfl

/-- Projection lemmas so issue #104 can compose the derived endpoint view
without unfolding the runtime shape. -/
theorem endpoints_toState (runtime : Runtime) :
    runtime.endpoints.toState = runtime.virtualMemory.memory := rfl

theorem endpoints_issued (runtime : Runtime) :
    runtime.endpoints.issued = runtime.virtualMemory.memory.issued := rfl

theorem endpoints_issuedAddressSpace (runtime : Runtime) :
    runtime.endpoints.issuedAddressSpace = runtime.virtualMemory.issuedAddressSpace := rfl

theorem endpoints_capabilities (runtime : Runtime) :
    runtime.endpoints.capabilities = runtime.virtualMemory.memory.capabilities := rfl

/-- The single object-lifetime history: an identifier consumed under any kind
is consumed for every kind. -/
def issuedObject (runtime : Runtime) (object : ObjectId) : Bool :=
  runtime.virtualMemory.memory.issued object ||
    runtime.virtualMemory.issuedAddressSpace object

/-- Typed creation result.  `exhausted` is the identity-domain failure and is
distinct from every underlying subsystem denial, including the separate
capability-generation exhaustion. -/
inductive CreationResult (ε : Type) where
  | issued (identity : Nat)
  | exhausted
  | rejected (reason : ε)
  deriving DecidableEq, Repr

structure CreationOutcome (ε : Type) where
  runtime : Runtime
  result : CreationResult ε

/-! ## Authoritative creation operations

Each creation draws the candidate identity from its domain issuer, runs the
internal lifecycle transition with exactly that identity, and commits the
advanced issuer only together with an accepted transition.  No caller word
participates in identity selection.
-/

/-- Create the next subject lifetime.  The issued identity is returned, never
accepted from the caller. -/
def createSubject (runtime : Runtime) : CreationOutcome SubjectLifecycle.CreateError :=
  match LifetimeIssuer.issue runtime.subjectIssuer with
  | .exhausted => { runtime, result := .exhausted }
  | .issued identity issuer =>
      let outcome := SubjectLifecycle.create runtime.lifecycle identity
      match outcome.result with
      | .accepted =>
          { runtime := { runtime with subjectIssuer := issuer, lifecycle := outcome.state }
            result := .issued identity }
      | .rejected reason => { runtime, result := .rejected reason }

/-- Allocate the next memory-object lifetime for a trusted subject and slot. -/
def allocateMemory (runtime : Runtime) (subject : SubjectId) (slot : SlotId) :
    CreationOutcome MemoryLifecycle.AllocationError :=
  match LifetimeIssuer.issue runtime.objectIssuer with
  | .exhausted => { runtime, result := .exhausted }
  | .issued object issuer =>
      let outcome := MemoryLifecycle.allocate runtime.virtualMemory.memory object subject slot
      match outcome.result with
      | .accepted =>
          { runtime := { runtime with
              objectIssuer := issuer
              virtualMemory := { runtime.virtualMemory with memory := outcome.state } }
            result := .issued object }
      | .rejected reason => { runtime, result := .rejected reason }

/-- Create the next endpoint-object lifetime for a trusted subject and slot. -/
def createEndpoint (runtime : Runtime) (subject : SubjectId) (slot : SlotId) :
    CreationOutcome EndpointIPC.CreateError :=
  match LifetimeIssuer.issue runtime.objectIssuer with
  | .exhausted => { runtime, result := .exhausted }
  | .issued object issuer =>
      let outcome := EndpointIPC.create runtime.endpoints object subject slot
      match outcome.result with
      | .accepted =>
          { runtime := { installEndpoints runtime outcome.state with objectIssuer := issuer }
            result := .issued object }
      | .rejected reason => { runtime, result := .rejected reason }

/-- Create the next address-space-object lifetime for a trusted subject/slot. -/
def createAddressSpace (runtime : Runtime) (subject : SubjectId) (slot : SlotId) :
    CreationOutcome VirtualMapping.CreateError :=
  match LifetimeIssuer.issue runtime.objectIssuer with
  | .exhausted => { runtime, result := .exhausted }
  | .issued addressSpace issuer =>
      let outcome := VirtualMapping.createAddressSpace runtime.virtualMemory addressSpace
        subject slot
      match outcome.result with
      | .accepted =>
          { runtime := { runtime with objectIssuer := issuer, virtualMemory := outcome.state }
            result := .issued addressSpace }
      | .rejected reason => { runtime, result := .rejected reason }

/-! ## Fault-driven cleanup and ordinary operations

Cleanup consumes the same never-reused bounded identity: none of these
operations reads or writes either issuer, and each leaves both append-only
histories intact.
-/

/-- Terminate a subject lifetime; the identity remains consumed forever. -/
def terminateSubject (runtime : Runtime) (subject : SubjectId) :
    Runtime × SubjectLifecycle.Result SubjectLifecycle.TerminateError :=
  let outcome := SubjectLifecycle.terminate runtime.lifecycle subject
  ({ runtime with lifecycle := outcome.state }, outcome.result)

/-- Release a memory object through the shared mapping-aware retirement. -/
def releaseMemory (runtime : Runtime) (subject : SubjectId) (slot : SlotId) :
    Runtime × VirtualMapping.Result MemoryLifecycle.ReleaseError :=
  let outcome := VirtualMapping.release runtime.virtualMemory subject slot
  ({ runtime with virtualMemory := outcome.state }, outcome.result)

/-- Destroy an endpoint object through the shared endpoint retirement. -/
def destroyEndpoint (runtime : Runtime) (subject : SubjectId) (slot : SlotId) :
    Runtime × EndpointIPC.Result EndpointIPC.DestroyError :=
  let outcome := EndpointIPC.destroy runtime.endpoints subject slot
  (installEndpoints runtime outcome.state, outcome.result)

/-- Destroy an address-space object through the shared retirement. -/
def destroyAddressSpace (runtime : Runtime) (subject : SubjectId) (slot : SlotId) :
    Runtime × VirtualMapping.Result VirtualMapping.DestroyError :=
  let outcome := VirtualMapping.destroyAddressSpace runtime.virtualMemory subject slot
  ({ runtime with virtualMemory := outcome.state }, outcome.result)

/-- Ordinary endpoint send over the shared object-domain state. -/
def send (runtime : Runtime) (caller : SubjectId) (slot : SlotId)
    (payload : EndpointIPC.Payload) :
    Runtime × EndpointIPC.Result EndpointIPC.SendError :=
  let outcome := EndpointIPC.send runtime.endpoints caller slot payload
  (installEndpoints runtime outcome.state, outcome.result)

/-- Ordinary endpoint receive over the shared object-domain state. -/
def receive (runtime : Runtime) (caller : SubjectId) (slot : SlotId) :
    Runtime × EndpointIPC.ReceiveResult :=
  let outcome := EndpointIPC.receive runtime.endpoints caller slot
  (installEndpoints runtime outcome.state, outcome.result)

/-! ## Untrusted command boundary

The request words of a creation command are inert.  Identity selection reads
only the kernel-owned issuer, so no untrusted word can select the returned
identity, skip the next value, reach into the other domain's issuer, or turn
an exhaustion result into success.
-/

structure UntrustedRequest where
  word0 : UInt64
  word1 : UInt64
  deriving DecidableEq, Repr

/-- Userspace-facing subject creation: the untrusted request is ignored by
construction. -/
def createSubjectCommand (runtime : Runtime) (_request : UntrustedRequest) :
    CreationOutcome SubjectLifecycle.CreateError :=
  createSubject runtime

/-- Userspace-facing memory allocation: only the trusted subject and slot
participate; the untrusted request words are inert. -/
def allocateMemoryCommand (runtime : Runtime) (trustedSubject : SubjectId)
    (slot : SlotId) (_request : UntrustedRequest) :
    CreationOutcome MemoryLifecycle.AllocationError :=
  allocateMemory runtime trustedSubject slot

/-- The untrusted words cannot influence any part of the outcome. -/
theorem createSubjectCommand_confined (runtime : Runtime)
    (first second : UntrustedRequest) :
    createSubjectCommand runtime first = createSubjectCommand runtime second := rfl

theorem allocateMemoryCommand_confined (runtime : Runtime) (trustedSubject : SubjectId)
    (slot : SlotId) (first second : UntrustedRequest) :
    allocateMemoryCommand runtime trustedSubject slot first =
      allocateMemoryCommand runtime trustedSubject slot second := rfl

/-! ## Registry projections of the internal lifecycle transitions

These small lemmas expose exactly the issuance-relevant registries of each
reused transition, so the composite proofs and issue #104 can reason about the
issuer contract without unfolding every lifecycle map.
-/

theorem subject_create_accepted_registry (state : SubjectLifecycle.State)
    (subject : SubjectId)
    (h : (SubjectLifecycle.create state subject).result = .accepted) :
    (SubjectLifecycle.create state subject).state.issuedSubjects =
        SubjectLifecycle.setBool state.issuedSubjects subject true ∧
      (SubjectLifecycle.create state subject).state.capabilities.subjects =
        SubjectLifecycle.setBool state.capabilities.subjects subject true := by
  simp only [SubjectLifecycle.create] at h ⊢
  split <;> simp_all [SubjectLifecycle.reject]
  split <;> simp_all [SubjectLifecycle.reject]

theorem subject_terminate_registry (state : SubjectLifecycle.State) (subject : SubjectId) :
    (SubjectLifecycle.terminate state subject).state.issuedSubjects =
        state.issuedSubjects ∧
      ∀ candidate,
        (SubjectLifecycle.terminate state subject).state.capabilities.subjects candidate =
          true → state.capabilities.subjects candidate = true := by
  simp only [SubjectLifecycle.terminate]
  split
  · exact ⟨rfl, fun _ h => h⟩
  split
  · exact ⟨rfl, fun _ h => h⟩
  · refine ⟨rfl, ?_⟩
    intro candidate h
    by_cases heq : candidate = subject
    · subst candidate
      simp [SubjectLifecycle.terminateState, SubjectLifecycle.terminatedCapabilities,
        SubjectLifecycle.setBool] at h
    · simpa [SubjectLifecycle.terminateState, SubjectLifecycle.terminatedCapabilities,
        SubjectLifecycle.setBool, heq] using h

theorem memory_allocate_accepted_registry (memory : MemoryLifecycle.State)
    (object : ObjectId) (subject : SubjectId) (slot : SlotId)
    (h : (MemoryLifecycle.allocate memory object subject slot).result = .accepted) :
    (MemoryLifecycle.allocate memory object subject slot).state.issued =
        MemoryLifecycle.setIssued memory.issued object ∧
      (MemoryLifecycle.allocate memory object subject slot).state.capabilities.objects =
        MemoryLifecycle.setObject memory.capabilities.objects object true ∧
      (MemoryLifecycle.allocate memory object subject slot).state.capabilities.kinds =
        fun candidate => if candidate = object then some .memory
          else memory.capabilities.kinds candidate := by
  simp only [MemoryLifecycle.allocate] at h ⊢
  split <;> simp_all [MemoryLifecycle.reject]
  split <;> simp_all [MemoryLifecycle.reject]
  split <;> simp_all [MemoryLifecycle.reject]
  split <;> simp_all [MemoryLifecycle.reject]
  split <;> simp_all [MemoryLifecycle.reject]
  split <;> simp_all [MemoryLifecycle.reject, Capability.installRoot, Capability.install,
    MemoryLifecycle.activateObject]

theorem memory_release_registry (memory : MemoryLifecycle.State)
    (subject : SubjectId) (slot : SlotId) :
    (MemoryLifecycle.release memory subject slot).state.issued = memory.issued ∧
      (∀ object,
        (MemoryLifecycle.release memory subject slot).state.capabilities.objects object =
          true → memory.capabilities.objects object = true) ∧
      ∀ object kind,
        (MemoryLifecycle.release memory subject slot).state.capabilities.kinds object =
          some kind → memory.capabilities.kinds object = some kind := by
  refine ⟨MemoryLifecycle.release_preserves_issued memory subject slot, ?_, ?_⟩
  · intro object h
    simp only [MemoryLifecycle.release] at h
    split at h <;> try exact h
    next cap _ =>
      split at h <;> try exact h
      split at h <;> try exact h
      split at h <;> try exact h
      next frame _ =>
        split at h <;> try exact h
        by_cases heq : object = cap.object
        · subst object
          simp [MemoryLifecycle.retireCapabilities, MemoryLifecycle.setObject] at h
        · simpa [MemoryLifecycle.retireCapabilities, MemoryLifecycle.setObject, heq] using h
  · intro object kind h
    simp only [MemoryLifecycle.release] at h
    split at h <;> try exact h
    next cap _ =>
      split at h <;> try exact h
      split at h <;> try exact h
      split at h <;> try exact h
      next frame _ =>
        split at h <;> try exact h
        by_cases heq : object = cap.object
        · subst object
          simp [MemoryLifecycle.retireCapabilities] at h
        · simpa [MemoryLifecycle.retireCapabilities, heq] using h

theorem virtual_release_projections (state : VirtualMapping.State)
    (subject : SubjectId) (slot : SlotId) :
    (VirtualMapping.release state subject slot).state.memory =
        (MemoryLifecycle.release state.memory subject slot).state ∧
      (VirtualMapping.release state subject slot).state.issuedAddressSpace =
        state.issuedAddressSpace := by
  simp only [VirtualMapping.release]
  split
  · next reason hresult =>
      exact ⟨(MemoryLifecycle.release_rejected_unchanged state.memory subject slot reason
        hresult).symm, rfl⟩
  · next hresult =>
      split <;> exact ⟨rfl, rfl⟩

theorem endpoint_create_accepted_registry (state : EndpointIPC.State)
    (object : ObjectId) (subject : SubjectId) (slot : SlotId)
    (h : (EndpointIPC.create state object subject slot).result = .accepted) :
    (EndpointIPC.create state object subject slot).state.issued =
        EndpointIPC.setBool state.issued object true ∧
      (EndpointIPC.create state object subject slot).state.issuedAddressSpace =
        state.issuedAddressSpace ∧
      (EndpointIPC.create state object subject slot).state.capabilities.objects =
        EndpointIPC.setBool state.capabilities.objects object true ∧
      (EndpointIPC.create state object subject slot).state.capabilities.kinds =
        fun candidate => if candidate = object then some .endpoint
          else state.capabilities.kinds candidate := by
  simp only [EndpointIPC.create] at h ⊢
  split <;> simp_all [EndpointIPC.reject]
  split <;> simp_all [EndpointIPC.reject]
  split <;> simp_all [EndpointIPC.reject]
  split <;> simp_all [EndpointIPC.reject]
  split <;> simp_all [EndpointIPC.reject]
  split <;> simp_all [EndpointIPC.reject]
  split <;> simp_all [EndpointIPC.reject, EndpointIPC.activate, Capability.installRoot,
    Capability.install]

theorem endpoint_destroy_registry (state : EndpointIPC.State)
    (subject : SubjectId) (slot : SlotId) :
    (EndpointIPC.destroy state subject slot).state.issued = state.issued ∧
      (EndpointIPC.destroy state subject slot).state.issuedAddressSpace =
        state.issuedAddressSpace ∧
      (∀ object,
        (EndpointIPC.destroy state subject slot).state.capabilities.objects object = true →
          state.capabilities.objects object = true) ∧
      ∀ object kind,
        (EndpointIPC.destroy state subject slot).state.capabilities.kinds object =
          some kind → state.capabilities.kinds object = some kind := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [EndpointIPC.destroy]
    split <;> try rfl
    next cap _ =>
      split <;> try rfl
      split <;> try rfl
      split <;> try rfl
      split <;> rfl
  · simp only [EndpointIPC.destroy]
    split <;> try rfl
    next cap _ =>
      split <;> try rfl
      split <;> try rfl
      split <;> try rfl
      split <;> rfl
  · intro object h
    simp only [EndpointIPC.destroy] at h
    split at h <;> try exact h
    next cap _ =>
      split at h <;> try exact h
      split at h <;> try exact h
      split at h <;> try exact h
      split at h <;> try exact h
      by_cases heq : object = cap.object
      · subst object
        simp [EndpointIPC.retire, EndpointIPC.setBool] at h
      · simpa [EndpointIPC.retire, EndpointIPC.setBool, heq] using h
  · intro object kind h
    simp only [EndpointIPC.destroy] at h
    split at h <;> try exact h
    next cap _ =>
      split at h <;> try exact h
      split at h <;> try exact h
      split at h <;> try exact h
      split at h <;> try exact h
      by_cases heq : object = cap.object
      · subst object
        simp [EndpointIPC.retire] at h
      · simpa [EndpointIPC.retire, heq] using h

theorem address_space_create_accepted_registry (state : VirtualMapping.State)
    (addressSpace : ObjectId) (subject : SubjectId) (slot : SlotId)
    (h : (VirtualMapping.createAddressSpace state addressSpace subject slot).result =
      .accepted) :
    (VirtualMapping.createAddressSpace state addressSpace subject slot).state.memory.issued =
        MemoryLifecycle.setIssued state.memory.issued addressSpace ∧
      (VirtualMapping.createAddressSpace state addressSpace subject
          slot).state.issuedAddressSpace =
        VirtualMapping.setIssuedAddressSpace state.issuedAddressSpace addressSpace ∧
      (VirtualMapping.createAddressSpace state addressSpace subject
          slot).state.memory.capabilities.objects =
        MemoryLifecycle.setObject state.memory.capabilities.objects addressSpace true ∧
      (VirtualMapping.createAddressSpace state addressSpace subject
          slot).state.memory.capabilities.kinds =
        fun candidate => if candidate = addressSpace then some .addressSpace
          else state.memory.capabilities.kinds candidate := by
  simp only [VirtualMapping.createAddressSpace] at h ⊢
  split <;> simp_all [VirtualMapping.reject]
  split <;> simp_all [VirtualMapping.reject]
  split <;> simp_all [VirtualMapping.reject]
  split <;> simp_all [VirtualMapping.reject]
  split <;> simp_all [VirtualMapping.reject]
  split <;> simp_all [VirtualMapping.reject, VirtualMapping.clearAddressSpaceMappings,
    VirtualMapping.activateAddressSpace, Capability.installRoot, Capability.install]

theorem address_space_destroy_registry (state : VirtualMapping.State)
    (subject : SubjectId) (slot : SlotId) :
    (VirtualMapping.destroyAddressSpace state subject slot).state.memory.issued =
        state.memory.issued ∧
      (VirtualMapping.destroyAddressSpace state subject slot).state.issuedAddressSpace =
        state.issuedAddressSpace ∧
      (∀ object,
        (VirtualMapping.destroyAddressSpace state subject
            slot).state.memory.capabilities.objects object = true →
          state.memory.capabilities.objects object = true) ∧
      ∀ object kind,
        (VirtualMapping.destroyAddressSpace state subject
            slot).state.memory.capabilities.kinds object = some kind →
          state.memory.capabilities.kinds object = some kind := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [VirtualMapping.destroyAddressSpace]
    split <;> try rfl
    next cap _ =>
      split <;> try rfl
      split <;> try rfl
      split <;> try rfl
      next owner _ => split <;> rfl
  · simp only [VirtualMapping.destroyAddressSpace]
    split <;> try rfl
    next cap _ =>
      split <;> try rfl
      split <;> try rfl
      split <;> try rfl
      next owner _ => split <;> rfl
  · intro object h
    simp only [VirtualMapping.destroyAddressSpace] at h
    split at h <;> try exact h
    next cap _ =>
      split at h <;> try exact h
      split at h <;> try exact h
      split at h <;> try exact h
      next owner _ =>
        split at h <;> try exact h
        by_cases heq : object = cap.object
        · subst object
          simp [VirtualMapping.clearAddressSpaceMappings, VirtualMapping.retireAddressSpace,
            MemoryLifecycle.retireCapabilities, MemoryLifecycle.setObject] at h
        · simpa [VirtualMapping.clearAddressSpaceMappings, VirtualMapping.retireAddressSpace,
            MemoryLifecycle.retireCapabilities, MemoryLifecycle.setObject, heq] using h
  · intro object kind h
    simp only [VirtualMapping.destroyAddressSpace] at h
    split at h <;> try exact h
    next cap _ =>
      split at h <;> try exact h
      split at h <;> try exact h
      split at h <;> try exact h
      next owner _ =>
        split at h <;> try exact h
        by_cases heq : object = cap.object
        · subst object
          simp [VirtualMapping.clearAddressSpaceMappings, VirtualMapping.retireAddressSpace,
            MemoryLifecycle.retireCapabilities] at h
        · simpa [VirtualMapping.clearAddressSpaceMappings, VirtualMapping.retireAddressSpace,
            MemoryLifecycle.retireCapabilities, heq] using h

theorem send_registry (state : EndpointIPC.State) (caller : SubjectId) (slot : SlotId)
    (payload : EndpointIPC.Payload) :
    (EndpointIPC.send state caller slot payload).state.toState = state.toState ∧
      (EndpointIPC.send state caller slot payload).state.issuedAddressSpace =
        state.issuedAddressSpace := by
  simp only [EndpointIPC.send]
  split <;> try exact ⟨rfl, rfl⟩
  next cap _ =>
    split <;> try exact ⟨rfl, rfl⟩
    split <;> try exact ⟨rfl, rfl⟩
    split <;> try exact ⟨rfl, rfl⟩
    split <;> try exact ⟨rfl, rfl⟩
    split <;> exact ⟨rfl, rfl⟩

theorem receive_registry (state : EndpointIPC.State) (caller : SubjectId) (slot : SlotId) :
    (EndpointIPC.receive state caller slot).state.toState = state.toState ∧
      (EndpointIPC.receive state caller slot).state.issuedAddressSpace =
        state.issuedAddressSpace := by
  simp only [EndpointIPC.receive]
  split <;> try exact ⟨rfl, rfl⟩
  next cap _ =>
    split <;> try exact ⟨rfl, rfl⟩
    split <;> try exact ⟨rfl, rfl⟩
    split <;> try exact ⟨rfl, rfl⟩
    split <;> try exact ⟨rfl, rfl⟩
    split <;> exact ⟨rfl, rfl⟩

/-! ## Atomic issuance contract

Every creation either issues exactly the next counter value together with the
accepted internal transition, or preserves the complete runtime — including
both issuers and both histories — under the typed exhaustion or rejection.
-/

theorem createSubject_exhausted_unchanged (runtime : Runtime)
    (h : (createSubject runtime).result = .exhausted) :
    (createSubject runtime).runtime = runtime := by
  cases hissue : LifetimeIssuer.issue runtime.subjectIssuer with
  | exhausted => simp [createSubject, hissue]
  | issued identity issuer =>
      cases hresult : (SubjectLifecycle.create runtime.lifecycle identity).result with
      | accepted => simp [createSubject, hissue, hresult] at h
      | rejected reason => simp [createSubject, hissue, hresult]

theorem createSubject_rejected_unchanged (runtime : Runtime) (reason)
    (h : (createSubject runtime).result = .rejected reason) :
    (createSubject runtime).runtime = runtime := by
  cases hissue : LifetimeIssuer.issue runtime.subjectIssuer with
  | exhausted => simp [createSubject, hissue]
  | issued identity issuer =>
      cases hresult : (SubjectLifecycle.create runtime.lifecycle identity).result with
      | accepted => simp [createSubject, hissue, hresult] at h
      | rejected other => simp [createSubject, hissue, hresult]

/-- An issued subject identity is exactly the pre-state counter, is
representable, advances the counter by exactly one, and installs exactly the
accepted internal lifecycle transition. -/
theorem createSubject_issued (runtime : Runtime) (identity : Nat)
    (h : (createSubject runtime).result = .issued identity) :
    identity = runtime.subjectIssuer.next ∧
      LifetimeIssuer.Representable identity ∧
      (createSubject runtime).runtime.subjectIssuer.next =
        runtime.subjectIssuer.next + 1 ∧
      (SubjectLifecycle.create runtime.lifecycle runtime.subjectIssuer.next).result =
        .accepted ∧
      (createSubject runtime).runtime.lifecycle =
        (SubjectLifecycle.create runtime.lifecycle runtime.subjectIssuer.next).state := by
  cases hissue : LifetimeIssuer.issue runtime.subjectIssuer with
  | exhausted => simp [createSubject, hissue] at h
  | issued fresh issuer =>
      obtain ⟨hfresh, hnext, _, _⟩ := LifetimeIssuer.issued_facts hissue
      obtain ⟨hrepresentable, _⟩ := LifetimeIssuer.issued_representable hissue
      subst hfresh
      cases hresult : (SubjectLifecycle.create runtime.lifecycle
          runtime.subjectIssuer.next).result with
      | rejected reason => simp [createSubject, hissue, hresult] at h
      | accepted =>
          have hidentity : identity = runtime.subjectIssuer.next := by
            simpa [createSubject, hissue, hresult] using h.symm
          subst identity
          exact ⟨rfl, hrepresentable, by simp [createSubject, hissue, hresult, hnext],
            rfl, by simp [createSubject, hissue, hresult]⟩

theorem createSubject_object_domain_unchanged (runtime : Runtime) :
    (createSubject runtime).runtime.objectIssuer = runtime.objectIssuer ∧
      (createSubject runtime).runtime.virtualMemory = runtime.virtualMemory ∧
      (createSubject runtime).runtime.mailbox = runtime.mailbox ∧
      (createSubject runtime).runtime.sendHistory = runtime.sendHistory := by
  cases hissue : LifetimeIssuer.issue runtime.subjectIssuer with
  | exhausted => simp [createSubject, hissue]
  | issued identity issuer =>
      cases hresult : (SubjectLifecycle.create runtime.lifecycle identity).result <;>
        simp [createSubject, hissue, hresult]

/-- The typed exhaustion result is decided exactly by the subject issuer. -/
theorem createSubject_exhausted_iff (runtime : Runtime) :
    (createSubject runtime).result = .exhausted ↔
      LifetimeIssuer.exhausted runtime.subjectIssuer = true := by
  constructor
  · intro h
    cases hexhausted : LifetimeIssuer.exhausted runtime.subjectIssuer with
    | true => rfl
    | false =>
        have hissue : LifetimeIssuer.issue runtime.subjectIssuer =
            .issued runtime.subjectIssuer.next { next := runtime.subjectIssuer.next + 1 } := by
          simp [LifetimeIssuer.issue, hexhausted]
        cases hresult : (SubjectLifecycle.create runtime.lifecycle
            runtime.subjectIssuer.next).result <;>
          simp [createSubject, hissue, hresult] at h
  · intro hexhausted
    simp [createSubject, LifetimeIssuer.exhausted_issue _ hexhausted]

theorem allocateMemory_exhausted_unchanged (runtime : Runtime) (subject slot)
    (h : (allocateMemory runtime subject slot).result = .exhausted) :
    (allocateMemory runtime subject slot).runtime = runtime := by
  cases hissue : LifetimeIssuer.issue runtime.objectIssuer with
  | exhausted => simp [allocateMemory, hissue]
  | issued object issuer =>
      cases hresult : (MemoryLifecycle.allocate runtime.virtualMemory.memory object
          subject slot).result with
      | accepted => simp [allocateMemory, hissue, hresult] at h
      | rejected reason => simp [allocateMemory, hissue, hresult]

theorem allocateMemory_rejected_unchanged (runtime : Runtime) (subject slot reason)
    (h : (allocateMemory runtime subject slot).result = .rejected reason) :
    (allocateMemory runtime subject slot).runtime = runtime := by
  cases hissue : LifetimeIssuer.issue runtime.objectIssuer with
  | exhausted => simp [allocateMemory, hissue]
  | issued object issuer =>
      cases hresult : (MemoryLifecycle.allocate runtime.virtualMemory.memory object
          subject slot).result with
      | accepted => simp [allocateMemory, hissue, hresult] at h
      | rejected other => simp [allocateMemory, hissue, hresult]

/-- An issued memory-object identity is exactly the pre-state counter and the
runtime installs exactly the accepted internal allocation. -/
theorem allocateMemory_issued (runtime : Runtime) (subject slot) (object : Nat)
    (h : (allocateMemory runtime subject slot).result = .issued object) :
    object = runtime.objectIssuer.next ∧
      LifetimeIssuer.Representable object ∧
      (allocateMemory runtime subject slot).runtime.objectIssuer.next =
        runtime.objectIssuer.next + 1 ∧
      (MemoryLifecycle.allocate runtime.virtualMemory.memory runtime.objectIssuer.next
        subject slot).result = .accepted ∧
      (allocateMemory runtime subject slot).runtime.virtualMemory.memory =
        (MemoryLifecycle.allocate runtime.virtualMemory.memory runtime.objectIssuer.next
          subject slot).state := by
  cases hissue : LifetimeIssuer.issue runtime.objectIssuer with
  | exhausted => simp [allocateMemory, hissue] at h
  | issued fresh issuer =>
      obtain ⟨hfresh, hnext, _, _⟩ := LifetimeIssuer.issued_facts hissue
      obtain ⟨hrepresentable, _⟩ := LifetimeIssuer.issued_representable hissue
      subst hfresh
      cases hresult : (MemoryLifecycle.allocate runtime.virtualMemory.memory
          runtime.objectIssuer.next subject slot).result with
      | rejected reason => simp [allocateMemory, hissue, hresult] at h
      | accepted =>
          have hobject : object = runtime.objectIssuer.next := by
            simpa [allocateMemory, hissue, hresult] using h.symm
          subst object
          exact ⟨rfl, hrepresentable, by simp [allocateMemory, hissue, hresult, hnext],
            rfl, by simp [allocateMemory, hissue, hresult]⟩

theorem allocateMemory_subject_domain_unchanged (runtime : Runtime) (subject slot) :
    (allocateMemory runtime subject slot).runtime.subjectIssuer = runtime.subjectIssuer ∧
      (allocateMemory runtime subject slot).runtime.lifecycle = runtime.lifecycle := by
  cases hissue : LifetimeIssuer.issue runtime.objectIssuer with
  | exhausted => simp [allocateMemory, hissue]
  | issued object issuer =>
      cases hresult : (MemoryLifecycle.allocate runtime.virtualMemory.memory object
          subject slot).result <;>
        simp [allocateMemory, hissue, hresult]

theorem allocateMemory_exhausted_iff (runtime : Runtime) (subject slot) :
    (allocateMemory runtime subject slot).result = .exhausted ↔
      LifetimeIssuer.exhausted runtime.objectIssuer = true := by
  constructor
  · intro h
    cases hexhausted : LifetimeIssuer.exhausted runtime.objectIssuer with
    | true => rfl
    | false =>
        have hissue : LifetimeIssuer.issue runtime.objectIssuer =
            .issued runtime.objectIssuer.next { next := runtime.objectIssuer.next + 1 } := by
          simp [LifetimeIssuer.issue, hexhausted]
        cases hresult : (MemoryLifecycle.allocate runtime.virtualMemory.memory
            runtime.objectIssuer.next subject slot).result <;>
          simp [allocateMemory, hissue, hresult] at h
  · intro hexhausted
    simp [allocateMemory, LifetimeIssuer.exhausted_issue _ hexhausted]

theorem createEndpoint_exhausted_unchanged (runtime : Runtime) (subject slot)
    (h : (createEndpoint runtime subject slot).result = .exhausted) :
    (createEndpoint runtime subject slot).runtime = runtime := by
  cases hissue : LifetimeIssuer.issue runtime.objectIssuer with
  | exhausted => simp [createEndpoint, hissue]
  | issued object issuer =>
      cases hresult : (EndpointIPC.create runtime.endpoints object subject slot).result with
      | accepted => simp [createEndpoint, hissue, hresult] at h
      | rejected reason => simp [createEndpoint, hissue, hresult]

theorem createEndpoint_rejected_unchanged (runtime : Runtime) (subject slot reason)
    (h : (createEndpoint runtime subject slot).result = .rejected reason) :
    (createEndpoint runtime subject slot).runtime = runtime := by
  cases hissue : LifetimeIssuer.issue runtime.objectIssuer with
  | exhausted => simp [createEndpoint, hissue]
  | issued object issuer =>
      cases hresult : (EndpointIPC.create runtime.endpoints object subject slot).result with
      | accepted => simp [createEndpoint, hissue, hresult] at h
      | rejected other => simp [createEndpoint, hissue, hresult]

/-- An issued endpoint-object identity is exactly the pre-state counter and the
runtime installs exactly the accepted internal endpoint creation. -/
theorem createEndpoint_issued (runtime : Runtime) (subject slot) (object : Nat)
    (h : (createEndpoint runtime subject slot).result = .issued object) :
    object = runtime.objectIssuer.next ∧
      LifetimeIssuer.Representable object ∧
      (createEndpoint runtime subject slot).runtime.objectIssuer.next =
        runtime.objectIssuer.next + 1 ∧
      (EndpointIPC.create runtime.endpoints runtime.objectIssuer.next subject
        slot).result = .accepted ∧
      (createEndpoint runtime subject slot).runtime.endpoints =
        (EndpointIPC.create runtime.endpoints runtime.objectIssuer.next subject
          slot).state := by
  cases hissue : LifetimeIssuer.issue runtime.objectIssuer with
  | exhausted => simp [createEndpoint, hissue] at h
  | issued fresh issuer =>
      obtain ⟨hfresh, hnext, _, _⟩ := LifetimeIssuer.issued_facts hissue
      obtain ⟨hrepresentable, _⟩ := LifetimeIssuer.issued_representable hissue
      subst hfresh
      cases hresult : (EndpointIPC.create runtime.endpoints runtime.objectIssuer.next
          subject slot).result with
      | rejected reason => simp [createEndpoint, hissue, hresult] at h
      | accepted =>
          have hobject : object = runtime.objectIssuer.next := by
            simpa [createEndpoint, hissue, hresult] using h.symm
          subst object
          refine ⟨rfl, hrepresentable, by simp [createEndpoint, hissue, hresult, hnext],
            rfl, ?_⟩
          simp only [createEndpoint, hissue, hresult]
          exact installEndpoints_endpoints runtime _

theorem createEndpoint_subject_domain_unchanged (runtime : Runtime) (subject slot) :
    (createEndpoint runtime subject slot).runtime.subjectIssuer = runtime.subjectIssuer ∧
      (createEndpoint runtime subject slot).runtime.lifecycle = runtime.lifecycle := by
  cases hissue : LifetimeIssuer.issue runtime.objectIssuer with
  | exhausted => simp [createEndpoint, hissue]
  | issued object issuer =>
      cases hresult : (EndpointIPC.create runtime.endpoints object subject slot).result <;>
        simp [createEndpoint, hissue, hresult, installEndpoints]

/-- Identity exhaustion and capability-generation exhaustion remain separate
resources with distinct typed results at the endpoint-creation boundary. -/
theorem createEndpoint_exhausted_iff (runtime : Runtime) (subject slot) :
    (createEndpoint runtime subject slot).result = .exhausted ↔
      LifetimeIssuer.exhausted runtime.objectIssuer = true := by
  constructor
  · intro h
    cases hexhausted : LifetimeIssuer.exhausted runtime.objectIssuer with
    | true => rfl
    | false =>
        have hissue : LifetimeIssuer.issue runtime.objectIssuer =
            .issued runtime.objectIssuer.next { next := runtime.objectIssuer.next + 1 } := by
          simp [LifetimeIssuer.issue, hexhausted]
        cases hresult : (EndpointIPC.create runtime.endpoints runtime.objectIssuer.next
            subject slot).result <;>
          simp [createEndpoint, hissue, hresult] at h
  · intro hexhausted
    simp [createEndpoint, LifetimeIssuer.exhausted_issue _ hexhausted]

theorem createAddressSpace_exhausted_unchanged (runtime : Runtime) (subject slot)
    (h : (createAddressSpace runtime subject slot).result = .exhausted) :
    (createAddressSpace runtime subject slot).runtime = runtime := by
  cases hissue : LifetimeIssuer.issue runtime.objectIssuer with
  | exhausted => simp [createAddressSpace, hissue]
  | issued addressSpace issuer =>
      cases hresult : (VirtualMapping.createAddressSpace runtime.virtualMemory addressSpace
          subject slot).result with
      | accepted => simp [createAddressSpace, hissue, hresult] at h
      | rejected reason => simp [createAddressSpace, hissue, hresult]

theorem createAddressSpace_rejected_unchanged (runtime : Runtime) (subject slot reason)
    (h : (createAddressSpace runtime subject slot).result = .rejected reason) :
    (createAddressSpace runtime subject slot).runtime = runtime := by
  cases hissue : LifetimeIssuer.issue runtime.objectIssuer with
  | exhausted => simp [createAddressSpace, hissue]
  | issued addressSpace issuer =>
      cases hresult : (VirtualMapping.createAddressSpace runtime.virtualMemory addressSpace
          subject slot).result with
      | accepted => simp [createAddressSpace, hissue, hresult] at h
      | rejected other => simp [createAddressSpace, hissue, hresult]

/-- An issued address-space identity is exactly the pre-state counter and the
runtime installs exactly the accepted internal address-space creation. -/
theorem createAddressSpace_issued (runtime : Runtime) (subject slot) (addressSpace : Nat)
    (h : (createAddressSpace runtime subject slot).result = .issued addressSpace) :
    addressSpace = runtime.objectIssuer.next ∧
      LifetimeIssuer.Representable addressSpace ∧
      (createAddressSpace runtime subject slot).runtime.objectIssuer.next =
        runtime.objectIssuer.next + 1 ∧
      (VirtualMapping.createAddressSpace runtime.virtualMemory
        runtime.objectIssuer.next subject slot).result = .accepted ∧
      (createAddressSpace runtime subject slot).runtime.virtualMemory =
        (VirtualMapping.createAddressSpace runtime.virtualMemory
          runtime.objectIssuer.next subject slot).state := by
  cases hissue : LifetimeIssuer.issue runtime.objectIssuer with
  | exhausted => simp [createAddressSpace, hissue] at h
  | issued fresh issuer =>
      obtain ⟨hfresh, hnext, _, _⟩ := LifetimeIssuer.issued_facts hissue
      obtain ⟨hrepresentable, _⟩ := LifetimeIssuer.issued_representable hissue
      subst hfresh
      cases hresult : (VirtualMapping.createAddressSpace runtime.virtualMemory
          runtime.objectIssuer.next subject slot).result with
      | rejected reason => simp [createAddressSpace, hissue, hresult] at h
      | accepted =>
          have hspace : addressSpace = runtime.objectIssuer.next := by
            simpa [createAddressSpace, hissue, hresult] using h.symm
          subst addressSpace
          exact ⟨rfl, hrepresentable,
            by simp [createAddressSpace, hissue, hresult, hnext], rfl,
            by simp [createAddressSpace, hissue, hresult]⟩

theorem createAddressSpace_subject_domain_unchanged (runtime : Runtime) (subject slot) :
    (createAddressSpace runtime subject slot).runtime.subjectIssuer =
        runtime.subjectIssuer ∧
      (createAddressSpace runtime subject slot).runtime.lifecycle = runtime.lifecycle := by
  cases hissue : LifetimeIssuer.issue runtime.objectIssuer with
  | exhausted => simp [createAddressSpace, hissue]
  | issued addressSpace issuer =>
      cases hresult : (VirtualMapping.createAddressSpace runtime.virtualMemory addressSpace
          subject slot).result <;>
        simp [createAddressSpace, hissue, hresult]

theorem createAddressSpace_exhausted_iff (runtime : Runtime) (subject slot) :
    (createAddressSpace runtime subject slot).result = .exhausted ↔
      LifetimeIssuer.exhausted runtime.objectIssuer = true := by
  constructor
  · intro h
    cases hexhausted : LifetimeIssuer.exhausted runtime.objectIssuer with
    | true => rfl
    | false =>
        have hissue : LifetimeIssuer.issue runtime.objectIssuer =
            .issued runtime.objectIssuer.next { next := runtime.objectIssuer.next + 1 } := by
          simp [LifetimeIssuer.issue, hexhausted]
        cases hresult : (VirtualMapping.createAddressSpace runtime.virtualMemory
            runtime.objectIssuer.next subject slot).result <;>
          simp [createAddressSpace, hissue, hresult] at h
  · intro hexhausted
    simp [createAddressSpace, LifetimeIssuer.exhausted_issue _ hexhausted]

/-! ## Cleanup never touches an issuer -/

theorem terminateSubject_issuers_unchanged (runtime : Runtime) (subject) :
    (terminateSubject runtime subject).1.subjectIssuer = runtime.subjectIssuer ∧
      (terminateSubject runtime subject).1.objectIssuer = runtime.objectIssuer := by
  exact ⟨rfl, rfl⟩

theorem releaseMemory_issuers_unchanged (runtime : Runtime) (subject slot) :
    (releaseMemory runtime subject slot).1.subjectIssuer = runtime.subjectIssuer ∧
      (releaseMemory runtime subject slot).1.objectIssuer = runtime.objectIssuer := by
  exact ⟨rfl, rfl⟩

theorem destroyEndpoint_issuers_unchanged (runtime : Runtime) (subject slot) :
    (destroyEndpoint runtime subject slot).1.subjectIssuer = runtime.subjectIssuer ∧
      (destroyEndpoint runtime subject slot).1.objectIssuer = runtime.objectIssuer := by
  exact ⟨rfl, rfl⟩

theorem destroyAddressSpace_issuers_unchanged (runtime : Runtime) (subject slot) :
    (destroyAddressSpace runtime subject slot).1.subjectIssuer = runtime.subjectIssuer ∧
      (destroyAddressSpace runtime subject slot).1.objectIssuer = runtime.objectIssuer := by
  exact ⟨rfl, rfl⟩

/-- Cleanup and termination leave both append-only histories intact. -/
theorem terminateSubject_history_preserved (runtime : Runtime) (subject candidate) :
    (terminateSubject runtime subject).1.lifecycle.issuedSubjects candidate =
        runtime.lifecycle.issuedSubjects candidate ∧
      issuedObject (terminateSubject runtime subject).1 candidate =
        issuedObject runtime candidate := by
  refine ⟨?_, rfl⟩
  have := (subject_terminate_registry runtime.lifecycle subject).1
  simp [terminateSubject, this]

theorem releaseMemory_history_preserved (runtime : Runtime) (subject slot candidate) :
    issuedObject (releaseMemory runtime subject slot).1 candidate =
      issuedObject runtime candidate := by
  obtain ⟨hmemory, haddress⟩ := virtual_release_projections runtime.virtualMemory subject slot
  obtain ⟨hissued, _, _⟩ := memory_release_registry runtime.virtualMemory.memory subject slot
  simp [issuedObject, releaseMemory, hmemory, haddress, hissued]

theorem destroyEndpoint_history_preserved (runtime : Runtime) (subject slot candidate) :
    issuedObject (destroyEndpoint runtime subject slot).1 candidate =
      issuedObject runtime candidate := by
  obtain ⟨hissued, haddress, _, _⟩ := endpoint_destroy_registry runtime.endpoints subject slot
  simp only [issuedObject, destroyEndpoint, installEndpoints]
  rw [hissued, haddress]
  rfl

theorem destroyAddressSpace_history_preserved (runtime : Runtime) (subject slot candidate) :
    issuedObject (destroyAddressSpace runtime subject slot).1 candidate =
      issuedObject runtime candidate := by
  obtain ⟨hissued, haddress, _, _⟩ :=
    address_space_destroy_registry runtime.virtualMemory subject slot
  simp [issuedObject, destroyAddressSpace, hissued, haddress]

/-! ## Runtime invariant: counter/history agreement

Every live or historically issued identity is representable and strictly below
its domain counter, live lifetimes and kind registrations are recorded in the
single object history, and both counters stay inside the bounded domain.
-/

def Invariant (runtime : Runtime) : Prop :=
  (∀ subject, runtime.lifecycle.issuedSubjects subject = true →
    0 < subject ∧ subject < runtime.subjectIssuer.next) ∧
  (∀ subject, runtime.lifecycle.capabilities.subjects subject = true →
    runtime.lifecycle.issuedSubjects subject = true) ∧
  (∀ object, issuedObject runtime object = true →
    0 < object ∧ object < runtime.objectIssuer.next) ∧
  (∀ object, runtime.virtualMemory.memory.capabilities.objects object = true →
    issuedObject runtime object = true) ∧
  (∀ object kind, runtime.virtualMemory.memory.capabilities.kinds object = some kind →
    issuedObject runtime object = true) ∧
  runtime.subjectIssuer.next ≤ LifetimeIssuer.identityReserved ∧
  runtime.objectIssuer.next ≤ LifetimeIssuer.identityReserved

/-- The next candidate subject identity is never in history and never live. -/
theorem invariant_fresh_subject (runtime : Runtime) (hinv : Invariant runtime) :
    runtime.lifecycle.issuedSubjects runtime.subjectIssuer.next = false ∧
      runtime.lifecycle.capabilities.subjects runtime.subjectIssuer.next = false := by
  have hunissued : runtime.lifecycle.issuedSubjects runtime.subjectIssuer.next = false := by
    cases h : runtime.lifecycle.issuedSubjects runtime.subjectIssuer.next with
    | true => exact absurd (hinv.1 _ h).2 (Nat.lt_irrefl _)
    | false => rfl
  refine ⟨hunissued, ?_⟩
  cases h : runtime.lifecycle.capabilities.subjects runtime.subjectIssuer.next with
  | true => exact absurd (hinv.2.1 _ h) (by simp [hunissued])
  | false => rfl

/-- The next candidate object identity is never in either history view and
never live under any kind. -/
theorem invariant_fresh_object (runtime : Runtime) (hinv : Invariant runtime) :
    runtime.virtualMemory.memory.issued runtime.objectIssuer.next = false ∧
      runtime.virtualMemory.issuedAddressSpace runtime.objectIssuer.next = false ∧
      runtime.virtualMemory.memory.capabilities.objects runtime.objectIssuer.next =
        false := by
  have hunissued : issuedObject runtime runtime.objectIssuer.next = false := by
    cases h : issuedObject runtime runtime.objectIssuer.next with
    | true => exact absurd (hinv.2.2.1 _ h).2 (Nat.lt_irrefl _)
    | false => rfl
  have hviews := hunissued
  simp only [issuedObject, Bool.or_eq_false_iff] at hviews
  refine ⟨hviews.1, hviews.2, ?_⟩
  cases h : runtime.virtualMemory.memory.capabilities.objects runtime.objectIssuer.next with
  | true => exact absurd (hinv.2.2.2.1 _ h) (by simp [hunissued])
  | false => rfl

/-! ## Total, deterministic issuance under the invariant -/

/-- Subject creation is decided exactly by the issuer: exhaustion fails closed
and a live issuer always issues exactly the next representable identity. -/
theorem createSubject_total (runtime : Runtime) (hinv : Invariant runtime) :
    (LifetimeIssuer.exhausted runtime.subjectIssuer = true →
      (createSubject runtime).result = .exhausted) ∧
    (LifetimeIssuer.exhausted runtime.subjectIssuer = false →
      (createSubject runtime).result = .issued runtime.subjectIssuer.next) := by
  constructor
  · intro hexhausted
    exact (createSubject_exhausted_iff runtime).mpr hexhausted
  · intro hlive
    have hissue : LifetimeIssuer.issue runtime.subjectIssuer =
        .issued runtime.subjectIssuer.next { next := runtime.subjectIssuer.next + 1 } := by
      simp [LifetimeIssuer.issue, hlive]
    obtain ⟨hunissued, hdead⟩ := invariant_fresh_subject runtime hinv
    simp [createSubject, hissue, SubjectLifecycle.create, hunissued, hdead]

/-- The reused internal allocation can reject a caller identity as already
issued only when the history says so; under the invariant the issuer's fresh
identity can therefore never be rejected as a replay. -/
theorem memory_allocate_already_issued_reason (memory : MemoryLifecycle.State)
    (object : ObjectId) (subject : SubjectId) (slot : SlotId)
    (h : (MemoryLifecycle.allocate memory object subject slot).result =
      .rejected .objectAlreadyIssued) :
    memory.issued object = true := by
  simp only [MemoryLifecycle.allocate] at h
  split at h <;> simp_all [MemoryLifecycle.reject]
  split at h <;> simp_all [MemoryLifecycle.reject]
  split at h <;> simp_all [MemoryLifecycle.reject]
  split at h <;> simp_all [MemoryLifecycle.reject]
  split at h <;> simp_all [MemoryLifecycle.reject]
  split at h <;> simp_all [MemoryLifecycle.reject]

theorem endpoint_create_already_issued_reason (state : EndpointIPC.State)
    (object : ObjectId) (subject : SubjectId) (slot : SlotId)
    (h : (EndpointIPC.create state object subject slot).result =
      .rejected .objectAlreadyIssued) :
    (state.issued object || state.issuedAddressSpace object) = true := by
  simp only [EndpointIPC.create] at h
  split at h <;> simp_all [EndpointIPC.reject]
  split at h <;> simp_all [EndpointIPC.reject]
  split at h <;> simp_all [EndpointIPC.reject]
  split at h <;> simp_all [EndpointIPC.reject]
  split at h <;> simp_all [EndpointIPC.reject]
  split at h <;> simp_all [EndpointIPC.reject]
  split at h <;> simp_all [EndpointIPC.reject]

theorem endpoint_create_in_use_reason (state : EndpointIPC.State)
    (object : ObjectId) (subject : SubjectId) (slot : SlotId)
    (h : (EndpointIPC.create state object subject slot).result = .rejected .objectInUse) :
    state.capabilities.objects object = true := by
  simp only [EndpointIPC.create] at h
  split at h <;> simp_all [EndpointIPC.reject]
  split at h <;> simp_all [EndpointIPC.reject]
  split at h <;> simp_all [EndpointIPC.reject]
  split at h <;> simp_all [EndpointIPC.reject]
  split at h <;> simp_all [EndpointIPC.reject]
  split at h <;> simp_all [EndpointIPC.reject]
  split at h <;> simp_all [EndpointIPC.reject]

theorem address_space_create_already_issued_reason (state : VirtualMapping.State)
    (addressSpace : ObjectId) (subject : SubjectId) (slot : SlotId)
    (h : (VirtualMapping.createAddressSpace state addressSpace subject slot).result =
      .rejected .identifierAlreadyIssued) :
    (state.issuedAddressSpace addressSpace || state.memory.issued addressSpace) = true := by
  simp only [VirtualMapping.createAddressSpace] at h
  split at h <;> simp_all [VirtualMapping.reject]
  split at h <;> simp_all [VirtualMapping.reject]
  split at h <;> simp_all [VirtualMapping.reject]
  split at h <;> simp_all [VirtualMapping.reject]
  split at h <;> simp_all [VirtualMapping.reject]
  split at h <;> simp_all [VirtualMapping.reject]

theorem address_space_create_live_reason (state : VirtualMapping.State)
    (addressSpace : ObjectId) (subject : SubjectId) (slot : SlotId)
    (h : (VirtualMapping.createAddressSpace state addressSpace subject slot).result =
      .rejected .identifierLive) :
    state.memory.capabilities.objects addressSpace = true := by
  simp only [VirtualMapping.createAddressSpace] at h
  split at h <;> simp_all [VirtualMapping.reject]
  split at h <;> simp_all [VirtualMapping.reject]
  split at h <;> simp_all [VirtualMapping.reject]
  split at h <;> simp_all [VirtualMapping.reject]
  split at h <;> simp_all [VirtualMapping.reject]
  split at h <;> simp_all [VirtualMapping.reject]

/-- Every composite rejection reproduces an internal rejection of exactly the
issuer's candidate identity. -/
theorem allocateMemory_rejected_reason (runtime : Runtime) (subject slot reason)
    (h : (allocateMemory runtime subject slot).result = .rejected reason) :
    (MemoryLifecycle.allocate runtime.virtualMemory.memory runtime.objectIssuer.next
      subject slot).result = .rejected reason := by
  cases hissue : LifetimeIssuer.issue runtime.objectIssuer with
  | exhausted => simp [allocateMemory, hissue] at h
  | issued fresh issuer =>
      obtain ⟨hfresh, _, _, _⟩ := LifetimeIssuer.issued_facts hissue
      subst hfresh
      cases hresult : (MemoryLifecycle.allocate runtime.virtualMemory.memory
          runtime.objectIssuer.next subject slot).result with
      | accepted => simp [allocateMemory, hissue, hresult] at h
      | rejected other =>
          have : reason = other := by
            simpa [allocateMemory, hissue, hresult] using h.symm
          subst this
          rfl

theorem createEndpoint_rejected_reason (runtime : Runtime) (subject slot reason)
    (h : (createEndpoint runtime subject slot).result = .rejected reason) :
    (EndpointIPC.create runtime.endpoints runtime.objectIssuer.next subject slot).result =
      .rejected reason := by
  cases hissue : LifetimeIssuer.issue runtime.objectIssuer with
  | exhausted => simp [createEndpoint, hissue] at h
  | issued fresh issuer =>
      obtain ⟨hfresh, _, _, _⟩ := LifetimeIssuer.issued_facts hissue
      subst hfresh
      cases hresult : (EndpointIPC.create runtime.endpoints runtime.objectIssuer.next
          subject slot).result with
      | accepted => simp [createEndpoint, hissue, hresult] at h
      | rejected other =>
          have : reason = other := by
            simpa [createEndpoint, hissue, hresult] using h.symm
          subst this
          rfl

theorem createAddressSpace_rejected_reason (runtime : Runtime) (subject slot reason)
    (h : (createAddressSpace runtime subject slot).result = .rejected reason) :
    (VirtualMapping.createAddressSpace runtime.virtualMemory runtime.objectIssuer.next
      subject slot).result = .rejected reason := by
  cases hissue : LifetimeIssuer.issue runtime.objectIssuer with
  | exhausted => simp [createAddressSpace, hissue] at h
  | issued fresh issuer =>
      obtain ⟨hfresh, _, _, _⟩ := LifetimeIssuer.issued_facts hissue
      subst hfresh
      cases hresult : (VirtualMapping.createAddressSpace runtime.virtualMemory
          runtime.objectIssuer.next subject slot).result with
      | accepted => simp [createAddressSpace, hissue, hresult] at h
      | rejected other =>
          have : reason = other := by
            simpa [createAddressSpace, hissue, hresult] using h.symm
          subst this
          rfl

/-- Under the invariant, no composite creation can be rejected as a replayed
or still-live identity: the issuer's candidate is always genuinely fresh. -/
theorem allocateMemory_never_replays (runtime : Runtime) (subject slot)
    (hinv : Invariant runtime) :
    (allocateMemory runtime subject slot).result ≠ .rejected .objectAlreadyIssued := by
  intro h
  have hguard := memory_allocate_already_issued_reason _ _ _ _
    (allocateMemory_rejected_reason runtime subject slot _ h)
  have hfresh := (invariant_fresh_object runtime hinv).1
  simp [hfresh] at hguard

theorem createEndpoint_never_replays (runtime : Runtime) (subject slot)
    (hinv : Invariant runtime) :
    (createEndpoint runtime subject slot).result ≠ .rejected .objectAlreadyIssued ∧
      (createEndpoint runtime subject slot).result ≠ .rejected .objectInUse := by
  obtain ⟨hissued, haddress, hdead⟩ := invariant_fresh_object runtime hinv
  constructor
  · intro h
    have hguard := endpoint_create_already_issued_reason _ _ _ _
      (createEndpoint_rejected_reason runtime subject slot _ h)
    rw [endpoints_issued, endpoints_issuedAddressSpace] at hguard
    simp [hissued, haddress] at hguard
  · intro h
    have hguard := endpoint_create_in_use_reason _ _ _ _
      (createEndpoint_rejected_reason runtime subject slot _ h)
    rw [endpoints_capabilities] at hguard
    simp [hdead] at hguard

theorem createAddressSpace_never_replays (runtime : Runtime) (subject slot)
    (hinv : Invariant runtime) :
    (createAddressSpace runtime subject slot).result ≠
        .rejected .identifierAlreadyIssued ∧
      (createAddressSpace runtime subject slot).result ≠ .rejected .identifierLive := by
  obtain ⟨hissued, haddress, hdead⟩ := invariant_fresh_object runtime hinv
  constructor
  · intro h
    have hguard := address_space_create_already_issued_reason _ _ _ _
      (createAddressSpace_rejected_reason runtime subject slot _ h)
    simp [hissued, haddress] at hguard
  · intro h
    have hguard := address_space_create_live_reason _ _ _ _
      (createAddressSpace_rejected_reason runtime subject slot _ h)
    simp [hdead] at hguard

theorem allocateMemory_address_history_unchanged (runtime : Runtime) (subject slot) :
    (allocateMemory runtime subject slot).runtime.virtualMemory.issuedAddressSpace =
      runtime.virtualMemory.issuedAddressSpace := by
  cases hissue : LifetimeIssuer.issue runtime.objectIssuer with
  | exhausted => simp [allocateMemory, hissue]
  | issued object issuer =>
      cases hresult : (MemoryLifecycle.allocate runtime.virtualMemory.memory object
          subject slot).result <;>
        simp [allocateMemory, hissue, hresult]

theorem createEndpoint_issued_projections (runtime : Runtime) (subject slot object)
    (h : (createEndpoint runtime subject slot).result = .issued object) :
    (createEndpoint runtime subject slot).runtime.virtualMemory.memory =
        (EndpointIPC.create runtime.endpoints runtime.objectIssuer.next subject
          slot).state.toState ∧
      (createEndpoint runtime subject slot).runtime.virtualMemory.issuedAddressSpace =
        (EndpointIPC.create runtime.endpoints runtime.objectIssuer.next subject
          slot).state.issuedAddressSpace := by
  cases hissue : LifetimeIssuer.issue runtime.objectIssuer with
  | exhausted => simp [createEndpoint, hissue] at h
  | issued fresh issuer =>
      obtain ⟨hfresh, _, _, _⟩ := LifetimeIssuer.issued_facts hissue
      subst hfresh
      cases hresult : (EndpointIPC.create runtime.endpoints runtime.objectIssuer.next
          subject slot).result with
      | rejected reason => simp [createEndpoint, hissue, hresult] at h
      | accepted => simp [createEndpoint, hissue, hresult, installEndpoints]

/-! ## Invariant preservation

Every creation, cleanup, and ordinary operation preserves counter/history
agreement, so the invariant holds along every finite composite trace.
-/

theorem createSubject_preserves_invariant (runtime : Runtime) (hinv : Invariant runtime) :
    Invariant (createSubject runtime).runtime := by
  cases hresult : (createSubject runtime).result with
  | exhausted => rw [createSubject_exhausted_unchanged runtime hresult]; exact hinv
  | rejected reason =>
      rw [createSubject_rejected_unchanged runtime reason hresult]; exact hinv
  | issued identity =>
      obtain ⟨hidentity, hrepresentable, hnext, haccepted, hlifecycle⟩ :=
        createSubject_issued runtime identity hresult
      subst hidentity
      obtain ⟨hissuedmap, hsubjectsmap⟩ :=
        subject_create_accepted_registry runtime.lifecycle runtime.subjectIssuer.next
          haccepted
      obtain ⟨hobjIssuer, hvm, _, _⟩ := createSubject_object_domain_unchanged runtime
      rcases hinv with ⟨hsubBound, hsubLive, hobjBound, hobjLive, hkinds, hsubMax, hobjMax⟩
      have hio : ∀ object, issuedObject (createSubject runtime).runtime object =
          issuedObject runtime object := by
        intro object
        simp [issuedObject, hvm]
      have hpositive : 0 < runtime.subjectIssuer.next := hrepresentable.1
      have hbound : runtime.subjectIssuer.next < LifetimeIssuer.identityReserved :=
        hrepresentable.2
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro s hs
        rw [hlifecycle, hissuedmap] at hs
        rw [hnext]
        by_cases heq : s = runtime.subjectIssuer.next
        · subst s
          exact ⟨hpositive, Nat.lt_succ_self _⟩
        · simp [SubjectLifecycle.setBool, heq] at hs
          exact ⟨(hsubBound s hs).1, Nat.lt_succ_of_lt (hsubBound s hs).2⟩
      · intro s hs
        rw [hlifecycle, hsubjectsmap] at hs
        rw [hlifecycle, hissuedmap]
        by_cases heq : s = runtime.subjectIssuer.next
        · subst s
          simp [SubjectLifecycle.setBool]
        · simp [SubjectLifecycle.setBool, heq] at hs ⊢
          exact hsubLive s hs
      · intro object hobject
        rw [hio] at hobject
        rw [hobjIssuer]
        exact hobjBound object hobject
      · intro object hobject
        rw [hvm] at hobject
        rw [hio]
        exact hobjLive object hobject
      · intro object kind hkind
        rw [hvm] at hkind
        rw [hio]
        exact hkinds object kind hkind
      · rw [hnext]
        omega
      · rw [hobjIssuer]
        exact hobjMax

theorem allocateMemory_preserves_invariant (runtime : Runtime) (subject slot)
    (hinv : Invariant runtime) :
    Invariant (allocateMemory runtime subject slot).runtime := by
  cases hresult : (allocateMemory runtime subject slot).result with
  | exhausted =>
      rw [allocateMemory_exhausted_unchanged runtime subject slot hresult]; exact hinv
  | rejected reason =>
      rw [allocateMemory_rejected_unchanged runtime subject slot reason hresult]; exact hinv
  | issued object =>
      obtain ⟨hobject, hrepresentable, hnext, haccepted, hmemory⟩ :=
        allocateMemory_issued runtime subject slot object hresult
      subst hobject
      obtain ⟨hissuedmap, hobjectsmap, hkindsmap⟩ :=
        memory_allocate_accepted_registry runtime.virtualMemory.memory
          runtime.objectIssuer.next subject slot haccepted
      obtain ⟨hsubIssuer, hlifecycle⟩ :=
        allocateMemory_subject_domain_unchanged runtime subject slot
      have haddress := allocateMemory_address_history_unchanged runtime subject slot
      rcases hinv with ⟨hsubBound, hsubLive, hobjBound, hobjLive, hkinds, hsubMax, hobjMax⟩
      have hpositive : 0 < runtime.objectIssuer.next := hrepresentable.1
      have hbound : runtime.objectIssuer.next < LifetimeIssuer.identityReserved :=
        hrepresentable.2
      have hio : ∀ candidate, issuedObject (allocateMemory runtime subject slot).runtime
          candidate =
          (MemoryLifecycle.setIssued runtime.virtualMemory.memory.issued
              runtime.objectIssuer.next candidate ||
            runtime.virtualMemory.issuedAddressSpace candidate) := by
        intro candidate
        simp [issuedObject, hmemory, haddress, hissuedmap]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro s hs
        rw [hlifecycle] at hs
        rw [hsubIssuer]
        exact hsubBound s hs
      · intro s hs
        rw [hlifecycle] at hs ⊢
        exact hsubLive s hs
      · intro candidate hcandidate
        rw [hio] at hcandidate
        rw [hnext]
        by_cases heq : candidate = runtime.objectIssuer.next
        · subst candidate
          exact ⟨hpositive, Nat.lt_succ_self _⟩
        · simp [MemoryLifecycle.setIssued, heq] at hcandidate
          have hold := hobjBound candidate (by simpa [issuedObject] using hcandidate)
          exact ⟨hold.1, Nat.lt_succ_of_lt hold.2⟩
      · intro candidate hcandidate
        rw [hmemory, hobjectsmap] at hcandidate
        rw [hio]
        by_cases heq : candidate = runtime.objectIssuer.next
        · subst candidate
          simp [MemoryLifecycle.setIssued]
        · simp [MemoryLifecycle.setObject, heq] at hcandidate
          simp [MemoryLifecycle.setIssued, heq]
          simpa [issuedObject] using hobjLive candidate hcandidate
      · intro candidate kind hkind
        rw [hmemory, hkindsmap] at hkind
        rw [hio]
        by_cases heq : candidate = runtime.objectIssuer.next
        · subst candidate
          simp [MemoryLifecycle.setIssued]
        · simp [heq] at hkind
          simp [MemoryLifecycle.setIssued, heq]
          simpa [issuedObject] using hkinds candidate kind hkind
      · rw [hsubIssuer]
        exact hsubMax
      · rw [hnext]
        omega

theorem createEndpoint_preserves_invariant (runtime : Runtime) (subject slot)
    (hinv : Invariant runtime) :
    Invariant (createEndpoint runtime subject slot).runtime := by
  cases hresult : (createEndpoint runtime subject slot).result with
  | exhausted =>
      rw [createEndpoint_exhausted_unchanged runtime subject slot hresult]; exact hinv
  | rejected reason =>
      rw [createEndpoint_rejected_unchanged runtime subject slot reason hresult]; exact hinv
  | issued object =>
      obtain ⟨hobject, hrepresentable, hnext, haccepted, _⟩ :=
        createEndpoint_issued runtime subject slot object hresult
      subst hobject
      obtain ⟨hmemory, haddress⟩ :=
        createEndpoint_issued_projections runtime subject slot _ hresult
      obtain ⟨hissuedmap, haddressmap, hobjectsmap, hkindsmap⟩ :=
        endpoint_create_accepted_registry runtime.endpoints runtime.objectIssuer.next
          subject slot haccepted
      obtain ⟨hsubIssuer, hlifecycle⟩ :=
        createEndpoint_subject_domain_unchanged runtime subject slot
      rcases hinv with ⟨hsubBound, hsubLive, hobjBound, hobjLive, hkinds, hsubMax, hobjMax⟩
      have hpositive : 0 < runtime.objectIssuer.next := hrepresentable.1
      have hbound : runtime.objectIssuer.next < LifetimeIssuer.identityReserved :=
        hrepresentable.2
      have hio : ∀ candidate, issuedObject (createEndpoint runtime subject slot).runtime
          candidate =
          (EndpointIPC.setBool runtime.virtualMemory.memory.issued
              runtime.objectIssuer.next true candidate ||
            runtime.virtualMemory.issuedAddressSpace candidate) := by
        intro candidate
        simp only [issuedObject]
        rw [hmemory, haddress, hissuedmap, haddressmap]
        rfl
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro s hs
        rw [hlifecycle] at hs
        rw [hsubIssuer]
        exact hsubBound s hs
      · intro s hs
        rw [hlifecycle] at hs ⊢
        exact hsubLive s hs
      · intro candidate hcandidate
        rw [hio] at hcandidate
        rw [hnext]
        by_cases heq : candidate = runtime.objectIssuer.next
        · subst candidate
          exact ⟨hpositive, Nat.lt_succ_self _⟩
        · simp [EndpointIPC.setBool, heq] at hcandidate
          have hold := hobjBound candidate (by simpa [issuedObject] using hcandidate)
          exact ⟨hold.1, Nat.lt_succ_of_lt hold.2⟩
      · intro candidate hcandidate
        rw [hmemory, hobjectsmap] at hcandidate
        rw [hio]
        by_cases heq : candidate = runtime.objectIssuer.next
        · subst candidate
          simp [EndpointIPC.setBool]
        · simp [EndpointIPC.setBool, heq] at hcandidate ⊢
          simpa [issuedObject] using hobjLive candidate hcandidate
      · intro candidate kind hkind
        rw [hmemory, hkindsmap] at hkind
        rw [hio]
        by_cases heq : candidate = runtime.objectIssuer.next
        · subst candidate
          simp [EndpointIPC.setBool]
        · simp [heq] at hkind
          simp [EndpointIPC.setBool, heq]
          simpa [issuedObject] using hkinds candidate kind hkind
      · rw [hsubIssuer]
        exact hsubMax
      · rw [hnext]
        omega

theorem createAddressSpace_preserves_invariant (runtime : Runtime) (subject slot)
    (hinv : Invariant runtime) :
    Invariant (createAddressSpace runtime subject slot).runtime := by
  cases hresult : (createAddressSpace runtime subject slot).result with
  | exhausted =>
      rw [createAddressSpace_exhausted_unchanged runtime subject slot hresult]; exact hinv
  | rejected reason =>
      rw [createAddressSpace_rejected_unchanged runtime subject slot reason hresult]
      exact hinv
  | issued addressSpace =>
      obtain ⟨hspace, hrepresentable, hnext, haccepted, hvm⟩ :=
        createAddressSpace_issued runtime subject slot addressSpace hresult
      subst hspace
      obtain ⟨hissuedmap, haddressmap, hobjectsmap, hkindsmap⟩ :=
        address_space_create_accepted_registry runtime.virtualMemory
          runtime.objectIssuer.next subject slot haccepted
      obtain ⟨hsubIssuer, hlifecycle⟩ :=
        createAddressSpace_subject_domain_unchanged runtime subject slot
      rcases hinv with ⟨hsubBound, hsubLive, hobjBound, hobjLive, hkinds, hsubMax, hobjMax⟩
      have hpositive : 0 < runtime.objectIssuer.next := hrepresentable.1
      have hbound : runtime.objectIssuer.next < LifetimeIssuer.identityReserved :=
        hrepresentable.2
      have hio : ∀ candidate,
          issuedObject (createAddressSpace runtime subject slot).runtime candidate =
          (MemoryLifecycle.setIssued runtime.virtualMemory.memory.issued
              runtime.objectIssuer.next candidate ||
            VirtualMapping.setIssuedAddressSpace runtime.virtualMemory.issuedAddressSpace
              runtime.objectIssuer.next candidate) := by
        intro candidate
        simp [issuedObject, hvm, hissuedmap, haddressmap]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro s hs
        rw [hlifecycle] at hs
        rw [hsubIssuer]
        exact hsubBound s hs
      · intro s hs
        rw [hlifecycle] at hs ⊢
        exact hsubLive s hs
      · intro candidate hcandidate
        rw [hio] at hcandidate
        rw [hnext]
        by_cases heq : candidate = runtime.objectIssuer.next
        · subst candidate
          exact ⟨hpositive, Nat.lt_succ_self _⟩
        · simp [MemoryLifecycle.setIssued, VirtualMapping.setIssuedAddressSpace, heq]
            at hcandidate
          have hold := hobjBound candidate (by simpa [issuedObject] using hcandidate)
          exact ⟨hold.1, Nat.lt_succ_of_lt hold.2⟩
      · intro candidate hcandidate
        rw [hvm, hobjectsmap] at hcandidate
        rw [hio]
        by_cases heq : candidate = runtime.objectIssuer.next
        · subst candidate
          simp [MemoryLifecycle.setIssued]
        · simp [MemoryLifecycle.setObject, heq] at hcandidate
          simp [MemoryLifecycle.setIssued, VirtualMapping.setIssuedAddressSpace, heq]
          simpa [issuedObject] using hobjLive candidate hcandidate
      · intro candidate kind hkind
        rw [hvm, hkindsmap] at hkind
        rw [hio]
        by_cases heq : candidate = runtime.objectIssuer.next
        · subst candidate
          simp [MemoryLifecycle.setIssued]
        · simp [heq] at hkind
          simp [MemoryLifecycle.setIssued, VirtualMapping.setIssuedAddressSpace, heq]
          simpa [issuedObject] using hkinds candidate kind hkind
      · rw [hsubIssuer]
        exact hsubMax
      · rw [hnext]
        omega

theorem terminateSubject_preserves_invariant (runtime : Runtime) (subject)
    (hinv : Invariant runtime) :
    Invariant (terminateSubject runtime subject).1 := by
  obtain ⟨hissued, hsubjects⟩ := subject_terminate_registry runtime.lifecycle subject
  rcases hinv with ⟨hsubBound, hsubLive, hobjBound, hobjLive, hkinds, hsubMax, hobjMax⟩
  refine ⟨?_, ?_, hobjBound, hobjLive, hkinds, hsubMax, hobjMax⟩
  · intro s hs
    rw [show (terminateSubject runtime subject).1.lifecycle =
      (SubjectLifecycle.terminate runtime.lifecycle subject).state from rfl, hissued] at hs
    exact hsubBound s hs
  · intro s hs
    rw [show (terminateSubject runtime subject).1.lifecycle =
      (SubjectLifecycle.terminate runtime.lifecycle subject).state from rfl] at hs
    rw [show (terminateSubject runtime subject).1.lifecycle =
      (SubjectLifecycle.terminate runtime.lifecycle subject).state from rfl, hissued]
    exact hsubLive s (hsubjects s hs)

theorem releaseMemory_preserves_invariant (runtime : Runtime) (subject slot)
    (hinv : Invariant runtime) :
    Invariant (releaseMemory runtime subject slot).1 := by
  obtain ⟨hmemory, haddress⟩ := virtual_release_projections runtime.virtualMemory subject slot
  obtain ⟨hissued, hobjects, hkindsShrink⟩ :=
    memory_release_registry runtime.virtualMemory.memory subject slot
  rcases hinv with ⟨hsubBound, hsubLive, hobjBound, hobjLive, hkinds, hsubMax, hobjMax⟩
  have hio := releaseMemory_history_preserved runtime subject slot
  refine ⟨hsubBound, hsubLive, ?_, ?_, ?_, hsubMax, hobjMax⟩
  · intro candidate hcandidate
    rw [hio] at hcandidate
    exact hobjBound candidate hcandidate
  · intro candidate hcandidate
    rw [show (releaseMemory runtime subject slot).1.virtualMemory.memory =
      (VirtualMapping.release runtime.virtualMemory subject slot).state.memory from rfl,
      hmemory] at hcandidate
    rw [hio]
    exact hobjLive candidate (hobjects candidate hcandidate)
  · intro candidate kind hkind
    rw [show (releaseMemory runtime subject slot).1.virtualMemory.memory =
      (VirtualMapping.release runtime.virtualMemory subject slot).state.memory from rfl,
      hmemory] at hkind
    rw [hio]
    exact hkinds candidate kind (hkindsShrink candidate kind hkind)

theorem destroyEndpoint_preserves_invariant (runtime : Runtime) (subject slot)
    (hinv : Invariant runtime) :
    Invariant (destroyEndpoint runtime subject slot).1 := by
  obtain ⟨hissued, haddress, hobjects, hkindsShrink⟩ :=
    endpoint_destroy_registry runtime.endpoints subject slot
  rcases hinv with ⟨hsubBound, hsubLive, hobjBound, hobjLive, hkinds, hsubMax, hobjMax⟩
  have hio := destroyEndpoint_history_preserved runtime subject slot
  refine ⟨hsubBound, hsubLive, ?_, ?_, ?_, hsubMax, hobjMax⟩
  · intro candidate hcandidate
    rw [hio] at hcandidate
    exact hobjBound candidate hcandidate
  · intro candidate hcandidate
    rw [hio]
    have hold : runtime.endpoints.capabilities.objects candidate = true :=
      hobjects candidate hcandidate
    exact hobjLive candidate (by simpa [Runtime.endpoints] using hold)
  · intro candidate kind hkind
    rw [hio]
    have hold : runtime.endpoints.capabilities.kinds candidate = some kind :=
      hkindsShrink candidate kind hkind
    exact hkinds candidate kind (by simpa [Runtime.endpoints] using hold)

theorem destroyAddressSpace_preserves_invariant (runtime : Runtime) (subject slot)
    (hinv : Invariant runtime) :
    Invariant (destroyAddressSpace runtime subject slot).1 := by
  obtain ⟨hissued, haddress, hobjects, hkindsShrink⟩ :=
    address_space_destroy_registry runtime.virtualMemory subject slot
  rcases hinv with ⟨hsubBound, hsubLive, hobjBound, hobjLive, hkinds, hsubMax, hobjMax⟩
  have hio := destroyAddressSpace_history_preserved runtime subject slot
  refine ⟨hsubBound, hsubLive, ?_, ?_, ?_, hsubMax, hobjMax⟩
  · intro candidate hcandidate
    rw [hio] at hcandidate
    exact hobjBound candidate hcandidate
  · intro candidate hcandidate
    rw [hio]
    exact hobjLive candidate (hobjects candidate hcandidate)
  · intro candidate kind hkind
    rw [hio]
    exact hkinds candidate kind (hkindsShrink candidate kind hkind)

theorem send_preserves_invariant (runtime : Runtime) (caller slot payload)
    (hinv : Invariant runtime) :
    Invariant (send runtime caller slot payload).1 := by
  obtain ⟨hmemory, haddress⟩ := send_registry runtime.endpoints caller slot payload
  have hmemory' : (send runtime caller slot payload).1.virtualMemory.memory =
      runtime.virtualMemory.memory := hmemory
  have haddress' : (send runtime caller slot payload).1.virtualMemory.issuedAddressSpace =
      runtime.virtualMemory.issuedAddressSpace := haddress
  rcases hinv with ⟨hsubBound, hsubLive, hobjBound, hobjLive, hkinds, hsubMax, hobjMax⟩
  have hio : ∀ object, issuedObject (send runtime caller slot payload).1 object =
      issuedObject runtime object := by
    intro object
    simp [issuedObject, hmemory', haddress']
  refine ⟨hsubBound, hsubLive, ?_, ?_, ?_, hsubMax, hobjMax⟩
  · intro candidate hcandidate
    rw [hio] at hcandidate
    exact hobjBound candidate hcandidate
  · intro candidate hcandidate
    rw [hmemory'] at hcandidate
    rw [hio]
    exact hobjLive candidate hcandidate
  · intro candidate kind hkind
    rw [hmemory'] at hkind
    rw [hio]
    exact hkinds candidate kind hkind

theorem receive_preserves_invariant (runtime : Runtime) (caller slot)
    (hinv : Invariant runtime) :
    Invariant (receive runtime caller slot).1 := by
  obtain ⟨hmemory, haddress⟩ := receive_registry runtime.endpoints caller slot
  have hmemory' : (receive runtime caller slot).1.virtualMemory.memory =
      runtime.virtualMemory.memory := hmemory
  have haddress' : (receive runtime caller slot).1.virtualMemory.issuedAddressSpace =
      runtime.virtualMemory.issuedAddressSpace := haddress
  rcases hinv with ⟨hsubBound, hsubLive, hobjBound, hobjLive, hkinds, hsubMax, hobjMax⟩
  have hio : ∀ object, issuedObject (receive runtime caller slot).1 object =
      issuedObject runtime object := by
    intro object
    simp [issuedObject, hmemory', haddress']
  refine ⟨hsubBound, hsubLive, ?_, ?_, ?_, hsubMax, hobjMax⟩
  · intro candidate hcandidate
    rw [hio] at hcandidate
    exact hobjBound candidate hcandidate
  · intro candidate hcandidate
    rw [hmemory'] at hcandidate
    rw [hio]
    exact hobjLive candidate hcandidate
  · intro candidate kind hkind
    rw [hmemory'] at hkind
    rw [hio]
    exact hkinds candidate kind hkind

/-! ## Composite operation traces -/

inductive Operation where
  | createSubject
  | terminateSubject (subject : SubjectId)
  | allocateMemory (subject : SubjectId) (slot : SlotId)
  | releaseMemory (subject : SubjectId) (slot : SlotId)
  | createEndpoint (subject : SubjectId) (slot : SlotId)
  | destroyEndpoint (subject : SubjectId) (slot : SlotId)
  | createAddressSpace (subject : SubjectId) (slot : SlotId)
  | destroyAddressSpace (subject : SubjectId) (slot : SlotId)
  | send (caller : SubjectId) (slot : SlotId) (payload : EndpointIPC.Payload)
  | receive (caller : SubjectId) (slot : SlotId)
  deriving DecidableEq, Repr

def applyOperation (runtime : Runtime) : Operation → Runtime
  | .createSubject => (createSubject runtime).runtime
  | .terminateSubject subject => (terminateSubject runtime subject).1
  | .allocateMemory subject slot => (allocateMemory runtime subject slot).runtime
  | .releaseMemory subject slot => (releaseMemory runtime subject slot).1
  | .createEndpoint subject slot => (createEndpoint runtime subject slot).runtime
  | .destroyEndpoint subject slot => (destroyEndpoint runtime subject slot).1
  | .createAddressSpace subject slot => (createAddressSpace runtime subject slot).runtime
  | .destroyAddressSpace subject slot => (destroyAddressSpace runtime subject slot).1
  | .send caller slot payload => (send runtime caller slot payload).1
  | .receive caller slot => (receive runtime caller slot).1

def runOperations (runtime : Runtime) : List Operation → Runtime
  | [] => runtime
  | operation :: rest => runOperations (applyOperation runtime operation) rest

theorem applyOperation_preserves_invariant (runtime : Runtime) (operation : Operation)
    (hinv : Invariant runtime) : Invariant (applyOperation runtime operation) := by
  cases operation with
  | createSubject => exact createSubject_preserves_invariant runtime hinv
  | terminateSubject subject =>
      exact terminateSubject_preserves_invariant runtime subject hinv
  | allocateMemory subject slot =>
      exact allocateMemory_preserves_invariant runtime subject slot hinv
  | releaseMemory subject slot =>
      exact releaseMemory_preserves_invariant runtime subject slot hinv
  | createEndpoint subject slot =>
      exact createEndpoint_preserves_invariant runtime subject slot hinv
  | destroyEndpoint subject slot =>
      exact destroyEndpoint_preserves_invariant runtime subject slot hinv
  | createAddressSpace subject slot =>
      exact createAddressSpace_preserves_invariant runtime subject slot hinv
  | destroyAddressSpace subject slot =>
      exact destroyAddressSpace_preserves_invariant runtime subject slot hinv
  | send caller slot payload =>
      exact send_preserves_invariant runtime caller slot payload hinv
  | receive caller slot => exact receive_preserves_invariant runtime caller slot hinv

theorem runOperations_preserves_invariant (runtime : Runtime)
    (operations : List Operation) (hinv : Invariant runtime) :
    Invariant (runOperations runtime operations) := by
  induction operations generalizing runtime with
  | nil => exact hinv
  | cons operation rest ih =>
      exact ih _ (applyOperation_preserves_invariant runtime operation hinv)

/-- One composite step only grows the histories and the counters. -/
theorem applyOperation_history_monotone (runtime : Runtime) (operation : Operation) :
    (∀ subject, runtime.lifecycle.issuedSubjects subject = true →
      (applyOperation runtime operation).lifecycle.issuedSubjects subject = true) ∧
    (∀ object, issuedObject runtime object = true →
      issuedObject (applyOperation runtime operation) object = true) ∧
    runtime.subjectIssuer.next ≤ (applyOperation runtime operation).subjectIssuer.next ∧
    runtime.objectIssuer.next ≤ (applyOperation runtime operation).objectIssuer.next := by
  cases operation with
  | createSubject =>
      simp only [applyOperation]
      cases hresult : (createSubject runtime).result with
      | exhausted =>
          rw [createSubject_exhausted_unchanged runtime hresult]
          exact ⟨fun _ h => h, fun _ h => h, Nat.le_refl _, Nat.le_refl _⟩
      | rejected reason =>
          rw [createSubject_rejected_unchanged runtime reason hresult]
          exact ⟨fun _ h => h, fun _ h => h, Nat.le_refl _, Nat.le_refl _⟩
      | issued identity =>
          obtain ⟨hidentity, _, hnext, haccepted, hlifecycle⟩ :=
            createSubject_issued runtime identity hresult
          obtain ⟨hissuedmap, _⟩ :=
            subject_create_accepted_registry runtime.lifecycle runtime.subjectIssuer.next
              haccepted
          obtain ⟨hobjIssuer, hvm, _, _⟩ := createSubject_object_domain_unchanged runtime
          refine ⟨?_, ?_, ?_, ?_⟩
          · intro s hs
            rw [hlifecycle, hissuedmap]
            by_cases heq : s = runtime.subjectIssuer.next
            · subst s
              simp [SubjectLifecycle.setBool]
            · simpa [SubjectLifecycle.setBool, heq] using hs
          · intro o ho
            simpa [issuedObject, hvm] using ho
          · rw [hnext]
            omega
          · simp [hobjIssuer]
  | terminateSubject subject =>
      simp only [applyOperation]
      obtain ⟨hissued, _⟩ := subject_terminate_registry runtime.lifecycle subject
      refine ⟨?_, fun _ h => h, Nat.le_refl _, Nat.le_refl _⟩
      intro s hs
      rw [show (terminateSubject runtime subject).1.lifecycle =
        (SubjectLifecycle.terminate runtime.lifecycle subject).state from rfl, hissued]
      exact hs
  | allocateMemory subject slot =>
      simp only [applyOperation]
      obtain ⟨hsubIssuer, hlifecycle⟩ :=
        allocateMemory_subject_domain_unchanged runtime subject slot
      cases hresult : (allocateMemory runtime subject slot).result with
      | exhausted =>
          rw [allocateMemory_exhausted_unchanged runtime subject slot hresult]
          exact ⟨fun _ h => h, fun _ h => h, Nat.le_refl _, Nat.le_refl _⟩
      | rejected reason =>
          rw [allocateMemory_rejected_unchanged runtime subject slot reason hresult]
          exact ⟨fun _ h => h, fun _ h => h, Nat.le_refl _, Nat.le_refl _⟩
      | issued object =>
          obtain ⟨hobject, _, hnext, haccepted, hmemory⟩ :=
            allocateMemory_issued runtime subject slot object hresult
          obtain ⟨hissuedmap, _, _⟩ :=
            memory_allocate_accepted_registry runtime.virtualMemory.memory
              runtime.objectIssuer.next subject slot haccepted
          have haddress := allocateMemory_address_history_unchanged runtime subject slot
          refine ⟨?_, ?_, ?_, ?_⟩
          · intro s hs
            rw [hlifecycle]
            exact hs
          · intro o ho
            simp only [issuedObject] at ho ⊢
            rw [hmemory, hissuedmap, haddress]
            by_cases heq : o = runtime.objectIssuer.next
            · subst o
              simp [MemoryLifecycle.setIssued]
            · simpa [MemoryLifecycle.setIssued, heq] using ho
          · simp [hsubIssuer]
          · rw [hnext]
            omega
  | releaseMemory subject slot =>
      simp only [applyOperation]
      refine ⟨fun _ h => h, ?_, Nat.le_refl _, Nat.le_refl _⟩
      intro o ho
      rw [releaseMemory_history_preserved runtime subject slot o]
      exact ho
  | createEndpoint subject slot =>
      simp only [applyOperation]
      obtain ⟨hsubIssuer, hlifecycle⟩ :=
        createEndpoint_subject_domain_unchanged runtime subject slot
      cases hresult : (createEndpoint runtime subject slot).result with
      | exhausted =>
          rw [createEndpoint_exhausted_unchanged runtime subject slot hresult]
          exact ⟨fun _ h => h, fun _ h => h, Nat.le_refl _, Nat.le_refl _⟩
      | rejected reason =>
          rw [createEndpoint_rejected_unchanged runtime subject slot reason hresult]
          exact ⟨fun _ h => h, fun _ h => h, Nat.le_refl _, Nat.le_refl _⟩
      | issued object =>
          obtain ⟨hobject, _, hnext, haccepted, _⟩ :=
            createEndpoint_issued runtime subject slot object hresult
          obtain ⟨hmemory, haddress⟩ :=
            createEndpoint_issued_projections runtime subject slot object hresult
          obtain ⟨hissuedmap, haddressmap, _, _⟩ :=
            endpoint_create_accepted_registry runtime.endpoints runtime.objectIssuer.next
              subject slot haccepted
          refine ⟨?_, ?_, ?_, ?_⟩
          · intro s hs
            rw [hlifecycle]
            exact hs
          · intro o ho
            simp only [issuedObject] at ho ⊢
            rw [hmemory, haddress, hissuedmap, haddressmap]
            by_cases heq : o = runtime.objectIssuer.next
            · subst o
              simp [EndpointIPC.setBool]
            · have ho' : (runtime.endpoints.issued o ||
                  runtime.endpoints.issuedAddressSpace o) = true := ho
              simp only [EndpointIPC.setBool]
              rw [if_neg heq]
              exact ho'
          · simp [hsubIssuer]
          · rw [hnext]
            omega
  | destroyEndpoint subject slot =>
      simp only [applyOperation]
      refine ⟨fun _ h => h, ?_, Nat.le_refl _, Nat.le_refl _⟩
      intro o ho
      rw [destroyEndpoint_history_preserved runtime subject slot o]
      exact ho
  | createAddressSpace subject slot =>
      simp only [applyOperation]
      obtain ⟨hsubIssuer, hlifecycle⟩ :=
        createAddressSpace_subject_domain_unchanged runtime subject slot
      cases hresult : (createAddressSpace runtime subject slot).result with
      | exhausted =>
          rw [createAddressSpace_exhausted_unchanged runtime subject slot hresult]
          exact ⟨fun _ h => h, fun _ h => h, Nat.le_refl _, Nat.le_refl _⟩
      | rejected reason =>
          rw [createAddressSpace_rejected_unchanged runtime subject slot reason hresult]
          exact ⟨fun _ h => h, fun _ h => h, Nat.le_refl _, Nat.le_refl _⟩
      | issued addressSpace =>
          obtain ⟨hspace, _, hnext, haccepted, hvm⟩ :=
            createAddressSpace_issued runtime subject slot addressSpace hresult
          obtain ⟨hissuedmap, haddressmap, _, _⟩ :=
            address_space_create_accepted_registry runtime.virtualMemory
              runtime.objectIssuer.next subject slot haccepted
          refine ⟨?_, ?_, ?_, ?_⟩
          · intro s hs
            rw [hlifecycle]
            exact hs
          · intro o ho
            simp only [issuedObject] at ho ⊢
            rw [hvm, hissuedmap, haddressmap]
            by_cases heq : o = runtime.objectIssuer.next
            · subst o
              simp [MemoryLifecycle.setIssued]
            · simpa [MemoryLifecycle.setIssued,
                VirtualMapping.setIssuedAddressSpace, heq] using ho
          · simp [hsubIssuer]
          · rw [hnext]
            omega
  | destroyAddressSpace subject slot =>
      simp only [applyOperation]
      refine ⟨fun _ h => h, ?_, Nat.le_refl _, Nat.le_refl _⟩
      intro o ho
      rw [destroyAddressSpace_history_preserved runtime subject slot o]
      exact ho
  | send caller slot payload =>
      simp only [applyOperation]
      obtain ⟨hmemory, haddress⟩ := send_registry runtime.endpoints caller slot payload
      have hmemory' : (send runtime caller slot payload).1.virtualMemory.memory =
          runtime.virtualMemory.memory := hmemory
      have haddress' :
          (send runtime caller slot payload).1.virtualMemory.issuedAddressSpace =
            runtime.virtualMemory.issuedAddressSpace := haddress
      refine ⟨fun _ h => h, ?_, Nat.le_refl _, Nat.le_refl _⟩
      intro o ho
      simpa [issuedObject, hmemory', haddress'] using ho
  | receive caller slot =>
      simp only [applyOperation]
      obtain ⟨hmemory, haddress⟩ := receive_registry runtime.endpoints caller slot
      have hmemory' : (receive runtime caller slot).1.virtualMemory.memory =
          runtime.virtualMemory.memory := hmemory
      have haddress' : (receive runtime caller slot).1.virtualMemory.issuedAddressSpace =
          runtime.virtualMemory.issuedAddressSpace := haddress
      refine ⟨fun _ h => h, ?_, Nat.le_refl _, Nat.le_refl _⟩
      intro o ho
      simpa [issuedObject, hmemory', haddress'] using ho

theorem runOperations_history_monotone (runtime : Runtime) (operations : List Operation) :
    (∀ subject, runtime.lifecycle.issuedSubjects subject = true →
      (runOperations runtime operations).lifecycle.issuedSubjects subject = true) ∧
    ∀ object, issuedObject runtime object = true →
      issuedObject (runOperations runtime operations) object = true := by
  induction operations generalizing runtime with
  | nil => exact ⟨fun _ h => h, fun _ h => h⟩
  | cons operation rest ih =>
      obtain ⟨hsub, hobj, _, _⟩ := applyOperation_history_monotone runtime operation
      obtain ⟨ihsub, ihobj⟩ := ih (applyOperation runtime operation)
      exact ⟨fun s hs => ihsub s (hsub s hs), fun o ho => ihobj o (hobj o ho)⟩

/-- Stale-lifetime safety, object domain, single step: a retired issued object
can never be made live again by any composite operation. -/
theorem applyOperation_dead_object_stays_dead (runtime : Runtime)
    (operation : Operation) (object : ObjectId) (hinv : Invariant runtime)
    (hissued : issuedObject runtime object = true)
    (hdead : runtime.virtualMemory.memory.capabilities.objects object = false) :
    (applyOperation runtime operation).virtualMemory.memory.capabilities.objects object =
      false := by
  have hbound : object < runtime.objectIssuer.next := (hinv.2.2.1 object hissued).2
  have hne : object ≠ runtime.objectIssuer.next := Nat.ne_of_lt hbound
  cases operation with
  | createSubject =>
      simp only [applyOperation]
      obtain ⟨_, hvm, _, _⟩ := createSubject_object_domain_unchanged runtime
      rw [hvm]
      exact hdead
  | terminateSubject subject => exact hdead
  | allocateMemory subject slot =>
      simp only [applyOperation]
      cases hresult : (allocateMemory runtime subject slot).result with
      | exhausted =>
          rw [allocateMemory_exhausted_unchanged runtime subject slot hresult]
          exact hdead
      | rejected reason =>
          rw [allocateMemory_rejected_unchanged runtime subject slot reason hresult]
          exact hdead
      | issued fresh =>
          obtain ⟨_, _, _, haccepted, hmemory⟩ :=
            allocateMemory_issued runtime subject slot fresh hresult
          obtain ⟨_, hobjectsmap, _⟩ :=
            memory_allocate_accepted_registry runtime.virtualMemory.memory
              runtime.objectIssuer.next subject slot haccepted
          rw [hmemory, hobjectsmap]
          simpa [MemoryLifecycle.setObject, hne] using hdead
  | releaseMemory subject slot =>
      simp only [applyOperation]
      obtain ⟨hmemory, _⟩ := virtual_release_projections runtime.virtualMemory subject slot
      obtain ⟨_, hobjects, _⟩ :=
        memory_release_registry runtime.virtualMemory.memory subject slot
      rw [show (releaseMemory runtime subject slot).1.virtualMemory.memory =
        (VirtualMapping.release runtime.virtualMemory subject slot).state.memory from rfl,
        hmemory]
      cases hvalue : (MemoryLifecycle.release runtime.virtualMemory.memory subject
          slot).state.capabilities.objects object with
      | false => rfl
      | true => exact absurd (hobjects object hvalue) (by simp [hdead])
  | createEndpoint subject slot =>
      simp only [applyOperation]
      cases hresult : (createEndpoint runtime subject slot).result with
      | exhausted =>
          rw [createEndpoint_exhausted_unchanged runtime subject slot hresult]
          exact hdead
      | rejected reason =>
          rw [createEndpoint_rejected_unchanged runtime subject slot reason hresult]
          exact hdead
      | issued fresh =>
          obtain ⟨_, _, _, haccepted, _⟩ :=
            createEndpoint_issued runtime subject slot fresh hresult
          obtain ⟨hmemory, _⟩ :=
            createEndpoint_issued_projections runtime subject slot fresh hresult
          obtain ⟨_, _, hobjectsmap, _⟩ :=
            endpoint_create_accepted_registry runtime.endpoints runtime.objectIssuer.next
              subject slot haccepted
          have hdead' : runtime.endpoints.capabilities.objects object = false := hdead
          rw [hmemory, hobjectsmap]
          simpa [EndpointIPC.setBool, hne] using hdead'
  | destroyEndpoint subject slot =>
      simp only [applyOperation]
      obtain ⟨_, _, hobjects, _⟩ := endpoint_destroy_registry runtime.endpoints subject slot
      have hdead' : runtime.endpoints.capabilities.objects object = false := hdead
      cases hvalue : (EndpointIPC.destroy runtime.endpoints subject
          slot).state.capabilities.objects object with
      | false => exact hvalue
      | true => exact absurd (hobjects object hvalue) (by simp [hdead'])
  | createAddressSpace subject slot =>
      simp only [applyOperation]
      cases hresult : (createAddressSpace runtime subject slot).result with
      | exhausted =>
          rw [createAddressSpace_exhausted_unchanged runtime subject slot hresult]
          exact hdead
      | rejected reason =>
          rw [createAddressSpace_rejected_unchanged runtime subject slot reason hresult]
          exact hdead
      | issued fresh =>
          obtain ⟨_, _, _, haccepted, hvm⟩ :=
            createAddressSpace_issued runtime subject slot fresh hresult
          obtain ⟨_, _, hobjectsmap, _⟩ :=
            address_space_create_accepted_registry runtime.virtualMemory
              runtime.objectIssuer.next subject slot haccepted
          rw [hvm, hobjectsmap]
          simpa [MemoryLifecycle.setObject, hne] using hdead
  | destroyAddressSpace subject slot =>
      simp only [applyOperation]
      obtain ⟨_, _, hobjects, _⟩ :=
        address_space_destroy_registry runtime.virtualMemory subject slot
      cases hvalue : (VirtualMapping.destroyAddressSpace runtime.virtualMemory subject
          slot).state.memory.capabilities.objects object with
      | false => exact hvalue
      | true => exact absurd (hobjects object hvalue) (by simp [hdead])
  | send caller slot payload =>
      simp only [applyOperation]
      obtain ⟨hmemory, _⟩ := send_registry runtime.endpoints caller slot payload
      have hmemory' : (send runtime caller slot payload).1.virtualMemory.memory =
          runtime.virtualMemory.memory := hmemory
      rw [hmemory']
      exact hdead
  | receive caller slot =>
      simp only [applyOperation]
      obtain ⟨hmemory, _⟩ := receive_registry runtime.endpoints caller slot
      have hmemory' : (receive runtime caller slot).1.virtualMemory.memory =
          runtime.virtualMemory.memory := hmemory
      rw [hmemory']
      exact hdead

/-- Stale-lifetime safety, subject domain, single step. -/
theorem applyOperation_dead_subject_stays_dead (runtime : Runtime)
    (operation : Operation) (subject : SubjectId) (hinv : Invariant runtime)
    (hissued : runtime.lifecycle.issuedSubjects subject = true)
    (hdead : runtime.lifecycle.capabilities.subjects subject = false) :
    (applyOperation runtime operation).lifecycle.capabilities.subjects subject = false := by
  have hbound : subject < runtime.subjectIssuer.next := (hinv.1 subject hissued).2
  have hne : subject ≠ runtime.subjectIssuer.next := Nat.ne_of_lt hbound
  cases operation with
  | createSubject =>
      simp only [applyOperation]
      cases hresult : (createSubject runtime).result with
      | exhausted =>
          rw [createSubject_exhausted_unchanged runtime hresult]
          exact hdead
      | rejected reason =>
          rw [createSubject_rejected_unchanged runtime reason hresult]
          exact hdead
      | issued identity =>
          obtain ⟨_, _, _, haccepted, hlifecycle⟩ :=
            createSubject_issued runtime identity hresult
          obtain ⟨_, hsubjectsmap⟩ :=
            subject_create_accepted_registry runtime.lifecycle runtime.subjectIssuer.next
              haccepted
          rw [hlifecycle, hsubjectsmap]
          simpa [SubjectLifecycle.setBool, hne] using hdead
  | terminateSubject other =>
      simp only [applyOperation]
      obtain ⟨_, hsubjects⟩ := subject_terminate_registry runtime.lifecycle other
      rw [show (terminateSubject runtime other).1.lifecycle =
        (SubjectLifecycle.terminate runtime.lifecycle other).state from rfl]
      cases hvalue : (SubjectLifecycle.terminate runtime.lifecycle
          other).state.capabilities.subjects subject with
      | false => rfl
      | true => exact absurd (hsubjects subject hvalue) (by simp [hdead])
  | allocateMemory other slot =>
      rw [show (applyOperation runtime (.allocateMemory other slot)).lifecycle =
        (allocateMemory runtime other slot).runtime.lifecycle from rfl,
        (allocateMemory_subject_domain_unchanged runtime other slot).2]
      exact hdead
  | releaseMemory other slot => exact hdead
  | createEndpoint other slot =>
      rw [show (applyOperation runtime (.createEndpoint other slot)).lifecycle =
        (createEndpoint runtime other slot).runtime.lifecycle from rfl,
        (createEndpoint_subject_domain_unchanged runtime other slot).2]
      exact hdead
  | destroyEndpoint other slot => exact hdead
  | createAddressSpace other slot =>
      rw [show (applyOperation runtime (.createAddressSpace other slot)).lifecycle =
        (createAddressSpace runtime other slot).runtime.lifecycle from rfl,
        (createAddressSpace_subject_domain_unchanged runtime other slot).2]
      exact hdead
  | destroyAddressSpace other slot => exact hdead
  | send caller slot payload => exact hdead
  | receive caller slot => exact hdead

/-- Object kinds are immutable while live and can only be retired: no step can
rebind an issued identity's kind. -/
theorem applyOperation_kind_stable (runtime : Runtime) (operation : Operation)
    (object : ObjectId) (kind : Capability.ObjectKind) (hinv : Invariant runtime)
    (hkind : runtime.virtualMemory.memory.capabilities.kinds object = some kind) :
    (applyOperation runtime operation).virtualMemory.memory.capabilities.kinds object =
        some kind ∨
      (applyOperation runtime operation).virtualMemory.memory.capabilities.kinds object =
        none := by
  have hissued : issuedObject runtime object = true := hinv.2.2.2.2.1 object kind hkind
  have hbound : object < runtime.objectIssuer.next := (hinv.2.2.1 object hissued).2
  have hne : object ≠ runtime.objectIssuer.next := Nat.ne_of_lt hbound
  cases operation with
  | createSubject =>
      simp only [applyOperation]
      obtain ⟨_, hvm, _, _⟩ := createSubject_object_domain_unchanged runtime
      rw [hvm]
      exact Or.inl hkind
  | terminateSubject subject => exact Or.inl hkind
  | allocateMemory subject slot =>
      simp only [applyOperation]
      cases hresult : (allocateMemory runtime subject slot).result with
      | exhausted =>
          rw [allocateMemory_exhausted_unchanged runtime subject slot hresult]
          exact Or.inl hkind
      | rejected reason =>
          rw [allocateMemory_rejected_unchanged runtime subject slot reason hresult]
          exact Or.inl hkind
      | issued fresh =>
          obtain ⟨_, _, _, haccepted, hmemory⟩ :=
            allocateMemory_issued runtime subject slot fresh hresult
          obtain ⟨_, _, hkindsmap⟩ :=
            memory_allocate_accepted_registry runtime.virtualMemory.memory
              runtime.objectIssuer.next subject slot haccepted
          rw [hmemory, hkindsmap]
          simp only [hne, if_false]
          exact Or.inl hkind
  | releaseMemory subject slot =>
      simp only [applyOperation]
      obtain ⟨hmemory, _⟩ := virtual_release_projections runtime.virtualMemory subject slot
      obtain ⟨_, _, hkinds⟩ :=
        memory_release_registry runtime.virtualMemory.memory subject slot
      rw [show (releaseMemory runtime subject slot).1.virtualMemory.memory =
        (VirtualMapping.release runtime.virtualMemory subject slot).state.memory from rfl,
        hmemory]
      cases hvalue : (MemoryLifecycle.release runtime.virtualMemory.memory subject
          slot).state.capabilities.kinds object with
      | none => exact Or.inr rfl
      | some found =>
          have := hkinds object found hvalue
          rw [hkind] at this
          exact Or.inl (by rw [Option.some.inj this])
  | createEndpoint subject slot =>
      simp only [applyOperation]
      cases hresult : (createEndpoint runtime subject slot).result with
      | exhausted =>
          rw [createEndpoint_exhausted_unchanged runtime subject slot hresult]
          exact Or.inl hkind
      | rejected reason =>
          rw [createEndpoint_rejected_unchanged runtime subject slot reason hresult]
          exact Or.inl hkind
      | issued fresh =>
          obtain ⟨_, _, _, haccepted, _⟩ :=
            createEndpoint_issued runtime subject slot fresh hresult
          obtain ⟨hmemory, _⟩ :=
            createEndpoint_issued_projections runtime subject slot fresh hresult
          obtain ⟨_, _, _, hkindsmap⟩ :=
            endpoint_create_accepted_registry runtime.endpoints runtime.objectIssuer.next
              subject slot haccepted
          rw [hmemory, hkindsmap]
          simp only [hne, if_false]
          exact Or.inl hkind
  | destroyEndpoint subject slot =>
      simp only [applyOperation]
      obtain ⟨_, _, _, hkinds⟩ := endpoint_destroy_registry runtime.endpoints subject slot
      have hkind' : runtime.endpoints.capabilities.kinds object = some kind := hkind
      cases hvalue : (EndpointIPC.destroy runtime.endpoints subject
          slot).state.capabilities.kinds object with
      | none => exact Or.inr hvalue
      | some found =>
          have hfound := hkinds object found hvalue
          rw [hkind'] at hfound
          exact Or.inl (hvalue.trans (by rw [Option.some.inj hfound]))
  | createAddressSpace subject slot =>
      simp only [applyOperation]
      cases hresult : (createAddressSpace runtime subject slot).result with
      | exhausted =>
          rw [createAddressSpace_exhausted_unchanged runtime subject slot hresult]
          exact Or.inl hkind
      | rejected reason =>
          rw [createAddressSpace_rejected_unchanged runtime subject slot reason hresult]
          exact Or.inl hkind
      | issued fresh =>
          obtain ⟨_, _, _, haccepted, hvm⟩ :=
            createAddressSpace_issued runtime subject slot fresh hresult
          obtain ⟨_, _, _, hkindsmap⟩ :=
            address_space_create_accepted_registry runtime.virtualMemory
              runtime.objectIssuer.next subject slot haccepted
          rw [hvm, hkindsmap]
          simp only [hne, if_false]
          exact Or.inl hkind
  | destroyAddressSpace subject slot =>
      simp only [applyOperation]
      obtain ⟨_, _, _, hkinds⟩ :=
        address_space_destroy_registry runtime.virtualMemory subject slot
      cases hvalue : (VirtualMapping.destroyAddressSpace runtime.virtualMemory subject
          slot).state.memory.capabilities.kinds object with
      | none => exact Or.inr hvalue
      | some found =>
          have hfound := hkinds object found hvalue
          rw [hkind] at hfound
          exact Or.inl (hvalue.trans (by rw [Option.some.inj hfound]))
  | send caller slot payload =>
      simp only [applyOperation]
      obtain ⟨hmemory, _⟩ := send_registry runtime.endpoints caller slot payload
      have hmemory' : (send runtime caller slot payload).1.virtualMemory.memory =
          runtime.virtualMemory.memory := hmemory
      rw [hmemory']
      exact Or.inl hkind
  | receive caller slot =>
      simp only [applyOperation]
      obtain ⟨hmemory, _⟩ := receive_registry runtime.endpoints caller slot
      have hmemory' : (receive runtime caller slot).1.virtualMemory.memory =
          runtime.virtualMemory.memory := hmemory
      rw [hmemory']
      exact Or.inl hkind

/-- A retired (kind-erased) issued identity never regains any kind entry. -/
theorem applyOperation_none_kind_stays (runtime : Runtime) (operation : Operation)
    (object : ObjectId) (hinv : Invariant runtime)
    (hissued : issuedObject runtime object = true)
    (hnone : runtime.virtualMemory.memory.capabilities.kinds object = none) :
    (applyOperation runtime operation).virtualMemory.memory.capabilities.kinds object =
      none := by
  have hbound : object < runtime.objectIssuer.next := (hinv.2.2.1 object hissued).2
  have hne : object ≠ runtime.objectIssuer.next := Nat.ne_of_lt hbound
  cases operation with
  | createSubject =>
      simp only [applyOperation]
      obtain ⟨_, hvm, _, _⟩ := createSubject_object_domain_unchanged runtime
      rw [hvm]
      exact hnone
  | terminateSubject subject => exact hnone
  | allocateMemory subject slot =>
      simp only [applyOperation]
      cases hresult : (allocateMemory runtime subject slot).result with
      | exhausted =>
          rw [allocateMemory_exhausted_unchanged runtime subject slot hresult]
          exact hnone
      | rejected reason =>
          rw [allocateMemory_rejected_unchanged runtime subject slot reason hresult]
          exact hnone
      | issued fresh =>
          obtain ⟨_, _, _, haccepted, hmemory⟩ :=
            allocateMemory_issued runtime subject slot fresh hresult
          obtain ⟨_, _, hkindsmap⟩ :=
            memory_allocate_accepted_registry runtime.virtualMemory.memory
              runtime.objectIssuer.next subject slot haccepted
          rw [hmemory, hkindsmap]
          simp only [hne, if_false]
          exact hnone
  | releaseMemory subject slot =>
      simp only [applyOperation]
      obtain ⟨hmemory, _⟩ := virtual_release_projections runtime.virtualMemory subject slot
      obtain ⟨_, _, hkinds⟩ :=
        memory_release_registry runtime.virtualMemory.memory subject slot
      rw [show (releaseMemory runtime subject slot).1.virtualMemory.memory =
        (VirtualMapping.release runtime.virtualMemory subject slot).state.memory from rfl,
        hmemory]
      cases hvalue : (MemoryLifecycle.release runtime.virtualMemory.memory subject
          slot).state.capabilities.kinds object with
      | none => rfl
      | some found =>
          have := hkinds object found hvalue
          rw [hnone] at this
          cases this
  | createEndpoint subject slot =>
      simp only [applyOperation]
      cases hresult : (createEndpoint runtime subject slot).result with
      | exhausted =>
          rw [createEndpoint_exhausted_unchanged runtime subject slot hresult]
          exact hnone
      | rejected reason =>
          rw [createEndpoint_rejected_unchanged runtime subject slot reason hresult]
          exact hnone
      | issued fresh =>
          obtain ⟨_, _, _, haccepted, _⟩ :=
            createEndpoint_issued runtime subject slot fresh hresult
          obtain ⟨hmemory, _⟩ :=
            createEndpoint_issued_projections runtime subject slot fresh hresult
          obtain ⟨_, _, _, hkindsmap⟩ :=
            endpoint_create_accepted_registry runtime.endpoints runtime.objectIssuer.next
              subject slot haccepted
          rw [hmemory, hkindsmap]
          simp only [hne, if_false]
          exact hnone
  | destroyEndpoint subject slot =>
      simp only [applyOperation]
      obtain ⟨_, _, _, hkinds⟩ := endpoint_destroy_registry runtime.endpoints subject slot
      have hnone' : runtime.endpoints.capabilities.kinds object = none := hnone
      cases hvalue : (EndpointIPC.destroy runtime.endpoints subject
          slot).state.capabilities.kinds object with
      | none => exact hvalue
      | some found =>
          have hfound := hkinds object found hvalue
          rw [hnone'] at hfound
          cases hfound
  | createAddressSpace subject slot =>
      simp only [applyOperation]
      cases hresult : (createAddressSpace runtime subject slot).result with
      | exhausted =>
          rw [createAddressSpace_exhausted_unchanged runtime subject slot hresult]
          exact hnone
      | rejected reason =>
          rw [createAddressSpace_rejected_unchanged runtime subject slot reason hresult]
          exact hnone
      | issued fresh =>
          obtain ⟨_, _, _, haccepted, hvm⟩ :=
            createAddressSpace_issued runtime subject slot fresh hresult
          obtain ⟨_, _, _, hkindsmap⟩ :=
            address_space_create_accepted_registry runtime.virtualMemory
              runtime.objectIssuer.next subject slot haccepted
          rw [hvm, hkindsmap]
          simp only [hne, if_false]
          exact hnone
  | destroyAddressSpace subject slot =>
      simp only [applyOperation]
      obtain ⟨_, _, _, hkinds⟩ :=
        address_space_destroy_registry runtime.virtualMemory subject slot
      cases hvalue : (VirtualMapping.destroyAddressSpace runtime.virtualMemory subject
          slot).state.memory.capabilities.kinds object with
      | none => exact hvalue
      | some found =>
          have hfound := hkinds object found hvalue
          rw [hnone] at hfound
          cases hfound
  | send caller slot payload =>
      simp only [applyOperation]
      obtain ⟨hmemory, _⟩ := send_registry runtime.endpoints caller slot payload
      have hmemory' : (send runtime caller slot payload).1.virtualMemory.memory =
          runtime.virtualMemory.memory := hmemory
      rw [hmemory']
      exact hnone
  | receive caller slot =>
      simp only [applyOperation]
      obtain ⟨hmemory, _⟩ := receive_registry runtime.endpoints caller slot
      have hmemory' : (receive runtime caller slot).1.virtualMemory.memory =
          runtime.virtualMemory.memory := hmemory
      rw [hmemory']
      exact hnone

/-- An exhausted issuer is left untouched by every composite operation. -/
theorem applyOperation_exhausted_issuers_fixed (runtime : Runtime)
    (operation : Operation) :
    (LifetimeIssuer.exhausted runtime.subjectIssuer = true →
      (applyOperation runtime operation).subjectIssuer = runtime.subjectIssuer) ∧
    (LifetimeIssuer.exhausted runtime.objectIssuer = true →
      (applyOperation runtime operation).objectIssuer = runtime.objectIssuer) := by
  cases operation with
  | createSubject =>
      constructor
      · intro hexhausted
        simp only [applyOperation]
        rw [createSubject_exhausted_unchanged runtime
          ((createSubject_exhausted_iff runtime).mpr hexhausted)]
      · intro _
        exact (createSubject_object_domain_unchanged runtime).1
  | terminateSubject subject => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | allocateMemory subject slot =>
      constructor
      · intro _
        exact (allocateMemory_subject_domain_unchanged runtime subject slot).1
      · intro hexhausted
        simp only [applyOperation]
        rw [allocateMemory_exhausted_unchanged runtime subject slot
          ((allocateMemory_exhausted_iff runtime subject slot).mpr hexhausted)]
  | releaseMemory subject slot => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | createEndpoint subject slot =>
      constructor
      · intro _
        exact (createEndpoint_subject_domain_unchanged runtime subject slot).1
      · intro hexhausted
        simp only [applyOperation]
        rw [createEndpoint_exhausted_unchanged runtime subject slot
          ((createEndpoint_exhausted_iff runtime subject slot).mpr hexhausted)]
  | destroyEndpoint subject slot => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | createAddressSpace subject slot =>
      constructor
      · intro _
        exact (createAddressSpace_subject_domain_unchanged runtime subject slot).1
      · intro hexhausted
        simp only [applyOperation]
        rw [createAddressSpace_exhausted_unchanged runtime subject slot
          ((createAddressSpace_exhausted_iff runtime subject slot).mpr hexhausted)]
  | destroyAddressSpace subject slot => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | send caller slot payload => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | receive caller slot => exact ⟨fun _ => rfl, fun _ => rfl⟩

/-! ## Finite-trace stale-lifetime safety and exhaustion absorption -/

theorem runOperations_dead_object_stays_dead (runtime : Runtime)
    (operations : List Operation) (object : ObjectId) (hinv : Invariant runtime)
    (hissued : issuedObject runtime object = true)
    (hdead : runtime.virtualMemory.memory.capabilities.objects object = false) :
    (runOperations runtime operations).virtualMemory.memory.capabilities.objects object =
      false := by
  induction operations generalizing runtime with
  | nil => exact hdead
  | cons operation rest ih =>
      exact ih _ (applyOperation_preserves_invariant runtime operation hinv)
        ((applyOperation_history_monotone runtime operation).2.1 object hissued)
        (applyOperation_dead_object_stays_dead runtime operation object hinv hissued hdead)

theorem runOperations_dead_subject_stays_dead (runtime : Runtime)
    (operations : List Operation) (subject : SubjectId) (hinv : Invariant runtime)
    (hissued : runtime.lifecycle.issuedSubjects subject = true)
    (hdead : runtime.lifecycle.capabilities.subjects subject = false) :
    (runOperations runtime operations).lifecycle.capabilities.subjects subject = false := by
  induction operations generalizing runtime with
  | nil => exact hdead
  | cons operation rest ih =>
      exact ih _ (applyOperation_preserves_invariant runtime operation hinv)
        ((applyOperation_history_monotone runtime operation).1 subject hissued)
        (applyOperation_dead_subject_stays_dead runtime operation subject hinv hissued
          hdead)

theorem runOperations_none_kind_stays (runtime : Runtime) (operations : List Operation)
    (object : ObjectId) (hinv : Invariant runtime)
    (hissued : issuedObject runtime object = true)
    (hnone : runtime.virtualMemory.memory.capabilities.kinds object = none) :
    (runOperations runtime operations).virtualMemory.memory.capabilities.kinds object =
      none := by
  induction operations generalizing runtime with
  | nil => exact hnone
  | cons operation rest ih =>
      exact ih _ (applyOperation_preserves_invariant runtime operation hinv)
        ((applyOperation_history_monotone runtime operation).2.1 object hissued)
        (applyOperation_none_kind_stays runtime operation object hinv hissued hnone)

/-- Historical kind immutability along every finite trace: an issued identity
either keeps its exact kind or is retired; it never resolves to another kind. -/
theorem runOperations_kind_stable (runtime : Runtime) (operations : List Operation)
    (object : ObjectId) (kind : Capability.ObjectKind) (hinv : Invariant runtime)
    (hkind : runtime.virtualMemory.memory.capabilities.kinds object = some kind) :
    (runOperations runtime operations).virtualMemory.memory.capabilities.kinds object =
        some kind ∨
      (runOperations runtime operations).virtualMemory.memory.capabilities.kinds object =
        none := by
  induction operations generalizing runtime with
  | nil => exact Or.inl hkind
  | cons operation rest ih =>
      have hissued : issuedObject runtime object = true := hinv.2.2.2.2.1 object kind hkind
      have hinv' := applyOperation_preserves_invariant runtime operation hinv
      have hissued' := (applyOperation_history_monotone runtime operation).2.1 object
        hissued
      cases applyOperation_kind_stable runtime operation object kind hinv hkind with
      | inl hsome => exact ih _ hinv' hsome
      | inr hnone =>
          exact Or.inr (runOperations_none_kind_stays _ rest object hinv' hissued' hnone)

theorem runOperations_exhausted_absorbing (runtime : Runtime)
    (operations : List Operation) :
    (LifetimeIssuer.exhausted runtime.subjectIssuer = true →
      LifetimeIssuer.exhausted (runOperations runtime operations).subjectIssuer = true) ∧
    (LifetimeIssuer.exhausted runtime.objectIssuer = true →
      LifetimeIssuer.exhausted (runOperations runtime operations).objectIssuer = true) := by
  induction operations generalizing runtime with
  | nil => exact ⟨fun h => h, fun h => h⟩
  | cons operation rest ih =>
      obtain ⟨hsub, hobj⟩ := applyOperation_exhausted_issuers_fixed runtime operation
      obtain ⟨ihsub, ihobj⟩ := ih (applyOperation runtime operation)
      constructor
      · intro hexhausted
        exact ihsub (by rw [hsub hexhausted]; exact hexhausted)
      · intro hexhausted
        exact ihobj (by rw [hobj hexhausted]; exact hexhausted)

/-- The mature no-reuse/exhaustion bundle: along every finite composite trace
the invariant is preserved, no retired object or terminated subject identity
can ever become live again, and exhausted issuers stay exhausted. -/
theorem bounded_identity_no_reuse (runtime : Runtime) (operations : List Operation)
    (hinv : Invariant runtime) :
    Invariant (runOperations runtime operations) ∧
      (∀ object, issuedObject runtime object = true →
        runtime.virtualMemory.memory.capabilities.objects object = false →
        (runOperations runtime
          operations).virtualMemory.memory.capabilities.objects object = false) ∧
      (∀ subject, runtime.lifecycle.issuedSubjects subject = true →
        runtime.lifecycle.capabilities.subjects subject = false →
        (runOperations runtime operations).lifecycle.capabilities.subjects subject =
          false) ∧
      (LifetimeIssuer.exhausted runtime.subjectIssuer = true →
        LifetimeIssuer.exhausted (runOperations runtime operations).subjectIssuer =
          true) ∧
      (LifetimeIssuer.exhausted runtime.objectIssuer = true →
        LifetimeIssuer.exhausted (runOperations runtime operations).objectIssuer =
          true) := by
  refine ⟨runOperations_preserves_invariant runtime operations hinv, ?_, ?_,
    (runOperations_exhausted_absorbing runtime operations).1,
    (runOperations_exhausted_absorbing runtime operations).2⟩
  · intro object hissued hdead
    exact runOperations_dead_object_stays_dead runtime operations object hinv hissued hdead
  · intro subject hissued hdead
    exact runOperations_dead_subject_stays_dead runtime operations subject hinv hissued
      hdead

/-! ## Rejected cleanup preserves the complete runtime -/

theorem terminateSubject_rejected_unchanged (runtime : Runtime) (subject reason)
    (h : (terminateSubject runtime subject).2 = .rejected reason) :
    (terminateSubject runtime subject).1 = runtime := by
  have hstate := SubjectLifecycle.terminate_rejected_unchanged runtime.lifecycle subject
    reason h
  show { runtime with
    lifecycle := (SubjectLifecycle.terminate runtime.lifecycle subject).state } = runtime
  rw [hstate]

theorem releaseMemory_rejected_unchanged (runtime : Runtime) (subject slot reason)
    (h : (releaseMemory runtime subject slot).2 = .rejected reason) :
    (releaseMemory runtime subject slot).1 = runtime := by
  have hstate := VirtualMapping.release_rejected_unchanged runtime.virtualMemory subject
    slot reason h
  show { runtime with
    virtualMemory := (VirtualMapping.release runtime.virtualMemory subject slot).state } =
      runtime
  rw [hstate]

theorem destroyEndpoint_rejected_unchanged (runtime : Runtime) (subject slot reason)
    (h : (destroyEndpoint runtime subject slot).2 = .rejected reason) :
    (destroyEndpoint runtime subject slot).1 = runtime := by
  have hstate := EndpointIPC.destroy_rejected_unchanged runtime.endpoints subject slot
    reason h
  show installEndpoints runtime (EndpointIPC.destroy runtime.endpoints subject slot).state =
    runtime
  rw [hstate]
  rfl

theorem destroyAddressSpace_rejected_unchanged (runtime : Runtime) (subject slot reason)
    (h : (destroyAddressSpace runtime subject slot).2 = .rejected reason) :
    (destroyAddressSpace runtime subject slot).1 = runtime := by
  have hstate := VirtualMapping.destroy_rejected_unchanged runtime.virtualMemory subject
    slot reason h
  show { runtime with virtualMemory :=
    (VirtualMapping.destroyAddressSpace runtime.virtualMemory subject slot).state } =
      runtime
  rw [hstate]

/-! ## Concrete runtime and executable boundary traces -/

/-- Empty subject-domain lifecycle: no subject exists before the issuer's
first accepted creation. -/
def sampleLifecycle : SubjectLifecycle.State :=
  { capabilities :=
      { subjects := fun _ => false, objects := fun _ => false
        kinds := fun _ => none, slots := fun _ _ => none }
    issuedSubjects := fun _ => false
    ownedMemory := fun _ => none
    addressOwner := fun _ => none
    mapping := fun _ _ => none
    endpointOwner := fun _ => none
    mailbox := fun _ => none
    frameOwner := fun _ => none
    freeFrame := fun _ => false
    runnable := fun _ => false
    current := none }

/-- Object-domain state with three pre-admitted trusted subjects, two free
frames, and no issued object of any kind. -/
def sampleVirtualMemory : VirtualMapping.State :=
  { memory :=
      { capabilities :=
          { subjects := fun subject => subject < 3, objects := fun _ => false
            kinds := fun _ => none, slots := fun _ _ => none }
        allocator :=
          { frames := [4, 5]
            status := fun frame => if frame = 4 ∨ frame = 5 then .free else .reserved }
        binding := fun _ => none
        issued := fun _ => false }
    owner := fun _ => none
    mappings := fun _ _ => none
    issuedAddressSpace := fun _ => false }

/-- Concrete bounded runtime used by executable traces, the security-claim
non-vacuity witness, and the negative wrapping-issuer regression. -/
def sampleRuntime : Runtime :=
  { subjectIssuer := {}
    objectIssuer := {}
    lifecycle := sampleLifecycle
    virtualMemory := sampleVirtualMemory
    mailbox := fun _ => none
    sendHistory := fun _ => [] }

theorem sampleRuntime_invariant : Invariant sampleRuntime := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro subject h
    simp [sampleRuntime, sampleLifecycle] at h
  · intro subject h
    simp [sampleRuntime, sampleLifecycle] at h
  · intro object h
    simp [issuedObject, sampleRuntime, sampleVirtualMemory] at h
  · intro object h
    simp [sampleRuntime, sampleVirtualMemory] at h
  · intro object kind h
    simp [sampleRuntime, sampleVirtualMemory] at h
  · decide
  · decide

/-- Non-vacuity: the complete no-reuse bundle holds on a concrete mixed trace
covering both domains and all three object kinds. -/
example : Invariant (runOperations sampleRuntime
    [.createSubject, .allocateMemory 0 0, .createEndpoint 0 1, .createAddressSpace 0 2,
      .destroyEndpoint 0 1, .allocateMemory 1 0]) :=
  (bounded_identity_no_reuse sampleRuntime _ sampleRuntime_invariant).1

-- Sequential subject issuance from the kernel-owned counter.
private def subject1 := createSubject sampleRuntime
private def subject2 := createSubject subject1.runtime

example : subject1.result = .issued 1 ∧ subject2.result = .issued 2 := by native_decide
example : subject2.runtime.lifecycle.capabilities.subjects 1 = true ∧
    subject2.runtime.lifecycle.capabilities.subjects 2 = true ∧
    subject2.runtime.subjectIssuer.next = 3 := by native_decide

-- One object authority across the memory, endpoint, and address-space kinds:
-- identities 1, 2, 3 are consumed across kinds by the single issuer.
private def memory1 := allocateMemory subject2.runtime 0 0
private def endpoint2 := createEndpoint memory1.runtime 0 1
private def space3 := createAddressSpace endpoint2.runtime 0 2

example : memory1.result = .issued 1 ∧ endpoint2.result = .issued 2 ∧
    space3.result = .issued 3 := by native_decide
example : space3.runtime.virtualMemory.memory.capabilities.kinds 1 = some .memory ∧
    space3.runtime.virtualMemory.memory.capabilities.kinds 2 = some .endpoint ∧
    space3.runtime.virtualMemory.memory.capabilities.kinds 3 = some .addressSpace := by
  native_decide

-- Retiring the endpoint keeps identity 2 consumed for every kind: the next
-- accepted creation of any kind receives 4, and 2 stays dead with no mailbox.
private def retiredEndpoint := destroyEndpoint space3.runtime 0 1
private def memory4 := allocateMemory retiredEndpoint.1 1 0

example : retiredEndpoint.2 = .accepted := by native_decide
example : memory4.result = .issued 4 ∧ issuedObject memory4.runtime 2 = true ∧
    memory4.runtime.virtualMemory.memory.capabilities.objects 2 = false ∧
    memory4.runtime.virtualMemory.memory.capabilities.kinds 2 = none ∧
    memory4.runtime.mailbox 2 = none := by native_decide

-- Repeated cleanup is a typed, complete-state-preserving rejection.
example : (destroyEndpoint retiredEndpoint.1 0 1).2 = .rejected .staleHandle := by
  native_decide
example : (destroyEndpoint retiredEndpoint.1 0 1).1 = retiredEndpoint.1 :=
  destroyEndpoint_rejected_unchanged retiredEndpoint.1 0 1 .staleHandle (by native_decide)

-- A full slot rejects without advancing the issuer; a failed frame allocation
-- likewise leaves the counter and histories untouched.
example : (allocateMemory space3.runtime 0 0).result = .rejected .occupiedSlot ∧
    (allocateMemory space3.runtime 0 0).runtime.objectIssuer.next =
      space3.runtime.objectIssuer.next := by native_decide
example : (allocateMemory memory4.runtime 2 0).result = .rejected .exhausted ∧
    (allocateMemory memory4.runtime 2 0).runtime.objectIssuer.next =
      memory4.runtime.objectIssuer.next := by native_decide
example : (allocateMemory memory4.runtime 2 0).runtime = memory4.runtime :=
  allocateMemory_rejected_unchanged memory4.runtime 2 0 .exhausted (by native_decide)

-- Subject termination consumes the identity forever: the next creation issues
-- a fresh value and the terminated identity can never become live again.
private def terminated := terminateSubject subject2.runtime 1
private def subject3 := createSubject terminated.1

example : terminated.2 = .accepted := by native_decide
example : subject3.result = .issued 3 ∧
    subject3.runtime.lifecycle.capabilities.subjects 1 = false ∧
    subject3.runtime.lifecycle.issuedSubjects 1 = true := by native_decide
example : (terminateSubject subject3.runtime 1).2 = .rejected .alreadyTerminated := by
  native_decide
example : (terminateSubject subject3.runtime 1).1 = subject3.runtime :=
  terminateSubject_rejected_unchanged subject3.runtime 1 .alreadyTerminated
    (by native_decide)

-- Penultimate, terminal, and malformed-zero issuer boundaries fail closed with
-- the typed exhaustion result and the complete runtime preserved.
private def nearExhausted : Runtime :=
  { sampleRuntime with
    objectIssuer := { next := LifetimeIssuer.identityReserved - 1 } }
private def penultimate := allocateMemory nearExhausted 0 0

example : penultimate.result = .issued (LifetimeIssuer.identityReserved - 1) := by
  native_decide
example : (createEndpoint penultimate.runtime 0 1).result = .exhausted := by native_decide
example : (createAddressSpace penultimate.runtime 0 1).result = .exhausted := by
  native_decide
example : (allocateMemory penultimate.runtime 0 1).result = .exhausted := by native_decide
example : (createEndpoint penultimate.runtime 0 1).runtime = penultimate.runtime :=
  createEndpoint_exhausted_unchanged penultimate.runtime 0 1 (by native_decide)

private def malformedZero : Runtime :=
  { sampleRuntime with subjectIssuer := { next := 0 } }

example : (createSubject malformedZero).result = .exhausted := by native_decide

-- Identity exhaustion in one domain cannot leak into the other domain.
example : (createSubject penultimate.runtime).result = .issued 1 := by native_decide
private def subjectExhausted : Runtime :=
  { sampleRuntime with
    subjectIssuer := { next := LifetimeIssuer.identityReserved } }
example : (createSubject subjectExhausted).result = .exhausted ∧
    (allocateMemory subjectExhausted 0 0).result = .issued 1 := by native_decide

-- The capability-generation bound stays a separate resource: with a fresh
-- identity issuer but an exhausted root-capability generation, endpoint and
-- address-space creation return the precise generation error and preserve the
-- complete runtime, never the identity-domain exhaustion result.
private def generationExhausted : Runtime :=
  { sampleRuntime with
    virtualMemory := { sampleVirtualMemory with
      memory := { sampleVirtualMemory.memory with
        capabilities := { sampleVirtualMemory.memory.capabilities with
          nextIdentity := CapabilityHandle.generationReserved } } } }

example : (createEndpoint generationExhausted 0 0).result =
    .rejected .generationExhausted := by native_decide
example : (createAddressSpace generationExhausted 0 0).result =
    .rejected .generationExhausted := by native_decide
example : (allocateMemory generationExhausted 0 0).result = .rejected .exhausted := by
  native_decide
example : (createEndpoint generationExhausted 0 0).runtime = generationExhausted :=
  createEndpoint_rejected_unchanged generationExhausted 0 0 .generationExhausted
    (by native_decide)
example : (createEndpoint generationExhausted 0 0).runtime.objectIssuer.next = 1 := by
  native_decide

-- Untrusted request words are inert at the command boundary.
example : createSubjectCommand sampleRuntime { word0 := 0xdead, word1 := 0xbeef } =
    createSubjectCommand sampleRuntime { word0 := 0, word1 := 1 } := by rfl
example : (createSubjectCommand sampleRuntime
    { word0 := 0xffffffffffffffff, word1 := 42 }).result = .issued 1 := by native_decide

end LeanOS.BoundedLifecycle
