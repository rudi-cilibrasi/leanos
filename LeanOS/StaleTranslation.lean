import LeanOS.TLB

/-! # Canonical stale-translation invalidation step

`LeanOS.TLB` proves logical revocation-before-return for each cache operation.
This slice adds the *public step* consumed by the machine invalidation path:
a reviewed composite transition (`unmap`, `protect`, `release`, `destroy`, or a
root `switch`) checked against the authoritative model state, returning both the
new state and the exact machine effect the concrete path must perform before it
may return to the user, retire ownership, or publish frame reuse.

The acting subject, active address space, mapping identity, and affected virtual
page are derived from checked kernel state and generation-bound capability
handles; attacker words cannot select an invalidation target or claim
completion.  On the active no-PCID root, a `page` effect is one `invlpg` for the
exact linear page and `space`/`flush` are the reviewed complete CR3 reload.

This is a property of the finite Lean model.  The `invlpg`/CR3 instruction,
compiler, assembly, QEMU, and hardware remain trusted; nothing here proves the
processor flushed.
-/
namespace LeanOS.StaleTranslation

set_option linter.unusedSimpArgs false

open LeanOS
open LeanOS.VirtualMapping
open LeanOS.X86PageTable
open LeanOS.TLB

/-- The exact translation-cache invalidation the machine must perform for an
accepted transition.  `none` is the state-preserving rejection: no machine
mutation.  `page` is one page invalidation (`invlpg`) at the named address-space
page.  `space` retires all translations of a destroyed address space and
`flush` the complete cache; on the no-PCID root both are the reviewed CR3
reload. -/
inductive Effect where
  | none
  | page (addressSpace : AddressSpaceId) (page : VirtualPage)
  | space (addressSpace : AddressSpaceId)
  | flush
  deriving DecidableEq, Repr

/-- The reviewed composite transitions a subject may request.  Every payload
field names checked kernel state or a generation-bound capability slot, never a
raw attacker word interpreted as an address. -/
inductive Request where
  | unmap (actor : SubjectId) (addressSpace : AddressSpaceId) (page : VirtualPage)
  | protect (actor : SubjectId) (addressSpace : AddressSpaceId) (page : VirtualPage)
      (permissions : Permissions)
  | release (subject : SubjectId) (slot : SlotId)
  | destroy (subject : SubjectId) (slot : SlotId)
  | switch (addressSpace : AddressSpaceId)
  deriving Repr

/-- The canonical step result: the published cache/model state, whether the
logical transition was accepted, and the required machine effect. -/
structure Step where
  state : TLB.State
  accepted : Bool
  effect : Effect

/-- The model of what the invalidation instruction accomplishes on the finite
cache.  `step` already produces the invalidated cache; the `applyEffect_*_absent`
lemmas show the described effect removes exactly the affected translations, which
the `accepted_*_absent` corollaries confirm the returned cache already achieves. -/
def applyEffect (entries : List Entry) : Effect → List Entry
  | .none => entries
  | .page addressSpace page => eraseKey entries { addressSpace, page }
  | .space addressSpace => eraseSpace entries addressSpace
  | .flush => []

/-- The single public step.  The effect is a total function of the accepted
logical transition (its kind and checked target); rejection is inert and
requests no machine mutation. -/
def step (state : TLB.State) : Request → Step
  | .unmap actor addressSpace page =>
    match (TLB.unmap state actor addressSpace page).result with
    | .accepted =>
      { state := (TLB.unmap state actor addressSpace page).state
        accepted := true, effect := .page addressSpace page }
    | .rejected _ => { state, accepted := false, effect := .none }
  | .protect actor addressSpace page permissions =>
    match (TLB.protect state actor addressSpace page permissions).result with
    | .accepted =>
      { state := (TLB.protect state actor addressSpace page permissions).state
        accepted := true, effect := .page addressSpace page }
    | .rejected _ => { state, accepted := false, effect := .none }
  | .release subject slot =>
    match (TLB.release state subject slot).result with
    | .accepted =>
      { state := (TLB.release state subject slot).state
        accepted := true, effect := .flush }
    | .rejected _ => { state, accepted := false, effect := .none }
  | .destroy subject slot =>
    match (TLB.destroy state subject slot).result with
    | .accepted =>
      match Capability.lookup state.virtual.memory.capabilities subject slot with
      | .found cap =>
        { state := (TLB.destroy state subject slot).state
          accepted := true, effect := .space cap.object }
      | _ =>
        { state := (TLB.destroy state subject slot).state
          accepted := true, effect := .flush }
    | .rejected _ => { state, accepted := false, effect := .none }
  | .switch addressSpace =>
    { state := TLB.switch state addressSpace, accepted := true, effect := .flush }

/-! ## Rejection is inert; no machine mutation is requested -/

/-- A rejected transition preserves the complete cache/model state and requests
no invalidation.  (Root `switch` never rejects.) -/
theorem rejected_inert state request
    (h : (step state request).accepted = false) :
    (step state request).state = state ∧ (step state request).effect = .none := by
  cases request with
  | switch addressSpace => simp [step] at h
  | destroy subject slot =>
    simp only [step] at h ⊢
    split at h <;> try simp_all
    split at h <;> simp_all
  | _ =>
    simp only [step] at h ⊢
    split at h <;> simp_all

/-! ## The effect is determined by the accepted transition and its checked target -/

/-- Accepted `unmap` invalidates exactly the requested address-space page,
independent of the pre-state: an attacker cannot splice a different target. -/
theorem unmap_accepted_effect state actor addressSpace page
    (h : (step state (.unmap actor addressSpace page)).accepted = true) :
    (step state (.unmap actor addressSpace page)).effect = .page addressSpace page := by
  simp only [step] at h ⊢
  split at h <;> simp_all

/-- Accepted `protect` invalidates exactly the requested address-space page. -/
theorem protect_accepted_effect state actor addressSpace page permissions
    (h : (step state (.protect actor addressSpace page permissions)).accepted = true) :
    (step state (.protect actor addressSpace page permissions)).effect = .page addressSpace page := by
  simp only [step] at h ⊢
  split at h <;> simp_all

/-- Accepted `release` performs the reviewed complete-cache flush. -/
theorem release_accepted_effect state subject slot
    (h : (step state (.release subject slot)).accepted = true) :
    (step state (.release subject slot)).effect = .flush := by
  simp only [step] at h ⊢
  split at h <;> simp_all

/-- An accepted authoritative address-space destruction can only come from a
found capability, so the retired object identity is the one the checked handle
named. -/
theorem virtual_destroy_accepted_lookup state subject slot
    (h : (VirtualMapping.destroyAddressSpace state subject slot).result = .accepted) :
    ∃ cap, Capability.lookup state.memory.capabilities subject slot = .found cap := by
  simp only [VirtualMapping.destroyAddressSpace] at h
  split at h
  · simp_all [VirtualMapping.reject]
  · simp_all [VirtualMapping.reject]
  · next cap hlookup => exact ⟨cap, hlookup⟩

theorem tlb_destroy_accepted_lookup state subject slot
    (h : (TLB.destroy state subject slot).result = .accepted) :
    ∃ cap, Capability.lookup state.virtual.memory.capabilities subject slot = .found cap := by
  simp only [TLB.destroy] at h
  split at h
  · simp_all
  · next hvm => exact virtual_destroy_accepted_lookup state.virtual subject slot hvm

/-- Accepted `destroy` names exactly the checked capability's retired address
space; the space comes from the same generation-bound handle the authoritative
model destroyed, never from an attacker word. -/
theorem destroy_accepted_effect state subject slot
    (h : (step state (.destroy subject slot)).accepted = true) :
    ∃ cap, Capability.lookup state.virtual.memory.capabilities subject slot = .found cap ∧
      (step state (.destroy subject slot)).effect = .space cap.object := by
  have hresult : (TLB.destroy state subject slot).result = .accepted := by
    simp only [step] at h
    split at h <;> simp_all
  obtain ⟨cap, hlookup⟩ := tlb_destroy_accepted_lookup state subject slot hresult
  exact ⟨cap, hlookup, by simp only [step, hresult, hlookup]⟩

/-- A root `switch` is always accepted and always the reviewed complete flush. -/
theorem switch_effect state addressSpace :
    (step state (.switch addressSpace)).accepted = true ∧
      (step state (.switch addressSpace)).effect = .flush := by
  simp [step]

/-! ## Confinement: untrusted arguments cannot invalidate another subject -/

/-- An actor that is not the checked owner of the address space cannot unmap it:
the step rejects, preserves state, and requests no invalidation of that page. -/
theorem unmap_wrong_owner_inert state actor addressSpace page owner
    (howner : state.virtual.owner addressSpace = some owner) (hne : owner ≠ actor) :
    (step state (.unmap actor addressSpace page)).accepted = false ∧
      (step state (.unmap actor addressSpace page)).effect = .none ∧
      (step state (.unmap actor addressSpace page)).state = state := by
  have hreject : (TLB.unmap state actor addressSpace page).result = .rejected .notOwner := by
    simp [TLB.unmap, VirtualMapping.unmap, VirtualMapping.reject, howner,
      (by simpa using hne : owner != actor)]
  simp [step, hreject]

/-- Symmetric confinement for `protect`: a non-owner request is rejected and
inert, so it cannot invalidate another subject's page. -/
theorem protect_wrong_owner_inert state actor addressSpace page permissions owner
    (howner : state.virtual.owner addressSpace = some owner) (hne : owner ≠ actor) :
    (step state (.protect actor addressSpace page permissions)).accepted = false ∧
      (step state (.protect actor addressSpace page permissions)).effect = .none ∧
      (step state (.protect actor addressSpace page permissions)).state = state := by
  have hreject : (TLB.protect state actor addressSpace page permissions).result =
      .rejected .notOwner := by
    simp [TLB.protect, howner, (by simpa using hne : owner != actor)]
  simp [step, hreject]

/-! ## The described effect is sufficient for the TLB absence guarantees -/

theorem applyEffect_page_absent entries addressSpace page context :
    lookup (applyEffect entries (.page addressSpace page)) { addressSpace, page } context = none := by
  simpa [applyEffect] using invalidate_page_absent entries { addressSpace, page } context

theorem applyEffect_space_absent entries addressSpace key context
    (hkey : key.addressSpace = addressSpace) :
    lookup (applyEffect entries (.space addressSpace)) key context = none := by
  simpa [applyEffect] using invalidate_space_absent entries addressSpace key context hkey

theorem applyEffect_flush_absent entries key context :
    lookup (applyEffect entries .flush) key context = none := by
  simp [applyEffect, lookup]

/-- Accepted `unmap` returns a cache in which the affected page is absent —
directly the TLB revocation-before-return guarantee, now carried by the public
step. -/
theorem accepted_unmap_target_absent state actor addressSpace page context
    (h : (step state (.unmap actor addressSpace page)).accepted = true) :
    lookup (step state (.unmap actor addressSpace page)).state.entries
      { addressSpace, page } context = none := by
  simp only [step] at h ⊢
  split at h <;> try simp_all
  next hresult =>
    exact TLB.unmap_revokes_before_return state actor addressSpace page hresult context

/-- Accepted `protect` returns a cache in which the affected page is absent. -/
theorem accepted_protect_target_absent state actor addressSpace page permissions context
    (h : (step state (.protect actor addressSpace page permissions)).accepted = true) :
    lookup (step state (.protect actor addressSpace page permissions)).state.entries
      { addressSpace, page } context = none := by
  simp only [step] at h ⊢
  split at h <;> try simp_all
  next hresult =>
    exact TLB.protect_revokes_before_return state actor addressSpace page permissions hresult context

/-- Accepted `release` returns an empty cache: every stale hit for the retired
object is absent before reuse can be published. -/
theorem accepted_release_all_absent state subject slot key context
    (h : (step state (.release subject slot)).accepted = true) :
    lookup (step state (.release subject slot)).state.entries key context = none := by
  simp only [step] at h ⊢
  split at h <;> try simp_all
  next hresult =>
    exact TLB.release_revokes_before_return state subject slot hresult key context

/-- The published release cache is fully flushed, so no retired frame can be
reached through a stale cache hit before reuse is published. -/
theorem accepted_release_flushed state subject slot
    (h : (step state (.release subject slot)).accepted = true) :
    (step state (.release subject slot)).state.entries = [] := by
  simp only [step] at h ⊢
  split at h
  · next hres =>
      simp only [TLB.release] at hres ⊢
      split at hres <;> simp_all
  · simp_all

/-- Accepted `destroy` returns a cache in which every translation of the retired
address space is absent. -/
theorem accepted_destroy_space_absent state subject slot cap key context
    (hlookup : Capability.lookup state.virtual.memory.capabilities subject slot = .found cap)
    (hkey : key.addressSpace = cap.object)
    (h : (step state (.destroy subject slot)).accepted = true) :
    lookup (step state (.destroy subject slot)).state.entries key context = none := by
  have hresult : (TLB.destroy state subject slot).result = .accepted := by
    simp only [step] at h
    split at h <;> simp_all
  simp only [step, hresult, hlookup]
  exact TLB.destroy_revokes_before_return state subject slot cap hlookup hresult key context hkey

/-! ## The public step preserves the bounded-cache invariant -/

theorem step_preserves_coherent state request
    (hc : Coherent state) : Coherent (step state request).state := by
  cases request with
  | unmap actor addressSpace page =>
    simp only [step]; split
    · next h => exact TLB.unmap_accepted_coherent state actor addressSpace page hc (by simp [h])
    · exact hc
  | protect actor addressSpace page permissions =>
    simp only [step]; split
    · next h =>
        exact TLB.protect_accepted_coherent state actor addressSpace page permissions hc (by simp [h])
    · exact hc
  | release subject slot =>
    simp only [step]; split
    · next h => exact TLB.release_accepted_coherent state subject slot (by simp [h])
    · exact hc
  | destroy subject slot =>
    simp only [step]; split
    · next h =>
        have hacc : (TLB.destroy state subject slot).result = .accepted := by simp [h]
        split <;> exact TLB.destroy_accepted_coherent state subject slot hc hacc
    · exact hc
  | switch addressSpace => exact TLB.switch_coherent state addressSpace

/-! ## Executable fixtures and the full stale-translation narrative

`filled` caches a real translation for page 7 (frame 4) in address space 1,
owned by subject 0; `reused` is the post-release state whose retired object has
been re-allocated as a fresh object while page 7 stays unmapped. -/

def ctx : AccessContext :=
  { privilege := .user, kind := .read, writeProtect := true, nxEnable := true,
    smep := true, smap := true, ac := false }

private def testCaps : Capability.State :=
  { subjects := fun subject => subject = 0
    objects := fun object => object = 10 || object = 1 || object = 2
    kinds := fun object => if object = 10 then some .memory
      else if object = 1 || object = 2 then some .addressSpace else none
    slots := fun subject slot =>
      if subject = 0 ∧ slot = 0 then
        some (Capability.Capability.mk 10 .memory Capability.allRights 0 none)
      else if subject = 0 ∧ slot = 1 then
        some (Capability.Capability.mk 1 .addressSpace
          VirtualMapping.addressSpaceRootRights 0 none)
      else none }

private def testMemory : MemoryLifecycle.State :=
  { capabilities := testCaps
    allocator := { frames := [4], status := fun frame =>
      if frame = 4 then .owned 10 else .reserved }
    binding := fun object => if object = 10 then some 4 else none
    issued := fun object => object = 10 || object = 1 || object = 2 }

private def testVirtual : VirtualMapping.State :=
  { memory := testMemory
    owner := fun space => if space = 1 || space = 2 then some 0 else none
    mappings := fun space page =>
      if (space = 1 || space = 2) ∧ page = 7 then
        some { object := 10, permissions := { read := true } }
      else none
    issuedAddressSpace := fun space => space = 1 || space = 2 }

def cold : TLB.State := { virtual := testVirtual, active := some 1, entries := [] }

def filled : TLB.State :=
  match fill cold 7 ctx with
  | .ok (_, state) => state
  | .error _ => cold

def released : TLB.State := (TLB.release filled 0 0).state

def reused : TLB.State :=
  { released with virtual :=
      { released.virtual with
        memory := (MemoryLifecycle.allocate released.virtual.memory 11 0 0).state } }

def selectState (selector : UInt64) : TLB.State := if selector = 0 then filled else reused

-- The canary is really used: a CPL3 read at page 7 reaches frame 4 before mutation.
example : (access filled 7 ctx).toOption.map (fun result => result.1) = some 4 := by native_decide

-- Accepted unmap: exact single-page effect and the old page is gone from the cache.
example : (step filled (.unmap 0 1 7)).accepted = true := by native_decide
example : (step filled (.unmap 0 1 7)).effect = .page 1 7 := by native_decide
example : lookup (step filled (.unmap 0 1 7)).state.entries { addressSpace := 1, page := 7 } ctx =
    none := by native_decide
-- A later access cannot use the old translation: the page is now unmapped.
example : (access (step filled (.unmap 0 1 7)).state 7 ctx).isOk = false := by native_decide

-- Accepted protect keeps the mapping but still invalidates the page.
example : (step filled (.protect 0 1 7 { read := true })).accepted = true := by native_decide
example : (step filled (.protect 0 1 7 { read := true })).effect = .page 1 7 := by native_decide
example : lookup (step filled (.protect 0 1 7 { read := true })).state.entries
    { addressSpace := 1, page := 7 } ctx = none := by native_decide
-- Protect can only downgrade: adding write authority is rejected, no effect.
example : (step filled (.protect 0 1 7 { write := true })).accepted = false := by native_decide
example : (step filled (.protect 0 1 7 { write := true })).effect = .none := by native_decide

-- Wrong-owner requests are rejected and inert.
example : (step filled (.unmap 1 1 7)).accepted = false := by native_decide
example : (step filled (.unmap 1 1 7)).effect = .none := by native_decide
example : (step filled (.unmap 1 1 7)).state = filled :=
  (unmap_wrong_owner_inert filled 1 1 7 0 (by native_decide) (by decide)).2.2

-- Accepted release performs a full flush and empties the cache.
example : (step filled (.release 0 0)).accepted = true := by native_decide
example : (step filled (.release 0 0)).effect = .flush := by native_decide
example : (step filled (.release 0 0)).state.entries = [] := by native_decide

-- Accepted destruction retires the address space's translations.
example : (step filled (.destroy 0 1)).accepted = true := by native_decide
example : (step filled (.destroy 0 1)).effect = .space 1 := by native_decide
example : lookup (step filled (.destroy 0 1)).state.entries { addressSpace := 1, page := 7 } ctx =
    none := by native_decide

-- Switch away and back are the reviewed complete flush.
example : (step filled (.switch 2)).effect = .flush := by native_decide
example : (step (step filled (.switch 2)).state (.switch 1)).effect = .flush := by native_decide
example : (step filled (.switch 2)).state.entries = [] := by native_decide

-- Fresh-lifetime reuse: B receives the scrubbed, re-allocated frame while A's old
-- virtual page stays absent and unreachable through the retired translation.
example : (MemoryLifecycle.allocate released.virtual.memory 11 0 0).result = .accepted := by
  native_decide
example : reused.virtual.memory.binding 11 = some 4 := by native_decide
example : reused.virtual.mappings 1 7 = none := by native_decide
example : (access reused 7 ctx).isOk = false := by native_decide
example : (step reused (.unmap 0 1 7)).accepted = false := by native_decide

/-- Design witness: a cache that trusts a stale hit after the PTE is cleared
without invalidation would still reach frame 4. The public step never publishes
such a state; every accepted transition carries its invalidation effect. -/
def brokenCachedAccess (state : TLB.State) (page : VirtualPage)
    (context : AccessContext) : Option PhysicalFrame :=
  state.active.bind fun addressSpace =>
    (lookup state.entries { addressSpace, page } context).map (fun entry => entry.frame)

private def clearedWithoutInvalidation : TLB.State :=
  { filled with virtual := VirtualMapping.setMapping filled.virtual 1 7 none }

example : brokenCachedAccess clearedWithoutInvalidation 7 ctx = some 4 := by native_decide
example : brokenCachedAccess (step filled (.unmap 0 1 7)).state 7 ctx = none := by native_decide

/-! ## Fixed-width generated adapter and independent model expectation

The exported scalar adapter is a self-contained rendering of the reviewed
fixture decision; `staleTranslationModelExpected` independently evaluates the
authoritative `step` and encodes its outcome.  `Oracle` proves the two agree on
every corpus vector, and the hosted generated-C replay re-checks the adapter
against Lean's evaluation.  The effect encoding is deliberately upgradeable: when
issues #104/#105 land a composite stateful dispatcher, this scalar boundary is
replaced by sequence-level model-backed evidence. -/

/-- bits 0-7 effect tag (0 none, 1 page, 2 space, 3 flush); bits 8-15 effect
address space; bits 16-31 effect page; bit 32 accepted; bit 33 affected-absent
(the model discharged the required invalidation). -/
def affectedAbsent (s : Step) : Bool :=
  match s.effect with
  | .none => true
  | .page addressSpace page => lookup s.state.entries { addressSpace, page } ctx == none
  | .space addressSpace =>
      (s.state.entries.filter (fun entry => entry.key.addressSpace == addressSpace)).isEmpty
  | .flush => s.state.entries.isEmpty

def encodeStep (s : Step) : UInt64 :=
  let tag : UInt64 := match s.effect with
    | .none => 0 | .page _ _ => 1 | .space _ => 2 | .flush => 3
  let asField : UInt64 := match s.effect with
    | .page addressSpace _ => UInt64.ofNat addressSpace
    | .space addressSpace => UInt64.ofNat addressSpace
    | _ => 0
  let pageField : UInt64 := match s.effect with
    | .page _ page => UInt64.ofNat page | _ => 0
  tag + (asField % 256) * 0x100 + (pageField % 65536) * 0x10000 +
    (if s.accepted then 0x100000000 else 0) +
    (if affectedAbsent s then 0x200000000 else 0)

def decodeRequest (kind actor addressSpace page aux : UInt64) : Option Request :=
  if kind == 0 then some (.unmap actor.toNat addressSpace.toNat page.toNat)
  else if kind == 1 then
    some (.protect actor.toNat addressSpace.toNat page.toNat
      { read := aux &&& 1 == 1, write := aux &&& 2 == 2 })
  else if kind == 2 then some (.release actor.toNat aux.toNat)
  else if kind == 3 then some (.destroy actor.toNat aux.toNat)
  else if kind == 4 then some (.switch addressSpace.toNat)
  else none

/-- Independent expected word: evaluate the authoritative `step` and encode. -/
def staleTranslationModelExpected (kind actor addressSpace page aux selector : UInt64) : UInt64 :=
  match decodeRequest kind actor addressSpace page aux with
  | none => 0
  | some request => encodeStep (step (selectState selector) request)

/-- Self-contained scalar adapter over the reviewed fixture: subject 0 owns
address spaces 1 and 2; page 7 maps live object 10 (frame 4); memory slot 0 is
that object and address-space slot 1 is the space-1 root; selector 0 is the
filled cache and selector 1 the post-release reuse where page 7 is unmapped. -/
def staleTranslationDemo (kind actor addressSpace page aux selector : UInt64) : UInt64 :=
  let acceptedBit : UInt64 := 0x100000000
  let absentBit : UInt64 := 0x200000000
  let ownsSpace := addressSpace == 1 || addressSpace == 2
  let cached := selector == 0
  if kind == 0 then
    if actor == 0 && ownsSpace && page == 7 && cached then
      1 + (addressSpace % 256) * 0x100 + (page % 65536) * 0x10000 + acceptedBit + absentBit
    else absentBit
  else if kind == 1 then
    let read := aux &&& 1 == 1
    let write := aux &&& 2 == 2
    if actor == 0 && ownsSpace && page == 7 && cached && read && !write then
      1 + (addressSpace % 256) * 0x100 + (page % 65536) * 0x10000 + acceptedBit + absentBit
    else absentBit
  else if kind == 2 then
    if actor == 0 && aux == 0 && cached then 3 + acceptedBit + absentBit else absentBit
  else if kind == 3 then
    if actor == 0 && aux == 1 then 2 + 0x100 + acceptedBit + absentBit else absentBit
  else if kind == 4 then
    3 + acceptedBit + absentBit
  else 0

@[export leanos_stale_translation_demo]
def staleTranslationDemoExport (kind actor addressSpace page aux selector : UInt64) : UInt64 :=
  staleTranslationDemo kind actor addressSpace page aux selector

end LeanOS.StaleTranslation
