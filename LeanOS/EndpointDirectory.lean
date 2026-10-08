import LeanOS.Capability

/-!
# Endpoint directory (issue #485)

A directory subject holds one endpoint capability per registered name, with
the grant right, in its own slots of an unmodified `Capability.State`. A name
is a 64-bit word. A client asks for a name; the directory answers through the
reply to that call. A registered name is answered with a send-only copy of
the directory's capability, made by the authoritative `Capability.copy` with
the directory as the actor, so every `Capability` theorem (in particular
`copy_no_authority_amplification`, SC-CAP-AUTH) applies unchanged. An
unregistered name is a typed miss that changes nothing.

Theorems:

* `resolve_unregistered`, `resolve_miss_unchanged`: an unregistered name is
  the typed miss `unregistered`, and every miss leaves the capability state
  unchanged, so nothing is transferred.
* `resolve_resolved_held`: a resolved name delivers a capability for the
  same endpoint the directory holds under that name, with rights exactly
  `sendOnly`, a subset of the directory's rights, and only when the directory
  holds grant.
* `resolve_no_amplification`: after a resolution, every authority any subject
  has either existed before, or is the client's send right over an endpoint
  on which the directory itself held send and grant.
* `resolve_only_send`: a resolution never gives any subject receive, grant,
  revoke, read or write authority it did not already have.

`directoryResolve` is the allocation-free boot witness of the rights decision
(`directoryResolve_agrees`); the `endpoint-directory` image checks every
decision of its ring-3 directory against it.

None of these is a refinement claim about the booted kernel, `boot.S` or the
ring-3 directory, a liveness claim, or a claim about names beyond equality of
64-bit words.
-/
namespace LeanOS.EndpointDirectory

open LeanOS.Capability

/-- A name is one 64-bit word: no hierarchy and no strings. -/
abbrev Name := UInt64

/-- The directory subject and its registrations: each name maps to the
directory's own slot that holds the registered endpoint capability. -/
structure Directory where
  subject : SubjectId
  entries : List (Name × SlotId)
  deriving DecidableEq, Repr

/-- The directory slot registered under `name`, if any (most recent first). -/
def slotOf (d : Directory) (name : Name) : Option SlotId :=
  (d.entries.find? fun entry => entry.1 == name).map Prod.snd

/-- The rights a resolution delivers: send only. -/
def sendOnly : Rights := { send := true }

/-- The rights a server delegates to the directory on registration: send, and
grant so that the directory can copy it. -/
def registeredRights : Rights := { send := true, grant := true }

/-- Typed misses. -/
inductive Miss where
  /-- No registration under that name; nothing is transferred. -/
  | unregistered
  /-- A second registration of a registered name. -/
  | duplicate
  /-- The capability operation itself was refused. -/
  | denied (reason : Denial)
  deriving DecidableEq, Repr

inductive Answer where
  | resolved (slot : SlotId)
  | registered
  | miss (reason : Miss)
  deriving DecidableEq, Repr

/-- Resolve `name` for `client` with the directory's attenuation policy
`offered`, installing the answer in `clientSlot`. A registered name is a
`Capability.copy` of the directory's capability with `offered` requested, so
it needs the directory's grant right, `offered` a subset of what the
directory holds, and rights valid for the object's kind. An unregistered name
is a typed miss. -/
def resolveWith (offered : Rights) (st : State) (d : Directory) (client : SubjectId)
    (clientSlot : SlotId) (name : Name) : State × Answer :=
  match slotOf d name with
  | none => (st, .miss .unregistered)
  | some held =>
    match (copy st d.subject held client clientSlot offered).result with
    | .accepted => ((copy st d.subject held client clientSlot offered).state, .resolved clientSlot)
    | .rejected reason => ((copy st d.subject held client clientSlot offered).state,
        .miss (.denied reason))

/-- The directory's resolution: it offers send only. -/
def resolve (st : State) (d : Directory) (client : SubjectId) (clientSlot : SlotId)
    (name : Name) : State × Answer :=
  resolveWith sendOnly st d client clientSlot name

/-- The policy assumption of the theorems: a directory offers at most send. -/
def AttenuatesToSend (offered : Rights) : Prop := rightsSubset offered sendOnly = true

theorem sendOnly_attenuates : AttenuatesToSend sendOnly := rfl

/-- A server registers `name` by delegating its capability in `serverSlot`,
attenuated to `registeredRights`, into the directory's empty `directorySlot`. -/
def register (st : State) (d : Directory) (server : SubjectId) (serverSlot : SlotId)
    (directorySlot : SlotId) (name : Name) : State × Directory × Answer :=
  match slotOf d name with
  | some _ => (st, d, .miss .duplicate)
  | none =>
    match (copy st server serverSlot d.subject directorySlot registeredRights).result with
    | .accepted =>
      ((copy st server serverSlot d.subject directorySlot registeredRights).state,
        { d with entries := (name, directorySlot) :: d.entries }, .registered)
    | .rejected reason =>
      ((copy st server serverSlot d.subject directorySlot registeredRights).state, d,
        .miss (.denied reason))

/-! ## The shape of an accepted copy -/

/-- An accepted `copy` found a capability in the actor's source slot that
holds grant, of which the requested rights are a valid subset, and installed
exactly one fresh child of it in the destination slot; every other slot is
unchanged. -/
theorem copy_accepted_shape (st : State) (actor : SubjectId) (source : SlotId)
    (destination : SubjectId) (destinationSlot : SlotId) (requested : Rights)
    (haccepted : (copy st actor source destination destinationSlot requested).result =
      .accepted) :
    ∃ held, st.slots actor source = some held ∧ held.rights.grant = true ∧
      rightsSubset requested held.rights = true ∧
      rightsValid held.kind requested = true ∧
      ∀ subject slot,
        (copy st actor source destination destinationSlot requested).state.slots subject slot =
          if subject = destination ∧ slot = destinationSlot then
            some { identity := st.nextIdentity, parent := some held.identity,
                   object := held.object, kind := held.kind, rights := requested }
          else st.slots subject slot := by
  unfold copy at haccepted ⊢
  split at * <;> try simp_all [reject]
  next held hlookup =>
    refine ⟨held, lookup_found_slot st actor source held hlookup, ?_⟩
    split at * <;> try simp_all
    split at * <;> try simp_all
    split at * <;> try simp_all
    split at * <;> try simp_all
    split at * <;> try simp_all
    split at * <;> try simp_all
    intro subject slot
    simp [install]

/-- Only endpoint rights admit a valid subset of `sendOnly`. -/
theorem rightsValid_of_attenuates (kind : ObjectKind) (offered : Rights)
    (hoffered : AttenuatesToSend offered) (h : rightsValid kind offered = true) :
    kind = .endpoint := by
  obtain ⟨read, write, send, receive, grant, revoke⟩ := offered
  cases kind <;> cases read <;> cases write <;> cases send <;> cases receive <;>
    cases grant <;> cases revoke <;>
    simp_all [AttenuatesToSend, rightsValid, rightsSubset, sendOnly, nonemptyRights]

/-! ## Misses transfer nothing -/

/-- An unregistered name is the typed miss `unregistered`, with the
capability state unchanged. -/
theorem resolve_unregistered (offered : Rights) (st : State) (d : Directory)
    (client : SubjectId) (clientSlot : SlotId) (name : Name) (h : slotOf d name = none) :
    resolveWith offered st d client clientSlot name = (st, .miss .unregistered) := by
  simp [resolveWith, h]

/-- Every miss leaves the capability state unchanged. -/
theorem resolve_miss_unchanged (offered : Rights) (st : State) (d : Directory)
    (client : SubjectId) (clientSlot : SlotId) (name : Name) (m : Miss)
    (h : (resolveWith offered st d client clientSlot name).2 = .miss m) :
    (resolveWith offered st d client clientSlot name).1 = st := by
  unfold resolveWith at h ⊢
  split at * <;> try simp_all
  next held _ =>
    split at * <;> try simp_all
    next reason hrejected =>
      exact copy_rejected_unchanged st d.subject held client clientSlot offered reason hrejected

/-! ## A resolution delivers only what the directory holds, attenuated -/

/-- A resolved name delivers, in the client's slot, a capability for the same
endpoint object and kind that the directory holds under that name, with
exactly the offered rights; those are a subset of the directory's rights and
of send-only, and the directory's capability holds grant. -/
theorem resolve_resolved_held (offered : Rights) (hoffered : AttenuatesToSend offered)
    (st : State) (d : Directory) (client : SubjectId) (clientSlot : SlotId) (name : Name)
    (slot : SlotId)
    (h : (resolveWith offered st d client clientSlot name).2 = .resolved slot) :
    slot = clientSlot ∧
    ∃ heldSlot held delivered,
      slotOf d name = some heldSlot ∧
      st.slots d.subject heldSlot = some held ∧
      (resolveWith offered st d client clientSlot name).1.slots client clientSlot =
        some delivered ∧
      delivered.object = held.object ∧ delivered.kind = held.kind ∧
      held.kind = .endpoint ∧
      delivered.rights = offered ∧
      rightsSubset delivered.rights sendOnly = true ∧
      rightsSubset delivered.rights held.rights = true ∧
      held.rights.grant = true := by
  unfold resolveWith at h ⊢
  cases hslot : slotOf d name with
  | none => simp [hslot] at h
  | some heldSlot =>
    simp only [hslot] at h ⊢
    cases hres : (copy st d.subject heldSlot client clientSlot offered).result with
    | rejected reason => simp [hres] at h
    | accepted =>
      simp only [hres, Answer.resolved.injEq] at h ⊢
      obtain ⟨held, hheld, hgrant, hsubset, hvalid, hslots⟩ :=
        copy_accepted_shape st d.subject heldSlot client clientSlot offered hres
      refine ⟨h.symm, heldSlot, held,
        { identity := st.nextIdentity, parent := some held.identity,
          object := held.object, kind := held.kind, rights := offered },
        rfl, hheld, ?_, rfl, rfl, rightsValid_of_attenuates held.kind offered hoffered hvalid,
        rfl, hoffered, hsubset, hgrant⟩
      rw [hslots]
      simp

/-- No amplification: after a resolution, every authority of every subject
either existed before, or is the client's send right over an endpoint on
which the directory itself held both send and grant. -/
theorem resolve_no_amplification (offered : Rights) (hoffered : AttenuatesToSend offered)
    (st : State) (d : Directory) (client : SubjectId) (clientSlot : SlotId) (name : Name)
    (candidate : SubjectId) (object : ObjectId) (right : Right)
    (hauthority : HasAuthority (resolveWith offered st d client clientSlot name).1
      candidate object right) :
    HasAuthority st candidate object right ∨
      (candidate = client ∧ right = .send ∧
        HasAuthority st d.subject object .send ∧ HasAuthority st d.subject object .grant) := by
  unfold resolveWith at hauthority
  split at hauthority
  · exact Or.inl hauthority
  next heldSlot _ =>
    split at hauthority
    next haccepted =>
      obtain ⟨held, hheld, hgrant, hsubset, _, hslots⟩ :=
        copy_accepted_shape st d.subject heldSlot client clientSlot offered haccepted
      obtain ⟨slot, capability, hcap, hobject, hright⟩ := hauthority
      rw [hslots] at hcap
      by_cases hdest : candidate = client ∧ slot = clientSlot
      · simp only [hdest, and_self, ↓reduceIte, Option.some.injEq] at hcap
        subst hcap
        have hsend : right = .send := by
          cases right <;>
            simp_all [AttenuatesToSend, hasRight, permits, rightsSubset, sendOnly]
        subst hsend
        have hheldSend : held.rights.send = true := by
          simp_all [hasRight, permits, rightsSubset]
        refine Or.inr ⟨hdest.1, rfl, ⟨heldSlot, held, hheld, hobject, ?_⟩,
          ⟨heldSlot, held, hheld, hobject, ?_⟩⟩
        · simp [hasRight, permits, hheldSend]
        · simp [hasRight, permits, hgrant]
      · simp only [hdest, ↓reduceIte] at hcap
        exact Or.inl ⟨slot, capability, hcap, hobject, hright⟩
    next reason hrejected =>
      rw [copy_rejected_unchanged st d.subject heldSlot client clientSlot offered reason
        hrejected] at hauthority
      exact Or.inl hauthority

/-- A resolution never gives any subject a right other than send that it did
not already have: in particular never receive, grant or revoke. -/
theorem resolve_only_send (offered : Rights) (hoffered : AttenuatesToSend offered)
    (st : State) (d : Directory) (client : SubjectId) (clientSlot : SlotId) (name : Name)
    (candidate : SubjectId) (object : ObjectId) (right : Right) (hright : right ≠ .send)
    (hauthority : HasAuthority (resolveWith offered st d client clientSlot name).1
      candidate object right) :
    HasAuthority st candidate object right := by
  rcases resolve_no_amplification offered hoffered st d client clientSlot name candidate
    object right hauthority with h | ⟨_, hsend, _⟩
  · exact h
  · exact absurd hsend hright

/-- A new authority names an endpoint on which the directory already held
that right: the directory cannot hand out authority it does not hold. -/
theorem resolve_new_authority_held (offered : Rights) (hoffered : AttenuatesToSend offered)
    (st : State) (d : Directory) (client : SubjectId) (clientSlot : SlotId) (name : Name)
    (candidate : SubjectId) (object : ObjectId) (right : Right)
    (hauthority : HasAuthority (resolveWith offered st d client clientSlot name).1
      candidate object right)
    (hnew : ¬ HasAuthority st candidate object right) :
    HasAuthority st d.subject object right := by
  rcases resolve_no_amplification offered hoffered st d client clientSlot name candidate
    object right hauthority with h | ⟨_, hsend, hheld, _⟩
  · exact absurd h hnew
  · exact hsend ▸ hheld

/-- Resolutions preserve the capability invariant. -/
theorem resolve_preserves_wellFormed (offered : Rights) (st : State) (d : Directory)
    (client : SubjectId) (clientSlot : SlotId) (name : Name) (hst : WellFormed st) :
    WellFormed (resolveWith offered st d client clientSlot name).1 := by
  unfold resolveWith
  split
  · exact hst
  · split <;> exact copy_preserves_wellFormed st d.subject _ client clientSlot offered hst

/-! ## Registration -/

/-- A registered name is not registered twice; the duplicate changes nothing. -/
theorem register_duplicate_unchanged (st : State) (d : Directory) (server : SubjectId)
    (serverSlot directorySlot : SlotId) (name : Name) (slot : SlotId)
    (h : slotOf d name = some slot) :
    register st d server serverSlot directorySlot name = (st, d, .miss .duplicate) := by
  simp [register, h]

/-- After an accepted registration the name resolves to the directory slot
that holds the server's capability, attenuated to send and grant. -/
theorem register_accepted (st : State) (d : Directory) (server : SubjectId)
    (serverSlot directorySlot : SlotId) (name : Name)
    (h : (register st d server serverSlot directorySlot name).2.2 = .registered) :
    slotOf (register st d server serverSlot directorySlot name).2.1 name = some directorySlot ∧
    ∃ source installed,
      st.slots server serverSlot = some source ∧
      (register st d server serverSlot directorySlot name).1.slots d.subject directorySlot =
        some installed ∧
      installed.object = source.object ∧ installed.rights = registeredRights ∧
      rightsSubset registeredRights source.rights = true := by
  unfold register at h ⊢
  split at * <;> try simp_all
  next hnone =>
    split at * <;> try simp_all
    next haccepted =>
      obtain ⟨source, hsource, _, hsubset, _, hslots⟩ :=
        copy_accepted_shape st server serverSlot d.subject directorySlot registeredRights
          haccepted
      refine ⟨by simp [slotOf], source, hsource, ?_⟩
      rw [hslots]
      simp [hsubset]

/-! ## The boot witness

The `endpoint-directory` image encodes endpoint rights as bits (send 1,
receive 2, grant 4, revoke 8) and checks every reply of its ring-3 directory
against `directoryResolve`. -/

def sendBit : UInt64 := 1
def receiveBit : UInt64 := 2
def grantBit : UInt64 := 4
def revokeBit : UInt64 := 8

/-- The endpoint-rights word of `rights` (read and write are not endpoint
rights and have no bit). -/
def rightsCode (rights : Rights) : UInt64 :=
  (if rights.send then sendBit else 0) + (if rights.receive then receiveBit else 0) +
    (if rights.grant then grantBit else 0) + (if rights.revoke then revokeBit else 0)

/-- Witness answers outside rights words: an unregistered name, and a
registered capability that the directory cannot attenuate to send-only
(it lacks send or grant). -/
def unregisteredCode : UInt64 := 0x100
def deniedCode : UInt64 := 0x200

/-- The rights decision of a resolution: the delivered rights, if any. -/
def delivered (held : Rights) : Option Rights :=
  if held.grant && rightsSubset sendOnly held then some sendOnly else none

/-- An accepted resolution delivers exactly `delivered` of the held rights. -/
theorem resolve_delivered (st : State) (d : Directory) (client : SubjectId)
    (clientSlot : SlotId) (name : Name) (slot : SlotId)
    (h : (resolve st d client clientSlot name).2 = .resolved slot) :
    ∃ heldSlot held deliveredCap,
      slotOf d name = some heldSlot ∧ st.slots d.subject heldSlot = some held ∧
      (resolve st d client clientSlot name).1.slots client clientSlot = some deliveredCap ∧
      delivered held.rights = some deliveredCap.rights := by
  obtain ⟨_, heldSlot, held, cap, hslot, hheld, hcap, _, _, _, hrights, _, hsubset, hgrant⟩ :=
    resolve_resolved_held sendOnly sendOnly_attenuates st d client clientSlot name slot h
  refine ⟨heldSlot, held, cap, hslot, hheld, hcap, ?_⟩
  rw [hrights] at hsubset ⊢
  simp [delivered, hgrant, hsubset]

/-- Allocation-free boot witness of the directory's rights decision.
`registered` is 0 for an unregistered name; `held` is the directory's
endpoint-rights word for the registered capability. The answer is the
delivered rights word (send only), `unregisteredCode`, `deniedCode`, or 0
for a held word outside the four endpoint bits. -/
@[export leanos_directory_resolve]
def directoryResolve (registered held : UInt64) : UInt64 :=
  if registered == 0 then unregisteredCode
  else if held > 15 then 0
  else if (held &&& sendBit) == sendBit && (held &&& grantBit) == grantBit then sendBit
  else deniedCode

/-- The witness is the model's decision for every endpoint rights value. -/
theorem directoryResolve_agrees (held : Rights) :
    directoryResolve 1 (rightsCode held) =
      match delivered held with
      | some rights => rightsCode rights
      | none => deniedCode := by
  obtain ⟨read, write, send, receive, grant, revoke⟩ := held
  cases read <;> cases write <;> cases send <;> cases receive <;> cases grant <;>
    cases revoke <;> rfl

/-- An unregistered name gets the unregistered answer whatever is held. -/
theorem directoryResolve_unregistered (held : UInt64) :
    directoryResolve 0 held = unregisteredCode := rfl

/-- The witness never answers a rights word other than send-only, and answers
it only when the held word has both send and grant. -/
theorem directoryResolve_no_amplification (registered held : UInt64)
    (h : directoryResolve registered held < 0x100) :
    directoryResolve registered held = 0 ∨
      (directoryResolve registered held = sendBit ∧
        held &&& sendBit = sendBit ∧ held &&& grantBit = grantBit) := by
  unfold directoryResolve at h ⊢
  by_cases h0 : (registered == 0) = true
  · simp only [h0, ↓reduceIte, unregisteredCode] at h
    exact absurd h (by decide)
  · simp only [h0, Bool.false_eq_true, ↓reduceIte] at h ⊢
    by_cases h15 : held > 15
    · simp [h15]
    · simp only [h15, ↓reduceIte] at h ⊢
      by_cases hb : ((held &&& sendBit) == sendBit && (held &&& grantBit) == grantBit) = true
      · simp only [Bool.and_eq_true, beq_iff_eq] at hb
        simp [hb]
      · simp only [hb, Bool.false_eq_true, ↓reduceIte, deniedCode] at h
        exact absurd h (by decide)

/-! ## The boot run as a model script

The `endpoint-directory` image: the server (subject 2) holds endpoint 14 with
send, receive and grant, and registers it under `bootName`; the client
(subject 1) resolves `bootName`, then resolves `bootMissing`. -/

def bootDirectorySubject : SubjectId := 3
def bootServer : SubjectId := 2
def bootClient : SubjectId := 1
def bootEndpoint : ObjectId := 14
def bootRequestEndpoint : ObjectId := 12
def bootName : Name := 0x4543484f  -- "ECHO"
def bootMissing : Name := 0x4e4f4e45  -- "NONE"

/-- The boot authority, four slots per subject as in the image's kernel
table: the client's send-only capability for the directory's request
endpoint 12 in its slot 0, the server's capability for endpoint 14 with send,
receive and grant in its slot 0, and the directory's receive capability for
endpoint 12 in its slot 0. -/
def bootState : State :=
  installRoot
    (installRoot
      (installRoot
        { subjects := fun s => s == 1 || s == 2 || s == 3
          objects := fun o => o == bootEndpoint || o == bootRequestEndpoint
          kinds := fun o =>
            if o == bootEndpoint || o == bootRequestEndpoint then some .endpoint else none
          slotCapacity := fun _ => 4
          slots := fun _ _ => none }
        bootClient 0 bootRequestEndpoint .endpoint { send := true })
      bootServer 0 bootEndpoint .endpoint { send := true, receive := true, grant := true })
    bootDirectorySubject 0 bootRequestEndpoint .endpoint { receive := true }

def bootDirectory : Directory := { subject := bootDirectorySubject, entries := [] }

/-- The server registers `bootName` into directory slot 1. -/
def bootRegistered : State × Directory × Answer :=
  register bootState bootDirectory bootServer 0 1 bootName

/-- The client resolves `bootName` into its slot 1. -/
def bootResolved : State × Answer :=
  resolve bootRegistered.1 bootRegistered.2.1 bootClient 1 bootName

/-- The client then resolves `bootMissing`. -/
def bootMissed : State × Answer :=
  resolve bootResolved.1 bootRegistered.2.1 bootClient 1 bootMissing

theorem boot_registered : bootRegistered.2.2 = .registered := by decide

theorem boot_resolved : bootResolved.2 = .resolved 1 := by decide

/-- The miss changes nothing. -/
theorem boot_missed : bootMissed = (bootResolved.1, .miss .unregistered) :=
  resolve_unregistered sendOnly bootResolved.1 bootRegistered.2.1 bootClient 1 bootMissing
    (by decide)

/-- The client's resolved capability is send-only on endpoint 14. -/
theorem boot_client_capability :
    (bootResolved.1.slots bootClient 1).map (fun c => (c.object, c.kind, c.rights)) =
      some (bootEndpoint, .endpoint, sendOnly) := by
  decide

/-- The directory's registered capability holds send and grant, so the
witness answers send-only for it, and the unregistered answer for the miss. -/
theorem boot_witness :
    directoryResolve 1 (rightsCode registeredRights) = sendBit ∧
      directoryResolve 0 0 = unregisteredCode := by
  decide

end LeanOS.EndpointDirectory
