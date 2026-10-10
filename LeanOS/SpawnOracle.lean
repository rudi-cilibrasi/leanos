import LeanOS.FailStop.SpawnTraces
import LeanOS.FailStop.Evidence
import LeanOS.CompositeDispatcher

/-!
# Spawn: canonical command encoding and adversarial oracle vectors

ADR 0010 gate item 5 for explicit spawn (#489).  This is a **hosted, Lean-side
oracle only**.  The spawn command is not part of the generated boot
dispatcher (`CompositeDispatcher.dispatch`), has no C export, and is not a
ring-3 syscall: the version-one boot command decoder rejects the spawn tag as
an unknown command (`boot_dispatcher_rejects_spawn_tag`).

## Encoding

The command uses the dispatcher's `CommandWords` shape:

| Word | Meaning |
| --- | --- |
| `tag` | `0x7001` (`spawnCommandTag`) |
| `arg0` | spawn-capability generation word; zero is never issued and is rejected |
| `arg1` | endpoint handle word, decoded by `CapabilityHandle.decode` at the spawn |
| `arg2` | requested rights mask: bit 0 read, 1 write, 2 send, 3 receive, 4 grant, 5 revoke; other bits reserved |
| `arg3` | reserved, must be zero |

`decodeSpawn (encodeSpawn request) = .ok request` for every request with a
nonzero spawn word, and every word sequence that decodes is the encoding of
what it decodes to (`encodeSpawn_decodeSpawn`), so the encoding is canonical.

The result word is `0x7001` with status byte `0x01` in bits 16..23 for an
accepted spawn (the child and its address space are returned separately), or
with `0x80 + code` there for a rejection, one code per typed error
(`spawnErrorCode`, injective by `decodeSpawnErrorCode_spawnErrorCode`).

## Vectors

`spawnOracleSeed plan` is the dispatcher's well-formed seed
(`compositeDispatcherInitial`), in which subject 2 is current and holds
endpoint 10 with every endpoint right in slot 0 (handle word `0x30000`), with
the issuers set past the seed's histories and subject 2 granted spawn
generation 1.  `spawnVectors` covers every failure point, both issuer
exhaustions, stale and malformed parent handles, a parent handle presented by
the child, never-reuse after termination, and isolation of every other
subject; `spawn_vectors_pass` checks each one, including that every rejection
returns the pre-state's observable projections.
-/
namespace LeanOS.SpawnOracle

open LeanOS
open LeanOS.FailStop
open LeanOS.CompositeDispatcher (CommandWords DecodeError)

/-! ## Canonical encoding -/

def spawnCommandTag : UInt64 := 0x7001

def encodeRights (rights : Capability.Rights) : UInt64 :=
  (if rights.read then 1 else 0) + (if rights.write then 2 else 0) +
    (if rights.send then 4 else 0) + (if rights.receive then 8 else 0) +
    (if rights.grant then 16 else 0) + (if rights.revoke then 32 else 0)

def decodeRights (word : UInt64) : Except DecodeError Capability.Rights :=
  if 64 ≤ word then .error .reservedBits
  else .ok ⟨word &&& 1 != 0, word &&& 2 != 0, word &&& 4 != 0, word &&& 8 != 0,
    word &&& 16 != 0, word &&& 32 != 0⟩

def encodeSpawn (request : SpawnRequest) : CommandWords :=
  { tag := spawnCommandTag, arg0 := request.spawnWord, arg1 := request.endpointWord,
    arg2 := encodeRights request.rights, arg3 := 0 }

def decodeSpawn (words : CommandWords) : Except DecodeError SpawnRequest :=
  if words.tag != spawnCommandTag then .error .unknownCommand
  else if words.arg3 != 0 then .error .reservedBits
  else if words.arg0 = 0 then .error .noncanonicalArguments
  else match decodeRights words.arg2 with
    | .error reason => .error reason
    | .ok rights => .ok { spawnWord := words.arg0, endpointWord := words.arg1, rights }

theorem decodeRights_encodeRights (rights : Capability.Rights) :
    decodeRights (encodeRights rights) = .ok rights := by
  obtain ⟨read, write, send, receive, grant, revoke⟩ := rights
  cases read <;> cases write <;> cases send <;> cases receive <;> cases grant <;> cases revoke <;>
    rfl

/-- Every in-range rights word re-encodes to itself. -/
def rightsWordCanonical (index : Nat) : Bool :=
  match decodeRights (UInt64.ofNat index) with
  | .ok rights => encodeRights rights == UInt64.ofNat index
  | .error _ => true

theorem rightsWords_canonical : (List.range 64).all rightsWordCanonical = true := by
  decide

theorem encodeRights_decodeRights_all (index : Nat) (small : index < 64)
    (rights : Capability.Rights) (decoded : decodeRights (UInt64.ofNat index) = .ok rights) :
    encodeRights rights = UInt64.ofNat index := by
  have := List.all_eq_true.1 rightsWords_canonical index (List.mem_range.2 small)
  simp only [rightsWordCanonical, decoded, beq_iff_eq] at this
  exact this

theorem encodeRights_decodeRights (word : UInt64) (rights : Capability.Rights)
    (decoded : decodeRights word = .ok rights) : encodeRights rights = word := by
  have small : word.toNat < 64 := by
    unfold decodeRights at decoded
    split at decoded
    · contradiction
    · next bound =>
      have : ¬(64 ≤ word.toNat) := by
        intro h; apply bound; exact UInt64.le_iff_toNat_le.2 (by simpa using h)
      omega
  have := encodeRights_decodeRights_all word.toNat small rights
    (by simpa [UInt64.ofNat_toNat] using decoded)
  simpa [UInt64.ofNat_toNat] using this

/-- **Round trip.**  Every request with a nonzero spawn word decodes back from
its encoding. -/
theorem decodeSpawn_encodeSpawn (request : SpawnRequest) (nonzero : request.spawnWord ≠ 0) :
    decodeSpawn (encodeSpawn request) = .ok request := by
  simp [decodeSpawn, encodeSpawn, spawnCommandTag, nonzero, decodeRights_encodeRights]

/-- **Canonical.**  A word sequence that decodes is exactly the encoding of
its decoded request: no second encoding of the same request exists. -/
theorem encodeSpawn_decodeSpawn (words : CommandWords) (request : SpawnRequest)
    (decoded : decodeSpawn words = .ok request) : encodeSpawn request = words := by
  unfold decodeSpawn at decoded
  split at decoded
  · contradiction
  next tag =>
  split at decoded
  · contradiction
  next reserved =>
  split at decoded
  · contradiction
  split at decoded
  · contradiction
  next rights rightsDecoded =>
  cases decoded
  have tagEq : words.tag = spawnCommandTag := by simpa using tag
  have reservedEq : words.arg3 = 0 := by simpa using reserved
  have rightsEq := encodeRights_decodeRights _ _ rightsDecoded
  cases words
  simp_all [encodeSpawn]

/-- The generated boot dispatcher's version-one command decoder does not know
the spawn tag: spawn is not reachable through the boot boundary. -/
theorem boot_dispatcher_rejects_spawn_tag (arg0 arg1 arg2 arg3 : UInt64) :
    CompositeDispatcher.decodeCommand
      { tag := spawnCommandTag, arg0, arg1, arg2, arg3 } = .error .reservedBits := by
  simp [CompositeDispatcher.decodeCommand, spawnCommandTag, CompositeDispatcher.abiVersion]

/-! ## Result words -/

def createErrorCode : SubjectLifecycle.CreateError → UInt64
  | .alreadyLive => 0x04 | .alreadyIssued => 0x05

def addressSpaceErrorCode : VirtualMapping.CreateError → UInt64
  | .invalidSubject => 0x10 | .outOfRange => 0x11 | .generationExhausted => 0x12
  | .occupiedSlot => 0x13 | .identifierAlreadyIssued => 0x14 | .identifierLive => 0x15

def handleErrorCode : CapabilityHandle.WordResolveDenial → UInt64
  | .malformed .reservedSlot => 0x20 | .malformed .reservedGeneration => 0x21
  | .denied .invalidSubject => 0x22 | .denied .outOfRange => 0x23
  | .denied .staleHandle => 0x24 | .denied .kindMismatch => 0x25

def denialCode : Capability.Denial → UInt64
  | .invalidSubject => 0x30 | .staleSlot => 0x31 | .outOfRange => 0x32 | .occupiedSlot => 0x33
  | .full => 0x34 | .emptyRights => 0x35 | .missingGrant => 0x36 | .rightsNotSubset => 0x37
  | .missingRevoke => 0x38 | .objectMismatch => 0x39 | .kindMismatch => 0x3a
  | .invalidRights => 0x3b | .generationExhausted => 0x3c | .runtimeAuthorityRequired => 0x3d

/-- One code per typed spawn error. -/
def spawnErrorCode : SpawnError → UInt64
  | .missingSpawnRight => 0x01
  | .staleSpawnCapability => 0x02
  | .identityExhausted => 0x03
  | .identityRejected reason => createErrorCode reason
  | .slotTableFull => 0x06
  | .addressSpaceIdentityExhausted => 0x07
  | .addressSpaceUnavailable => 0x08
  | .endpointNotGrantable => 0x09
  | .invalidRights => 0x0a
  | .rightsNotSubset => 0x0b
  | .addressSpaceRejected reason => addressSpaceErrorCode reason
  | .endpointHandle reason => handleErrorCode reason
  | .endpointCopyRejected reason => denialCode reason

def allSpawnErrors : List SpawnError :=
  [.missingSpawnRight, .staleSpawnCapability, .identityExhausted,
    .identityRejected .alreadyLive, .identityRejected .alreadyIssued, .slotTableFull,
    .addressSpaceIdentityExhausted, .addressSpaceUnavailable, .endpointNotGrantable,
    .invalidRights, .rightsNotSubset,
    .addressSpaceRejected .invalidSubject, .addressSpaceRejected .outOfRange,
    .addressSpaceRejected .generationExhausted, .addressSpaceRejected .occupiedSlot,
    .addressSpaceRejected .identifierAlreadyIssued, .addressSpaceRejected .identifierLive,
    .endpointHandle (.malformed .reservedSlot), .endpointHandle (.malformed .reservedGeneration),
    .endpointHandle (.denied .invalidSubject), .endpointHandle (.denied .outOfRange),
    .endpointHandle (.denied .staleHandle), .endpointHandle (.denied .kindMismatch),
    .endpointCopyRejected .invalidSubject, .endpointCopyRejected .staleSlot,
    .endpointCopyRejected .outOfRange, .endpointCopyRejected .occupiedSlot,
    .endpointCopyRejected .full, .endpointCopyRejected .emptyRights,
    .endpointCopyRejected .missingGrant, .endpointCopyRejected .rightsNotSubset,
    .endpointCopyRejected .missingRevoke, .endpointCopyRejected .objectMismatch,
    .endpointCopyRejected .kindMismatch, .endpointCopyRejected .invalidRights,
    .endpointCopyRejected .generationExhausted,
    .endpointCopyRejected .runtimeAuthorityRequired]

def decodeSpawnErrorCode (code : UInt64) : Option SpawnError :=
  allSpawnErrors.find? fun error => spawnErrorCode error == code

theorem allSpawnErrors_complete (error : SpawnError) : error ∈ allSpawnErrors := by
  cases error <;> (try rename_i reason; cases reason) <;>
    (try rename_i inner; cases inner) <;> decide

theorem allSpawnErrors_codes_distinct :
    (allSpawnErrors.map spawnErrorCode).Nodup := by decide

/-- **Injective error codes.**  Decoding a rejection code recovers the typed
error exactly. -/
theorem decodeSpawnErrorCode_spawnErrorCode (error : SpawnError) :
    decodeSpawnErrorCode (spawnErrorCode error) = some error := by
  cases error <;> (try rename_i reason; cases reason) <;>
    (try rename_i inner; cases inner) <;> decide

def encodeSpawnResult : SpawnResult → UInt64
  | .spawned _ _ => ((0x01 : UInt64) <<< 16) ||| spawnCommandTag
  | .rejected error => (((0x80 : UInt64) + spawnErrorCode error) <<< 16) ||| spawnCommandTag

/-! ## The hosted oracle -/

/-- Decode, run under the latch, and encode.  A malformed command is reported
with the dispatcher's error word and never runs. -/
def oracleStep (state : CompositeState) (words : CommandWords) : CompositeState × UInt64 :=
  match decodeSpawn words with
  | .error reason => (state, CompositeDispatcher.errorWord reason)
  | .ok request =>
      match spawnGate state (.spawn request) with
      | { state := next, result := .completed (.spawn result) } => (next, encodeSpawnResult result)
      | { state := next, result := .rejectedBusy } => (next, 0xfe01)
      | { state := next, result := .rejectedHalted _ } => (next, 0xfe02)
      | { state := next, result := _ } => (next, 0xfe03)

/-- The observable projections a vector compares: issuer counters, the
subject and issued-subject registries, capability slots, object liveness and
kind, the capability identity frontier, address-space owners, and the spawn
record, over the identifiers the vectors use. -/
structure Observation where
  subjectNext : Nat
  objectNext : Nat
  nextIdentity : Nat
  subjects : List Bool
  issued : List Bool
  slots : List (List (Option Capability.Capability))
  objects : List Bool
  kinds : List (Option Capability.ObjectKind)
  owners : List (Option Nat)
  authority : List (Option SpawnCapability)
  parents : List (Option Nat)
  deriving DecidableEq, Repr

def observedSubjects : List Nat := [1, 2, 3, 4, 5]
def observedObjects : List Nat := [1, 2, 10, 20, 21, 22, 23]

def observe (state : CompositeState) : Observation :=
  { subjectNext := state.issuers.subject.next
    objectNext := state.issuers.object.next
    nextIdentity := state.capabilities.nextIdentity
    subjects := observedSubjects.map state.capabilities.subjects
    issued := observedSubjects.map state.lifecycle.issuedSubjects
    slots := observedSubjects.map fun subject =>
      (List.range 4).map (state.capabilities.slots subject)
    objects := observedObjects.map state.capabilities.objects
    kinds := observedObjects.map state.capabilities.kinds
    owners := observedObjects.map state.virtualMemory.owner
    authority := observedSubjects.map state.spawn.authority
    parents := observedSubjects.map state.spawn.parent }

/-- The oracle seed: the dispatcher's seed with the issuers past its
histories and spawn generation 1 granted to subject 2. -/
def spawnOracleSeed (plan : BootPageTablePlan.Plan) : CompositeState :=
  { compositeDispatcherInitial plan with
    issuers := { subject := { next := 3 }, object := { next := 21 } }
    spawn := { authority := fun subject => if subject = 2 then some { generation := 1 } else none
               nextGeneration := 2 } }

/-- The seed is the dispatcher's well-formed seed with only the issuers and
the spawn record changed, which no authoritative conjunct reads. -/
theorem spawnOracleSeed_authoritativeRuntimeWellFormed (plan : BootPageTablePlan.Plan) :
    AuthoritativeRuntimeWellFormed (spawnOracleSeed plan) := by
  have holds := compositeDispatcherInitial_authoritativeRuntimeWellFormed plan
  rw [authoritativeRuntimeWellFormed_iff_all] at holds ⊢
  intro invariant member
  apply invariant.dependsOn (compositeDispatcherInitial plan) _ _ (holds invariant member)
  intro projection supported
  cases projection <;> try rfl
  case issuers =>
    have issuers : ∀ invariant, invariant ∈ authoritativeInvariants →
        !invariant.support.contains .issuers = true := by decide
    have := issuers invariant member
    simp only [decide_eq_true_eq] at supported
    simp [supported] at this
  case spawn =>
    have := List.all_eq_true.1 spawn_unsupported invariant (List.mem_append_left _ member)
    simp only [decide_eq_true_eq] at supported
    simp [supported] at this

/-- Subject 2's endpoint-10 handle word (slot 0, generation 3). -/
def parentEndpointWord : UInt64 := 0x30000

def sendOnly : Capability.Rights := { send := true }

def request (spawnWord endpointWord : UInt64) (rights : Capability.Rights) : CommandWords :=
  encodeSpawn { spawnWord, endpointWord, rights }

/-- The accepted command. -/
def acceptedCommand : CommandWords := request 1 parentEndpointWord sendOnly

def withSubjectNext (state : CompositeState) (next : Nat) : CompositeState :=
  { state with issuers := { state.issuers with subject := { next } } }

def withObjectNext (state : CompositeState) (next : Nat) : CompositeState :=
  { state with issuers := { state.issuers with object := { next } } }

def withSlotCapacity (state : CompositeState) (subject capacity : Nat) : CompositeState :=
  let capabilities := { state.capabilities with
    slotCapacity := fun candidate =>
      if candidate = subject then capacity else state.capabilities.slotCapacity candidate }
  { state with
    capabilities
    lifecycle := { state.lifecycle with capabilities }
    virtualMemory := { state.virtualMemory with
      memory := { state.virtualMemory.memory with capabilities } } }

/-- Subject 2 first delegates a send-and-grant copy of endpoint 10 into its
own slot 3 (generation 6), through the authoritative gate. -/
def withNarrowEndpoint (state : CompositeState) (rights : Capability.Rights) : CompositeState :=
  (authoritativeGate state (.ordinary (.capabilityCopy 0 2 3 rights))).state

/-- One adversarial vector: a pre-state, a command, the expected result word,
and whether the post-state must be observably the pre-state. -/
structure SpawnVector where
  name : String
  pre : CompositeState
  words : CommandWords
  expected : UInt64
  rollback : Bool

def rejectWord (error : SpawnError) : UInt64 := encodeSpawnResult (.rejected error)

def acceptWord : UInt64 := encodeSpawnResult (.spawned 0 0)

def spawnVectors (plan : BootPageTablePlan.Plan) : List SpawnVector :=
  let seed := spawnOracleSeed plan
  [ { name := "accepted", pre := seed, words := acceptedCommand, expected := acceptWord,
      rollback := false }
  , { name := "missing spawn right", pre := (revokeSpawnAuthority seed 2),
      words := acceptedCommand, expected := rejectWord .missingSpawnRight, rollback := true }
  , { name := "stale spawn generation", pre := seed,
      words := request 2 parentEndpointWord sendOnly,
      expected := rejectWord .staleSpawnCapability, rollback := true }
  , { name := "regranted spawn capability, old generation",
      pre := (grantSpawnAuthority (revokeSpawnAuthority seed 2) 2).1,
      words := acceptedCommand, expected := rejectWord .staleSpawnCapability, rollback := true }
  , { name := "zero spawn word is noncanonical", pre := seed,
      words := request 0 parentEndpointWord sendOnly,
      expected := CompositeDispatcher.errorWord .noncanonicalArguments, rollback := true }
  , { name := "reserved rights bit", pre := seed,
      words := { acceptedCommand with arg2 := 64 },
      expected := CompositeDispatcher.errorWord .reservedBits, rollback := true }
  , { name := "reserved argument", pre := seed,
      words := { acceptedCommand with arg3 := 1 },
      expected := CompositeDispatcher.errorWord .reservedBits, rollback := true }
  , { name := "subject identities exhausted",
      pre := withSubjectNext seed LifetimeIssuer.identityReserved,
      words := acceptedCommand, expected := rejectWord .identityExhausted, rollback := true }
  , { name := "subject issuer behind a live identity", pre := withSubjectNext seed 2,
      words := acceptedCommand, expected := rejectWord (.identityRejected .alreadyLive),
      rollback := true }
  , { name := "child slot table too small", pre := withSlotCapacity seed 3 1,
      words := acceptedCommand, expected := rejectWord .slotTableFull, rollback := true }
  , { name := "object identities exhausted",
      pre := withObjectNext seed LifetimeIssuer.identityReserved,
      words := acceptedCommand, expected := rejectWord .addressSpaceIdentityExhausted,
      rollback := true }
  , { name := "address-space identifier already issued", pre := withObjectNext seed 1,
      words := acceptedCommand,
      expected := rejectWord (.addressSpaceRejected .identifierAlreadyIssued), rollback := true }
  , { name := "address-space identifier owned as memory", pre := withObjectNext seed 21 |>
        fun state => { state with lifecycle := { state.lifecycle with
          ownedMemory := fun object => if object = 21 then some (2, 4)
            else state.lifecycle.ownedMemory object } },
      words := acceptedCommand, expected := rejectWord .addressSpaceUnavailable,
      rollback := true }
  , { name := "malformed endpoint handle", pre := seed,
      words := request 1 0xffff sendOnly,
      expected := rejectWord (.endpointHandle (.malformed .reservedSlot)), rollback := true }
  , { name := "stale endpoint generation", pre := seed,
      words := request 1 0x40000 sendOnly,
      expected := rejectWord (.endpointHandle (.denied .staleHandle)), rollback := true }
  , { name := "endpoint handle out of range", pre := seed,
      words := request 1 0x30007 sendOnly,
      expected := rejectWord (.endpointHandle (.denied .outOfRange)), rollback := true }
  , { name := "address-space handle named as endpoint", pre := seed,
      words := request 1 0x40001 sendOnly,
      expected := rejectWord (.endpointHandle (.denied .kindMismatch)), rollback := true }
  , { name := "endpoint without grant", pre := withNarrowEndpoint seed { send := true },
      words := request 1 0x60003 sendOnly,
      expected := rejectWord .endpointNotGrantable, rollback := true }
  , { name := "rights invalid for an endpoint", pre := seed,
      words := request 1 parentEndpointWord { read := true },
      expected := rejectWord .invalidRights, rollback := true }
  , { name := "rights exceed the parent's", pre := withNarrowEndpoint seed
        { send := true, grant := true },
      words := request 1 0x60003 { receive := true },
      expected := rejectWord .rightsNotSubset, rollback := true } ]

/-- Run one vector. -/
def runVector (vector : SpawnVector) : CompositeState × UInt64 :=
  oracleStep vector.pre vector.words

def vectorPasses (vector : SpawnVector) : Bool :=
  let (post, word) := runVector vector
  word == vector.expected &&
    (!vector.rollback || observe post == observe vector.pre)

/-! ## Accepted-spawn, isolation, and never-reuse vectors -/

def acceptedPost (plan : BootPageTablePlan.Plan) : CompositeState :=
  (oracleStep (spawnOracleSeed plan) acceptedCommand).1

/-- The child's expected slots: endpoint 10 with send only, derived from the
parent's identity 3, and the root of address space 21. -/
def expectedChildSlots : List (Option Capability.Capability) :=
  [ some ⟨10, .endpoint, sendOnly, 7, some 3⟩
  , some ⟨21, .addressSpace, VirtualMapping.addressSpaceRootRights, 6, none⟩
  , none, none ]

def acceptedChecks (plan : BootPageTablePlan.Plan) : Bool :=
  let pre := spawnOracleSeed plan
  let post := acceptedPost plan
  -- the child is identity 3, its address space object 21
  (spawn pre { spawnWord := 1, endpointWord := parentEndpointWord, rights := sendOnly }).result
      == .spawned 3 21 &&
  -- inheritance set exactly
  (List.range 4).map (post.capabilities.slots 3) == expectedChildSlots &&
  -- isolation: subjects 1 and 2 keep their slots, the spawn table is unchanged
  (List.range 4).map (post.capabilities.slots 1) == (List.range 4).map (pre.capabilities.slots 1) &&
  (List.range 4).map (post.capabilities.slots 2) == (List.range 4).map (pre.capabilities.slots 2) &&
  post.spawn.authority 3 == none && post.spawn.authority 2 == pre.spawn.authority 2 &&
  post.spawn.parent 3 == some 2 &&
  -- the child cannot use the parent's handle word: it is stale in the child's space
  (match CapabilityHandle.resolveCurrent post.capabilities { caller := 3 } parentEndpointWord
      .endpoint with
    | .error (.denied .staleHandle) => true
    | _ => false) &&
  -- nothing else: not runnable, not queued, empty address space, zero budget
  post.lifecycle.runnable 3 == false && !(post.scheduler.ready.contains 3) &&
  post.virtualMemory.owner 21 == some 3 &&
  (List.range 4).all (fun page => post.virtualMemory.mappings 21 page == none) &&
  post.budgetLimit 3 == 0

/-- Never-reuse: spawn, terminate the child, spawn again.  The second child is
identity 4 with address space 22, not the terminated identity 3. -/
def reuseChecks (plan : BootPageTablePlan.Plan) : Bool :=
  let first := acceptedPost plan
  let terminated := (authoritativeGate first (.ordinary (.terminateSubject 3))).state
  let second := oracleStep terminated acceptedCommand
  second.2 == acceptWord &&
    (spawn terminated { spawnWord := 1, endpointWord := parentEndpointWord, rights := sendOnly }).result
      == .spawned 4 22 &&
    second.1.lifecycle.issuedSubjects 3 == true && second.1.capabilities.subjects 3 == false

def allChecks (plan : BootPageTablePlan.Plan) : Bool :=
  (spawnVectors plan).all vectorPasses && acceptedChecks plan && reuseChecks plan

/-- **Every vector passes** on the sample boot plan the dispatcher uses.  This
is a closed, bounded evaluation (`native_decide`, classified `bounded-model`
in `scripts/native-decide-modules.tsv`); the plan is retained in the state
only as return evidence, which spawn never reads. -/
theorem spawn_vectors_pass :
    (match BootPageTablePlan.compile BootPageTablePlan.sampleInput with
      | .ok plan => allChecks plan
      | .error _ => false) = true := by
  native_decide

end LeanOS.SpawnOracle
