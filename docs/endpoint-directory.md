# Endpoint directory

Issue #485 adds the first name service: a ring-3 directory subject that
resolves a name to an attenuated, send-only endpoint capability. It follows
the Phase 3 shape: one subject, one capability, one theorem, one QEMU
transcript.

## The model

`LeanOS/EndpointDirectory.lean` layers the directory over an unmodified
`Capability.State`, so the capability theorems (in particular SC-CAP-AUTH)
apply unchanged.

- A **name** is one 64-bit word. There are no hierarchical or string names.
- A **directory** is a subject and its registrations: each name maps to one of
  the directory's own slots.
- **`register`**: a server delegates the capability in one of its slots into
  an empty directory slot, with `Capability.copy`, attenuated to
  `registeredRights` (send and grant). A name that is already registered is
  the typed miss `duplicate` and changes nothing.
- **`resolveWith offered`**: a registered name is answered by
  `Capability.copy` of the directory's capability for that name into the
  client's slot, requesting `offered`. That copy needs the directory's grant
  right, `offered` a subset of what the directory holds, and rights valid for
  the object's kind. An unregistered name is the typed miss `unregistered`.
  A refused copy is the typed miss `denied` with the copy's own reason.
- **`resolve`** is `resolveWith sendOnly`: the directory offers send and
  nothing else.

The theorems assume only that the directory's policy offers at most send
(`AttenuatesToSend offered`):

| Theorem | Statement |
| --- | --- |
| `resolve_resolved_held` | A resolved name delivers a capability for the same endpoint the directory holds under that name, with exactly the offered rights. Those are a subset of the directory's rights and of send-only, and the directory's capability holds grant. |
| `resolve_no_amplification` | After a resolution, every authority of every subject existed before, or is the client's send right over an endpoint on which the directory held send and grant. |
| `resolve_only_send` | A resolution never gives receive, grant, revoke, read or write to anyone who lacked it. |
| `resolve_new_authority_held` | New authority is always authority the directory already had. |
| `resolve_unregistered`, `resolve_miss_unchanged` | An unregistered name is the typed miss `unregistered`, and every miss leaves the capability state unchanged. |

`LeanOS.SecurityClaims` restates them as SC-DIRECTORY-NO-AMPLIFICATION
(`endpoint_directory_no_amplification`) and SC-DIRECTORY-MISS
(`endpoint_directory_miss_transfers_nothing`). See
[security-claims.md](security-claims.md) for the rows and their exclusions.

The negative fixture `tests/negative/AmplifyingEndpointDirectory.lean` builds a
directory that offers send and receive. Its policy is not `AttenuatesToSend`,
so the claim cannot be instantiated for it, and `check.sh` requires the
fixture to fail to typecheck with that diagnostic.

## The boot witness

The kernel encodes endpoint rights as bits: send 1, receive 2, grant 4,
revoke 8. `directoryResolve registered held` is the allocation-free export
`leanos_directory_resolve`:

- 0x100 (`unregisteredCode`) when the name is not registered;
- 1 (send only) when the held word has send and grant;
- 0x200 (`deniedCode`) otherwise;
- 0 for a held word outside the four bits.

`directoryResolve_agrees` proves that it equals the model's rights decision
(`delivered`) for every endpoint rights value, and
`directoryResolve_no_amplification` that it never answers more than send. The
model oracle replays it as adapter `EndpointDirectory.resolve` (id 24) over
20 vectors, `hosted_directory_resolve_vectors_exact`.

## The endpoint-directory image

The `endpoint-directory` scenario boots three subjects in their own address
spaces, as in the `three-subject` image:

- **C, the directory**, built from `subjects/directory` with the subject
  template (#484, [subjects.md](subjects.md)) and linked into slot C;
- **B, a server**, in `boot.S`;
- **A, a client**, in `boot.S`.

### Capabilities

Every subject has a kernel-owned table of four slots, and every request names
a slot of the caller's own table (RDX):

| Subject | Slot 0 at boot | Gains |
| --- | --- | --- |
| A (1), client | endpoint 12, send | slot 1: endpoint 14, send (from the directory) |
| B (2), server | endpoint 14, send, receive and grant | nothing |
| C (3), directory | endpoint 12, receive | slot 1: endpoint 14, send and grant (from B) |

The table changes only by two copies. Each is checked like `Capability.copy`:
the source holds grant, and the delegated rights are a nonempty subset of the
source's rights.

### Syscalls

| Number | Subject | Operation |
| --- | --- | --- |
| 80 | B | register: delegate slot RDX with rights RCX under the name RBX |
| 81 | A | call the directory through slot RDX with the name RBX; the answer is the installed slot, or the typed miss 0x100 |
| 7 | any | receive through slot RDX (needs the receive right) |
| 83 | C | describe the last received message: kind, and for a registration the directory slot and rights |
| 82 | C | reply through the one-shot reply capability with a copy of slot RBX attenuated to RCX (0xff and 0 for none), then receive through slot RDX |
| 8 | A | send RBX through slot RDX (needs the send right) |
| 9 | B | report the delivered word and its preserved initial-context canary (final) |

A request the caller's table does not allow is refused without effect. It
returns `1 | reason << 8`, with typed reasons, and the kernel records it as
`@10/CAP@ event=refuse`.

### The directory's own attenuation

The directory keeps its registrations (name, slot, rights) in its own memory.
For a call it looks the name up. If it holds send and grant for that name, it
offers the send right only; otherwise it offers nothing. The kernel then
checks the answer:

1. The copy check above, against C's table.
2. The witness: `leanos_directory_resolve(registered, held)` must equal the
   offered rights. A directory that offered receive as well would pass the
   copy check, because it holds receive, but fail here.
3. The kernel keeps a shadow of the registrations it routed. It uses the
   shadow only to check the directory's answer against the model:
   - a registered name must be answered from exactly the registered slot;
   - a name the shadow does not hold must be answered with no capability,
     the witness must give 0x100, and the client's table must be unchanged.

Any disagreement stops the machine (`directory-model-decision`,
`directory-model-miss`). Before any subject runs, the kernel also checks the
witness against its own copy rule for all 16 rights words
(`@10/CAP@ event=install ... model=agree`).

### The run

1. The kernel checks C's slot and page tables and the witness, then enters C.
   C blocks on a receive through slot 0.
2. B is dispatched from its initial context. It registers endpoint 14 under
   `ECHO`, delegating send and grant: the kernel installs the copy in C's
   slot 1, and the registration becomes C's message. B then blocks on a
   receive through its slot 0.
3. A is dispatched fresh and calls the directory with `ECHO`. The kernel
   creates A's one-shot reply capability and queues the call behind the
   registration, and C runs.
4. C records the registration, receives the call, and replies with slot 1
   attenuated to send. The witness agrees, and the kernel installs endpoint
   14, send only, in A's slot 1. C blocks, and A resumes with answer 1.
5. A tries to receive through slot 1. It is refused with `missing-right`.
6. A calls the directory with `NONE`. C finds no registration and replies
   with no capability. The witness gives the typed miss, A's table is
   unchanged, and A resumes with 0x100.
7. A sends `PING` through slot 1. B is woken with exactly that word and
   reports it, together with the canary from its initial context.
8. The kernel checks the counts and A's table (endpoint 14, send only, in
   slot 1), then prints `@10/FINAL@ status=PASS`.

`scripts/expectations/endpoint-directory.transcript` is the exact expected
transcript. `EndpointDirectory.bootRegistered`, `bootResolved` and
`bootMissed` are the same run in the model: `boot_registered`,
`boot_resolved`, `boot_missed` and `boot_client_capability`.

```sh
python3 scripts/run-emulator-evidence.py run --scenario endpoint-directory --output endpoint-directory.json
```

## Exclusions

- **No refinement.** The QEMU run is one finite trace. The witness check
  covers the rights decision only. Nothing proves that the C kernel,
  `boot.S`, the subject build rule or the ring-3 directory implement the
  model.
- **No registration policy.** Any holder of a grant-bearing endpoint
  capability could register any unused name. The run has one registration.
  Who may register which name is not modeled.
- **No names beyond words.** There are no hierarchical or string names, no
  persistence, and no unregistration.
- **No new revocation.** Revocation is the existing `Capability.revoke`. The
  run revokes nothing.
- **No confidentiality of the name space.** A miss tells the caller that a
  name is not registered.
- **No scheduling claim.** The schedule is the kernel's fixed state machine,
  as in the other three-subject images.
