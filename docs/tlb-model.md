# Single-core TLB model

`LeanOS.TLB` models a finite 16-entry translation cache keyed by address-space
identity and virtual page. Each entry records its access context and classified
physical frame. Every cache hit is revalidated against the current encoded
page-table walk before use. Thus effective U/S, R/W, NX, CR0.WP, SMEP, SMAP,
AC, live object binding, and allocator ownership are checked at access time.

The model is sequential and uses eager invalidation. `protect` and `unmap`
publish the page-table change and remove the page's translations atomically.
Destruction removes all entries for that identity. Release conservatively
flushes the complete cache while publishing lifecycle-produced tables. CR3
switch also flushes everything; there are no PCIDs or global mappings. This is
costlier than selective release invalidation but makes publication order clear.

Lean proves successful accesses agree with a current privileged page-table
classification and current allocator ownership. It also proves affected keys
are absent when accepted unmap returns, accepted release leaves no cache hit,
accepted protection and destruction remove affected hits, cache capacity is
invariant under fill and invalidation, and every rejected unmap, protection,
release, or destruction leaves the complete cache/model state unchanged.
Executable examples exercise repeated page invalidation, space invalidation,
switch-away/back flushing, and the negative constructions. The negative
witnesses show that clearing a PTE without invalidation retains stale cache data
and that omitting address-space identity aliases equal virtual pages; the normal
access path rejects stale data because of current-walk revalidation.

We assume x86 effective-permission semantics, that serializing CR3 reload
without PCID invalidates modeled non-global translations, and that INVLPG has
completed for the named linear page before return on this single core. We also
assume page-table stores and invalidation are ordered as the atomic transition.
The ISA guarantees, compiler, assembly, QEMU, and hardware are trusted, not
proved. SMP shootdowns, PCID, global/huge pages, nested paging, speculation,
replacement performance, and concurrent mutation are outside scope.

## Canonical invalidation step (`LeanOS.StaleTranslation`)

`LeanOS.StaleTranslation.step` is the single public operation the machine
invalidation path consumes. It takes one reviewed composite `Request` (unmap,
protect, release, destroy, or a root switch) checked against the authoritative
`LeanOS.TLB` cache/virtual-mapping state, and returns the published state, an
`accepted` flag, and the exact machine `Effect`:

- `none` for a state-preserving rejection: the machine performs no invalidation;
- `page addressSpace page` for an accepted unmap or protect: one `invlpg` at the
  exact linear page;
- `space addressSpace` for an accepted destruction and `flush` for an accepted
  release or a root switch: the reviewed complete CR3 reload on the no-PCID root,
  since there are no PCIDs or global mappings whose semantics could differ.

The acting subject, active address space, mapping identity, and affected page are
derived from checked kernel state and generation-bound capability handles;
attacker words cannot select an invalidation target or claim completion. Lean
proves the accepted effect is determined by the transition and its checked target
(`unmap_accepted_effect`, `protect_accepted_effect`, `release_accepted_effect`,
`destroy_accepted_effect`, `switch_effect`), that a non-owner request is rejected
and inert (`unmap_wrong_owner_inert`, `protect_wrong_owner_inert`), that the
returned cache has the affected translation absent (`accepted_unmap_target_absent`,
`accepted_protect_target_absent`, `accepted_release_all_absent`,
`accepted_destroy_space_absent`) so a later access cannot use the old
translation, that release publishes a fully flushed cache before reuse
(`accepted_release_flushed`), and that the step preserves the bounded-cache
invariant (`step_preserves_coherent`). `applyEffect` models what the invalidation
instruction accomplishes and `applyEffect_page_absent`/`applyEffect_space_absent`/
`applyEffect_flush_absent` show the described effect is sufficient for absence.

`SC-STALE-TRANSLATION-INVALIDATION` restates the effect/target/confinement
bundle. The `LeanOS.Oracle` `StaleTranslation.scalar` block (accepted
unmap/protect, wrong-owner rejections, release/destroy/switch effects,
unmapped-page and post-reuse rejections, permission amplification, and a
malformed encoding) is replayed by the hosted generated-C oracle and in every
QEMU boot image; Lean and the generated C agree on each vector.

The canonical `CompositeDispatcher` now also has a bounded branch from its
authoritatively replayed `directMapped` state. An accepted syscall unmap of page
7 publishes reply `0x301901`, whose typed meaning is exactly
`Effect.page 2 7`; a rejected unmap of absent page 9 stutters on the complete
state and publishes `Effect.none`. `mixed_unmap_effect_confined` prevents the
accepted effect from being spliced onto another canonical pre-state or command,
and `mixed_accepted_unmap_publication_order` identifies the published
translation state with the same `StaleTranslation.step` result.

The dispatcher additionally carries a 13-edge prepare/acknowledge sequence from
`LeanOS.InvalidationPublication`. An accepted writable-to-read-only protect,
plus accepted release, destroy, and switch steps, retain the full published
pre-state while their exact page/space/flush
effect is pending. A fresh logical ticket binds each acknowledgement to the
step that issued it, so an older flush cannot acknowledge a later switch flush.
Wrong-owner and stale-release operations, mismatched effects, malformed
encodings, and wrong-state acknowledgements are inert. Only an exact
ticket/effect pair publishes the recorded successor, and bounded reuse is
disabled until release and destruction are both acknowledged with no pending
effect. The final allocation is the existing finite object-11 proof witness;
the separately modeled frame-budget path below supplies the authoritative
quota/reclamation/scrub/fresh-handle machine scenario.

The authoritative composite cleanup and root-switch paths now close the
corresponding global cache invariant. `ResumablePreemption.cleanupSubject`
uses a complete modeled flush because termination can release memory objects
mapped through roots other than the retiring subject's root.
`gate_terminateSubject_accepted_flushes_translations` proves that accepted
cleanup preserves `FailStop.RuntimeWellFormed` and leaves every cache lookup
absent; `gate_resumePreempt_accepted_flushes_translations` proves the same
global invariant and empty-cache result for an accepted save/select/restore
root switch. The merged frame-budget path additionally binds its authoritative
termination and explicit release edges to distinct generated tokens whose
typed meaning is `.flush`. In the QEMU termination/reuse path, A's PTE store,
the no-PCID CR3 flush and readback, effect completion, and released-capacity
publication are ordered before scrub or fresh-object mapping. The protocol's
pending state is carried by `CompositeState.invalidationPublication`, and
`FailStop.AuthoritativeRuntimeWellFormed.publication` requires that published
and pending cache states remain coherent. The transition-bound generated token
and concrete completion latch connect that model invariant to this bounded
machine path without claiming general model-to-binary refinement.

`FrameBudgetScenario.RetirementPublication` also carries this ordering through
the shared budget-and-scrub model rather than only through the C latch.
Preparation retains the complete pre-retirement runtime while holding the
computed termination successor privately. A wrong edge token stutters, and
fresh allocation/mapping rejects while that successor is pending. The exact
termination acknowledgement is the first transition that exposes released
capacity and frame 100 as reclaimed; only the following existing
`FrameScrub.allocate` transition scrubs the whole frame and republishes it as
fresh object 21 for B.

The full `FailStop.CompositeState` integration remains future work.
`authoritativeCurrentUnmap_accepted_publication` is a conditional refinement
lemma: it assumes that the publication record already equals the resumable TLB
projection. `bootRuntime` does not currently construct that premise, and the
ordinary authoritative gate deliberately retains the publication record while
mapping, cleanup, and root-switch operations may change the runtime projection.
Therefore this PR does not claim a boot-rooted or globally preserved
full-composite invalidation boundary. The proved public claim is the standalone
stateful publication protocol; the generated dispatcher and QEMU paths below
provide bounded tested evidence, not a refinement from the global runtime.

Every boot image then consumes that exact generated reply in a bounded
runtime-mutable machine window at virtual page 7. Address space B is first
backed by a reviewed “before” frame. The active-root path clears B's volatile
PTE, executes `invlpg (0x7000)`, and only then publishes completion; remapping
the now-uncached window to a second frame yields the reviewed “after” value.
The inactive-root path repeats the same clear with A selected, loads B's CR3,
checks the selected root and absent PTE, and only then publishes completion;
a later B reload exposes the second frame. Both paths finally restore the
boot-plan leaf. These accesses are kernel observations of the concrete
machine-path ordering.

The dedicated stale-translation image extends that bounded path through
same-frame reuse. CPL3 subject B first reads the old canary through B/page 7,
which fills a real translation, and supplies the value and address to the
canonical unmap syscall. With B's no-PCID root still selected, the kernel
clears the leaf, executes the exact `invlpg (0x7000)`, checks the absent leaf,
and publishes the generated composite reply. Only then does the one-shot reuse
adapter scrub every word of that exact physical frame, bind the generated
post-reuse fixture (fresh object 11 owns frame 4 while the retired page remains
absent), establish replacement owner/lifetime metadata, write the replacement
canary, map that exact frame present-user at A/page 7, recheck both complete
live-table relations, and publish reuse. Subject B then rereads 0x7000 without
an intervening CR3 load and takes a real CPL3 not-present page fault. The
contained handler checks that B/page 7 is still absent and the replacement
canary in the reused physical frame is intact. Only after that denial does the
entry path load A's root and return a fresh subject-A context; CPL3 A reads the
replacement canary through A/page 7 and reports the observed value to the
checked syscall path while B/page 7 remains absent.

This is finite QEMU evidence that the old virtual access did not observe the
replacement canary in this execution. The generated fixture proves its named
model allocation/absence facts, while the C phase checks, compiled stores,
`invlpg`, page walk, exception delivery, and QEMU behavior remain trusted or
tested rather than a refinement proof. The bounded C owner/lifetime metadata
is scenario attestation; it is not a general allocator ABI or dynamic quota
policy.

Because this image carries additional CPL3 probe code, it retains its own
complete generated boot-page-table plan. The build requires that plan to match
the final linked image byte-for-byte; the ordinary fault images continue to
share their exact common plan. This separation does not exempt any immutable
leaf from checking.

The live page-table checker does not ignore those mutable leaves. Its
kernel-owned phase is one of `boot`, `before`, `unmapped`, `after`, or `reused`,
and each phase admits exactly one B/page-7 value: the generated boot leaf, the
reviewed before-frame leaf, zero, or the reviewed after-frame leaf. A/page 7
must remain at its generated boot value until `reused`, when it must name the
exact scrubbed before-frame; B/page 7 must simultaneously remain absent. Every
ancestor and all other A/B leaves remain byte-for-byte equal to the generated
plan after masking only hardware-managed accessed/dirty bits. The machine path
checks the complete two-root relation before each prefill, after each
invalidation and replacement, and at the fresh-owner CPL3 report. Guest
negatives reject a wrong frame, publication of the unmapped phase while a leaf
remains present, and an unknown phase; the existing mutation matrix continues
to reject changes outside the window.
This relation and its policy checker are trusted C/static evidence, not a Lean
proof or a refinement theorem.

`check-runtime-invalidation-policy.sh` checks the fixed generated state,
command, reply, address-space and page in source and checks
PTE-store/invalidation/publication order in final disassembly. Its focused
negative corpus rejects a wrong page, wrong root, omitted `invlpg`, invalidation
before the PTE store, publication before invalidation, forged typed reply,
widened mutable-root scope, and acceptance of an unknown mutable phase. The
QEMU trace is machine evidence for
before/unmap/replacement-frame visibility and confinement, not a proof of
processor TLB semantics. Instruction completion, page-walk hardware, compiler
correctness, and physical TLB coherence remain trusted.

The dedicated runner-negative corpus separately rejects skipped CPL3 prefill,
wrong page/root, omitted or reordered invalidation/publication, omitted or
pre-unmap reuse, reuse publication before the replacement-canary write, a
corrupted replacement canary, an omitted or wrong-root fresh-owner CPL3 read,
an incidental CR3 reload, software-walker-only
or direct-called denial, stale-access success, partial/reordered records, guest
failure, reset, triple fault, and hang. Source-policy negatives also reject a
reuse phase detached from the complete live-table relation, publication before
scrub, and selection of the filled rather than post-reuse generated state.
These are protocol/static checks over controlled fixtures; the accepted QEMU
row remains the independent machine observation.
