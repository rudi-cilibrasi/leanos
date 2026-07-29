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

Every boot image then consumes that exact generated reply in a bounded
runtime-mutable machine window at virtual page 7. Address space B is first
backed by a reviewed “before” frame. The active-root path clears B's volatile
PTE, executes `invlpg (0x7000)`, and only then publishes completion; remapping
the now-uncached window to a second frame yields the reviewed “after” value.
The inactive-root path repeats the same clear with A selected, loads B's CR3,
checks the selected root and absent PTE, and only then publishes completion;
a later B reload exposes the second frame. Both paths finally restore the
boot-plan leaf. These accesses are kernel observations of the concrete
machine-path ordering. A dedicated CPL3 prefill followed by a real
architectural denial, with the retired physical frame scrubbed and republished
to a fresh lifetime while the old virtual address remains absent, is still
required for the complete issue.

The live page-table checker does not ignore that mutable leaf. Its
kernel-owned phase is one of `boot`, `before`, `unmapped`, or `after`, and each
phase admits exactly one B/page-7 value: the generated boot leaf, the reviewed
before-frame leaf, zero, or the reviewed after-frame leaf. Every ancestor and
all other A/B leaves remain byte-for-byte equal to the generated plan after
masking only hardware-managed accessed/dirty bits. The machine path checks the
complete relation before each prefill, after each invalidation and replacement,
and after restoration. Guest negatives reject a wrong frame, publication of
the unmapped phase while a leaf remains present, and an unknown phase; the
existing mutation matrix continues to reject changes outside the window.
This relation and its policy checker are trusted C/static evidence, not a Lean
proof or a refinement theorem.

`check-runtime-invalidation-policy.sh` checks the fixed generated state,
command, reply, address-space and page in source and checks
PTE-store/invalidation/publication order in final disassembly. Its focused
negative corpus rejects a wrong page, wrong root, omitted `invlpg`, forged
typed reply, widened mutable-root scope, and acceptance of an unknown mutable
phase. The QEMU trace is machine evidence for
before/unmap/replacement-frame visibility and confinement, not a proof of
processor TLB semantics. Instruction completion, page-walk hardware, compiler
correctness, and physical TLB coherence remain trusted.
