# Multiboot2 memory-map normalization

`LeanOS.BootMemoryMap` is a bounded executable model between a typed
Multiboot2 handoff and `FrameAllocator.init`. `LeanOS.BootMemoryMapDecoder`
provides the preceding immutable-byte boundary: it decodes a copied
little-endian information structure into exactly that `Handoff` type, then
feeds the existing normalizer without introducing a second classification
policy. Copying the bounded structure from physical memory remains a trusted
boot integration step.

## Immutable byte boundary

`BootMemoryMapDecoder.Input` contains the preserved boot magic, information
address, and a finite byte list. The decoder rejects buffers smaller than 16
bytes or larger than 64 KiB before tag traversal. It checks the advertised
total size against the immutable copy, the reserved information-header word,
every little-endian load, aligned tag advance, tag extent, and alignment
padding extent. Multiboot2 does not define alignment padding bytes, so their
values are ignored while reserved information-header and entry words must be
zero.

Exactly one version-zero memory-map tag with 24-byte entries and one final
8-byte end tag are accepted. Unknown tags are retained as typed ignored tags;
unknown memory types are conservatively decoded as reserved. Early or missing
end tags, duplicate or missing maps, truncated fields, unsupported layouts,
and excess tags or entries reject deterministically.
Every accepted `Decoded` value carries the exact entries accepted by
`BootMemoryMap.validateHandoff` and a checked byte/tag/entry-bounds witness.
`decodeAndNormalize` is the sole composition helper for this slice, and its
success theorem exposes the exact decoded handoff used by `normalize`.
`Except` rejection has no handoff or normalized partial-result projection.

`BootMemoryMapDecoderABI` exposes a version-one generated-C query boundary over
one immutable `ByteArray`. Accepted queries return the total size, every
decoded entry triple, and every canonical normalized-region triple. Rejections
return a stable stage and typed error code; they expose no accepted projection.
Each query starts from the complete byte buffer, so callers cannot continue
state with bytes from another handoff. `scripts/check-boot-handoff-host.sh`
replays checked-in accepted, overlap-order, truncation, and arbitrary-padding
fixtures through generated C and compares complete projections rather than a
digest or caller-supplied stage flags.

The boxed version-one query is hosted evidence, not a permitted freestanding
entry point. `BootMemoryMapStreaming` therefore adds a version-two scalar
transport boundary as the next integration boundary. Reset binds the
Multiboot2 magic, aligned information address, bounded aligned extent, and
stream identity. Each transition accepts one canonical little-endian chunk of
one through eight bytes only at the exact next offset. The terminal bit must
agree exactly with exhaustion of the bound extent. A different buffer identity,
stale offset or version, malformed state, extent overflow, early or late
terminal bit, nonzero unused high byte, or replay after completion rejects and
exposes no chunk.

The ABI state is seven `UInt64` words: version, status, typed transport error,
bound identity, bound extent, next offset, and a diagnostic continuity chain.
Queries 7 and 8 expose the current chunk and byte count only for a successful
transition. Callers replay one pure transition for every desired result word
and must commit the returned state words together before reading another
chunk. Input and state may not alias the immutable source buffer. Reset starts
only at offset zero; completed or rejected states cannot be resumed. Replaying
an old active state with its old chunk is deterministic, but supplies no new
authority. The chain is diagnostic and is not treated as a collision-resistant
authentication code.

`accepted_step_advances_exactly`, `accepted_step_preserves_stream`,
`accepted_step_exposes_exact_chunk`, and
`accepted_step_terminal_iff_extent` prove the scalar offset, identity/extent,
chunk, and terminal projections used by this protocol. Completed-state replay
rejection and rejection non-projection have separate lemmas. In the proof-side
exact sequence model, `replay_continuity` proves that any accepted chunk list
preserves one identity and extent and that its final offset equals the initial
offset plus the exact sum of accepted byte counts.
`scripts/check-boot-handoff-stream.sh` compiles the generated exports into a
standalone freestanding ELF, replays the checked-in accepted buffer in twelve
chunks plus negative state transitions, executes it, rejects undefined
symbols, and rejects retained allocation, boxed-value, big-`Nat`, or
initialization-runtime symbols. Its final-ELF inventory also rejects the boxed
whole-buffer query, fixture query, and legacy scalar allocation-check export.
This is sole-transport-boundary evidence for the focused artifact, not yet a
claim about the production boot image's physical-memory reader.

The production image now retains those same two generated exports.  Its
physical-memory TCB reads the already bounded, aligned information extent in
eight-byte chunks, replays each pure transition for all state/result words,
and copies only the exact chunk exposed by an accepted transition into a
64-KiB aligned static buffer.  The parser reads that immutable boot-lifetime
copy rather than rereading physical handoff memory. Every image variant
requires the generated init/step symbols in the final ELF.  This establishes
the production copy/ownership and exact stream-continuity checkpoint.

`BootMemoryMapStreamAuthority` is the version-four, allocation-free production
consumer of that copy. Its scalar state machine reads aligned raw words,
validates the information header, tag sizes and advances, ignored-tag extents,
the unique version-zero 24-byte memory map, every entry range/reserved field,
the 64-tag bound, and the terminal end tag. Its nineteen-word state carries a
tag count incremented only when a tag header is accepted; attempting a 65th
tag rejects with the dedicated `tooManyTags` code before it can complete or
grant authority. For one candidate frame, it retains full usable
coverage and any non-usable overlap independent of entry order. C no longer
walks memory-map tags, classifies entries, maintains a frame bitmap, or calls
`leanos_boot_allocation_check`.

The generated manifest boundary takes all nine checked reservation identities
in canonical order: low memory, loaded image, page tables, descriptor tables,
kernel stacks, ordinary-entry guard, ordinary-entry stack, embedded users, and
the Multiboot information copy. It validates nonempty contained ranges and the
adjacent ordinary-entry layout, including the rich model's rounded-frame
disjointness from page tables, descriptor tables, other kernel stacks, and
embedded users. It rounds overlap at page granularity, supplies the first
candidate after the mandatory low-memory reservation, and rejects any selected
candidate covered by a later live interval. This preserves usable holes before
the loaded image or Multiboot information and matches the ascending first-free
order of `FrameAllocator.allocate`. Generated selection preserves the first
eligible decoded candidate. After C executes and verifies the physical zeroing
loop, generated publication rechecks the selected-frame, decoded-status,
coverage, overlap, manifest, and scrub tuple before exposing an object token.

The scalar decoder accepts the same zero-entry memory-map tag shape as the
rich decoder. Such a tag decodes completely, then fails closed at the shared
reservation/allocation boundary because it yields no region and no usable
candidate; it is not classified as a malformed tag by only one path.

`BootMemoryMapStreamPipeline` now supplies the proof-side composition contract
for the next production step. A rich decoder input exists only after exact
model replay completes at the bound extent, and its byte list is proved equal
to the ordered concatenation of accepted chunks. The composition then calls
the existing byte decoder, `BootReservation.initializeAllocator` (which calls
the existing normalizer and overlay), and `FrameAllocator.allocate`; it accepts
no caller-supplied parsed fields or policy flags. Its authority value retains
the equations for all four transitions. Successful selection additionally
carries the existing `usableFrameSound` predicate, the boot-accessible bound,
and reservation exclusion. A complete projection includes every decoded
entry, normalized region, checked reservation interval, overlaid region, and
the selected frame; changing any projection field rejects with
`outputMutation`. Executable fixtures cover exact byte reconstruction and
selection plus cross-identity splicing, reordered chunks, and selected-frame
mutation.

The exact 65-tag fixture is shared at the byte level by the scalar replay and
`BootMemoryMapStreamPipeline`. The
`sixtyFiveTag_exactByte_scalar_richPipeline_agreement` theorem proves exact
chunk reconstruction and that both paths reject the same bytes at their
respective `tooManyTags` errors. The freestanding generated-C replay exercises
the same 560-byte layout and requires scalar error code 5, while source policy
requires production consumers to retain all nineteen ABI words and pass the
tag-count word on every transition.

This checkpoint does not claim that the continuity chain authenticates bytes,
that generated C or the final binary refines Lean, or that the scalar parser is
extensionally equal to the rich `BootMemoryMapDecoder.decode` and
`BootReservation.initializeAllocator` projection for every possible input.
The existing version-one decoder corpus and `BootMemoryMapStreamPipeline`
remain the rich typed specification. Expanding scalar-to-rich comparison from
the concrete 65-tag repair to every accepted/rejected projection remains a
documented correspondence assumption.

The controlled `malformed-handoff` image changes only the reserved high word
of the copied Multiboot information header while preserving the real GRUB
identity, extent, offsets, and generated streaming transition. Thus the
production generated decoder—not a hosted substitute—observes the malformed
raw word and must emit exactly
`LEANOS/7 BOOTALLOC status=FAIL reason=decode-rejected`. The dedicated QEMU
runner requires the independent guest-error exit signal, rejects reset, hang,
wrong or duplicate records, and fails if any handoff, map, allocation, scrub,
publication, or final success authority escapes. Both the final ELF and
two-pass linker plan, the exact QEMU command and serial log, and negative
diagnostics are retained by the release-blocking evidence matrix.

No trusted declaration, foreign primitive, runtime shim, or other TCB entry is
added by this slice. The proof-side composition uses only existing executable
definitions and proved witnesses; the residual trusted boundary remains the
one documented by ADR 0002 and the immutable-copy assumptions above.

## Accepted subset and bounds

The model requires the Multiboot2 boot magic, an 8-byte-aligned information
address, an aligned and exact total size, bounded tag traversal, exactly one
memory-map tag, and a final 8-byte end tag. Memory-map entries use the 24-byte
version-zero format. Tag sizes must advance by a positive, aligned amount and
must agree with the entry count. Limits are 64 tags, 64 KiB of tag data, 256
entries, 512 normalized regions, and 4096 expanded frames. Addresses are
checked with explicit unsigned 64-bit base-plus-length arithmetic. Raw entries
may extend beyond the deliberately small 16 MiB scan limit so the model can
consume the project's 128 MiB QEMU handoff; normalization clips its bounded
frame scan at that limit. The information-structure address and its complete
advertised extent must also fit in the unsigned 64-bit address space.

Every error returns `Except.error`; no allocator state or partial prefix is
available. These finite limits make validation and normalization total and
bound adversarial CPU and allocation cost.

## Conservative normal form

Frames are 4 KiB. A usable frame must be wholly covered by at least one usable
entry. Any overlap with reserved, ACPI, NVS, bad-memory, or unknown non-usable
input dominates usable input regardless of order. A partial usable page is
classified as reserved rather than usable. The classifier walks frame numbers
in ascending order, deduplicates by
construction, and merges adjacent equal classifications, yielding deterministic
nonzero, page-aligned, sorted, disjoint `FrameAllocator.Region` values.
`classifyFrame_eq_of_perm`, `singletonRegions_eq_of_perm`, and
`normalizedEntryRegions_eq_of_perm` prove that every normalization stage
exposed to later reservation work is invariant under `List.Perm`.
`validateEntries_isOk_eq_of_perm` proves equal entry-validation acceptance
versus rejection. `normalizeEntries_regions_eq_of_perm` lifts those facts
through every normalization and allocator-acceptance gate, while
`normalizedRegions_eq_of_valid_handoff_perm` states the final result for two
structurally accepted handoffs: they either both reject or both return exactly
the same allocator regions. Permutation preserves length and multiplicity, so
tag sizing, entry-count, and resource bounds are not weakened. The raw witness
list remains available in `Normalized`, but its order is not observable through
allocation policy.

Malformed permutations can report different error constructors because entry
validation reports the first bad descriptor. The theorem intentionally claims
only the same success/rejection status and, on success, the same regions; it
does not canonicalize diagnostics. Structural handoff fields and tag order are
unchanged by this result.

`accepted_usable_sound` states the central executable predicate: every frame in
an emitted usable region has complete usable coverage and no overlap with any
non-usable entry. `accepted_shape`, `accepted_sorted_disjoint`, and
`accepted_within_physical_limit` record the normal-form and range properties.
`accepted_refines_allocator` proves successful normalization is accepted by
`FrameAllocator.init`. Negative examples cover unsafe rounding and
first-entry-wins overlap handling.

## Evidence and trust boundary

`./scripts/check.sh` builds every module with no-sorries mode and runs the
proof-integrity escape-hatch scan and regression fixture. Executable examples
enumerate all permutations of small overlap/fragmentation, duplicate, and
partial-page/above-limit corpora. Other examples cover adjacent merging,
overflow, entries crossing the scan limit, unsupported versions,
malformed/missing tags, and bounded rejection. A deliberately
first-entry-wins classifier supplies a local counterexample: swapping usable
and reserved overlapping entries changes its answer.

Firmware and the bootloader remain trusted to describe real hardware
truthfully. Physical-memory copying, boot assembly, compiler, generated code,
and binary-to-model correspondence remain outside these proofs. The byte
decoder proves properties of the immutable finite copy; it does not prove that
the copy agrees with physical memory. Production selection and publication now
consume the generated version-three decoder and complete reservation manifest.
The focused freestanding replay covers canonical decoding,
usable/non-usable overlap, arbitrary ignored-tag padding, manifest
exclusion, stable selection, and publication mutation. Controlled
malformed-handoff QEMU replay reaches the production generated decoder and
rejects before authority. A proved complete-projection correspondence remains
follow-up proof work.
