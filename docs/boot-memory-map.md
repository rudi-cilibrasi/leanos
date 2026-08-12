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
address, and a finite byte list. The decoder rejects information addresses
below the scalar production boundary's 4 KiB minimum and buffers smaller than 16
bytes or larger than 64 KiB before tag traversal. It checks the advertised
total size against the immutable copy, the reserved information-header word,
every little-endian load, aligned tag advance, tag extent, and alignment
padding extent. Multiboot2 does not define alignment padding bytes, so their
values are ignored while reserved information-header and entry words must be
zero. Zero-length entries and fixed-width base-plus-length overflow are also
rejected here, matching the production streaming parser's accepted-state
language rather than deferring those failures to normalization.

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
chunks plus negative state transitions, and executes a raw-word rejection
corpus covering a nonzero information-header word, malformed tag size,
duplicate and missing maps, unsupported map layout, zero-length, reserved-word,
and overflowing entries, a missing end tag, the 65-tag limit, and the
257-entry limit. Each fixture requires the exact typed scalar error code. The
check rejects undefined symbols and retained allocation, boxed-value,
big-`Nat`, or initialization-runtime symbols. Its final-ELF inventory also
rejects the boxed whole-buffer query, fixture query, and legacy scalar
allocation-check export.
`malformedRawCorpus_scalar_rich_exactDiagnostics` replays the same malformed
classes in Lean and records the exact rich decoder or normalization error
paired with each generated scalar diagnostic; no paired rich rejection reaches
scalar candidate authority.
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
the 64-tag bound, and the terminal end tag. Its first nineteen state words carry a
tag count incremented only when a tag header is accepted; attempting a 65th
tag rejects with the dedicated `tooManyTags` code before it can complete or
grant authority. Four additional result words form a typed entry event on
exactly an accepted entry-type transition. Production walks the immutable copy
once, retains at most 256 generated entry triples in static storage, and feeds
each event to `leanos_boot_projection_entry`. That generated export updates a
fixed 64-word usable/blocked projection covering all 4096 boot-accessible
frames. C performs no tag walk, byte decode, entry classification, overlap
rounding, or authority-field synthesis.

The generated projection-manifest boundary takes all nine checked reservation identities
in canonical order: low memory, loaded image, page tables, descriptor tables,
kernel stacks, ordinary-entry guard, ordinary-entry stack, embedded users, and
the Multiboot information copy. It validates nonempty contained ranges and the
adjacent ordinary-entry layout, including the rich model's rounded-frame
disjointness from page tables, descriptor tables, other kernel stacks, and
embedded users. It rounds overlap at page granularity, supplies the first
candidate after the mandatory low-memory reservation, and rejects any selected
frame covered by a later live interval. Each returned reservation word is
retained beside the usable/blocked words, and
`leanos_boot_projection_free` applies reservation precedence. The single
`leanos_boot_projection_finish` terminal result consumes all 64 canonical free
words at once, finds the first set frame internally, and returns typed
status/error, selected frame, owner, decoded count, reported top, and a
candidate token. Its additional next-frame field applies the same ascending
first-eligible rule after the boot-published frame, so #204's frame-budget
scenario consumes the identical decoded/normalized/reserved projection rather
than rescanning raw bytes. It accepts no caller-selected frame or
caller-supplied coverage/reservation booleans, but its 64 projection words
remain caller-owned transport and are not publication authority. Production
replays the same generated decoder over the immutable copy with the candidate
as target, requires complete status, equal decoded count/top, full usable
coverage, no non-usable overlap, and the generated per-frame manifest
decision, then passes those terminal words to
`leanos_boot_publish_authority`. Thus a forged projection candidate, including
one paired with `entryCount=0`, cannot publish. C executes and verifies
physical zeroing before exposing the generated publication result.

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

The reconstruction premise is universal rather than corpus-specific:
`canonicalChunks_reconstruct` proves that canonical fixed-width chunking
flattens to every aligned byte buffer exactly, `canonicalChunks_replay` proves
the same chunks consume the complete extent with one identity and no offset
gap, and `assemble_canonicalChunks` packages those facts as the exact immutable
input accepted by the rich decoder boundary. Corpus fixtures now use this
canonical constructor instead of a parallel fixture-only chunker.
`chunkWord_readU64_agreement` additionally binds byte-to-`UInt64` packing to
the rich decoder's little-endian eight-byte reader for arbitrary successful
reads. `scalarStep_readU64_refines` lifts that agreement to every one of the
nineteen persistent parser words returned from an arbitrary scalar state
transition. `accepted_entryType_exposes_canonical_event` separately binds the
four parse-once event words to the exact accepted base, length, and canonical
memory kind.
`checkedScalarReplay_eq_scalarReplay` then lifts the checked byte reads across
the complete replay, including the production loop's first-error stop.
`canonicalChunks_readU64` proves that every chunk of any aligned canonical
decomposition supplies such a read, while
`assembled_canonical_checkedScalarReplay` binds that whole replay to the exact
immutable input reconstructed for the rich decoder. These remain proof-side
model statements: they do not refine generated C, the Lean compiler/runtime,
the linker, GRUB, firmware, QEMU, or hardware. Terminal parser errors now
participate in the same fail-closed result as transition errors:
`rejected_step_exposes_no_state` and
`scalarStep_rejected_exposes_no_state` prove that every rejected transition
zeros all parser, classification, target-frame, and tag-counter state words.
The freestanding replay checks that complete non-projection contract across
each generated-C malformed-handoff diagnostic, including terminal
`missingEnd`.

`BootMemoryMapFullProjectionABI` makes the exact rich transition executable as
a hosted generated-C boundary without calling the scalar parser. Its sole
fixture export starts from immutable raw bytes, calls
`BootMemoryMapDecoder.decode`, passes the resulting handoff unchanged to
`BootReservation.initializeAllocator`, calls `FrameAllocator.allocate`, and
serializes every decoded entry, normalized region, checked reservation interval
(including identity and lifetime), overlaid region, and the selected frame.
Rejection exposes only a typed stage/error code and no projection word. The
accepted corpus combines duplicate usable entries, usable/non-usable overlaps,
both entry orders, an unknown memory type, a partial page, and reservations
crossing normalized regions. Separate fixtures retain the exact 256-entry bound
and reject a missing end tag, fixed-width address overflow, and a substituted
selected frame.

`scripts/check-boot-memory-full-projection.sh` builds the generated C and hosted
ELF twice and requires byte-identical object files and final ELFs. It replays
the complete 90-word projection, checks that reversed input changes only the
raw witness order, and retains generated C, ELF hashes, symbol inventory,
section headers, disassembly, results, and mutation diagnostics under
`build/boot-memory-full-projection`. Final-ELF policy requires the sole rich
fixture export and rejects the scalar decode/manifest/select/publication
exports and legacy adapters. The deliberately false
`BootMemoryFullProjectionMutation` Lean fixture must also fail with the
expected semantic diagnostic.

The exact 65-tag fixture is shared at the byte level by the scalar replay and
`BootMemoryMapStreamPipeline`. The
`sixtyFiveTag_exactByte_scalar_richPipeline_agreement` theorem proves exact
chunk reconstruction and that both paths reject the same bytes at their
respective `tooManyTags` errors. The freestanding generated-C replay exercises
the same 560-byte layout and requires scalar error code 5, while source policy
requires production consumers to retain the parser words plus typed event and
pass the tag-count word on every transition.

This checkpoint does not claim that the continuity chain authenticates bytes
or that generated C or the final binary refines Lean. The boxed exact-rich
generated-C fixture is hosted evidence and remains absent from the
allocation-free production image.
`BootMemoryMapScalarRichEquivalence.field_words_iff_rich_predicates` proves the
candidate-policy comparison for arbitrary entry lists, checked reservation
intervals, and frames. `consume_canonical_projection_iff` fixes the candidate
identity and all three production decision words directly from those rich
objects, so its public equivalence has no caller-supplied field equations.
`roundInterval_contains_iff_byteRangeReserves` proves each checked half-open
byte range reserves exactly the frames selected by the production overlap
test, and `rounded_ranges_reservedBy_iff` composes that result over the complete
nine-identity manifest (in fact, over any successfully rounded list). Thus the
production manifest word and the rich reservation overlay cannot omit or add a
range after rounding.
`accepted_authority_projection_consumable` then derives reservation exclusion
from the accepted allocation witness itself and projects every accepted rich
decode/reserve/allocate authority into the same decision without an external
readiness premise. Final-ELF policy requires
`leanos_boot_consume_exact_projection`, rejects the superseded selector, and
QEMU requires `projection=scalar-checked` from the production path. This does
not establish scalar-acceptance-to-rich-authority existence or rejection
agreement; the hosted rich boundary remains separate.
`ScrubbedPublication` additionally retains proof that the atomic scrub model
published that exact rich-selected frame. Its complete-authority theorem
derives exact scalar selection, publication, freshness, and allocator
ownership from the rich result and accepted scrub transition, without
accepting rescan identity or scrub-success scalar words as independent
authority. `sharedAllocatorScrubState` now constructs the scrub pre-state with
the exact reservation-overlaid allocator retained by the rich authority.
`scrubbedPublicationOfAuthority_complete` rewrites the scrub model's sole
allocator call with the rich `allocatedBy` equation, constructing the complete
certificate for arbitrary prior bytes without a second allocator state,
accepted bit, rescan identity, or selected-frame equality premise.

`runCanonical` is the proof-only composition of those production gates for an
arbitrary immutable raw input. It first requires the scalar
`manifestValid` predicate, constructs the complete nine-identity manifest,
and then invokes the exact rich decode/reserve/allocate transition.
`runCanonical_acceptance_binding` proves in one acceptance statement that the
raw input reaches `BootMemoryMapDecoder.decode` unchanged, the positional
manifest validates to the canonical rounded intervals retained by the
reservation result, and the selected authority is accepted by
`consumeExactProjection` with fields derived only from that result.
`runCanonical_raw_bytes_extensional` additionally proves that equal magic,
information address, and immutable bytes cannot produce different complete
rich projections for equal manifest words and owner. These theorems are
universal over byte buffers and contain no fixture or entry-order premise; they
add no generated export.
`authorizeCanonical` now routes the same proof-only composition through the
complete rich-projection comparison rather than returning `run` authority
directly. `authorizeCanonical_acceptance_binding` preserves the raw decoder,
canonical interval, reservation, allocation, and exact scalar-consumer
equations while additionally proving that every claimed decoded entry,
normalized region, checked interval, overlaid region, and selected frame is
the canonical projection of the returned authority. The gate also replays
the canonical scalar stream at the rich-selected frame and checks its terminal
projection. `authorizeCanonical_acceptance_scalar_agreement` universally exposes its
terminal status, diagnostic, usable-coverage, and non-usable-overlap agreement
for every accepted authorization, and
`authorizeCanonical_scalarReplay_projection_binding` feeds those actual replay
words into `consumeExactProjection` without a caller-supplied agreement
premise. The rich decoder retains a
proof-only `SuccessfulTagDecodeTraversal` for every
successful recursive tag walk. Its constructors bind each accepted tag header
to the exact source word and aligned advance, bind a memory-map tag to its
layout word and `SuccessfulEntryDecodeTraversal`, and bind the terminal end tag
to the advertised extent. `successfulTagDecodeTraversal_extracts_entry_traversal`
now inducts through ignored tags on both sides of the unique map, reconstructs
their exact typed order through the terminal end tag, and proves that typed
extraction returns the source-certified map entries.
`successfulRichDecodeTraversal_entries_source` then uses the retained
`validateHandoff` equation to identify that source walk with exactly
`decoded.entries`; an existential shadow entry list cannot satisfy the bridge.
`canonicalInfoStep_of_richTraversal` now consumes the retained information
header from that source certificate, proves its 64-bit word is represented
without truncation, selects the exact first canonical chunk, and establishes
the complete admitted scalar cursor at offset eight in the tag phase.
`infoStepWords_of_admitted` proves that phase transition directly from the
production scalar definition rather than a shadow parser.
`successfulTagDecodeTraversal_offset_lt_total` proves that every retained tag
step begins with a complete header inside the advertised extent, and
`scalarAligned8_eq_richAligned8` proves that the scalar parser's
`(size + 7)` ceiling alignment is exactly the rich decoder's `aligned8`
advance throughout the admitted 64 KiB bound. In particular, it does not use
the false floor identity `size / 8 * 8` for non-aligned ignored tags.
`successfulTagDecodeTraversal_header_advance` packages that equality with the
exact retained source header and bounded successor cursor at every rich tag
constructor, supplying the local cursor/fuel step needed by the remaining
whole-tag induction. Finally,
`canonicalFirstTagStep_source_refines` binds the first tag header at offset
eight to canonical chunk index one, its exact rich-decoder word, nonterminal
bit, and every production scalar query.
`canonicalTagStep_source_refines` lifts that source agreement to every aligned
offset in the retained recursive tag traversal, including the exact terminal
bit for the end tag. `endTagStepWords_of_admitted` derives the production
scalar `complete`/`noError`/`phaseDone` state for that exact end word, and
`successfulScalarRichTraversal_endTag` packages the canonical final chunk as
the terminal base case of `SuccessfulScalarRichTraversal`.
`ignoredTagHeaderStepWords_of_admitted` now proves that an admitted non-map,
non-end tag header advances the production cursor by exactly eight bytes,
installs its exact content and aligned-padding counters, and preserves all
map, entry, and classification fields;
`successfulScalarRichTraversal_ignoredTagHeader` packages that header as the
next non-entry traversal step.
`ignoredTagBodyStepWords_of_admitted` proves the matching production step for
each ignored content or alignment-padding word: the cursor advances by eight,
the padded counter decreases by eight, the content counter drains to zero,
and map, entry, and classification fields are preserved.
`successfulScalarRichTraversal_ignoredTagBody` packages that word around an
arbitrary continuation. `SuccessfulIgnoredTagSpan` threads the exact scalar
state through every accepted ignored content/padding word, and
`successfulScalarRichTraversal_ignoredTagSpan` composes the complete span
around the later traversal without permitting reordering or splicing.
`canonicalChunks_length` fixes the number of chunks in that source sequence,
while `successfulIgnoredTagSpan_canonical` now selects every body/padding word
at its retained source index, proves its production transition accepted, and
threads the exact cursor, counters, and phase to the next word.
`successfulIgnoredTagSpan_of_ignoredTagTraversal` obtains each complete span
directly from the rich ignored-tag continuation and rounded source advance;
the following retained tag header proves that no body word can be terminal.
`successfulScalarRichTraversal_ignoredTagTraversal` feeds that certificate
into `successfulScalarRichTraversal_ignoredTagSpan`, fixing both the canonical
body list and intermediate scalar state without a shadow traversal.
`memoryMapTagHeaderStepWords_of_admitted` next proves that the unique admitted
map header enters the layout phase with its exact entry-byte count and marks
the map as seen; `successfulScalarRichTraversal_memoryMapTagHeader` packages
that transition around the remaining layout and entry traversal.
`memoryMapLayoutStepWords_of_admitted` then validates the retained 24-byte,
version-zero layout word and selects the first-entry phase (or the following
tag for an empty map), preserving the exact entry-byte count and accumulated
classification state; `successfulScalarRichTraversal_memoryMapLayout`
packages that transition as the next non-entry traversal step.
`canonicalMemoryMapLayoutStep_source_refines` now binds the retained rich
layout word to the canonical chunk immediately after its map header, including
the exact source slice, packed word, nonterminal bit, and every production
transition query. The following retained tag header proves that even an empty
map's layout word cannot be presented as terminal. Its dropped-list equation
lets the continuation-style layout constructor consume that same canonical
sequence without rebuilding or splicing chunks.
`successfulScalarRichTraversal_canonicalMemoryMapLayout` performs that
composition, lifting a traversal over the canonical suffix after the layout
word to the exact suffix beginning at the retained layout word.
`canonicalMemoryMapEntrySteps_source_refines` similarly binds the three exact
source reads retained by each rich entry traversal to consecutive canonical
chunks for its base, length, and type words. The following tag header supplies
the room proving that even the final type word is nonterminal. Its
dropped-suffix equation prevents any of the three words from being reordered
or replaced by an equal packed value from another position.
`successfulScalarRichTraversal_canonicalMemoryMapEntry_with_successor` then
consumes that exact triple through the production transition, attaches the
precise decoded `RawEntry` to the classification fold, and returns the exact
post-entry scalar state over those same canonical chunks.
`entryBaseStepWords_of_admitted`, `entryLengthStepWords_of_admitted`, and
`entryTypeStepError_of_admitted` now derive the three production phase
transitions for one retained rich entry. They preserve the exact pending
base/length words and validate the rich decoder's reserved high word,
nonzero length, overflow bound, and entry limit.
`entryTypeStepWords_of_admitted` strengthens the final transition to expose
the complete canonical successor state: cursor, remaining entry bytes,
next phase, incremented entry count, sticky usable/non-usable classification,
highest usable end, target, and tag count. This is the state-continuity
contract needed by the recursive entry traversal; later entries cannot begin
from caller-invented counters or classification words.
`successfulScalarRichTraversal_memoryMapEntry_with_successor` lifts that full
contract into the proof-side traversal relation. Its canonical-source
corollary fixes both the attached entry and successor state to the immutable
buffer's exact dropped suffix.
`canonicalMemoryMapEntrySuccessor_threads_remaining` now consumes the
successor's phase, remaining-byte, and entry-count equations together with
the rich traversal's exact remaining entry count. It resolves the conditional
successor to either the next entry-base phase or the following tag phase,
proves the remaining byte count is exactly that count times 24, and preserves
the 256-entry budget without relying on wrapped scalar arithmetic.
`CanonicalMemoryMapEntryState` packages that boundary as one reusable
predicate: source cursor, phase, remaining byte count, entry budget, sticky
classification bounds, target, and tag count must all describe the same
canonical suffix. The
`successfulScalarRichTraversal_canonicalMemoryMapEntry_threads_remaining`
step consumes one exact rich entry and an already-constructed continuation,
attaches the corresponding `RawEntry`, and returns the successor with that
predicate instantiated for precisely one fewer entry.
`successfulScalarRichTraversal_canonicalMemoryMapEntries` recursively selects
every canonical triple from `SuccessfulEntryDecodeTraversal`, constructs the
continuation from the final entry backward, and prevents an intermediate
scalar state or remaining-entry count from being supplied independently.
`canonicalMemoryMapEntries_terminal_classification` projects that complete
entry traversal through `successfulScalarRichTraversal_terminal_words`: the
terminal usable-coverage and non-usable-overlap words are exactly the folds
over every accepted rich entry in source order.

`successfulScalarRichTraversal_beforeMemoryMap` and
`successfulScalarRichTraversal_afterMemoryMap` now perform the complete
retained tag induction. They compose ignored spans around the unique map,
consume its canonical header, layout, and complete entry traversal, and finish
at the retained end tag. `successfulScalarRichTraversal_of_decode` prepends
the information-header transition and identifies the source map entries with
exactly `decoded.entries`. Finally,
`canonicalScalarReplay_agrees_authority` folds that universal traversal to
prove that every rich-decoder authority necessarily has scalar
`complete`/`noError` terminal words and the exact usable and blocked
classifications. Thus `scalarTerminalProjectionMatches_canonicalScalarReplay`
proves that the retained fail-closed terminal comparison succeeds for every
rich authority; the executable check remains in place as defense in depth.

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
rejects before authority. Hosted generated-C executes and compares the complete
rich projection directly; the universal candidate theorem and final-ELF/QEMU
policy bind the allocation-free production consumer to its exact result.
