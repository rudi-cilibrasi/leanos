# Multiboot2 memory-map normalization

`LeanOS.BootMemoryMap` is a bounded executable model between an untrusted
Multiboot2 handoff and `FrameAllocator.init`. It is not a byte parser. A future
adapter must decode the little-endian structure into the typed `Handoff` value;
the model validates every fixed-width field it consumes before producing any
allocator input.

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
versus rejection. Permutation preserves length and multiplicity, so tag sizing,
entry-count, and resource bounds are not weakened. The raw witness list remains
available in `Normalized`, but its order is not observable through allocation
policy.

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
truthfully. The byte decoder, boot assembly, compiler, generated code, and
binary-to-model correspondence are also outside these proofs. This model proves
only conservative interpretation of the supplied typed structure. Kernel,
page-table, stack, and bootloader-buffer reservations are intentionally left to
the next overlay layer.
