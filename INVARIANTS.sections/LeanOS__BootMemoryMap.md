# Normalizing the boot memory map

After the firmware's memory description has been decoded, the kernel must turn it into a clean list of memory regions its allocator can trust. This file's theorems guarantee two things about that step: the outcome never depends on the order in which firmware happened to list its entries, and every accepted region list is well-formed, non-overlapping, honest about which memory is truly usable, and acceptable to the memory allocator. A rejected memory map yields no regions at all.

- `any_eq_of_perm` — A stepping-stone fact used by later theorems: asking whether any firmware entry passes a given test gives the same yes-or-no answer regardless of the order the entries are listed in.
- `classifyFrame_eq_of_perm` — Classifying a 4 KiB frame of memory as usable or reserved depends only on what the firmware entries say, never on the order they arrived in.
- `singletonRegions_eq_of_perm` — The frame-by-frame scan that turns firmware entries into memory regions produces exactly the same result for any reordering of the entries.
- `normalizedEntryRegions_eq_of_perm` — The final merged region list handed to the memory allocator is identical no matter how the firmware entries are ordered.
- `usableSound_eq_of_perm` — A stepping-stone fact used by later theorems: the safety check that every region marked usable really is usable gives the same verdict for any reordering of the entries.
- `validateEntries_isOk_eq_of_perm` — Reordering the entries can change which malformed entry gets reported first, but can never change whether the list as a whole is accepted or rejected.
- `normalize_functional` — Bookkeeping: normalizing the same memory map twice always gives the same result.
- `accepted_shape` — Every region in an accepted result is well-formed: none is empty and none extends past the supported memory limit.
- `accepted_sorted_disjoint` — Regions in an accepted result never overlap; each one ends before the next begins.
- `accepted_usable_sound` — Every frame emitted as usable is wholly covered by a usable firmware entry and never overlaps any non-usable entry.
- `accepted_within_physical_limit` — Every accepted region lies entirely below the fixed physical-memory ceiling the boot model supports.
- `accepted_refines_allocator` — The memory allocator accepts every region list that normalization accepts, so an accepted map can always actually be used to start allocating.
- `buildNormalized_region_projection` — Spelling out the definition: the region-building step succeeds and produces regions exactly when a simpler pass-or-fail restatement of the same checks says it should.
- `normalizeEntries_regions_eq_of_perm` — Building allocator regions from two reorderings of the same entries either fails for both or succeeds for both with identical regions.
- `normalizedRegions_eq_of_valid_handoff_perm` — Two accepted memory maps whose entries are the same items in different orders produce exactly the same allocator regions, including agreeing on acceptance versus rejection.
- `rejected_has_no_regions` — Whenever normalization rejects a memory map, no region list is produced at all.
