# Replaying the whole boot-memory pipeline from C

This file wraps the entire boot-memory pipeline — decoding the firmware's bytes, overlaying the kernel's own reservations, and allocating the first free memory frame — into one replayable transition whose result can be read out number by number from ordinary compiled C code. The theorems guarantee the readout is bound to the real pipeline: an accepted result carries evidence for every stage and for the exact inputs used, a claimed result that differs in any detail is rejected, and a rejected run exposes nothing but its error code.

- `run_functional` — Bookkeeping: running the full transition on the same inputs twice always gives the same result.
- `rejected_has_no_authority` — Whenever the full transition rejects, it produces no result value at all.
- `accepted_authority_chain` — Every accepted result carries the full chain of successes: the decoder accepted its bytes, the reservation overlay accepted the decoded handoff, and the allocator accepted the overlaid regions.
- `accepted_decode_traversal` — Every accepted result carries the byte-by-byte decoding certificate for its decoded memory map, obtained without relying on any caller-claimed output.
- `accepted_inputs` — An accepted result records exactly the three inputs it was run with — the raw bytes, the reservation manifest, and the requesting owner — and none of them can be swapped after the fact.
- `accepted_selection_sound` — The memory frame selected by an accepted run is genuinely usable according to the decoded entries, lies within the supported range, and is not covered by any boot reservation.
- `accepted_claim_is_canonical` — The authorization step accepts a caller's claimed summary only when it matches, field for field, the canonical summary of the freshly computed result.
- `authorize_acceptance_binding` — A successful authorization guarantees both halves at once: the returned result is what actually running the three inputs produces, and the caller's claimed summary equals its canonical summary.
- `accepted_result_words` — Spelling out the definition: reading numbers out of an accepted result draws them from its canonical summary and nowhere else.
- `accepted_result_is_exact_projection` — Spelling out the definition: a result's summary consists of exactly its decoded entries, normalized regions, reservation intervals, overlaid regions, and selected frame.
- `rejected_result_has_no_projection` — A rejected result exposes only the version, the rejected status, and the error code; every other number read from it is zero.
