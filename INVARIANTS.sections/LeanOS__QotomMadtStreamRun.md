# Qotom scalar stream traversal model

This proof-side model carries actual scalar projections between consumed bytes. It is not an exported production implementation and does not yet establish full equivalence with authoritative table decoding.

- `step_retains_projections` — Every successful model step returns exactly the scalar query’s state projections.
- `step_has_no_error` — Every successful model step has zero in the scalar error projection.
- `step_advances_offset` — Every successful model step advances the actual byte offset by exactly one.
- `run_append` — Traversing concatenated byte sequences is equivalent to passing the first segment’s exact successful state into the second segment.

- `step_advances_offset_nat` — Each successful step increases the natural-number offset by one without machine-word wraparound.
- `run_consumes_exact_length` — A successful traversal advances by precisely the length of the supplied byte list.
- `run_append_success` — A successful concatenated traversal yields an actual intermediate state through which both segments succeed.
