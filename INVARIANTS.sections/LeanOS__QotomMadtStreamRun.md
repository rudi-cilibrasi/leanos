# Qotom scalar stream traversal model

This proof-side model carries actual scalar projections between consumed bytes. It is not an exported production implementation and does not yet establish full equivalence with authoritative table decoding.

- `step_retains_projections` — Every successful model step returns exactly the scalar query’s state projections.
- `step_has_no_error` — Every successful model step has zero in the scalar error projection.
- `step_advances_offset` — Every successful model step advances the actual byte offset by exactly one.
- `run_append` — Traversing concatenated byte sequences is equivalent to passing the first segment’s exact successful state into the second segment.

- `step_advances_offset_nat` — Each successful step increases the natural-number offset by one without machine-word wraparound.
- `run_consumes_exact_length` — A successful traversal advances by precisely the length of the supplied byte list.
- `run_append_success` — A successful concatenated traversal yields an actual intermediate state through which both segments succeed.

- `run_cons_success` — A successful nonempty traversal exposes its actual successful first step and remaining run.
- `step_starts_record` — Starting at a cleared record boundary carries the actual kind-byte projections and preserves all inventory fields.
- `run_header_retains_framing` — A successful two-byte header run proves a supported kind, its matching length, payload offset two, cleared payload fields and unchanged inventory from the original state.

- `step_payload_framing` — Successful payload steps carry unchanged kind and length with the record offset advanced by one.
- `step_completes_boundary` — A successful completed record returns the actual carried state to cleared partial fields.
- `step_nonprocessor_inventory` — Non-processor payload steps preserve all six carried inventory fields.
- `run_nonprocessor_payload` — Traversing a complete bounded non-processor payload returns to a record boundary with unchanged inventory.
- `run_nonprocessor_record` — A successful header-plus-payload traversal of a correctly sized non-processor record preserves the original inventory and returns to a boundary.

- `step_processor_payload` — The carried-state model retains the scalar processor payload update and unchanged inventory.
- `step_processor_complete` — The final payload byte checks the actual reconstructed ID/flags, advances the processor count and restores a boundary.
- `run_processor_payload` — A successful six-byte processor payload binds its final guard to the supplied ID and four flags bytes through actual intermediate states.
- `run_processor_record` — A successful complete eight-byte processor record validates the supplied payload, advances the original count once and restores a boundary.

- `run_processor_record_typed` — The actual ID and reference-decoded flags of a successful processor record identify the exact typed baseline member at the original processor count.
- `run_processor_record_count_nat` — That original count is below four and advances by exactly one in natural-number arithmetic, without wraparound.

- `run_records_count` — Successful traversal of a byte-preserving record sequence restores a boundary and advances the count by exactly its number of processor records.
- `run_records_members` — Every processor in that sequence occupies its exact baseline index despite interspersed ignored records.
- `initialized_records_complete_inventory` — Starting from the initial state and ending at count four yields exactly the full typed baseline inventory for the supplied record view.
