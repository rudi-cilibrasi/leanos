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

- `step_terminal_count` — An actual terminal step carries count four into its returned state.
- `run_terminal_count` — A nonempty successful traversal with terminal status ends with count four.
- `initialized_terminal_records_inventory` — Terminal success from the initial state yields the full ordered baseline inventory for the supplied byte-preserving record view, without a separate count assumption.

- `step_terminal_boundary` — An actual terminal transition clears all partial fields in the carried state.
- `run_terminal_boundary` — A nonempty terminal traversal ends at a record boundary.
- `run_boundary_requires_payload` — Reaching a boundary from inside a payload requires enough actual remaining bytes to complete it.
- `run_payload_boundary` — Successfully consuming exactly the remaining payload restores a boundary for any record kind.
- `wire_record_of_payload` — A correctly sized header and payload construct a record view that preserves every supplied byte.
- `run_boundary_record_decomposition` — A successful raw-byte traversal between boundaries constructs a complete record decomposition without caller-supplied parsed records.
- `initialized_raw_terminal_inventory` — Terminal success on arbitrary bytes from the initial state constructs their exact record view and proves the complete ordered baseline processor inventory.

- `run_record_reference_decode` — Every successful complete streamed record produces exactly its reference-decoded raw record and restores a boundary.
- `run_records_reference_decode` — Successful record sequences agree with the authoritative entry decoder whenever its fuel bounds their record count.
- `records_length_le_bytes` — Byte-count fuel always suffices for a byte-preserving record sequence.
- `records_reference_normalize` — Normalizing the reference record view produces its exact bounded processor list with authoritative provenance.
- `initialized_raw_reference_snapshot` — Terminal success from the initial state agrees with authoritative raw-entry decoding and normalization to the Qotom baseline snapshot.
- `validated_table_reference_snapshot` — After existing ACPI envelope and fixed-header validation, terminal stream success yields the authoritative complete-table baseline snapshot.

- `step_terminal_control_fields` — An actual terminal step supplies the final offset, table bounds, cleared partial fields, processor count and BSP IDs.
- `run_terminal_control_fields` — A nonempty terminal traversal supplies those control fields without caller-provided replacements.
- `run_processor_prefix_inventory` — Actual processor payload prefixes preserve the inventory until the final byte and advance framing by their consumed length.
- `run_processor_record_seen_bits` — A complete processor record sets exactly the next baseline bit while retaining the prefix inventory through earlier bytes.
- `processor_prefix_mask_step` — Extending an admissible processor prefix adds precisely the next ID bit to its exact mask.
- `run_records_seen_prefix` — Complete record sequences preserve the exact ordered duplicate-detection mask invariant.
- `initialized_terminal_seen_bits` — Terminal success on arbitrary bytes returns exactly the four baseline ID bits and zero upper limbs.
- `initialized_terminal_finish_binding` — Every finish-shape field comes from the actual initialized terminal state, and scalar finish acceptance equals typed BSP-binding success.
- `validated_terminal_finish_binding` — The validated table and actual stream result construct the authoritative topology witness and establish the finish/binder equivalence without supplied topology or replacement terminal fields.
