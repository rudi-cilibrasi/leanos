# Qotom scalar MADT candidate

These checks describe the values accepted by the scalar topology stream and its BSP bridge. They do not prove where supplied state came from, establish application-processor dormancy, or authorize platform execution.

- `native_local_apic_nmi_records_are_unusable` — Every Local APIC NMI record in the captured Qotom MADT has reserved flag bits or an invalid LINT input, so none qualifies as a usable ACPI routing record.
- `nmi_policy_acceptance_iff` — The NMI quarantine gate accepts exactly four byte-identical captured records in their recorded order and only when no routing authority is requested.
- `nmi_policy_never_authorizes_routing` — Any accepted NMI quarantine result proves that routing authority remained disabled.
- `inherited_lvt_policy_acceptance_iff` — The inherited-LVT gate accepts exactly the measured BSP identity/base, four identical `0x00010000` LINT samples, stable sampling, zero routing authority, zero writes, and exact mapping restoration.

- `processor_matches_iff` — A processor matches exactly when its position is below four, its APIC ID is twice that position, and it is enabled.
- `processor_matches_rejects_disabled` — A disabled processor never matches, regardless of position or APIC ID.
- `byte_step_out_of_range` — Every projection index above fifteen returns zero for arbitrary stream inputs.
- `byte_step_version` — The version word is always one, even for invalid stream inputs.
- `finish_acceptance_requires` — Acceptance requires every complete terminal-state field, valid length and observation bounds, available BSP observation, required CPU features, matching executing ID, and the expected APIC base.
- `finish_acceptance_iff` — Those complete scalar conditions are also sufficient for acceptance; this equivalence does not establish the provenance of the supplied state.

- `finish_typed_observation_iff` — For a supplied topology witness and complete terminal shape, widening any typed BSP observation to scalar arguments preserves exactly the typed validity condition.
- `finish_typed_binding_iff` — Under those same assumptions, scalar acceptance is equivalent to the existing typed bootstrap binder succeeding on the same observation.

- `processor_matches_typed_record` — When the scalar guard accepts a decoded processor and its online-capable flag is clear, that record equals the typed baseline member at the same position.
- `guarded_processors_equal_baseline` — Any four-record decoded list satisfying those guards at every index equals the complete typed baseline inventory. Parsing must still establish the guards.

- `completed_processor_requires_guard` — An error-free final byte of an eight-byte local-APIC record establishes the actual processor guard and a clear online-capable flag in the reconstructed flags.
- `completed_processor_advances_count` — That successful completed record advances the processor count by exactly one, so disabled records cannot silently keep the old position.

- `processor_id_byte_retained` — A successful local-APIC ID-byte transition stores the supplied byte exactly.
- `processor_flags_byte_accumulated` — A successful nonterminal flags-byte transition ORs the byte into its little-endian position in the supplied accumulator.

- `flags_bytes_match_reference` — Accumulating four arbitrary bytes with shifts and bitwise OR yields exactly the reference decoder’s natural-number flags value, without overflow.
- `flags_predicates_match_reference` — Testing the reconstructed enabled and online-capable bits agrees with the reference arithmetic predicates for all byte values, including reserved high bits.

- `completed_processor_clears_partial_state` — At the last byte of a local-APIC record, every partial-record projection is zero, including on rejection.
- `successful_byte_advances_offset` — Every error-free transition exposes exactly the preceding byte offset plus one as its next offset.
- `successful_byte_position_bounded` — An error-free transition uses the supplied current offset and lies within the bounded MADT entry region.

- `nonprocessor_preserves_inventory` — After retaining a non-processor kind, every successful remaining byte preserves the processor count, admitted ID and all duplicate-detection limbs.
- `record_kind_starts_clean` — Starting from cleared partial fields retains the actual kind byte, advances the record offset to one and preserves the inventory.
- `completed_record_clears_partial_state` — A completed record past its length byte exposes zero in every partial-record field, including when rejected.

- `record_kind_supported` — A successful kind byte is one of the four supported record types.
- `record_length_retained` — A successful length byte matches its retained supported kind, is stored unchanged, advances to payload offset two and preserves the inventory.
- `payload_preserves_framing` — Successful nonterminal payload transitions retain the record kind and length while advancing the record offset by one.

- `processor_payload_fields` — Each successful nonterminal processor payload byte updates only its specified ID/flags field and record offset while preserving the inventory.

- `terminal_byte_has_no_error` — Terminal status entails zero error and the final byte position.
- `terminal_byte_count` — Terminal status requires exactly four processors in the returned count projection.

- `terminal_byte_clears_record` — Terminal success clears every partial-record projection, because the final byte must finish its record.

- `completed_processor_seen_bits` — A completed guarded processor sets exactly its next baseline ID bit in the first duplicate-detection limb and preserves the other limbs.
- `terminal_byte_bsp` — Terminal success binds the executing CPU and returned admitted ID to BSP zero through the actual final error checks.

- `machine_topology_admission_exact_state_accepted` — The production gate accepts the exact captured root, complete copy sequence, unique processor table, successful four-processor consumer result, expected APIC base and executing BSP identity.
- `machine_topology_admission_rejected_consumer_rejected` — A rejected topology consumer result remains rejected at the production gate instead of being replaced by plausible output fields.
- `machine_topology_admission_substituted_count_rejected` — The production gate rejects a successful-looking consumer result whose processor count was substituted after parsing.
- `machine_topology_admission_wrong_base_rejected` — The production gate rejects an otherwise exact topology result when the observed APIC base differs from the Qotom profile.
