# Qotom scalar MADT candidate

These checks describe the values accepted by the scalar topology stream and its BSP bridge. They do not prove where supplied state came from, establish application-processor dormancy, or authorize platform execution.

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
