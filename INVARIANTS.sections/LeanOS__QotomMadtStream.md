# Qotom scalar MADT candidate

These checks describe the values accepted by the scalar topology stream and its BSP bridge. They do not prove where supplied state came from, establish application-processor dormancy, or authorize platform execution.

- `processor_matches_iff` — A processor matches exactly when its position is below four, its APIC ID is twice that position, and it is enabled.
- `processor_matches_rejects_disabled` — A disabled processor never matches, regardless of position or APIC ID.
- `byte_step_out_of_range` — Every projection index above fifteen returns zero for arbitrary stream inputs.
- `byte_step_version` — The version word is always one, even for invalid stream inputs.
- `finish_acceptance_requires` — Acceptance requires every complete terminal-state field, valid length and observation bounds, available BSP observation, required CPU features, matching executing ID, and the expected APIC base.
- `finish_acceptance_iff` — Those complete scalar conditions are also sufficient for acceptance; this equivalence does not establish the provenance of the supplied state.
