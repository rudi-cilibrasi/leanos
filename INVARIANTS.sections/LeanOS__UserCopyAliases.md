# Bounded supervisor copy aliases

The planner derives at most two distinct physical frames from whole-request validation and maps them in reserved slots of a supplied closed kernel table. It does not establish that the supplied table is closed or install translations. Each alias exposes an entire page; the bounded transfer routine must enforce byte offsets and lengths while the aliases are active.

- `alias_permissions` — Every alias is supervisor-only and NX, and is writable exactly for a write-validated request.
- `outside_slots_preserved` — Projection leaves every mapping outside the two reserved slots unchanged.
- `ancestors_preserved` — Projection leaves all modeled ancestor entries unchanged.
- `frameLeaf_member` — An alias leaf names a supplied frame and has precisely the selected permissions.
- `prepared_validated` — An accepted plan comes from successful whole-request validation, contains at most two distinct frames, and uses the specified projection.
- `prepared_frame_authorized` — Every planned frame occurs in the validated byte-location list.
- `prepared_checks` — Accepted slots are canonical and unused, and all planned frames are protected and representable.
- `projected_alias` — Every alias in a reserved slot names a supplied frame and retains supervisor/NX and direction-specific write permissions.
- `prepared_alias_authorized` — Every present alias in an accepted plan comes from a validated byte location with the required alias permissions.
- `alias_execution_denied` — With NX enabled, the modeled supervisor page walker cannot execute a present copy alias, even without SMAP.
- `alias_user_read_denied` — The modeled page walker denies user-mode reads through a present supervisor copy alias.
