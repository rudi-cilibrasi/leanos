# Closing kernel mappings by physical frame

This proposed page-table projection removes every virtual alias of each frame in a supplied protected-frame inventory. Its proofs concern fresh modeled page walks. They do not establish inventory completeness, installed roots, cached translations, copy windows, or permission to enter user mode.

- `protected_leaf_absent` — A mapping of a listed physical frame is absent after closing the table, regardless of its user/supervisor permission bit.
- `unprotected_leaf_preserved` — A mapping of an unlisted frame retains its complete original leaf and permissions.
- `retained_leaf_original` — Every retained leaf came from that same virtual page in the original table and names an unlisted frame; closing cannot create or redirect a mapping.
- `protected_access_denied` — The modeled page walker cannot translate a removed protected mapping for any access context, without assuming SMAP or a particular AC state.
- `protected_aliases_absent` — Two virtual aliases of the same listed frame disappear together, including supervisor aliases.
- `close_preserves_ancestors` — Closing changes no ancestor entry; it only filters leaves.
- `close_idempotent_leaf` — Closing the same inventory twice leaves each page exactly as it was after the first close.
