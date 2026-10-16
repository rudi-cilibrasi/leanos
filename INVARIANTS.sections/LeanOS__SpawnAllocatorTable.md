# The old fixed spawn table is a fragment of the allocator

The spawn family's earlier boot boundary was a fixed table of states and edges. These checks show that the table's states are allocator records and its edges are allocator steps, so the allocator replaces the table without changing any decision it made.

- `tokens_abstract` — Every state of the old fixed spawn table that the allocator represents names a complete kernel state whose allocator record is bounded and encodes exactly to canonical words (checked by evaluation).
- `allocatorEdges_count` — Forty-five of the old table's fifty-four edges start at an allocator record and run an allocator command.
- `edges_are_allocator_steps` — Every one of those edges is one allocator step: the same status, the same value word, and the successor record of the edge's complete post-state (checked by evaluation).
- `edges_are_word_steps` — The fixed-width generated allocator decides every one of those edges on the thirteen words exactly as the table did (checked by evaluation).
