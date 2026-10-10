# Resource guarantees along runs that include spawning

This section extends the whole-run resource result to runs that mix spawning with every other kernel step. Along any such run the full rulebook holds at the end, no subject identity is created twice by any creation path, issued identities are never reused, and every subject's frame allowance and usage stay exactly the same.

- `ResourceBudgetGrows.refl` — Bookkeeping: every state keeps its own frame table, frame contents, frames, bindings, and subject history.
- `ResourceBudgetGrows.trans` — Bookkeeping: keeping the frame records and growing the subject history carries across two consecutive steps.
- `ResourceHistoryGrows.budgetGrows` — Bookkeeping: the earlier, stronger history fact implies the weaker one used for runs with spawning.
- `ResourceBudgetGrows.budget` — When the frame table and frames are unchanged, every subject's frame allowance and usage are unchanged.
- `spawnGate_grows` — Every spawn-family step keeps the frame records and only adds to the subject history.
- `SpawnTraceStep.admissible_preserves` — Every step of a run with spawning, under its stated condition, keeps the full rulebook and the resource guarantee.
- `SpawnTraceStep.admissible_grows` — Every step of a run with spawning keeps the frame records and only adds to the subject history.
- `SpawnTraceStep.created_fresh` — An identity a step creates, including a spawned child, was not issued before that step and is issued after it.
- `runSpawnSteps_admissible` — Along a whole run with spawning, the rulebook holds at the end and the frame records are kept.
- `createdAlongSpawn_fresh` — Along a whole run with spawning, no identity is created twice, and each created identity was not issued at the start and is issued at the end.
- `spawn_resource_trace` — Main result: along every run of kernel steps that may include spawning, the rulebook holds at the end, no identity is ever created twice or reused, the issued history only grows, and every subject's frame allowance and usage stay exactly the same, so every spawned child keeps a zero budget.
- `runSpawnSteps_composite` — Runs without spawning are a special case: they behave exactly as the earlier whole-run result describes.
