# Observer isolation across whole scheduled runs

These theorems combine the scheduler — the part of the kernel that decides which program runs and which address space it owns — with the single-step privacy model above. Every request from a program carries a claimed identity and address space, but those claims are used only to reject stale requests: accepted work always runs with the identity and address space the scheduler itself derives. The headline result is that over any finite run, only the declared visible events determine what an observer ends up seeing; the hidden private activity of unrelated programs, however much of it there is, leaves no trace.

- `isSilent_iff` — Spelling out the definition: the executable yes/no silence check answers yes exactly when a step meets the privacy model's silent-step condition.
- `normalizedMappings_idem` — Bookkeeping: cleaning up the mapping table against the scheduler's records a second time changes nothing, so one normalization pass is already final.
- `sync_agrees` — Whenever the combined state is rebuilt from the scheduler's authoritative records, the older observation-side fields agree with those records exactly — the legacy fields are proved mirrors, not a second source of truth.
- `accepted_actor_uses_current_owned_space` — An accepted request names exactly the program the scheduler currently selected, that program is live, and the address space used is the one the scheduler says that program owns — never one the caller merely claimed.
- `noncurrent_actor_rejected` — A request claiming to come from any program other than the currently selected one is always rejected, whatever the operation is.
- `silent_actor_observe_unchanged` — An accepted request whose operation is silent for a given observer leaves that observer's entire view unchanged.
- `executeOne_replays` — After one executed request, the observer's view equals the old view with the request's declared event (if any) replayed on top of it; silent requests declare no event and change nothing visible.
- `executeOne_preserves_adapter` — Bookkeeping: executing one request keeps the legacy observation fields in exact agreement with the scheduler's authoritative records.
- `run_replays` — The same replay guarantee for a whole finite run: the observer's final view equals the starting view with the run's declared events replayed onto it one at a time.
- `run_preserves_adapter` — Bookkeeping: the agreement between legacy fields and authoritative records survives any finite run of requests.
- `finite_trace_lowEquiv` — The main isolation theorem: two finite runs that start indistinguishable to an observer and declare the same visible events (schedules, replies, deliveries, sharing, capability and resource outcomes) end indistinguishable to that observer, even when they differ in how many and which silent steps unrelated programs took along the way.
