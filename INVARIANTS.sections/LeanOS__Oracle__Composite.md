# Oracle rows for the stateful kernel dispatcher

The oracle rows for the stateful dispatcher: its scenario and hostile rows, the mixed walk, the cache-invalidation protocol, the boot capability transfer, and the in-flight revocation trace. Each canonical edge set is backed by its proved correspondence to the authoritative kernel, and the trace theorems pin each step's exact result word.

- `hosted_inFlight_revocation_vectors_refine` — Every in-flight revocation record is backed by the step-by-step refinement of the authoritative gate.
- `composite_inFlight_revocation_trace_agrees` — The expected control word of each record of the in-flight revocation trace (corpus rows 398 through 408) is exactly the typed reply selector for that step.
- `composite_inFlight_revocation_negatives_reject` — The three hostile in-flight revocation records — the revocation words replayed against the pre-offer seed, a spliced mixed-corpus revocation, and a receipt attempted before the switch — are all rejected before any kernel logic runs.
- `hosted_mixed_vectors_refine` — Every hosted mixed-scenario row is consequently backed by the separately proved, non-circular fact that its edge faithfully reflects the authoritative kernel model.
- `hosted_invalidation_vectors_refine` — Every invalidation-protocol row is likewise backed by its own proved correspondence to the authoritative publication protocol.
- `composite_invalidation_trace_agrees` — Each named step of the invalidation walk produces its exact expected result word, and the three hostile rows produce their exact rejection codes.
- `composite_invalidation_same_effect_replay_rejected` — Replaying an old acknowledgement ticket as a later acknowledgement is rejected even though both acknowledgements ask for the same kind of cache flush.
- `composite_mixed_trace_agrees` — Eight spot-checked steps of the mixed walk — including the transfer offer, the accepted map, the blocking receive, the fault cleanup, and the page-protection pair — produce their exact expected result words.
