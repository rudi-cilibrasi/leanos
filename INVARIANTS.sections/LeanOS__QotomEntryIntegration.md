# Qotom CPL3 entry/return checkpoint

This checkpoint accepts only the exact first Qotom CPL3 entry exercise: two entries, one completed return, distinct aligned subject and closed roots, active closed-root agreement, a validated hardware frame and all fifteen saved general-purpose registers, entry readback and final return reload. It never grants general CPL3 authority.

- `query_never_authorizes_cpl3` — Every possible machine report leaves general CPL3 authority zero.
- `checkpoint_claim_requires_acceptance` — A published frame-and-register checkpoint requires every scalar entry/return condition to be accepted.
