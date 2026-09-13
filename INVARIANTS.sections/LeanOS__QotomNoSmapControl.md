# Qotom no-SMAP control checkpoint

The control checkpoint admits only the exact SMEP transition under WP/NXE with SMAP, PCID, PGE, and interrupts disabled. It identifies the bounded two-root strategy but publishes no roots and grants no CPL3 authority.

- `query_never_authorizes_cpl3` — Every input leaves CPL3 authority zero.
- `query_never_claims_root_publication` — Every input reports both the closed root and copy root as unpublished.
- `transition_one_iff` — The transition result is accepted exactly when the modeled preconditions and exact CR4 transition hold.
