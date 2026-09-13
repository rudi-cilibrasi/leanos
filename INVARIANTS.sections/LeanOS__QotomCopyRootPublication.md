# Qotom copy-root publication checkpoint

This checkpoint accepts only the exact first Qotom root-construction result, complete protected-frame scans, a sixteen-byte cross-page transfer, and final closed-root readback. It may report both roots published only after that whole predicate succeeds, and it never grants CPL3 authority.

- `query_never_authorizes_cpl3` — Every possible input leaves CPL3 authority zero.
- `publication_requires_acceptance` — A published-root result can occur only when every construction, layout, scan, transfer, and readback condition is accepted.
