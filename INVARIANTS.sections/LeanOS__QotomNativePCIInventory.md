# Native Qotom PCI inventory observations

These proofs bind the supplied native sixteen-function observation, including EHCI, to a distinct closed inventory. They preserve raw registers for later device policy and do not establish authoritative enumeration, DMA containment or CPL3 admission.

- `decodeAll_preserves_raw` — Successful decoding preserves every supplied raw header and its order.
- `check_preserves_raw` — An accepted native inventory retains the caller's complete raw headers, including Command/Status and BAR/window observations.
- `witness_has_complete_inventory` — Every native witness matches the entire native baseline projection.
- `witness_has_sixteen_functions` — Every native witness has exactly sixteen functions.
- `distinct_from_historical` — A native witness cannot have the same header list as a historical fifteen-function witness.
