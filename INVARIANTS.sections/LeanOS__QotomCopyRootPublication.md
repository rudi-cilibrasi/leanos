# Qotom copy-root publication checkpoint

This checkpoint accepts only the exact first Qotom root-construction result, complete protected-frame scans, a sixteen-byte cross-page transfer, and final closed-root readback. The caller names one of exactly three audited protected-page inventories: the ordinary five-page one, the six-page one of the DHCP-subject lab image, whose subject A code spans two pages, or the eight-page one of the production image, which adds the third subject's code and stack pages. It may report both roots published only after that whole predicate succeeds, and it never grants CPL3 authority.

- `query_never_authorizes_cpl3` — Every possible input leaves CPL3 authority zero.
- `publication_requires_acceptance` — A published-root result can occur only when every construction, layout, scan, transfer, and readback condition is accepted.
- `accepted_inventory_exact` — Acceptance pins the inventory to one of the three audited rows, and to the one the caller named: five protected pages, three removed and 4,088 retained for the ordinary variant; six, four and 4,087 for the DHCP-subject variant; or eight, four and 4,085 for the production variant. No other variant or count is admitted.
- `base_inventory_publishes` — The ordinary five-page inventory, with all other conditions met, publishes both roots with an empty error mask.
- `dhcp_subject_inventory_publishes` — The DHCP-subject six-page inventory, with all other conditions met, publishes both roots with an empty error mask.
- `production_inventory_publishes` — The production eight-page inventory, with all other conditions met, publishes both roots with an empty error mask.
- `variants_reject_each_others_inventory` — Each variant rejects the others' counts with the protected-count and removed/retained error bits, and an unknown variant is rejected with its own error bit as well.
