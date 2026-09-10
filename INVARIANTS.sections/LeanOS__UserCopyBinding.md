# Copy policy and subject-page-table agreement

The binding gate validates the whole request through the object/lifecycle policy,
then checks each location against an independently supplied subject page table.
Both observations must remain stable. This fresh-walk model does not establish
snapshot provenance, cached translations, lifetime stability or root installation.

- `bound_validated` — Every accepted location list is exactly the policy validator's result and passes every independent table agreement check.
- `bound_walk_exact` — Every accepted byte's subject-page-table classification resolves to its policy-validated physical frame with the requested access.
- `bound_length` — The accepted list contains exactly one location per requested byte.
- `validation_rejected` — Policy rejection is preserved without attempting the page-table binding gate.
