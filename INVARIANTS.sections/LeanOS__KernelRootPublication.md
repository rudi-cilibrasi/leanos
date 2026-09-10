# Kernel-root publication and cached authority

This single-core model deliberately permits cached hits without fresh page-table revalidation. Publication returns a required reload effect and a post-flush state only with PCID and PGE disabled. The target must already be authorized. These proofs do not establish that hardware executed a reload or invalidated translations.

- `accepted_requires_controls` — Publication acceptance requires both PCID and global pages disabled.
- `unsupported_unchanged` — Unsupported controls reject without changing state or requesting a machine effect.
- `accepted_requires_reload` — Every acceptance requires a reload, selects the target table and produces an empty modeled cache, even when reusing a root.
- `published_access_fresh` — Accesses in the accepted post-flush state agree with fresh walks of the target table.
- `published_protected_denied` — Publishing the closed-root projection denies protected mappings despite arbitrary prior cached authority.
- `replacement_retains_hit` — Table replacement alone preserves a matching cached hit, exposing the missing-invalidation hazard.
