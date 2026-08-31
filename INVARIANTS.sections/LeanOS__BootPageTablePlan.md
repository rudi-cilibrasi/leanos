# The boot page-table plan

Page tables are the hardware maps that decide which memory each program can see and with what permissions. This file's theorems cover the plan for the page tables the kernel builds at boot: a plan value can only be produced by the checker itself, so each theorem about an accepted plan is a guarantee that no plan skipping that check can exist. Collectively they ensure the two user programs get genuinely separate views of memory, no page is ever writable and executable at once, and the memory holding the page tables themselves is never exposed or reallocated.

- `compile_deterministic` — Bookkeeping: compiling the same plan input twice always gives the same result.
- `accepted_wx` — In an accepted plan, no page is ever both writable and executable.
- `accepted_ownership` — Every page in an accepted plan belongs to the right owner: kernel pages are never user-accessible, and each user page belongs to the one program whose address space contains it.
- `accepted_user_avoids_live_table_frames` — No user-accessible page in an accepted plan ever maps the physical memory that holds the live page tables themselves.
- `accepted_distinct_user_views` — The two user programs never share a user-accessible piece of physical memory; their views are kept apart.
- `accepted_structurally_valid` — Every mapping in an accepted plan is well-formed: marked present, within the supported address range, and with no forbidden hardware bits set.
- `accepted_refines_policy` — Every mapping's permission bits are exactly the ones the reviewed policy prescribes for its region class, so the compiler cannot invent its own encoding.
- `accepted_supervisor_confinement` — Kernel regions — code, data, stacks, page tables, device windows, and DMA-remapping tables — are never accessible to user programs in an accepted plan.
- `accepted_policy_attributes` — Each region class in an accepted plan carries exactly its reviewed permission profile; for example, kernel code is read-only and executable while kernel data and user stacks are writable but never executable.
- `accepted_distinct_views` — The two address spaces of an accepted plan start from different physical frames, so they really are two separate maps.
- `accepted_no_duplicate_leaf` — An accepted plan never maps the same page of the same address space twice.
- `accepted_table_frames_reserved` — Every physical frame used for page tables in an accepted plan is covered by the reviewed page-table reservation, so the memory allocator can never hand it out to anyone else.
- `accepted_table_frames_representable` — Every page-table frame in an accepted plan lies within the range the hardware mapping format can express.
- `accepted_table_frames_distinct` — The page-table frames of an accepted plan are all different, so no table shares storage with another table or with a root.
- `accepted_compiled_layout_bound` — The list of live table frames recorded in an accepted plan is exactly the layout built from its roots and the ancestor tables the compiler accepted, committing the plan to that one layout.
- `accepted_mmio_confined` — Device windows and RAM never overlap in an accepted plan: every device mapping points at or beyond the identity-mapped boot window, and every other mapping stays inside it.
- `accepted_remapping_frames_reserved` — Every accepted plan has passed the check that its DMA-remapping table frames are identity-mapped and covered by the validated boot reservation, so they are protected from allocation just like the CPU page tables.
- `decoded_validation_deterministic` — Bookkeeping: comparing the same decoded live page-table report against the same plan twice always gives the same verdict.
