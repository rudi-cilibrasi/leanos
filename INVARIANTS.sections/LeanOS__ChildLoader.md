# Loading an admitted program into a new child

This section is about the loader: a user program that creates a child and has the kernel fill the child's memory from a program file that was checked when the system was built. It shows that the child ends up with exactly that file's pieces, each with the access rights the build-time check accepted; that the loader can never make the kernel map memory from outside the reserved area holding the file; and that any failed request throws the half-built child away completely.

- `rejection_rolls_back` — Whenever a request for the child being loaded is rejected, the result is the "nothing loaded" state: the child is discarded.
- `rollback_empty` — The discarded state has no child, no pages, nothing loaded, and no frames used.
- `refused_unchanged` — A request that does not name the child being loaded changes nothing.
- `load_outside_authority_rejected` — A load whose claimed source lies outside the loader's reserved area is rejected and discards the child.
- `inside_rollback` — The discarded state trivially satisfies the "only from the reserved area" rule.
- `pageCount_pos` — Bookkeeping: a page inside a piece of the file is one of that piece's pages.
- `step_preserves_inside` — Whatever the loader asks, every page mapped in place comes from inside the reserved area, and every copied page uses a frame given to the child.
- `exact_rollback` — The discarded state trivially satisfies the exactness rule.
- `leafOf_matches` — Every page the kernel installs for a piece has that piece's rights, and is a copy exactly when the piece is writable.
- `pageEnd_aligned` — Bookkeeping: the rounded-up end of a piece lies on a page boundary.
- `inSegment_disjoint` — Two pieces that start on page boundaries and do not overlap share no page.
- `plan_disjoint` — Any two different pieces of an accepted file do not overlap.
- `plan_aligned` — Every piece of an accepted file starts on a page boundary.
- `step_preserves_exact` — Every request keeps the rule that the child's pages are exactly the pages of the pieces loaded so far, each with its piece's rights.
- `started_exact` — When the child is started, every piece of the file is loaded and the child's pages are exactly the pages of the file's pieces.
- `started_exact_unique` — With an accepted file, each such page carries the rights of the one piece that contains it.
- `toNat_ofNat_small` — Bookkeeping: a small number turned into a 64-bit word and back is unchanged.
- `ofNat_lt_ofNat` — Bookkeeping: comparing two small numbers as 64-bit words is comparing the numbers.
- `loaderSource_agrees` — The numeric source check the running kernel uses gives exactly the model's answer: inside the reserved area at the accepted place, outside it, or inside but at the wrong place.
- `frames_short_agrees` — The numeric frame check gives exactly the model's "not enough frames" answer.
- `flags_bits` — Bookkeeping: each condition packed into the flags word can be read back.
- `start_flags_bits` — The same for the start request's flags word.
- `loaderDecide_load` — The numeric decision for a load, read through its flags, is a fixed chain of the model's checks.
- `loaderDecide_start` — The numeric decision for a start, read through its flags, is a fixed chain of the model's checks.
- `loader_witness_agrees_start` — For a start request, the numeric decision the running kernel uses is exactly the model's encoded answer.
- `loader_witness_agrees_load` — For a load request with small numbers, the numeric checks the running kernel uses give exactly the model's encoded answer.
