# Setting up the IOMMU at boot (VT-d plan)

The IOMMU is the chip that polices which parts of memory each device may touch, and it makes its decisions by walking lookup tables the kernel installs before switching it on. These theorems pin down that boot-time plan exactly: the tables the kernel builds deny every device by default, the byte layout of each table entry is an exact two-way translation with no ambiguity, and the switch-on procedure is checked step by step so that a reordered, skipped, or tampered activation is caught rather than silently accepted.

- `physicalFrameLimit_value` — Spelling out the definition: the largest memory-frame number the plan will ever accept is exactly 1,099,511,627,776, matching the machine's addressable range.
- `domainLimit_value` — Spelling out the definition: the number of distinct protection domains the tables can name is exactly 65,536.
- `decode_encode_root` — Writing a well-formed top-level table entry into its raw hardware words and reading it back returns exactly the entry you started with.
- `encode_decode_root` — Every raw word pair the top-level decoder accepts is precisely what the encoder would have produced, so there are no acceptable-but-unwritable entries and no hidden extra bit patterns.
- `root_entry_encoding_injective` — Two different well-formed top-level entries can never share the same raw hardware words, so a word in memory pins down one entry unambiguously.
- `decode_encode_context` — Writing a well-formed per-device table entry into its raw hardware words and reading it back returns exactly the entry you started with.
- `encode_decode_context` — Every raw word pair the per-device decoder accepts is precisely what the encoder would have produced, so acceptance and encoding describe the same set of entries.
- `context_entry_encoding_injective` — Two different well-formed per-device entries can never share the same raw hardware words.
- `compile_deterministic` — Compiling the same boot input twice always produces the same plan or the same rejection; the compiler has no randomness or hidden state.
- `accepted_context_entries_absent` — Every plan the compiler accepts marks all 256 per-device slots as absent, so out of the gate no device is authorized to touch any memory.
- `accepted_requesters_bound_once` — In an accepted plan each device identity is looked up through exactly one table slot, with exactly 256 slots in total, so no device can answer through a second, forgotten entry.
- `accepted_maps_no_frame` — No memory frame whatsoever is reachable through an accepted plan; since no per-device entry is present, there are no second-stage tables to walk at all.
- `accepted_root_shape` — An accepted plan's top-level table has exactly one live entry, pointing bus 0 at the reserved per-device table, and every other entry is absent.
- `accepted_tables_distinct` — An accepted plan never stores its two tables in the same memory frame, so writing one can never corrupt the other.
- `accepted_reservation_checked` — Every accepted plan carries proof that the memory frames holding its tables were checked against the boot-time memory reservation list.
- `accepted_cpu_tables_disjoint` — Every accepted plan carries proof that its table frames do not overlap the processor's own page tables, so building one cannot scribble on the other.
- `accepted_state_deny_all` — Acceptance is only possible when the kernel's device-ownership records themselves list no device assignments and no memory grants; the compiler refuses anything else.
- `accepted_agrees_with_domain_projection` — The accepted plan agrees with the kernel's own authority ledger: no matter which device identity or generation you ask about, the ledger resolves to no live assignment.
- `pair_words_length` — Bookkeeping: laying a list of table entries out as low-word/high-word pairs always yields exactly twice as many words as entries.
- `accepted_root_words_length` — Bookkeeping: the raw top-level table an accepted plan emits is exactly 512 words, two per entry for all 256 entries.
- `accepted_context_words_length` — Bookkeeping: the raw per-device table an accepted plan emits is exactly 512 words, two per entry for all 256 entries.
- `decoded_validation_deterministic` — Re-checking the live IOMMU against the plan gives the same verdict every time it is run on the same reading; the checker has no randomness or hidden state.
- `stepTag_injective` — Every distinct step of the activation procedure gets its own distinct numeric tag, so no two steps can ever be confused in the activation journal.
- `canonicalJournalUInt64_toNat` — Bookkeeping: the fixed constant the running system compares journals against is exactly the encoded form of the one correct eight-step activation sequence.
- `validateActivation_alignment_matches_pageBytes` — A stepping-stone fact used to tie two views together: the alignment test the activation checker performs on a table address agrees exactly with alignment on the page size used everywhere else in the model.
- `assignedEDUTransferScalar_refines_authoritative_scenario` — For the fixed assigned-EDU scenario, the allocation-free scalar boundary returns exactly the same verdict as the authoritative transfer model for both allowed directions and the reviewed wrong-direction, boundary-crossing, and wrong-source denials.
- `validateActivation_deterministic` — The final activation check, run on the same ten observed hardware values, always returns the same accept-or-reject code; there is no randomness or hidden state.
