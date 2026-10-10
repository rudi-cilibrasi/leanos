# Admitting one program file at build time

Before a program file built for the system can be stored in the boot image for a future loader, the build runs a checker over the file's raw bytes. The checker reads the file's header and its list of memory pieces ("segments"). It either accepts the file and produces an exact plan of where each piece goes and what it may do, or refuses it with one named reason. These theorems guarantee that the plan is exactly what the file says, that every refusal names a check that really failed, and that every accepted file has each property the policy demands: a sane 64-bit x86 header, a bounded number of pieces, page-aligned pieces that are never both writable and runnable, bounded sizes, addresses inside the reserved user area, no two pieces sharing a page, and a starting point inside the runnable code. A final theorem ties the accepted plan to the reserved memory where the file's bytes are kept.

- `Rejection.mem_all` — Bookkeeping: the checker's list of refusal reasons names every possible reason, so none can be skipped.
- `firstRejection_none_iff` — The checker finds no refusal reason exactly when every one of its checks passes.
- `check_ok_iff` — A file is accepted exactly when no check fails, and the accepted plan is then exactly the one computed from the file — never a different one.
- `check_error_sound` — Whenever the checker refuses a file, the reason it gives names a check that really fails for that file.
- `check_total` — Every file has one of two outcomes: accepted with its exact plan, or refused for a listed reason whose check really fails.
- `admit_plan_exact` — The accepted plan records the file's real size and starting point, and lists exactly the file's loadable pieces, in file order, with their addresses, sizes, file positions and permissions.
- `admitted_no_violation` — A stepping-stone fact: for an accepted file, no refusal reason applies.
- `admitted_plan` — A stepping-stone fact: an accepted file's plan is the one computed from the file.
- `admitted_header` — An accepted file has a complete header with the right identifying bytes, and is a 64-bit, little-endian, current-version x86-64 executable with the standard header sizes.
- `admitted_program_headers_bounded` — An accepted file lists at most eight pieces, and that list lies inside the file. The file itself is bounded in size. It has at least one loadable piece and at most eight.
- `admitted_segments_aligned` — Every accepted piece starts on a page boundary, both in memory and in the file, so it can be mapped directly from page-aligned storage.
- `admitted_no_writable_executable` — No accepted piece is both writable and runnable.
- `admitted_segment_sizes` — Every accepted piece takes up between one byte and the fixed maximum of memory, and its stored bytes never exceed its memory size.
- `admitted_segments_in_file` — Every accepted piece's stored bytes lie inside the file.
- `admitted_segments_in_user_window` — Every accepted piece lies entirely inside the fixed user address area.
- `pairwiseDisjoint_iff` — Bookkeeping: the checker's quick test for "no two pieces share a page" agrees exactly with the mathematical statement of that property.
- `admitted_segments_disjoint` — No two accepted pieces share a memory page.
- `admitted_entry_in_text` — An accepted file's starting point lies inside the stored bytes of a piece that is runnable and not writable — its code.
- `admitted_program_header_types` — Every piece an accepted file lists is either loadable or a harmless non-runnable stack marker, and uses no permission bits beyond read, write and run.
- `placed_sources_reserved` — Once an accepted plan is tied to the reserved memory holding the file, it keeps exactly the accepted pieces. Each piece's source bytes then start on a page boundary and lie inside both the reserved range and the boot reservation for embedded programs.
- `parse_programHeaders_length` — The byte reader never reads more than the fixed maximum number of piece descriptions, however many the file claims.
- `userWindow_above_boot_plan` — The user address area for accepted files starts at or above the end of everything the boot page tables map, so accepted pieces can never overlap a boot mapping.
