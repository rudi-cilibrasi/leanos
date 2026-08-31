# Protecting boot-critical memory from the allocator

During startup the kernel overlays its own list of memory regions that are already in use — the loaded kernel image, its page tables, its stacks, and similar — on top of the memory map handed over by firmware, before the general-purpose memory allocator opens for business. These theorems guarantee that the combined map is checked and consistent, that the kernel's reservations always win over firmware's classification, and that the allocator can never hand out a memory frame the boot process already depends on.

- `initialize_functional` — Bookkeeping: setting up the allocator from the same firmware map and the same reservation list always produces the identical outcome; there is no hidden variation.
- `accepted_normalized` — Whenever setup succeeds, the published memory map is never empty, every region in it is well-formed, and no two regions overlap.
- `accepted_reservation_precedence` — In an accepted map, every memory frame covered by a boot reservation is marked reserved, no matter how firmware had classified it.
- `accepted_preserves_usable_soundness` — The overlay never invents memory: every frame the accepted map calls usable was already called usable by firmware.
- `accepted_separates_ordinary_entry` — In an accepted map, the guard area sits immediately before the stack used for entering ordinary programs, and neither of them overlaps the page tables, descriptor tables, other kernel stacks, or embedded user programs.
- `accepted_reservations_nonfree` — Setup marks every frame of every checked reservation as not free, and the allocator state is published only after this check has actually succeeded.
- `allocation_selects_initially_free` — A stepping-stone fact used by the headline result: whenever an allocation succeeds, the frame it hands out was free beforehand.
- `allocation_excludes_reservations` — The headline guarantee: no first allocation from the published allocator can ever return a frame covered by any live boot reservation.
