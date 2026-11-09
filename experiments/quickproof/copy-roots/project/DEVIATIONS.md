# Deviations of the copy-roots project

The theorems are about the program below, not about the kernel image byte for
byte. Every difference from the C the kernel compiles is listed here; quote a
result together with this file (QuickProof `docs/GUARANTEES.md`).

## D1. A wrapper unit (`patch/roots_unit.c`)

The headers' functions are `static inline`. The unit includes
`include/frame_copy_window.h`, which includes
`include/qotom_copy_root_builder.h`, both unchanged. It gives the three
functions the laws call external names:

- `roots_build` for `qotom_build_copy_roots`;
- `window_build` for `frame_window_build`;
- `window_root_exact` for `frame_window_root_exact`.

Each wrapper only forwards its arguments, and its body is proved like every
other function.

The functions they call are proved too: `qotom_root_table_entry`,
`qotom_root_phys_ok`, `qotom_root_phys_disjoint`, `qotom_root_protected_frame`,
`qotom_root_source_ancestors`, `frame_window_pages` and
`frame_window_geometry_ok`. Nothing else is linked: the code calls no Lean
export, no assembly and no libc function. `qotom_root_phys` and
`frame_window_transfer` are declared in the headers but not reached.

## Not deviations, but limits of the laws

- **The physical addresses are integers the caller supplies.** The theorems
  hold for every value of `source_phys`, `closed_phys` and the window's
  `fetch_phys` and `send_phys`. That each is the address its storage really
  has is the caller's obligation. The kernel and the Qotom images meet it
  through `qotom_root_phys` under their identity map of the arena. CompCert's
  memory model cannot state it: its pointers are not integers.
- **Storage separation is given by distinct objects.** The laws pass roots,
  inventories and records that are distinct C objects, as the kernel does
  (static storage) and as VST's separating conjunction requires. The builder
  copies the inventory and the aliases before it writes anything, so their
  placement does not matter. A result record that overlaps a root is not
  covered; that needs a pointer cast.
- **Pointer arguments.** `copy_roots_exact` passes each of the builder's six
  pointers as NULL or as its object. The window laws pass valid objects,
  because the kernel and the Qotom images always do.
- **The scan's inventory has its true length.** `window_scan_exact` assumes
  `n <= 16` for the 16-entry array: `frame_window_root_exact` reads
  `protected_count` entries without checking a bound, and its callers pass
  the builder's accepted count.
- **Partial correctness.** Termination is not claimed, though every loop is
  bounded.
- **One thread, no interrupts, no TLB.** The theorems are about the
  construction and the scan in memory. Publishing a root (CR3 loads, TLB
  invalidation, interrupts during a transfer) is outside them. ADR 0017 and
  `docs/frame-copy-window.md` describe those obligations.
