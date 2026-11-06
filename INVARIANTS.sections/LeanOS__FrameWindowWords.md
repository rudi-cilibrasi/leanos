# The page tables the kernel's code builds for a copy window are the ones the window theorems are about

The frame copy window theorems (in `LeanOS/FrameCopyWindow.lean`) are about an idealised description of the window's page tables: closed page tables that show no program's pages, plus a few reserved pages showing the requesting program's own frame pages. The kernel builds the real page tables with handwritten code, and a separate machine-checked proof about that code (made with the QuickProof tool, outside this Lean build) shows exactly which 64-bit page-table entries it writes when it succeeds. These theorems close the gap between the two descriptions: they read those entries the way the processor reads them and show that they are exactly the idealised page tables, so every window theorem applies to the page tables the code builds. Nothing here re-proves the QuickProof result itself; matching its written statement with the definitions here is a reading step.

- `high_bits_clear` — A frame number below 2^40 has none of its higher bits set.
- `aliasWord_frame` — The entry the code writes for a window page names exactly the intended physical frame.
- `aliasWord_flags` — That entry is marked present, writable exactly when the window is for copying in, never usable by a program, and never executable.
- `decode_aliasWord` — Read the way the processor reads it, that entry shows the intended frame as a kernel-only, never-executable page whose write permission is the window's.
- `closedWord_closed` — Page tables whose entries are the source entries with every entry for a protected frame removed show no protected frame at all.
- `windowWord_decode` — For a window of the reviewed shape, the window entries the code writes, read the way the processor reads them, are exactly the idealised window page tables built on the closed ones.
- `window_roots_of_words` — When the closed, copy-in and copy-out page tables hold exactly the entries the code's proof says, the closed ones show no protected frame and the two window ones are exactly the idealised windows, writable and read-only.
- `window_roots_protected` — So the window page tables the code builds show a protected frame only in a reserved slot, only as a kernel-only, never-executable view of the requester's own frame page, writable only in the window for copying in.
- `window_roots_other_absent` — In particular they show no page of any other program.
