# Native Qotom EHCI legacy register capture

A protected Win7 Legacy USB boot followed the observed HCCPARAMS pointer
`0x68`. The list contained one header at `0x68`, raw `0x00010001`, with
next pointer zero. The control/status dword at `0x6c` was `0x00082005`.
These are sequential observations. No ownership semaphore, SMI control,
controller stop or reset was written. FINAL remained `qotom-platform-pending`.

FreeBSD returned automatically after 34.324360197992064 seconds of serial quiet.
Boot time changed from 1789148738 to 1789149591; the one-shot request was consumed.
Independent read-only SSH checked the installed image, recovery files and
`request=none`. The filesystem check passed. Serial was FTDI/null modem COM1,
38400 baud, 8N1, no flow control.

ELF SHA256:
`64a5e46f2f99c3d273569be2abea03e9633e11817cc8123657532e0510810723`.
Build provenance remains bd9d94c with dirty integration sources; the capture
runner was 5e95558. The guarded installer checked USB serial 11758C40 and
old/staged hashes, backed up boot files, and checked the filesystem and hashes.

This establishes a bounded legacy-list observation under the lab mapping
assumptions. It does not establish firmware exclusion, controller quiescence,
DMA containment or platform/CPL3 admission. No operator-visible display result
was obtained. Hardware issues remain open.
