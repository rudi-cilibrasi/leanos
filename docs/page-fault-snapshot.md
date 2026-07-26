# Canonical x86 page-fault snapshot

`LeanOS.InterruptEntry.normalizePageFault` is the canonical inbound provenance
boundary for vector 14. It consumes an already normalized generic
`InterruptEntry` plus the CR2 sample and kernel-owned paging context. It does
not implement page-table policy or runtime recovery.

## Supported error word

| Bit | Meaning | Treatment |
| --- | --- | --- |
| 0 | `P`: non-present (0) or protection (1) | Admitted and retained |
| 1 | `W/R`: read (0) or write (1) | Admitted; derives access kind |
| 2 | `U/S`: supervisor (0) or user (1) | Admitted; must match saved-CS origin |
| 3 | `RSVD`: reserved-bit violation | Typed terminal rejection |
| 4 | `I/D`: data (0) or instruction fetch (1) | Admitted; derives execute |
| 5 and above | PK, shadow-stack, SGX, and unselected fields | Typed unsupported-bit rejection |

Instruction fetch takes precedence over `W/R`; otherwise `W/R` selects write
or read. A caller-supplied access label is not an input. CR2 must be canonical.
The snapshot retains the full word and derives `faultPage = CR2 / 4096`.
WP, NXE, SMEP, and SMAP come from kernel context. Saved GPRs and diagnostics
cannot affect authorization.

## Version-one codec manifest

The canonical encoding is exactly 19 `UInt64` words.

| Index | Field |
| ---: | --- |
| 0 | Version, exactly `1` |
| 1 | Vector, exactly `14` |
| 2 | Raw architectural error word |
| 3 | Full CR2 fault address |
| 4 | Derived 4 KiB fault page |
| 5 | Derived access: read `0`, write `1`, execute `2` |
| 6 | Non-present `0` or protection `1` |
| 7 | Supervisor `0` or user `1` |
| 8 | Kernel-selected current subject |
| 9 | Kernel-selected active address space |
| 10 | Kernel-sampled active CR3 |
| 11 | WP/NXE/SMEP/SMAP bits `0..3`; higher bits zero |
| 12 | Saved RIP |
| 13 | Saved CS |
| 14 | Saved RFLAGS |
| 15 | Saved user RSP, or zero for supervisor origin |
| 16 | Saved user SS, or zero for supervisor origin |
| 17 | Kernel-selected entry-stack identity |
| 18 | Reserved, exactly zero |

Decoding requires exactly 19 words. It rejects truncation, extension, wrong
version, nonzero reserved fields, unsupported controls, noncanonical address,
page mismatch, unsupported error bits, and derived-field relabeling.
`decode_encode_canonical_page_fault` proves valid-record roundtrip and
`canonical_page_fault_encoding_injective` proves injectivity. Generated corpus
rows preserve per-vector inputs and identifiers in `build/boot/corpus.tsv`.

## Trusted boundary

The model assumes x86 supplies the error word and CR2 for the same fault and
that assembly samples them before either can be replaced. Generated C,
handwritten assembly/C, compiler/linker, QEMU, firmware, and hardware remain
trusted/tested; the proofs do not establish those assumptions or final-binary
refinement.
