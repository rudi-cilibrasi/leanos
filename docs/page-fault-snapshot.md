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
page mismatch, unsupported error bits, derived-field relabeling, noncanonical
saved RIP, a missing RFLAGS bit one, zero authority/stack identities, and
saved-CS/RSP/SS shapes outside the reviewed kernel (`0x08`) and user
(`0x23`/`0x1b`) profiles.
`decode_encode_canonical_page_fault` proves valid-record roundtrip and
`canonical_page_fault_encoding_injective` proves injectivity.
`decoded_canonical_page_fault_has_normalized_preimage` proves every decoded
record is the serialization of a concrete accepted `normalizePageFault`
snapshot. That codec-only preimage reconstructs context for representability;
it grants no authority. The action boundary instead requires an independently
supplied trusted `PageFaultContext`, normalizes under that context, and compares
the resulting complete serialization with the decoded record.
`authorized_canonical_has_trusted_normalized_preimage` and
`authorized_canonical_binds_trusted_context` prove that authorization carries
this independent witness and exact subject/address-space/CR3/control binding.
At this action boundary, the kernel-owned subject and address-space `Nat`
identities must satisfy `AuthorityIdentityRepresentable`, meaning each is
strictly below `2^64`. This checked premise makes the subject/address-space
equality exact after conversion back to `Nat`; authorization does not compare
identities only after a truncating `UInt64.ofNat`. Zero remains rejected by the
codec, while the previously admitted all-ones word remains in range. Decode
failures, unrepresentable trusted identities, and forged authority/control
fields return no authorization and leave containment state unchanged.
Dedicated negative fixtures cover each subject, address-space, CR3, WP, NXE,
SMEP, and SMAP mutation, plus trusted subject and address-space values equal to
`2^64 + 1`. Generated corpus rows preserve per-vector inputs and identifiers in
`build/boot/corpus.tsv`.

## Trusted boundary

The model assumes x86 supplies the error word and CR2 for the same fault.
The runtime adapter spells the version-one encoding as one 19-word C record.
Assembly samples CR2 exactly once before the first call and preserves that word
beside the saved GPR bank and hardware error/frame. After generic entry
normalization, `authorize_page_fault_snapshot` constructs the record once as a
`const` object, samples CR3, current subject/address-space identity, WP, NXE,
SMEP, and SMAP into it, and invokes the generated provenance adapter. It then
samples the selected compiled root/report and fault-page leaf and passes those
independent observations to the allocation-free generated strengthened
agreement transition. The machine lowering is restricted to its fixed CPL3
page-zero read probe. Immediately before the transition it executes `invlpg`
on the recorded fault address; the reviewed interval does not access page
zero, so a translation refilled after address-space activation cannot satisfy
the checked lookup-absence input. Present write and NX denial cases remain
model coverage and are not runtime-lowering claims. The generated result
carries an explicit contain,
fatal, kernel-diagnostic, or reject tag; handwritten C only decodes that tag.
Only a contain tag can call `page_fault_handler`, which receives the same
record rather than separately selected raw arguments. Kernel-origin
WP/SMEP/SMAP diagnostics require the distinct generated diagnostic tag. The
generated route binds the exact armed probe state to its expected error word,
saved RIP, CR2 address, recovery RIP, and completed probe state; stale or
forged purposes are fatal. The C diagnostic handler consumes that typed
recovery result and cannot reclassify the mutable probe state or snapshot.
Diagnostic recovery cannot enter user containment.

Source and final-ELF policy gates require capture-before-normalization,
provenance-before-strengthened-agreement-before-handler order, exactly one CR2
read, exactly one typed containment-handler and diagnostic-handler call site,
the complete fixed diagnostic tuple arguments, and a page-zero
invalidation operand: source policy fixes the helper input to zero, while the
final-ELF policy requires the zeroing instruction immediately before `invlpg`
through that same register. A wrong-target negative fixture must be rejected.
Negative fixtures also reject a forged diagnostic purpose, both a direct
handler bypass, and routing a generated fatal result to containment. A
separately labeled EFER read is
excluded from the unchanged nine-read fast-entry inventory. The scalar
lowering, live report decoder,
generated C, handwritten assembly/C, compiler/linker, QEMU, firmware, and
hardware remain trusted/tested; these policy checks are not a proof of x86
delivery, atomicity, C immutability, or final-binary refinement.
