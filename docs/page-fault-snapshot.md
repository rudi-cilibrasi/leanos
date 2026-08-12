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
agreement transition. The machine lowering admits three fixed, separately
booted CPL3 probes: the page-zero supervisor read, a write to an exported
byte in A's present user read-only text leaf, and an instruction fetch from an
exported payload in A's present user writable NX stack leaf. Immediately before the transition
it executes `invlpg` on the immutable snapshot's exact fault address, closing
the single-core stale-translation assumption for the live leaf consumed by the
generated agreement result. The write image also verifies in the handler that
the target byte retains its linked `0xa5` canary. The NX image verifies that
the fixed payload was written before the fetch and requires hardware error
word 21 with CR2 and saved RIP both equal to the payload. If NX execution
unexpectedly succeeds, the payload invokes an unsupported syscall and reaches
the guest-error path instead of a containment pass. The generated result
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
the complete fixed diagnostic tuple arguments, and one snapshot-derived
`invlpg` helper. The supervisor-read image requires subject A's first instruction
to be a direct branch to `user_a_fault_instruction`, requires that site to be
the exact eight-byte page-zero read in the final ELF, and binds error 5, read
access, protection violation, CR2 zero, and the saved RIP to that exported site
before containment. The separate read-only-write image similarly direct-branches
to the exported `movb` site, binds error 7, write access, CR2 to
`user_a_write_target`, and retains the unchanged-target canary. The emitted
NX image direct-branches through the exported preparation site, checks the
four fixed payload stores and final direct branch in the linked ELF, binds
error 21 and execute access, and requires the target to remain within the
model-generated NX stack extent. The emitted hardware-fault record also names the exact
generated dispatch word, complete cleanup mask, and selected survivor.
Independent runner fixtures reject a changed or zeroed raw error word, CR2,
RIP, access kind, dispatch word, or live leaf permissions. A separate ordered
`PF-WALK` record retains the expected and live page-zero leaves and the
generated supervisor-denial classification before cleanup. The build-retained
`fault-containment-policy-report.txt` records the linked final-ELF addresses
and the same architectural/dispatch tuple. A separate ordered `PF-SNAPSHOT`
record retains all 19 decimal codec words directly from the immutable
production object after generated authorization and dispatch. The runner
independently resolves CR3, saved RIP, and user RSP against the final ELF,
while the shared initial CPL3 frame constructs fixed RFLAGS `0x216` rather
than inheriting ambient arithmetic flags from preceding boot checks. Source
and final-ELF policy gates enforce that construction. The runner requires
every fixed word and the exact generated authorization/route, and
publishes that one record as `fault-containment-snapshot.txt`. Missing,
duplicated, malformed, corrupted, or reordered snapshot/replay records are
controlled failures.
Two additional fresh images exercise the integrity boundary. The reserved-bit
image clears NX from every active A leaf, disables `EFER.NXE`, restores NX only
on the selected instruction leaf, invalidates that exact page, and executes a
real CPL3 read whose hardware snapshot carries RSVD because NX is reserved
while NXE is disabled. This intentionally changes the paging-controls snapshot
and complete live page-table report. The walk-mismatch image preserves the
hardware error, CR2, saved RIP, and live walk while changing exactly one
expected-leaf permission bit supplied to the same generated transition. Both
must produce one typed `PF-TERMINAL` record and debug-exit status 37. The
reserved-bit image retains the canonical authorization-failure route
`0x0200000000000002`; the walk-mismatch image retains the snapshot/walk
disagreement route `0x0200000000000003`. The runner rejects normal-success or
generic-error
statuses and any containment, cleanup, B-dispatch, user-return, final-success,
duplicate, or post-terminal record.

Tagged builds retain all three containment ISOs and both integrity-fatal ISOs,
final ELFs and maps, serial transcripts, canonical snapshots or terminal
records, disassemblies, final page-table plans, and policy reports in the
attested release bundle. `SHA256SUMS` covers each retained file.
Wrong-instruction, indirect-entry, wrong-handler-binding, changed NX payload,
indirect NX branch, and wrong NX error-binding fixtures must be rejected.
Negative fixtures also reject a forged diagnostic purpose, both a direct
handler bypass, and routing a generated fatal result to containment. A
separately labeled EFER read is
excluded from the unchanged nine-read fast-entry inventory. The scalar
lowering, live report decoder,
generated C, handwritten assembly/C, compiler/linker, QEMU, firmware, and
hardware remain trusted/tested; these policy checks are not a proof of x86
delivery, atomicity, C immutability, or final-binary refinement.
