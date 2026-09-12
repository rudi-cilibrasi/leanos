# Qotom MADT scalar stream

`LeanOS.QotomMadtStream` provides an allocation-free candidate path for the
captured four-processor Qotom topology. The Qotom production checkpoint
consumes it through the bounded C caller. The q35 stream and its
single-processor policy remain unchanged.

The caller must first validate the complete MADT envelope, including its
signature, length and checksum, through the existing authoritative ACPI path.
Start at byte offset 44 with scalar state
`[44,0,0,0,0,0,0,256,0,0,0,0]`. Pass each byte exactly once in order, carrying
words 3 through 14 of the preceding successful transition into the next call.
Do not reconstruct terminal state from expected constants.

`leanos_qotom_madt_stream_byte_step_query` takes those twelve state words,
table length, executing APIC ID, byte offset, byte value and projection index.
Word 0 is version 1; word 1 is active (1), rejected (2), or complete (3);
word 2 is the rejection reason. Words 3–14 carry the next state; word 15
returns the consumed byte. Unsupported projection indices return zero.
Rejected transitions expose no state words.

The processor records must enumerate enabled APIC IDs 0, 2, 4, 6 in that
order, with no online-capable, disabled, duplicate or additional processors.
The executing processor must be ID 0. IOAPIC, interrupt-source override and
local-NMI records have checked record lengths. Their interrupt routing fields
are not validated by this stream. In particular, the captured malformed NMI
routing fields are not made acceptable by processor-inventory success.

The separate `leanos_qotom_madt_nmi_policy_query` binds the four exact
six-byte native Local APIC NMI records to policy 1, quarantine. It rejects a
different count, any byte drift, or nonzero routing authority with errors
87, 88 and 89. Lean checks the ACPI flag/LINT fields and proves every retained
record unusable as a route. The C consumer extracts the records only after the
generated entry stream has accepted all framing, then requires quarantine
before it calls the BSP finish gate.

The `leanos_qotom_inherited_lvt_policy_query` export separately binds the
physical BSP LINT observation. Acceptance requires the expected APIC base and
executing ID, two identical samples of `0x00010000` from each LINT register,
stable sampling, disabled routing authority, zero writes and exact mapping
restoration. The export returns the accepted policy and both raw values; errors
90 through 97 preserve the failed boundary. It does not enable interrupts or
program the local APIC.

`leanos_qotom_madt_stream_finish_query` receives terminal status/error, the
12 terminal state words, table length, executing ID, CPUID EDX, MSR-read
availability, IA32_APIC_BASE, sampled executing ID and projection index.
It checks complete terminal shape and observation widths, then requires the
MSR/APIC features, available observation, matching executing ID, BSP flag and
exact APIC base `0xfee00900`. Version is 1. Status 1 returns candidate executing
ID/count/APIC base in words 2/3/4; status 2 rejects terminal shape or scalar
bounds; status 5 returns the existing BSP-binding error code in word 2.
Higher projection indices return zero.

`finish_acceptance_iff` characterizes acceptance for arbitrary scalar inputs.
The byte-level proofs establish exact ID retention, little-endian flags,
processor guards, count advancement, framing, and state preservation. Their
composition in the carried-state model connects the actual validated bytes and
returned terminal fields to the authoritative decoder and typed BSP binder.

Each projection of a transition must use the same old state, table length,
executing ID, offset and byte. Read all needed projections into temporary
storage, validate status/error/version, and only then replace the twelve state
words. Updating state between projection calls would describe different
transitions and falls outside the proven contract. Reject immediately on an
error; require active status before the last byte and terminal status on the
last byte. Pass the actual final status, error and state to finish, together
with the same executing ID and the observed BSP values.

`LeanOS.QotomMadtStreamRun` is an allocating proof-side traversal of the actual
scalar query. The replay starts it from the documented initial state; the
traversal also accepts an explicit state for segment composition. It rejects
nonzero error projections and carries all twelve state projections plus terminal
status. Successful steps retain those exact values. Its `run_append` theorem
composes byte segments through the actual intermediate result, and
`run_append_success` extracts that state from a successful combined run.
`run_consumes_exact_length` proves exact consumption in natural-number
arithmetic, with no wrapped offset advancement. `run_header_retains_framing`
composes the actual kind and length steps from a cleared boundary, establishing
supported framing and unchanged inventory after both bytes.
`run_nonprocessor_record` composes a complete correctly sized non-processor
record, proving boundary restoration and inventory preservation for arbitrary
payload bytes. The stream leaves routing interpretation to the separate
quarantine gate.
`run_processor_record` composes all eight actual bytes of a local-APIC record,
binds the guard to their ID and flags, advances the original count once and
restores a clean boundary. `run_processor_record_typed` identifies the exact
typed baseline processor using the reference decoder’s fields, and the count
advance is proved without wraparound. `WireRecord` provides a byte-preserving
record view for sequence composition. The sequence proofs establish exact
processor counting and ordered membership. Terminal status establishes count
four and clears all partial record fields. The payload framing proofs show
that a successful traversal ending at a boundary has enough bytes to complete
each declared record. `run_boundary_record_decomposition` recursively constructs
a byte-preserving record view from those actual bytes.
`initialized_raw_terminal_inventory` therefore proves that arbitrary raw input
accepted with terminal status from the initial state has exactly the complete
ordered baseline processor inventory, without a caller-supplied decomposition
or final count assumption.

`WireRecord.rawValue` retains the reference decoder’s processor fields and
supported non-processor framing. `run_records_reference_decode` proves that the
actual successful record sequence decodes to that exact reference view, with
byte-count fuel sufficient for all records. The normalizer bridge proves its
exact processor list and ACPI source/version provenance.
`validated_table_reference_snapshot` establishes complete-table soundness:
after the existing ACPI envelope and fixed MADT header checks, successful
terminal traversal of that validated table’s entry bytes yields the exact
Qotom baseline through `decodeCompleteMadtSnapshot`.

The carried-state proofs also establish the exact terminal offset and bounds,
cleared partial fields, count four, admitted/executing BSP zero, and bitset
`85, 0, 0, 0`. Processor payload prefixes preserve inventory until the final
byte adds the next baseline bit; sequence induction carries that invariant
through ignored records.
`validated_terminal_finish_binding` constructs the topology witness from the
validated table and proves that the finish query on the actual returned state
accepts exactly when the typed BSP binder accepts the same observation. It
requires no caller-supplied topology witness or replacement terminal fields.

The decoder result remains a soundness theorem for successful traversal, not
a proof that every reference-admitted table succeeds in the scalar parser.
The allocating model is not a production export. Kernel consumption now binds
the exact malformed NMI bytes to disabled routing authority, but still needs a
reviewed inherited-LVT and later interrupt-controller policy. AP dormancy and
the other hardware admission obligations also remain physical assumptions.

Run `bash scripts/check-qotom-madt-stream-host.sh` with the repository Lean
toolchain on PATH and the pinned CI container for sanitizer runs. Pass
`ordinary` or `sanitized` to run one mode; the default runs both. It checks 47 native-derived table cases against the full
MADT decoder and Qotom policy, with the carried-state model checked on the
same cases, plus 14 malformed scalar probes, 28 finish cases,
and 9 typed BSP-policy comparisons. The physical MADT and BSP observations
are manifest-hash pinned; mutated tables have their outer length/checksum
repaired only to compare the same entry bytes. The C harness carries actual
stream terminal outputs into the finish query for all table cases and composes
each with every observation whose standalone terminal shape is valid, including
the captured BSP observation and malformed/unavailable observation probes.

Ordinary and ASan/UBSan generated C must agree. Both modes check runtime
function-entry coverage of all scalar exports from the hosted-boundary manifest.
Sanitized mode uses the shared pinned compiler, flags and runtime settings,
and verifies sanitizer switches on the generated object. A separate retained-symbol
link probe requires both scalar exports to link without undefined symbols or
Lean runtime dependencies. That probe is not a bootable kernel and does not
establish a final production object's hardware-write contract. The runner is registered in the repository-wide hosted manifest.

See [the consumer review](qotom-madt-consumer-review.md) for the checked caller
contract and the remaining production integration obligations.
