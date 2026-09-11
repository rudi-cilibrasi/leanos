# Qotom MADT scalar stream

`LeanOS.QotomMadtStream` provides an allocation-free candidate path for the
captured four-processor Qotom topology. The production kernel does not yet
consume it. The q35 stream and its single-processor policy remain unchanged.

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

`leanos_qotom_madt_stream_finish_query` receives terminal status/error, the
12 terminal state words, table length, executing ID, CPUID EDX, MSR-read
availability, IA32_APIC_BASE, sampled executing ID and projection index.
It checks complete terminal shape and observation widths, then requires the
MSR/APIC features, available observation, matching executing ID, BSP flag and
exact APIC base `0xfee00900`. Version is 1. Status 1 returns candidate executing
ID/count/APIC base in words 2/3/4; status 2 rejects terminal shape or scalar
bounds; status 5 returns the existing BSP-binding error code in word 2.
Higher projection indices return zero.

`finish_acceptance_iff` proves the exact acceptance conditions for arbitrary
scalar inputs, including every terminal-state field and numeric bound.
This is a contract about values: it does not establish their provenance.
The full byte-stream refinement proof against the authoritative list decoder
remains unfinished. `guarded_processors_equal_baseline` proves that any four
decoded records satisfying the scalar guard at every index form the exact typed
inventory. `completed_processor_requires_guard` establishes those guard and
online-flag premises at a successful final byte of a local-APIC record, and
`completed_processor_advances_count` proves that the count advances by one.
The stream also proves retention of the actual ID byte and accumulation of
each nonterminal flags byte. The reference decoder has a matching single-record
lemma, `BootTopology.decode_local_apic_record_cons`, for arbitrary payload
bytes and a decoded tail. `flags_bytes_match_reference` and
`flags_predicates_match_reference` prove exact agreement of the accumulated
flags and both flag predicates with the reference arithmetic. The full proof
still must compose those field
transitions and preserve the initialized state across the entire table.
Successful transitions now have general current-offset/bounds and next-offset
proofs. Starting a record from cleared state preserves the inventory and
retains the actual kind byte; non-processor record bytes preserve all inventory
fields. Successful header bytes prove a supported kind and its exact retained
length. Nonterminal payload bytes retain that framing and advance the record
offset by one. Completed records clear their partial state, including ignored
records. Given an existing topology witness and complete terminal
shape, `finish_typed_binding_iff` proves that widening any typed BSP observation
to scalar arguments preserves success of the existing typed binder. This does
not construct the topology witness from the byte stream. None of these
candidate results establishes AP dormancy, DMA quarantine, interrupt routing,
no-SMAP isolation, or permission to enter CPL3.

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
payload bytes. It does not validate the ignored routing fields.
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

The remaining refinement work is to connect that constructed record view to
the authoritative complete MADT decoder and normalizer, including the outer
validated table envelope. This model is not a production export; production
wiring and its hardware admission obligations remain unfinished.

Run `bash scripts/check-qotom-madt-stream-host.sh` with the repository Lean
toolchain on PATH and the pinned CI container for sanitizer runs. Pass
`ordinary` or `sanitized` to run one mode; the default runs both. It checks 47 native-derived table cases against the full
MADT decoder and Qotom policy, with the carried-state model checked on the
same cases, plus 14 malformed scalar probes, 28 finish cases,
and 9 typed BSP-policy comparisons. The physical MADT and BSP observations
are manifest-hash pinned; mutated tables have their outer length/checksum
repaired only to compare the same entry bytes. The C harness carries actual
stream terminal outputs into the finish query for all table cases.

Ordinary and ASan/UBSan generated C must agree. Both modes check runtime
function-entry coverage of both exports from the hosted-boundary manifest.
Sanitized mode uses the shared pinned compiler, flags and runtime settings,
and verifies sanitizer switches on the generated object. A separate retained-symbol
link probe requires both scalar exports to link without undefined symbols or
Lean runtime dependencies. That probe is not a bootable kernel and does not
establish a final production object's hardware-write contract. The runner is registered in the repository-wide hosted manifest.
