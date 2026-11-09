# Deviations of the madt-generated-admission project

The theorem is about the program below, not about the kernel image byte for
byte. Every difference from the C the kernel compiles is listed here; quote a
result together with this file (QuickProof `docs/GUARANTEES.md`).

## D1. A wrapper unit (`patch/madt_admission_unit.c`)

The functions of `include/madt_generated_admission.h` are `static inline`.
The unit includes the header unchanged and gives each of its four functions
an external name:

- `madt_generated_admission`, which `boot_allocate` calls, as
  `madt_admission`;
- `madt_generated_envelope`, which the Qotom production candidate and the lab
  capture call alone (through the kernel's `validate_generated_madt_envelope`),
  as `madt_envelope`;
- `madt_generated_entries` and `madt_topology_admission_result`, which the
  admission composes, as `madt_entries` and `madt_result`.

Each wrapper only forwards its arguments, and its body is proved like every
other function.

## D2. A shim for the generated `boundary-abi.h` (`patch/boundary-abi.h`)

The generated header declares every Lean export. The shim declares only the
three the header calls, with the generated prototypes:

- `leanos_boot_machine_madt_envelope_byte_step_query`;
- `leanos_boot_machine_madt_entry_stream_byte_step_query`;
- `leanos_boot_machine_topology_admission_result_query`.

## D3. The Lean exports are the law's

The kernel links the header with the C that Lean compiles from
`LeanOS/BootTopology.lean`. The law links it with its own three functions of
the same names and prototypes instead: an adversarial Lean that may answer
any value, a different one on every call. Each function checks its call
against the caller obligations of the exports' documentation:

- `machineMadtEnvelopeByteStepQuery`: words 3 to 5 (next byte, declared
  length, checksum) of each transition are carried into the next, from
  (0, 0, 0); each byte is asked at its own offset, of the copy's length, with
  the terminal marker exactly at the last byte;
- `machineMadtEntryStreamByteStepQuery`: only the words the preceding
  transition emitted (3 to 14) are carried, from the initial state
  `[44,0,0,0,0,0,0,256,0,0,0,0]`; each byte after the 44-byte header is asked
  at its own offset, with the table length and the executing APIC ID;
- `machineTopologyAdmissionResultQuery`: the arguments are the caller's
  terminal words, and in `madt_generated_admission` one MADT, the accepted
  admission (status 1, detail 0), the APIC ID the entry stream admitted and
  the executing APIC ID.

The header's proof does not depend on those functions. It holds for every
implementation that answers each call with a 64-bit value. What the answers
of the real exports mean is what the Lean definitions and theorems of
`LeanOS.BootTopology` state. The step that stays trusted is reading the law's
protocol and the exports' documentation as the same, and the calling
convention: the Lean-compiled functions take and return `uint64_t` as
declared (ADR 0029).

## Not deviations, but limits of the law

- The copy is an object of exactly `length` bytes. The kernel passes the bytes
  and length of the unique MADT copy that `acpi_copy_root_and_tables` selects
  (`acpi.madt`), a copy of at least 36 bytes whose declared length and
  checksum `acpi_validate_copied_sdt` checked; that it is that copy, and stays
  immutable, is the caller's obligation, outside this theorem (the
  acpi-table-copy project proves the selection).
- An empty copy passes the envelope without a call: no transition is asked,
  and the initial state (0, 0, 0) meets the final checks. Every caller rejects
  it afterwards: `madt_generated_admission` in the entries' bounds, the Qotom
  candidate and the lab capture in their own checks of 44 bytes or fewer.
- The statuses the header returns are the theorem's. That the kernel's
  `madt_generated_require` maps each to the failure reason of its step, and
  that `boot_allocate` calls `madt_generated_admission` with the copy, the
  executing APIC ID of the handoff, the generated root selection
  (`decoded.word[39]`, `decoded.word[40]`), the copied root's address and the
  two table counts, is outside it; `scripts/check-boot-handoff-stream.sh`
  checks both on the source.
- What the kernel does with the published APIC ID (it fails the handoff
  unless it is the executing one, `topology-admission-publication`) is outside
  it.
- Single-threaded: nothing else writes the copy while the header runs.
- Partial correctness: termination is not claimed, though every loop is
  bounded.
