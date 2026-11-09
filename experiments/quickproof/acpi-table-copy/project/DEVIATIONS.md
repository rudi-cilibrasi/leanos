# Deviations of the acpi-table-copy project

The theorem is about the program below, not about the kernel image byte for
byte. Every difference from the C the kernel compiles is listed here; quote a
result together with this file (QuickProof `docs/GUARANTEES.md`).

## D1. A wrapper unit (`patch/acpi_unit.c`)

The functions of `include/acpi_table_copy.h` are `static inline`. The unit
includes the header unchanged and gives `acpi_copy_root_and_tables`, the
pipeline `boot_allocate` calls, the external name `acpi_pipeline`. The wrapper
only forwards its arguments, and its body is proved like every other function.

## D2. A shim for the generated `boundary-abi.h` (`patch/boundary-abi.h`)

The generated header declares every Lean export. The shim declares only the
two the pipeline calls, with the generated prototypes:

- `leanos_boot_machine_acpi_copy_stream_step_query`;
- `leanos_boot_machine_acpi_copy_sequence_step_query`.

## D3. The physical copy is the law's

The kernel passes `boot_acpi_physical_copy`, which copies through the
page-table aperture of `copy_acpi_physical_bytes` and returns 1; it fails the
handoff itself (`topology-sdt-address`, `-window`, `-address-space`) instead of
returning 0. The law passes its own firmware instead: a copy that may fail, or
write any bytes, different ones on every call, and that checks every call: the
context, the address, the destination and the length.

The pipeline's proof does not depend on that firmware. It holds for every
callback that, given a destination of `length` writable bytes, writes them and
returns nonzero, or returns 0; the law instantiates it. The aperture, the
address translation, the TLB invalidation and what physical memory holds stay
a trusted boundary, outside this theorem (issue #614).

## D4. The Lean exports are the law's

The kernel links the pipeline with the C that Lean compiles from
`LeanOS/BootTopology.lean`. The law links it with its own two functions of the
same names and prototypes instead: an adversarial Lean that may answer any
value, a different one on every call. Each function checks its call against
the caller obligations of the exports' documentation:

- `machineAcpiCopyStreamStepQuery`: the returned next-byte (word 4) and
  next-copy (word 5) cursors are fed into the next transition, each chunk is
  bound to its table's address and declared length, and the terminal marker
  is set exactly on the last chunk;
- `machineAcpiCopySequenceStepQuery`: `currentOrdinal` is carried from the
  returned word 3, the table ordinal is the table's index, the table is
  complete, and the final-table marker is set exactly on the last one.

The pipeline's proof does not depend on those functions. It holds for every
implementation that answers each call with a 64-bit value. What the answers
of the real exports mean is what the Lean definitions and theorems of
`LeanOS.BootTopology` state (the copy budget, the stream and the sequence).
The step that stays trusted is reading the law's protocol and the exports'
documentation as the same, and the calling convention: the Lean-compiled
functions take and return `uint64_t` as declared (ADR 0029).

## Not deviations, but limits of the law

- The capacities are arguments. The kernel passes 65,536 bytes for the root
  (`boot_acpi_root_copy`) and one MiB for the tables (`boot_acpi_table_copy`),
  both multiples of 8; the law takes any capacity, each arena an object of
  exactly that many bytes. The storage the kernel passes does not alias: two
  arenas, the copy slots `boot_acpi_table_copies` and a header scratch on
  `boot_allocate`'s stack. The law passes four distinct objects.
- The statuses the pipeline returns are the theorem's. That the kernel's
  `acpi_table_copy_require` maps each to its failure reason, and that
  `boot_allocate` calls the pipeline with the generated root selection
  (`decoded.word[39]`, `decoded.word[40]`), is outside it;
  `scripts/check-boot-handoff-stream.sh` checks both on the source.
- The lab capture (`hardware/lab/qotom-acpi.c.inc`, `qotom-bsp.c.inc`) composes
  the header's steps itself through the kernel's adapters; that composition is
  not this theorem's.
- Single-threaded: nothing else writes the arenas or the copy slots while the
  pipeline runs. That the copies stay immutable afterwards is the caller's
  obligation.
- Partial correctness: termination is not claimed, though every loop is
  bounded.
