# QuickProof project 6: the ACPI root and table copy pipeline of `boot_allocate` (#614)

This experiment proves three things about the C that copies the firmware's
ACPI tables for `boot_allocate`, against any firmware and any answers of the
Lean exports it calls. Every copy stays inside its storage. Every copied byte
is replayed through the generated copy stream. The MADT is selected only from
complete, checked copies. It uses
[QuickProof](https://github.com/genproof/quickproof-public) v0.1.0 (Coq 8.20.1,
VST 2.15, CompCert 3.15) on
[`include/acpi_table_copy.h`](../../../include/acpi_table_copy.h).

Before anything validates them, `boot_allocate` copies the selected RSDT or
XSDT into a 64-KiB root arena, then every table the root lists into a one-MiB
table arena. Two generated exports of `LeanOS/BootTopology.lean` decide each
step:

- the copy stream step, asked five words for each 8-byte chunk of a copy;
- the copy sequence step, asked three words for each table.

The MADT the pipeline selects is the input of
[project 7](../madt-generated-admission/README.md). The Lean theorems of
`LeanOS.BootTopology` say what the answers mean. This theorem is about the C
between the firmware and them, under CompCert's semantics for x86-64, for
every input the law allows. The decision record is ADR 0030, with the
amendment of issue #614.

The code was not provable as written. It ended every check in the `noreturn`
`handoff_fail`, returned structs by value and used kernel globals. Issue #614
moved it into the header (ADR 0030 refactor 1):

- **The physical copy** is a callback, so the trusted aperture copy stays in
  the kernel.
- **Storage.** The arenas, the header scratch and the copy slots are
  arguments.
- **Statuses.** Each check returns its own status, and the kernel's
  `acpi_table_copy_require` maps each status to the reason its check gave
  before.

The order of checks, the Lean calls, the reasons and the serial protocol are
unchanged.

## The law

The law is a C program in [`project/harness/`](project/harness/). Its first
comment states the claim, and that comment, not this summary, is what a reader
must review.

**`table_copy_exact`: the whole pipeline, against any firmware and any Lean.**
The harness supplies two adversaries:

- **A firmware** whose every copy may fail or write any bytes, different ones
  on every call, so a table's header and its full copy may disagree.
- **A Lean** that answers every call with any 64-bit value, a different one
  each time.

Both check every call. The root selection may be any kind and any address.
The two arenas may have any capacities and hold any bytes. For all of these,
`acpi_copy_root_and_tables`:

- calls the copy only with its context and the SDT's address. It first copies
  the 36-byte header into the scratch. Only if the header declares a length
  of 36 to 65,536 bytes that fits does it then copy that length into the
  destination. So no copy leaves its object or exceeds 64 KiB;
- replays every copy through the stream, five calls per 8-byte chunk, with
  the chunk as the firmware wrote it and the cursors carried from the answers
  before. It goes on only when the answers accept the transition, and returns
  the status of the first check that fails;
- accepts the root's envelope, checksum, width, entry count and entries, and
  each table's placement, cursor and sequence step, exactly under the stated
  conditions. After the last table it calls nothing more;
- leaves both arenas holding the firmware's bytes where it asked for a copy and
  their prior bytes elsewhere, whatever it returns;
- fills each copy slot and result field exactly when its step completes, and
  leaves every other one unchanged;
- on OK, publishes the entry count and the one table whose signature is
  `APIC`, the tables tiling the arena from 0, in order, each padded to 8 bytes.

So no firmware and no Lean answer can make the pipeline:

- copy outside its storage;
- admit a table it did not replay through the stream;
- select a MADT from an unchecked or partial copy.

The law's firmware and Lean are the reference. They keep their own copy of
what was written and answered, and check every call and the returned status
against it. One law therefore gives both directions: each call is the one the
protocol requires, and each status is the one the answers decide.

Not claimed (`project/DEVIATIONS.md`):

- the aperture copy itself (address translation, TLB invalidation, what
  physical memory holds), which stays a trusted boundary;
- what the answers of the real Lean exports mean: the `BootTopology` theorems
  say that;
- that the kernel maps each status to its reason and passes the generated root
  selection: `scripts/check-boot-handoff-stream.sh` checks both on the source;
- the lab capture's own composition of the steps;
- termination, though every loop is bounded;
- anything about the compiled kernel (CompCert's C is not GCC's).

## The proof's shape

`Defs.v` models the pipeline as one state machine over the answers of its
three callees, the copy callback and the two exports:

- `run x (start x) h` is the pipeline's stage after the answers `h`;
- `next_call x h` is the call it makes next;
- `pipeline x h` is its outcome when it returns: the status, the published
  table count and MADT, and the memory it leaves (header scratch, arenas,
  result and slots).

Every byte the pipeline reads, the firmware wrote first. So the calls and the
status depend only on the answers, the selection and the two capacities, never
on what the storage held before. The prior bytes show only in what it leaves
behind.

`AcpiSpecs.v` specifies the three callees by a protocol over an abstract oracle
`Ora gv ctx pl x h`, the firmware and the Lean behind the inputs `x` after they
have answered the calls `h`. Each callee is asked only for `next_call x h` and
records its answer. The pipeline's postcondition says the callees answered
exactly the calls `h` of a run with outcome `pipeline x h`, and that memory is
that outcome's. `InternalSpecs.v` specifies each internal function of the
header as one phase of the machine.

Several checks of the C cannot fail, because they test what the pipeline has
just computed. The model leaves them out, and the body proofs show they pass:

- `ROOT_COPY`, `ROOT_VECTOR`, `INCOMPLETE` and `MADT_SELECTION` in
  `acpi_copy_root_and_tables`;
- in `acpi_copy_root_tables`:
  - `BINDING`;
  - `BUDGET` on a padded length below the length;
  - `SEQUENCE` after the loop;
- `ROOT_ENTRY_INDEX` in `acpi_decode_root_entry`.

They stay in the code as defense in depth.

## Results

`qp verify` on a fresh clone: **PASS** ([`VERIFY.md`](VERIFY.md)).

| Theorem | Result | Axioms |
| --- | --- | --- |
| `table_copy_exact` | PROVED | 13: standard + VST malloc |

The statement and `whole_prog` are identical to the frozen contract, and the
regenerated Clight is identical to the committed Clight. The proof sources
contain no `Admitted`, `admit`, `Axiom`, `Parameter` or `Conjecture`.

`qp check` ([`CHECK.md`](CHECK.md)) covers all 221 mutation sites:

- 3,000 native ASan/UBSan runs and 20 CompCert-interpreter runs, all clean;
- 3 mutants dead code, 205 of the 218 others killed. The 13 survivors are
  equivalent:
  - **Eight survivors are in tests that cannot be true.** Each changes an
    `||` to `&&`, or one operand's comparison or constant, in a test whose
    operands are all false wherever the pipeline reaches it:
    - `ROOT_COPY`: two survivors;
    - `ROOT_VECTOR`: one;
    - `BINDING`: one;
    - `ROOT_ENTRY_INDEX`: two, one of them `>=` to `>`;
    - in `acpi_validate_copied_sdt`'s envelope check, the part
      `bytes == 0 || length < 36`, false on every copy the pipeline makes:
      two.

    The first six are in checks listed above.
  - **Two are dead initial values.** `copied_table_count` and
    `selected_madt` start at 1. Each is read only after the callee that
    writes it returns OK.
  - **One is an idempotent write-back.** The stream's write-back loop starts
    at byte 1. It writes the exposed chunk over the copy, and the `EXPOSED`
    check has just required that chunk to be the copy's own bytes, so
    byte 0 already holds its value.
  - **Two are shifts of byte 7** of a length, by 23 instead of 24: once in
    the header's decoding, once in the envelope check. A nonzero byte 7
    makes either value above 65,536. The copy's length check rejects either
    with `SDT_LENGTH`, and the envelope check finds either different from a
    length of at most 65,536.

What it took (development machine, 12 CPUs):

| Item | Measure |
| --- | --- |
| C under test | 381 lines (one header), 1 wrapper; 1 law, 436 + 49 lines |
| Coq written | 10,384 lines in 52 files (the contract included), by component below |
| Shared model and specs | `Defs.v`, `AcpiSpecs.v`, `InternalSpecs.v`, `Bodies.v`: 1,121 lines |
| The header's ten functions and the wrapper | `Pipe*.v`: 3,357 lines in 12 files |
| The law's `main`, firmware, Lean exports and helpers | `Law*.v` and the contract: 5,777 lines in 35 files, + 129 lines |
| Who wrote it | AI agents (Claude Opus 5.5 in Claude Code). One agent wrote the refactor and the law, and another the model and the specifications. Two more then proved the bodies and the law in parallel, in 7.7 and 9.4 hours. |

`qp verify` checks all of it in 42 minutes with 6 build jobs. Its largest
files, the root and table pipeline and the law's stream export, each need
about 3 to 4 GB of memory.

## Reproducing

```sh
scripts/check-quickproof.sh --check acpi-table-copy
```

[`check.conf`](check.conf) makes `qp check` run all 221 mutation sites rather
than a sample of 40, so the kill count the gate compares covers the whole
header. `scripts/check-quickproof-pins.sh`, part of `scripts/check.sh`, fails
on any difference from [`pins.tsv`](pins.tsv) in:

- `include/acpi_table_copy.h`;
- `LeanOS/BootTopology.lean`, whose exports the law's protocol and the shim's
  prototypes follow;
- any file of `project/` or `proof/`.

## Files

- `project/`: the QuickProof project. It holds:
  - `project.conf` (the pins) and `quickproof.conf`;
  - the law;
  - `env/`, the input distributions for the native and interpreter runs only;
  - `patch/`: the wrapper unit, its header and the export shim;
  - `DEVIATIONS.md`.
- `proof/src/`: the Coq proof sources. `qp assemble` regenerates everything
  else in the proof repository.
- `CHECK.md`, `VERIFY.md`, `check.conf`, `pins.tsv`.

QuickProof is under the PolyForm Noncommercial License 1.0.0, and its
toolchain includes CompCert under the INRIA Non-Commercial License. The files
here were written for LeanOS and are under its license. Running them uses
QuickProof under its own.
