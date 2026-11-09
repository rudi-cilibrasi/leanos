# QuickProof project 7: the canonical MADT admission of `boot_allocate` (#617)

This experiment proves that the C of LeanOS's canonical MADT admission asks
exactly the questions the generated Lean exports require of it, carries their
answers unchanged, and returns exactly the status they decide, for any
answers of those exports. It uses
[QuickProof](https://github.com/genproof/quickproof-public) v0.1.0 (Coq 8.20.1,
VST 2.15, CompCert 3.15) on
[`include/madt_generated_admission.h`](../../../include/madt_generated_admission.h).

`boot_allocate` admits the unique MADT copy that
[`include/acpi_table_copy.h`](../../../include/acpi_table_copy.h) selects
([its project](../acpi-table-copy/README.md)) through three generated exports
of `LeanOS/BootTopology.lean`:

- the envelope byte step, asked seven words per byte of the copy;
- the entry-stream byte step, asked sixteen words per byte after the 44-byte
  fixed header, with twelve state words carried from byte to byte;
- the topology admission result, asked four words.

The Lean theorems of `LeanOS.BootTopology` say what the answers mean. This
theorem is about the C between them, under CompCert's semantics for x86-64,
for every input the law allows. The decision record is ADR 0030, with the
amendment of issue #617.

The code was not provable as written: three kernel helpers called
`handoff_fail` directly and read the copy through the kernel's
`struct copied_acpi_sdt`. Issue #617 moved them into the header (ADR 0030
refactor 1). Each check returns its own status, and the kernel's
`madt_generated_require` maps each status to the reason its check gave
before. The Lean calls, the order of checks, the reasons and the serial
protocol are unchanged.

## The law

The law is a C program in [`project/harness/`](project/harness/). Its first
comment states the claim, and that comment, not this summary, is what a reader
must review.

**`admission_exact`: each of the header's four functions, against any Lean.**
The harness supplies the three exports itself: an adversarial Lean that
answers every call with any 64-bit value, a different one each time, and
checks each call. The copy may hold any bytes and have any 32-bit length; the
executing APIC ID and the ten result arguments may be anything. `main` calls
one of the four functions, and that function:

- calls the envelope step exactly seven times per byte, in order, all with
  one unchanged old state, the byte, its offset and the terminal marker, from
  (0, 0, 0) and then from words 3 to 5 of the previous byte's answers;
- calls the entry-stream step exactly sixteen times per byte after the fixed
  header, all with one unchanged old state of twelve words, from the initial
  state and then from words 3 to 14 of the previous byte's answers, and
  rejects a copy of 44 bytes or fewer or an executing APIC ID above 255
  without a call;
- goes to the next byte only when the answers accept the transition, and
  otherwise returns the status of the first word that rejects it and calls
  nothing more;
- after the last byte, returns the status of the first final check that
  fails;
- calls the admission result exactly four times with its arguments, which in
  an admission are the caller's five words, one MADT, the accepted admission
  and the APIC ID the entries admitted;
- writes the APIC ID record only when it returns OK, with the ID the entries
  or the result admitted, and never writes the copy.

An admission runs the envelope, then the entries, then the result, and
returns the first status that is not OK.

The law's Lean is the reference. It keeps its own copy of the state, the
answers and the bytes, and checks every call and the returned status against
them. One law therefore gives both directions: each call is the one the
exports require, and each status is the one the answers decide.

Not claimed (`project/DEVIATIONS.md`):

- what the answers of the real Lean exports mean: the Lean theorems say that;
- that the copy is the unique, immutable MADT copy, or that the kernel maps
  each status to its reason: `scripts/check-boot-handoff-stream.sh` checks the
  mapping and the call on the source;
- termination, though every loop is bounded;
- anything about the compiled kernel (CompCert's C is not GCC's).

## The proof's shape

`Defs.v` models the four functions as one state machine over the exports'
answers, whose stages are those of the law's `struct law`:

- `run x (start x) h` is the function's stage after the answers `h`;
- `next_call x h` is the call it makes next;
- `returns x h` is its outcome when it returns: the status and the APIC ID it
  writes, if any.

The specifications (`MgaSpecs.v`) are parameterized by an abstract oracle
`Ora gv x h`, the Lean behind the inputs `x` after it has answered the calls
`h`. Each export's specification asks it only for `next_call x h` and records
its answer. Each function's postcondition says the Lean answered exactly the
calls `h` of a run with outcome `returns x h`, the copy is unchanged, and the
APIC ID record holds the outcome's ID on OK and its prior value otherwise.
`InternalSpecs.v` specifies each of the header's functions as one phase of
the machine.

## Results

`qp verify` on a fresh clone: **PASS** ([`VERIFY.md`](VERIFY.md)).

| Theorem | Result | Axioms |
| --- | --- | --- |
| `admission_exact` | PROVED | 13: standard + VST malloc |

The statement and `whole_prog` are identical to the frozen contract, and the
regenerated Clight is identical to the committed Clight. The proof sources
contain no `Admitted`, `admit`, `Axiom`, `Parameter` or `Conjecture`.

`qp check` ([`CHECK.md`](CHECK.md)) covers all 209 mutation sites:

- 3,000 native ASan/UBSan runs and 20 CompCert-interpreter runs, all clean;
- 3 mutants dead code, 202 of the 206 others killed. The four survivors are
  equivalent:
  - In the entries' final APIC ID check, `state[7] > 255u` becomes
    `state[6] > 255u`, which is false because the enabled count `state[6]` is 1
    there. The original test adds nothing either: the check's other test
    rejects any `state[7]` other than the executing APIC ID, which the bounds
    check keeps at 255 or below.
  - The local arrays `state` and `answer` become one element larger, and no
    function indexes past their first size.
  - `madt_generated_admission`'s `admitted_apic_id` starts at 1, not 0. It is
    read only after the entries return OK, and they write it first.

What it took (development machine, 12 CPUs):

| Item | Measure |
| --- | --- |
| C under test | 201 lines (one header), 4 wrappers; 1 law, 292 lines |
| Coq written | 3,970 lines in 28 files (the contract included), by component below |
| Shared model and specs | `Defs.v`, `MgaSpecs.v`, `InternalSpecs.v`, `Bodies.v`: 599 lines |
| The header's four functions and their wrappers | `BodyLemmas.v` and `*Proof*.v`: 933 lines |
| The law's `main`, Lean exports and helpers | `Law*.v` and its contract: 2,317 + 121 lines |
| Who wrote it | AI agents (Claude Opus 5.5 in Claude Code). One agent wrote the refactor and the law, and another the model and the specifications. Two more then proved the bodies and the law in parallel, in 0.8 and 2.5 hours. |

`qp verify` checks all of it in 9 minutes with 6 build jobs.

## Reproducing

```sh
scripts/check-quickproof.sh --check madt-generated-admission
```

[`check.conf`](check.conf) makes `qp check` run all 209 mutation sites
rather than a sample of 40, so the kill count the gate compares covers the
whole header. `scripts/check-quickproof-pins.sh`, part of `scripts/check.sh`,
fails when `include/madt_generated_admission.h`, `LeanOS/BootTopology.lean`
(the exports the law's protocol and the shim's prototypes follow) or any file
of `project/` or `proof/` differs from [`pins.tsv`](pins.tsv).

## Files

- `project/`: the QuickProof project. It holds `project.conf` (the pins),
  `quickproof.conf`, the law, `env/` (input distributions for the native and
  interpreter runs only), `patch/` (the wrapper unit, its header and the
  export shim) and `DEVIATIONS.md`.
- `proof/src/`: the Coq proof sources; everything else in the proof
  repository is regenerated by `qp assemble`.
- `CHECK.md`, `VERIFY.md`, `check.conf`, `pins.tsv`.

QuickProof is under the PolyForm Noncommercial License 1.0.0, and its
toolchain includes CompCert under the INRIA Non-Commercial License. The files
here were written for LeanOS and are under its license. Running them uses
QuickProof under its own.
