# QuickProof project 4: the PCI segment scan against any device (#606)

This experiment proves the exact behaviour of LeanOS's PCI segment scan with
[QuickProof](https://github.com/genproof/quickproof-public) v0.1.0 (Coq 8.20.1,
VST 2.15, CompCert 3.15):
[`boot/pci-enumeration.h`](../../../boot/pci-enumeration.h).

`pci_enumerate_segment` reads the first sixteen dwords of every readable
function of one configuration segment: 256 buses, 32 devices and 8 functions,
in order, into a 16-entry snapshot (`docs/pci-enumeration.md`). Every header
it reads comes from the device. The Qotom PCI diagnostic kernel and the lab's
final PCI admission capture collect the inventory with it, and the inventory
checks consume its snapshot. The theorem is about the C source under
CompCert's semantics for x86-64, for every input the law allows. The decision
record is ADR 0030, with its #606 amendment.

The code was not provable as written: it returned `struct
pci_enumeration_result` by value, which `clightgen` refuses (the pilot's survey,
ADR 0030 refactor 1). Issue #606 made it return the status and write the
result through an optional pointer. Statuses, locations, reads and the
published snapshot are unchanged.

## The law

The law is a C program in [`project/harness/`](project/harness/). Its first
comment states the claim, and that comment, not this summary, is what a reader
must review.

**`enumeration_exact`: the scan's whole behaviour, against any device.** The
device may fail any read or answer any value, a different one each time. Each
of the callback, the snapshot and the result record may be NULL. For every
such device the scan:

- reads exactly in bus, device, function order:
  - each function's identity dword;
  - right after an identity that names a vendor other than 0xffff, while
    fewer than 16 functions have been found, that function's dwords 4 to 60.
- reads nothing after a failed read or after the 17th function found. So it
  makes at most 65536 + 16 × 15 reads, all of conventional space;
- returns INVALID_ARGUMENT, without a read, exactly when the callback or the
  snapshot is NULL;
- returns READ_FAILED exactly when a read failed, naming it, and
  CAPACITY_EXCEEDED exactly at the 17th function, naming it. It publishes
  count 0 on both;
- otherwise returns OK after all 65536 identity reads, and publishes exactly
  the functions found, in order, each with the 16 dwords the device answered.

The law's device is the reference. It checks every read against that order
and keeps its own copy of the functions found, and `main` compares the
snapshot with that copy. One law gives both safety and completeness: when no
read fails and at most 16 functions answer, OK is the only status left.

Not claimed (`project/DEVIATIONS.md`):

- the kernel's own readers (mechanism #1, ECAM), their address decoding, and
  real buses: the law brings its own device;
- that the segment is an atomic snapshot (the law is stated in terms of the
  answers the scan got);
- termination, though every loop is bounded;
- anything about the compiled kernel (CompCert's C is not GCC's).

## The proof's shape

`Defs.v` models the scan as a state machine over the device's answers:

- `run start h` is the scan's state after the answers `h`;
- `next_read h` is the read it makes next;
- `scan h` is its outcome when it returns.

The scan's specification (`EnumSpecs.enum_pre_post`) is parameterized by an
abstract device `Dev ctx h`. Its read protocol (`read_spec Dev`) asks the
callback only for `next_read h`. That is the strongest ordering fact the scan
can promise, and the law's device needs it to discharge its own checks. The
postcondition says the device answered exactly the reads `h` of a scan with
outcome `scan h`.

## Results

`qp verify` on a fresh clone: **PASS** ([`VERIFY.md`](VERIFY.md)).

| Theorem | Result | Axioms |
| --- | --- | --- |
| `enumeration_exact` | PROVED | 10: standard + VST malloc |

The statement and `whole_prog` are identical to the frozen contract, and the
regenerated Clight is identical to the committed Clight. The proof sources
contain no `Admitted`, `admit`, `Axiom`, `Parameter` or `Conjecture`.

`qp check` ([`CHECK.md`](CHECK.md)):

- 3,000 native ASan/UBSan runs and 10 CompCert-interpreter runs, all clean;
- 34 of 34 mutants killed.

What it took (development machine, 12 CPUs):

| Item | Measure |
| --- | --- |
| C under test | 105 lines (one header), 1 wrapper; 1 law, 138 lines |
| Coq written | 2,776 lines in 25 files (the contract included), by component below |
| Shared model and specs | `Defs.v`, `EnumSpecs.v`, `Bodies.v`: 228 lines |
| `pci_enumeration_finish`, `pci_enumerate_segment`, `enum_scan` | `Scan*.v`: 616 lines |
| The law's `main`, device and helpers | `Law*.v` and its contract: 1,831 + 101 lines; `LawMain.v` alone takes 7 to 12 min |
| Who wrote it | AI agents (Claude Opus 5.5 in Claude Code). One session wrote the law, the model and the specifications; two agents then proved the scan's bodies and the law in parallel, in 1.2 and 3.5 hours. |

`qp verify` checks all of it in 17 minutes with 6 build jobs.

## Reproducing

```sh
scripts/check-quickproof.sh --check pci-enumeration
```

[`check.conf`](check.conf) gives the interpreter 600 s per seed: a run that
scans the whole segment makes 65,536 reads or more through the law's checking
device. At the default 10 s, 6 of 10 seeds timed out, and at 120 s on a loaded
machine, 1 of 10 did. The gate counts a timed-out seed as a failure, because
it gives no verdict.
`scripts/check-quickproof-pins.sh`, part of `scripts/check.sh`, fails when
`boot/pci-enumeration.h` or any file of `project/` or `proof/` differs from
[`pins.tsv`](pins.tsv). The pci-capabilities project pins
`boot/pci-enumeration.h` too, and it was re-verified at #606's refactor.

## Files

- `project/`: the QuickProof project. It holds `project.conf` (the pins),
  `quickproof.conf`, the law, `env/` (input distributions for the native and
  interpreter runs only), `patch/` (the wrapper unit and its header) and
  `DEVIATIONS.md`.
- `proof/src/`: the Coq proof sources; everything else in the proof
  repository is regenerated by `qp assemble`.
- `CHECK.md`, `VERIFY.md`, `check.conf`, `pins.tsv`.

QuickProof is under the PolyForm Noncommercial License 1.0.0, and its
toolchain includes CompCert under the INRIA Non-Commercial License. The files
here were written for LeanOS and are under its license. Running them uses
QuickProof under its own.
