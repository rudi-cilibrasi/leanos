# QuickProof project 3: the PCI capability walker against any device (#604)

This experiment proves two properties of LeanOS's handwritten PCI capability
walker with [QuickProof](https://github.com/genproof/quickproof-public)
v0.1.0 (Coq 8.20.1, VST 2.15, CompCert 3.15):
[`boot/pci-capabilities.h`](../../../boot/pci-capabilities.h).

`pci_collect_capabilities` follows a function's conventional capability list.
Every pointer it follows comes from the device, so a hostile or faulty device
controls the walk (`docs/pci-capability-observation.md`). The PM, AF and PCI
Express observations, the Qotom Broadcom assignment and D3 paths, and the lab
capture all consume what it publishes. The theorems are about the C source
under CompCert's semantics for x86-64, for every input the laws allow. The
decision record is ADR 0030, with its #604 amendment.

The code was not provable as written: it returned `struct
pci_capability_result` by value, which `clightgen` refuses (the pilot's survey,
ADR 0030 refactor 1). Issue #604 made it return the status and write the
result through an optional pointer. Statuses, offsets, reads and the
published snapshot are unchanged.

## The laws

Each law is a C program in [`project/harness/`](project/harness/). Its first
comment states the claim, and that comment, not this summary, is what a reader
must review.

- **`capabilities_adversarial`: no device can misdirect the walker.** The
  device may fail any read or answer any value, a different one each time. It
  can change its configuration space between reads or lie. Each of the
  callback, the initial header, the snapshot and the result record may be
  NULL. For every such device and every initial header, the walker:
  - asks only for the header's bus, device and function, only for
    dword-aligned offsets of conventional space (at most 0xfc), and at most
    4 + 48 times;
  - returns ARGUMENT, without a read, exactly when an argument is NULL or the
    header is invalid (device above 31, function above 7, header type above
    1, vendor 0xffff);
  - on every other failure, names it exactly: the failed read, the changed
    header word, the absent header, or the bad or repeated pointer. It
    publishes count 0;
  - on OK, publishes exactly the headers it read, in order: the first at the
    list head, each next at the previous header's pointer, the last pointer 0.
    Every offset is at least 0x40, aligned and distinct, and there are at most
    48.
- **`capabilities_complete`: a well-formed list is read whole.** For a device
  whose space is fixed and holds any list of up to 48 headers, at distinct
  aligned offsets of at least 0x40, linked in order and terminated, with
  ids other than 0xff, the walker returns OK and publishes exactly those
  headers. So the adversarial law's safety is not bought by rejecting real
  lists.

Not claimed (`project/DEVIATIONS.md`):

- the kernel's own readers (ECAM and mechanism #1), their address decoding,
  and real buses: each law brings its own device;
- that the configuration space is an atomic snapshot (law 1 is stated in
  terms of the answers the walker got);
- termination, though every loop is bounded;
- anything about the compiled kernel (CompCert's C is not GCC's).

## The proof's shape

The walker's specification (`CapsSpecs.collect_pre_post`) is parameterized
by an abstract device `Dev ctx bdf h`, the device after answering the reads
`h`. The callback obeys a protocol (`read_spec Dev`): each read appends one
answer to `h`. The postcondition says the device answered exactly the reads
of `Defs.walk words h`, a Coq function of the answers, and that the outcome
is `walk`'s. Both laws instantiate `Dev` with their own device. One proof of
the walker serves both laws and any future caller's device.

**Spec finding.** Law 2 could not be proved with the device owning the whole
fixed space. The walker's postcondition says only that some space W' exists
whose answers agree with `h`. Nothing ties W' back to the planted space W, so
a W' with id 0xff at the first header is consistent with status ABSENT. The
law 2 device holds half of the space's share, and `main` keeps the other half
through the call. Afterwards VST's `data_at_values_cohere` forces W' = W. The
walker's specification is unchanged: it is stated for every `Dev`.

## Results

`qp verify` on a fresh clone: **PASS** ([`VERIFY.md`](VERIFY.md)).

| Theorem | Result | Axioms |
| --- | --- | --- |
| `capabilities_adversarial` | PROVED | 10: standard + VST malloc |
| `capabilities_complete` | PROVED | 10: standard + VST malloc |
| `suite` (both, with one specification per function) | PROVED | 10: standard + VST malloc |

The statements and `whole_prog` are identical to the frozen contract, and the
regenerated Clight is identical to the committed Clight. The proof sources
contain no `Admitted`, `admit`, `Axiom`, `Parameter` or `Conjecture`.

`qp check` ([`CHECK.md`](CHECK.md)):

- 3,000 native ASan/UBSan runs per law and 20 CompCert-interpreter runs per
  law, all clean;
- 36 of 40 mutants killed.

The four survivors are equivalent:

- `offsets[4]` becomes `offsets[5]`: the loop reads only the first four
  entries;
- three change a constant of the cycle set's bit,
  `UINT64_C(1)<<((offset-64)/4)`, to 63, 2 or 3 (the report does not say
  which constant). Each reading was checked by hand (63, 2 or 3 for the 64;
  2 for the 1; 3 for the 4). On the aligned offsets 0x40–0xfc that the test
  just before admits, each still gives distinct offsets distinct bits of the
  64-bit set, so it detects the same repeats.

What it took (development machine, 12 CPUs):

| Item | Measure |
| --- | --- |
| C under test | 85 lines (one header), 1 wrapper; 2 laws, 247 lines |
| Coq written | 4,917 lines in 30 files (the three contracts included), by component below |
| Shared model and specs | `Defs.v`, `CapsSpecs.v`, `Bodies.v`: 215 lines, one specification per function for both laws |
| `pci_capability_finish`, `pci_collect_capabilities`, `caps_collect` | `CollectLemmas.v`, `CollectProof.v`: 897 lines, about 5 min to check |
| Law 1 `main` and helpers | `Adv*.v` and its contract: 2,337 + 104 lines, about 16 min |
| Law 2 `main` and helpers | `Comp*.v` and its contract: 1,238 + 104 lines |
| Who wrote it | AI agents (Claude Opus 5.5 in Claude Code). One session wrote the laws, the model and the shared specifications; three agents then proved the walker's bodies and each law's `main` in parallel, in 1.5, 2.1 and 3.9 hours. |

`qp verify` checks all of it in 18 minutes with 6 build jobs, against 44 to
53 for the copy roots.

## Reproducing

```sh
scripts/check-quickproof.sh --check pci-capabilities
```

`scripts/check-quickproof-pins.sh`, part of `scripts/check.sh`, fails when
`boot/pci-capabilities.h`, `boot/pci-enumeration.h` (the header and callback
types), or any file of `project/` or `proof/` differs from
[`pins.tsv`](pins.tsv).

## Files

- `project/`: the QuickProof project. It holds `project.conf` (the pins),
  `quickproof.conf`, the two laws, `env/` (input distributions for the native
  and interpreter runs only), `patch/` (the wrapper unit and its header) and
  `DEVIATIONS.md`.
- `proof/src/`: the Coq proof sources; everything else in the proof
  repository is regenerated by `qp assemble`.
- `CHECK.md`, `VERIFY.md`, `pins.tsv`.

QuickProof is under the PolyForm Noncommercial License 1.0.0, and its
toolchain includes CompCert under the INRIA Non-Commercial License. The files
here were written for LeanOS and are under its license. Running them uses
QuickProof under its own.
