# QuickProof project 9: the frame selection, scrub and publication of `boot_allocate` (#627)

This experiment proves that the C which turns the generated decoder's answers
into the one frame LeanOS's boot allocator publishes asks exactly the
questions the generated Lean exports require of it, scrubs exactly the frame
they select and only once every check accepted it, and returns exactly the
status their answers decide, for any answers of those exports, any candidate
decoder and any scrub. It uses
[QuickProof](https://github.com/genproof/quickproof-public) v0.1.0 (Coq 8.20.1,
VST 2.15, CompCert 3.15) on
[`include/boot_frame_selection.h`](../../../include/boot_frame_selection.h).

With projects 6 to 8 (the ACPI table copy, the MADT admission, and the
Multiboot2 handoff copy and decoder), this covers `boot_allocate` from the
handoff to the published frame. After the MADT admission, `boot_allocate`
uses six exports of `LeanOS/BootMemoryMapStreamAuthority.lean`:

- the manifest overlay, asked three words for each of the 64 bitmap blocks,
  and the free word, asked once per block;
- the projection's terminal result, asked nine words with the 64 free words;
- for each decoded candidate, the manifest's answer and the exact-projection
  consumer;
- the authority result, asked five words about the selected frame.

The Lean theorems of that module say what the answers mean. This theorem is
about the C between the decoder's states and the exports, under CompCert's
semantics for x86-64, for every input the law allows. The decision record is
ADR 0030, with the amendment of issue #627.

The code was not provable as written. It ran inside `boot_allocate`: every
check ended in the `noreturn` `handoff_fail`, each candidate's decoded state
was returned by value and copied with volatile loads, and the scrub was a
volatile zero-then-read loop over physical memory. Issue #627 moved the code
into the header (ADR 0030 refactor 1):

- the candidate decoder and the scrub are callbacks;
- no decoder state is copied: the selection decodes candidates into state 0
  until one is accepted, and the frame-budget scan decodes later candidates
  into state 1;
- the manifest, the projection's bitmaps and every result are arguments and
  caller storage, and the frame-budget scenario is a runtime argument,
  `take_next`;
- each condition of each check returns its own status, 30 in all, and the
  kernel's `boot_frame_require` maps each to the reason its check gave
  before.

The Lean calls, the order of checks, the reasons and the serial protocol are
unchanged. The production mutation fixtures keep their places between the
steps, which is why the steps stay separate functions.

## The law

The law is a C program in [`project/harness/`](project/harness/). Its first
comment states the claim, and that comment, not this summary, is what a reader
must review.

**`frame_selection_exact`: the selection, scrub and publication, against any
decoder, any scrub and any Lean.** The harness supplies the candidate decoder,
the scrub and the six exports itself:

- a decoder that writes any 41 words to the state it is given and answers any
  status;
- a scrub that answers any value;
- an adversarial Lean that answers every call with any 64-bit value, a
  different one each time.

Each checks every call. The manifest, the decoded state, the bitmaps, the
results, both decoder states and the records may hold any values, and so may
`take_next` and the frame arguments of a step called alone. `main` calls
`boot_allocate`'s sequence of the seven steps (the terminal, the selection,
the cross-check, the scrub, the publication result and check, and, with
`take_next`, the rescan), or one step alone. The law states:

- each call and each argument, including the state row the decoder is given;
- that the selection takes exactly the first candidate every answer accepts,
  and stops at the first decoder rejection;
- that the scrub runs once, with exactly the selected frame, and only after
  every cross-check accepted it;
- that the authority result is asked only after the scrub succeeded;
- the status of the first failed check;
- every word each step writes, and that every other word keeps its value.

The law's decoder, scrub and Lean are the reference. They keep the state the
header must carry and check every call against it, and the law's model
(`harness/frame_selection_exact.h`) keeps its own copy of what memory must
hold. After each step `main` compares the status, every object and the
records with it. One law therefore gives both directions: each call is the
one the exports require, and each status is the one the answers decide.

Not claimed (`project/DEVIATIONS.md`):

- what the answers of the real Lean exports mean: the Lean theorems say that;
- that the kernel's decoder is `boot_handoff_decode_candidate` over the
  handoff copy, which project 8 proves, and what the kernel's scrub does to
  physical memory;
- the kernel's mapping from statuses to reasons and its mutation fixtures
  between the steps, which `scripts/check-boot-handoff-stream.sh` checks on
  the source;
- termination, though every loop is bounded;
- anything about the compiled kernel (CompCert's C is not GCC's).

## The proof's shape

`Defs.v` models each of the seven steps as a state machine over the answers of
the header's eight callees, whose stages are the law's `expect` with its
counters:

- `start x` is a step's first stage, and `run x (start x) h` its stage after
  the answers `h`;
- `next_call x h` is the call it makes next;
- `returns x h` is its outcome when it returns: the status and the memory it
  leaves, which keeps what the step does not write.

`allocate_next` composes `boot_allocate`'s sequence: each step starts from the
memory the previous one returned.

The specifications (`FrameSpecs.v`) are parameterized by an abstract oracle
over the decoder's and the scrub's contexts and the two decoder states. The
decoder and the scrub are `func_ptr'` specifications, and each export's
specification asks only for `next_call x h` and records its answer. Each
wrapper's postcondition gives a complete run of its step, its status and the
contents of every object it is given. The law instantiates the oracle with
`struct law`, through a relation that ties the law's stages and counters to
the model's progress and records the states pointer, which the decoder
compares with the row it is given.

The model was checked against the real header before any proof was written.
A native driver ran the header in 101 scripted runs, 75,309 calls, among them
five full 4,096-candidate scans, and reached all 31 statuses. The model gave
the same calls, status and memory on every run. All 14 deliberately broken
models were caught.

One step needed care. The selection's branch where the scan goes on into
state 1 updates the law's record at five levels. Unfolding those nested
updates copied the record once per field and level, and the proof of the
consume export ran out of memory at 6 GB. Stating that branch's record flat,
with its two relation facts as separate lemmas, brought it to 1.8 GB.

## Results

`qp verify` on a fresh clone: **PASS** ([`VERIFY.md`](VERIFY.md)).

| Theorem | Result | Axioms |
| --- | --- | --- |
| `frame_selection_exact` | PROVED | 13: standard + VST malloc |

The statement and `whole_prog` are identical to the frozen contract, and the
regenerated Clight is identical to the committed Clight. The proof sources
contain no `Admitted`, `admit`, `Axiom`, `Parameter` or `Conjecture`.

`qp check` ([`CHECK.md`](CHECK.md)) covers all 195 mutation sites:

- 3,000 native ASan/UBSan runs and 20 CompCert-interpreter runs, all clean;
- the VST lint is clean;
- 191 of the 191 live mutants killed. The other 4 are dead code: they change
  the outer dimension of the `states[2][41]` parameter, which C adjusts to a
  pointer either way.

What it took (development machine, 12 CPUs):

| Item | Measure |
| --- | --- |
| C under test | 346 lines (one header), 7 wrappers; 1 law, 529 lines and a 97-line header |
| Coq written | 7,406 lines in 48 files (the contract included), by component below |
| Shared model and specs | `Defs.v`, `FrameSpecs.v`, `InternalSpecs.v`, `Bodies.v`: 1,365 lines |
| The header's seven functions and their wrappers | `Fs*.v`: 966 lines in 8 files |
| The law's `main`, callees and helpers | `Law*.v` and its contract: 4,927 lines in 35 files + 148 lines |
| Who wrote it | AI agents (Claude Opus 5.5 in Claude Code). One agent wrote the refactor and the law, and another the model and the specifications. Two more then proved the bodies and the law in parallel. The bodies took 1.4 hours, reusing project 8's fast LOCAL removal and pointer facts. The law took about 6.8 hours: its first agent stopped after 5.3 hours when its session ended, and a second finished it in 1.5 hours. |

`qp verify` checks all of it in 42 minutes with 6 build jobs. The largest of
the law's files, `LawManifest.v`, needs 3.4 GB.

## Reproducing

```sh
scripts/check-quickproof.sh --check boot-frame-selection
```

[`check.conf`](check.conf) makes `qp check` run all 195 mutation sites
rather than a sample of 40, so the kill count the gate compares covers the
whole header, and gives each interpreter seed 30 s.
`scripts/check-quickproof-pins.sh`, part of `scripts/check.sh`, fails when
`include/boot_frame_selection.h`, the Lean module (the exports the law's
protocol and the shim's prototypes follow) or any file of `project/` or
`proof/` differs from [`pins.tsv`](pins.tsv).

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
