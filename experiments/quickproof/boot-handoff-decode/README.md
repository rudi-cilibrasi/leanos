# QuickProof project 8: the Multiboot2 handoff copy and decoder of `boot_allocate` (#624)

This experiment proves that the C of LeanOS's Multiboot2 handoff copy and
decoder reads exactly the bootloader memory it must, asks exactly the
questions the generated Lean exports require of it, and returns exactly the
status their answers decide, for any bootloader memory and any answers of
those exports. It uses
[QuickProof](https://github.com/genproof/quickproof-public) v0.1.0 (Coq 8.20.1,
VST 2.15, CompCert 3.15) on
[`include/boot_handoff_decode.h`](../../../include/boot_handoff_decode.h).

This is the first C in LeanOS that reads memory the bootloader wrote.
`boot_allocate` copies the Multiboot2 information into an immutable copy, one
8-byte chunk at a time through the generated copy stream, and then decodes the
copy through the generated decoder. It uses five exports of
`LeanOS/BootMemoryMapStreaming.lean` and `LeanOS/BootMemoryMapStreamAuthority.lean`:

- the stream reset, asked seven words, and the stream transition, asked nine
  words per chunk, with seven state words carried from chunk to chunk;
- the decoder reset and the decoder transition, each asked 41 words, the
  transition once per chunk with 35 words of the current state;
- the block projection, asked four words for each of the 64 bitmap blocks at
  each memory-map entry.

The Lean theorems of those modules say what the answers mean. This theorem is
about the C between the bootloader's memory and the exports, under CompCert's
semantics for x86-64, for every input the law allows. The decision record is
ADR 0030, with the amendment of issue #624.

The code was not provable as written. The copy read physical memory through
the identity map, every check ended in the `noreturn` `handoff_fail`, the
decoder copied 41-word states by value and the projection wrote kernel
globals. Issue #624 moved the code into the header (ADR 0030 refactor 1):

- the physical read and the projection's entry record are callbacks;
- the decoder alternates between two caller states instead of copying them;
- the bitmaps and every result are caller storage;
- each check returns its own status, 57 in all, and the kernel's
  `boot_handoff_require` maps each to the reason its check gave before.

The reads, the Lean calls, the order of checks, the reasons and the serial
protocol are unchanged.

## The law

The law is a C program in [`project/harness/`](project/harness/). Its first
comment states the claim, and that comment, not this summary, is what a reader
must review.

**`handoff_decode_exact`: the copy and the decoder, against any bootloader and
any Lean.** The harness supplies the bootloader's memory, the entry record and
the five exports itself:

- a bootloader whose every read answers any eight bytes, a different value
  each time, so the size read and chunk 0 may disagree;
- an adversarial Lean that answers every call with any 64-bit value, a
  different one each time;
- a record that checks each entry it is given.

Each checks every call. The magic, the address and the candidate may be
anything, and every object (the copy, the bitmaps, the two states and the
records) may hold any values. `main` makes one of four calls: an allocation
(the extent, then, on OK, the copy and the projection with the extent it
wrote, as `boot_allocate` calls them), or the copy, the projection or the
candidate decoder alone. Each:

- reads the information's first eight bytes once, and, once the bounds accept
  the extent they give, each chunk once and in order;
- copies a chunk only after the stream's answers accept it, with the chunk as
  read;
- asks each transition about exactly the state, offset and chunk it carries,
  and stops at the first rejection;
- at each entry event, records the entry in one of the 256 slots and asks the
  block projection about every block, in order;
- accepts a handoff, or a candidate, only when the decoder's final state does;
- returns the status of the first check that fails, and writes only the
  copy's accepted chunks, the bitmaps, the two states and, on OK, its record.

The law's bootloader, record and Lean are the reference. They keep their own
copy of the state, the answers and the chunks, check every call against them,
and `main` compares the status and every object with the law's model. One law
therefore gives both directions: each read and call is the one the exports
require, and each status is the one the answers decide.

Not claimed (`project/DEVIATIONS.md`):

- what the answers of the real Lean exports mean: the Lean theorems say that;
- the physical read and the record themselves, and the kernel's mapping from
  statuses to reasons, which `scripts/check-boot-handoff-stream.sh` checks on
  the source;
- the kernel's use of the decoded words after the decoder: the frame
  selection is project 9's ([#627](https://github.com/rudi-cilibrasi/leanos/issues/627));
- termination, though every loop is bounded;
- anything about the compiled kernel (CompCert's C is not GCC's).

## The proof's shape

`Defs.v` models the four calls as one state machine over the callees'
answers, whose stages are those of the law's `struct law`:

- `run x (start x) h` is the machine's stage after the answers `h`;
- `next_call x h` is the read or call it makes next;
- `returns x h` is its outcome when it returns: the status and the memory it
  leaves.

An allocation is two calls of the law. The extent's postcondition leaves the
machine at `after_extent`, where the projection's precondition starts.

The specifications (`HandoffSpecs.v`) are parameterized by an abstract oracle
`Ora gv ctx rctx x h`, the bootloader, the record and the Lean behind the
inputs `x` after they have answered the calls `h`, for the read's and the
record's contexts. Each callee's specification asks it only for
`next_call x h` and records its answer. Each function's postcondition says the
callees answered exactly the calls `h` of a run with outcome `returns x h`,
and every object it is given holds that outcome's contents. `InternalSpecs.v`
specifies each of the header's functions as one phase of the machine.

The model was checked against the real header before any proof was written.
A native driver ran the header in 762 scripted runs, 77,202 calls, and the
model gave the same calls, status and memory on every one. All 6 deliberately
broken models were caught.

## Results

`qp verify` on a fresh clone: **PASS** ([`VERIFY.md`](VERIFY.md)).

| Theorem | Result | Axioms |
| --- | --- | --- |
| `handoff_decode_exact` | PROVED | 13: standard + VST malloc |

The statement and `whole_prog` are identical to the frozen contract, and the
regenerated Clight is identical to the committed Clight. The proof sources
contain no `Admitted`, `admit`, `Axiom`, `Parameter` or `Conjecture`.

`qp check` ([`CHECK.md`](CHECK.md)) covers all 431 mutation sites:

- 3,000 native ASan/UBSan runs and 20 CompCert-interpreter runs, all clean;
- 14 mutants dead code, 410 of the 417 others killed. The seven survivors are
  equivalent:
  - `boot_handoff_project`'s `length` and `decoded` start at 1, not 0. Both
    are written before they are read.
  - In the stream transition's arguments, `state[1]` becomes `state[2]`, or
    `state[2]` becomes `state[1]`. Both words are 0 at every call: the reset
    is accepted only with words 1 and 2 at 0, and a transition before the last
    chunk only with word 1 at 0 and word 2 at 0.
  - The stream's `answer` array becomes one element larger, and no function
    indexes past its first size.
  - The copy's final `state[5] != total` check becomes `state[4] != total`.
    Both are false there: an accepted reset and every accepted transition
    have word 4 equal to the extent, and the last accepted chunk has word 5
    equal to it too (the reset's 0 when the extent is 0). The original check
    is defense in depth.
  - The loop that carries words 0 to 6 of the answers starts at 1. Word 0 is
    2 in the reset and in every accepted transition, so the state's word 0 is
    already the answer's.

  Each was applied by hand and run over many native seeds without a failure.

What it took (development machine, 12 CPUs):

| Item | Measure |
| --- | --- |
| C under test | 419 lines (one header), 5 wrappers; 1 law, 494 lines |
| Coq written | 8,159 lines in 47 files (the contract included), by component below |
| Shared model and specs | `Defs.v`, `HandoffSpecs.v`, `InternalSpecs.v`, `Bodies.v`: 1,119 lines |
| The header's seven functions and their wrappers | `Hd*.v`: 1,807 lines in 11 files |
| The law's `main`, callees and helpers | `Law*.v` and its contract: 5,101 lines in 31 files + 132 lines |
| Who wrote it | AI agents (Claude Opus 5.5 in Claude Code). One agent wrote the refactor and the law, and another the model and the specifications. Two more then proved the bodies and the law in parallel, in 3.4 and 6.5 hours. |

`qp verify` checks all of it in 28 minutes with 6 build jobs. Its
largest file, `HdProjection.v`, needs 3.6 GB.

## Reproducing

```sh
scripts/check-quickproof.sh --check boot-handoff-decode
```

[`check.conf`](check.conf) makes `qp check` run all 431 mutation sites
rather than a sample of 40, so the kill count the gate compares covers the
whole header, and gives each interpreter seed 30 s. `scripts/check-quickproof-pins.sh`,
part of `scripts/check.sh`, fails when `include/boot_handoff_decode.h`, the
two Lean modules (the exports the law's protocol and the shim's prototypes
follow) or any file of `project/` or `proof/` differs from
[`pins.tsv`](pins.tsv).

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
