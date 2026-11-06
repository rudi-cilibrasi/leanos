# QuickProof project 2: the copy roots and frame-window roots (#599)

This experiment proves three properties of LeanOS's handwritten page-table
builders with [QuickProof](https://github.com/genproof/quickproof-public)
v0.1.0 (Coq 8.20.1, VST 2.15, CompCert 3.15):

- [`include/qotom_copy_root_builder.h`](../../../include/qotom_copy_root_builder.h);
- [`include/frame_copy_window.h`](../../../include/frame_copy_window.h).

These headers keep every subject's frames out of the kernel's closed root on
the J1900, which has no SMAP (ADR 0017, `docs/frame-copy-window.md`). The
theorems are about the C source under CompCert's semantics for x86-64, for
every input the laws allow. The decision record is ADR 0030, with its #599
amendment.

The code was not provable as written: each table entry embedded the next
table's address through a pointer-to-integer cast, and the storage checks
ordered and subtracted unrelated pointers. Both are undefined in CompCert.
Issue #599 first made every root's physical address an integer argument; on
the identity-mapped kernel the values are unchanged.

## The laws

Each law is a C program in [`project/harness/`](project/harness/). Its first
comment states the claim, and that comment, not this summary, is what a reader
must review.

- **`copy_roots_exact`: the copy-root builder's whole contract.** For any
  source root, closed and copy storage, inventory, alias list, result record
  and physical placements, with each of the six pointers possibly NULL,
  `qotom_build_copy_roots`:
  - returns OK exactly when every argument is valid;
  - otherwise writes nothing;
  - never changes the source;
  - on OK writes exactly a closed root, which is the source with every present
    leaf of a protected frame removed, and a copy root, which is the closed
    root plus exactly the requested supervisor no-execute aliases. Both roots'
    non-leaf entries name their own tables at their physical addresses, and
    the result holds the exact counts.
- **`window_roots_isolated`: the window builder.** `frame_window_build`
  returns OK exactly when:
  - the four physical ranges are valid and pairwise disjoint;
  - the window has the reviewed geometry (`LeanOS.FrameCopyWindow.geometryOk`);
  - the source and the inventory are well-formed;
  - the window's frames are protected and its alias slots absent;
  - a prior build's counts match.

  On OK the closed root is as above, and the fetch and send roots equal it
  except at the alias slots, where they map exactly the holder's window
  frames, supervisor and no-execute: writable in the fetch root, read-only in
  the send root.
- **`window_scan_exact`: the kernel's scan.** `frame_window_root_exact`, which
  the kernel and the Qotom production image run over every built root,
  returns 1 exactly on roots of that shape and changes nothing.

Not claimed (`project/DEVIATIONS.md`):

- that each physical address is where its storage is: the caller's
  obligation, met by `qotom_root_phys` under the identity map;
- the completeness of the inventory;
- CR3 publication, TLB behaviour and interrupts;
- termination;
- anything about the compiled kernel (CompCert's C is not GCC's).

## The seam with Lean

`LeanOS.FrameCopyWindow` proves the window's isolation theorems
(`windowRoot_protected`, `windowRoot_other_absent`, the copy refinements)
assuming the kernel's roots are `windowRoot closed g w` over a `Closed` root.
Its docstring used to say the construction was "tested, not proved".
`window_roots_isolated` states the leaf words the C writes, and
[`LeanOS/FrameWindowWords.lean`](../../../LeanOS/FrameWindowWords.lean) proves
in Lean that exactly those words decode to the model's hypotheses:

| Side | Theorem | Statement |
| --- | --- | --- |
| Coq, the C | `window_roots_isolated` | on OK, for every page `p`: `closed.pt[p] == (present(s) && member(frame(s)) ? 0 : s)`; at an alias slot `fetch.pt[p] == (((base >> 12) + (p - slot)) << 12) \| P \| NX \| W` and `send.pt[p]` the same without `W`; elsewhere both equal `closed.pt[p]` |
| Lean, the model | `FrameWindowWords.window_roots_of_words` (SC-FRAME-WINDOW-WORDS) | if the leaves are `closedWord frames (source p)` and `windowWord closed base limit slot w p` under `geometryOk`, then `Closed (decodeRoot closed) (Protected frames)` and `decodeRoot fetch = windowRoot (decodeRoot closed) (geometryOf base limit slot) true`, and the same for `send` with `false` |

`closedWord` and `windowWord` transcribe the C law's expressions. Reading the
two as the same is the one step between the tools that stays trusted, as for
the early text console. The bit facts (frame field, permission bits) are
proved in Lean with `decide` over bounded ranges, on the standard three axioms
only.

## Results

`qp verify` on a fresh clone: **PASS** ([`VERIFY.md`](VERIFY.md)).

| Theorem | Result | Axioms |
| --- | --- | --- |
| `copy_roots_exact` | PROVED | 10: standard + VST malloc |
| `window_roots_isolated` | PROVED | 10: standard + VST malloc |
| `window_scan_exact` | PROVED | 10: standard + VST malloc |
| `suite` (all three, with one specification per function) | PROVED | 10: standard + VST malloc |

The statements and `whole_prog` are identical to the frozen contract, and the
regenerated Clight is identical to the committed Clight. The proof sources
contain no `Admitted`, `admit`, `Axiom`, `Parameter` or `Conjecture`.

`qp check` ([`CHECK.md`](CHECK.md)):

- 3,000 native ASan/UBSan runs per law and 10 CompCert-interpreter runs per
  law, all clean, with no timed-out seed;
- 39 of 40 mutants killed.

The survivor turns `return 1` into `return 2` in `qotom_root_protected_frame`,
whose callers test only truth, so it is equivalent. The first check, with
safety laws only, killed 34. The extra mutants died once the window law also
required acceptance of valid input and the scan got its own law; those were
mutants of the scan, and one in the geometry was a distribution gap of the
input generator.

What it took (development machine, 12 CPUs):

| Item | Measure |
| --- | --- |
| C under test | 207 + 156 lines (two headers), 3 wrappers; 3 laws, 497 lines |
| Coq written | 8,512 lines in 38 files (generated contract headers included), by component below |
| Shared model and specs | `Defs.v`, `RootsSpecs.v`, `Bodies.v`: 437 lines, one specification per function for all three laws |
| Small functions and wrappers | `SmallProof.v`: 495 lines |
| `qotom_build_copy_roots` | `BuildLemmas.v`, `BuildProof.v`: 1,182 lines, about 31 min to check |
| `frame_window_root_exact`, `frame_window_build` | `Window*.v`: 1,185 lines, about 10 min |
| Law 1 `main` and helpers | `Law1*.v`: 1,700 lines; `Law1Main.v` about 40 min |
| Law 2 `main` and helpers | `Law2*.v`: 1,959 lines, about 19 min |
| Law 3 `main` and helpers | `Law3*.v` and its contract: 994 + 285 lines, about 25 min |
| Who wrote it | AI agents (Claude Opus 5.5 in Claude Code). One session wrote the laws, the model and the shared specifications; six agents then proved the bodies and each law's `main` in parallel, in 36 minutes to 6.6 hours each. |

**Spec findings.** The body agents proved the specifications as given, with
one exception. The first builder specification let the inventory and alias
arrays be empty. An empty array gives no valid pointer, but the builder's
`!protected_frames` and `!aliases` tests need one in both VST and CompCert.
The builder agent stopped and reported a counterexample, and the
specification now requires nonempty arrays, as every caller passes.

**Cost.** VST dominates. With several 44 KiB roots in the frame, a failed
unification of two root-typed `data_at` items unfolds both 4096-word arrays
and costs minutes. The proofs freeze the roots they do not touch around every
load, store and call. They also seal roots behind an opaque wrapper, and in
law 3 prove `main` under the whole program's compspecs. `qp verify` checks
all of it in 44 to 53 minutes with 6 build jobs: `BuildProof.v` and
`Law1Main.v` alone take 31 and 40 minutes. The pilot took 9.

## Reproducing

```sh
scripts/check-quickproof.sh --check copy-roots
```

[`check.conf`](check.conf) gives the interpreter 120 s per seed: each run
pushes three to six 44 KiB roots through the builders, which takes about 20 s
there. The script rejects a check report with a timed-out interpreter seed.
`scripts/check-quickproof-pins.sh`, part of `scripts/check.sh`, fails when
either header, `LeanOS/FrameWindowWords.lean`, or any file of `project/` or
`proof/` differs from [`pins.tsv`](pins.tsv).

## Files

- `project/`: the QuickProof project. It holds `project.conf` (the pins),
  `quickproof.conf`, the three laws, `env/` (input distributions for the
  native and interpreter runs only), `patch/` (the wrapper unit and its
  header) and `DEVIATIONS.md`.
- `proof/src/`: the Coq proof sources; everything else in the proof
  repository is regenerated by `qp assemble`.
- `CHECK.md`, `VERIFY.md`, `check.conf`, `pins.tsv`.

QuickProof is under the PolyForm Noncommercial License 1.0.0, and its
toolchain includes CompCert under the INRIA Non-Commercial License. The files
here were written for LeanOS and are under its license. Running them uses
QuickProof under its own.
