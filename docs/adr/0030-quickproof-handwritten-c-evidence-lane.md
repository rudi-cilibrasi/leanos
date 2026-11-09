# ADR 0030: QuickProof as an evidence lane for handwritten library C

## Status

Accepted as an optional evidence lane, issue #597. Pilot:
[`experiments/quickproof/boot-text-console`](../../experiments/quickproof/boot-text-console/README.md),
`qp verify` PASS for both laws.
QuickProof is not part of the merge gate (see "License" below).

## Context

LeanOS has three kinds of executable code, with three kinds of evidence:

| Code | Size at `ee64a79` | Evidence before #597 |
| --- | --- | --- |
| C emitted from Lean exports | per export | rung 3 for 12 exports: the emitted C computes the Lean definition on every input under the reviewed C-subset semantics (ADRs 0023, 0029) |
| Handwritten C: `boot/kernel.c`, the `boot/*.h` and `include/*.h` helpers, `hardware/wifi/*.h`, `subjects/*.c` | 11,254 + 4,435 + 818 lines | hosted tests (ordinary, ASan/UBSan), QEMU scenarios, Qotom runs; **no proof** |
| Assembly (`boot/boot.S`, entry stubs, fixtures) | 6,312 lines | QEMU scenarios and probes; no proof |

The C-subset method cannot reach the handwritten C. It gives meaning to
scalar `uint64_t`/`uint8_t` code with `goto` join points. Handwritten helpers
walk byte buffers, index arrays and write through struct pointers. A C
semantics with a memory model, written and reviewed in Lean, would be a
CompCert-sized project.

[QuickProof](https://github.com/genproof/quickproof-public) (GenProof, v0.1.0,
2026-11-02) proves properties of C code with VST and CompCert's Clight semantics
in Coq. A property is a C program, the spec or law, that draws arbitrary inputs
(`nondet_*`), restricts them (`qp_assume`) and checks results (`qp_assert`). It
becomes `Theorem law : harness_safe whole_prog`, VST's whole-program judgement.
Read through VST's adequacy theorem, it means that no run of the program, for
any input the spec allows, has undefined behaviour in CompCert's semantics, so
every assertion holds and every access is in bounds. That reading has the
caveat in "TCB of a QuickProof result" below. AI agents write the proof. `qp verify` checks it from a fresh clone
against a frozen contract and an axiom allow-list.

## What the pilot measured

The pilot proves the early boot text console end to end. It covers the
Multiboot2 tag-chain parser, which reads bytes the bootloader controls, and the
VGA text writer, whose memory safety depends on a Lean-decided predicate. The
results are in the experiment's README.

1. **The tool runs here.** The published Docker image verified its own example
   in 43 s on the development machine. `qp check` (VST lint, 3,000 native
   ASan/UBSan runs, CompCert-interpreter runs, mutants) takes about 25 s per run
   on this project.
2. **The pre-proof checks find weak specs fast.** On the first spec,
   mutation testing killed 0 of 22 mutants. Uniformly random bytes almost never
   form a Multiboot2 chain, so the writer was never reached. A structured
   `env.c`, a window sized exactly to the advertised surface, and a second
   (completeness) law raised it to 26 of 40. The remaining survivors are
   classified (equivalent, unclaimed, model-by-design, distribution gap) in
   the experiment's `CHECK-NOTES.md`.
3. **Two semantics, one scalar seam.** The console calls one Lean export,
   `leanos_boot_text_surface`. Each tool proves the half it can reach:
   - Lean (this repository's method, ADR 0029):
     `Refinement.BootTextConsoleC.bootTextSurfaceC_spec`. The emitted C of the
     export returns 1 exactly when `kind = 2 ∧ bits = 16 ∧ address = 753664 ∧
     0 < width ≤ 160 ∧ 0 < height ≤ 64 ∧ pitch % 2 = 0 ∧ 2·width ≤ pitch ∧
     pitch ≤ 512`, and 0 otherwise (SC-BOOT-TEXT-SURFACE-REFINEMENT).
   - Coq (QuickProof): the console's C, linked with a 25-line C model of the
     export, satisfies both laws, for every input. The model is proved in VST
     to return 1 exactly on `valid_geo_iff`, the same conjunction over the
     integers.

   Two cross-tool steps remain trusted. The first is reading that the two
   conjunctions are the same; both are printed next to each other in the
   experiment's README. The second is the `uint64_t` calling convention that
   every rung-3 theorem assumes.
4. **Coverage of the remaining handwritten C is limited by C style, not by
   the tool.** A static survey (`qp lint` and `qp audit` on call-only harnesses,
   experiment README) finds:
   - Six PCI/MADT helper headers (about 650 lines) return result structs by
     value. 11 functions; `clightgen` refuses them.
   - The copy-root builder and the frame window (318 lines) write
     page-table entries that embed the address of the next table. That is 13
     pointer-to-integer casts, which are undefined in CompCert's block-based
     memory model, plus 3 struct assignments.
   - `boot/kernel.c` has 135 inline-assembly sites and 225 `volatile` uses
     around MMIO and port I/O. Assembly is out of reach for both methods.

## Decision

1. **Keep the C-subset method for emitted C.** It is faster: the new
   refinement proof is one `csym_refine` call that checks in about 2 s. Its
   claims stay in the Lean claim index. QuickProof adds nothing there except an
   independent reading of the same C under CompCert's semantics, which is not
   worth a second toolchain.
2. **Use QuickProof for handwritten library-style C**: parsers and writers
   that work on memory passed to them, with hardware behind callbacks. These
   are exactly the pieces of the trusted path that currently have only tests.
   Each such component gets a project under `experiments/quickproof/`, with its
   laws, deviations, models of the Lean exports it calls and the proof sources.
3. **State every Lean seam as a scalar contract proved on both sides**: a
   rung-3 refinement theorem in Lean and the model's VST specification in
   Coq, with the same conjunction. A component whose safety depends on an
   export without a rung-3 theorem is modelled with any behaviour (`nondet`),
   or not proved.
4. **Report QuickProof results as their own evidence class**, "proved under
   CompCert's C semantics (QuickProof/VST)". They are not Lean theorems, so
   they are not in `INVARIANTS.md` or `LeanOS.SecurityClaims`. The README and
   `docs/security-claims.md` name them as such.
5. **Pin what a proof depends on.** Each project names the LeanOS commit its
   theorems cover. Its `pins.tsv` lists the repository files the theorems
   depend on: the C under test, the Lean source of each modelled export, and
   the project's own laws, units and proof sources.
   `scripts/check-quickproof-pins.sh` needs no QuickProof and runs in
   `scripts/check.sh`. It fails when any pinned file differs at `HEAD`, so a
   change needs a re-check (`scripts/check-quickproof.sh`) and a pin update, in
   the same way as refinement drift.
6. **Prefer refactors that open more C to proof**, where they also simplify
   the kernel. Two are now justified:
   - results through out-parameters instead of struct returns, in the PCI/MADT
     helpers;
   - physical addresses passed to the root builder as integers (it already
     assumes the identity map) instead of derived from pointers.

   Each needs its own issue and review. #597 changes no production C.

   **Amendment (#599).** The second refactor landed. The copy-root builder,
   the source check and the window builder take each root's physical address
   as an integer, check storage on physical ranges and copy their inputs
   before writing. The values are unchanged on the identity-mapped kernel,
   which passes `qotom_root_phys(&root)`. The second project,
   [`experiments/quickproof/copy-roots`](../../experiments/quickproof/copy-roots/README.md),
   proves three laws:
   - `copy_roots_exact`: the builder's whole contract, accepting exactly the
     valid arguments, writing nothing on rejection, and the exact roots and
     counts on acceptance;
   - `window_roots_isolated`: `frame_window_build`, with the same
     exactness;
   - `window_scan_exact`: the kernel's leaf-by-leaf scan accepts exactly the
     right roots.

   Its seam with Lean is not a scalar export. The law states the leaf words of
   the roots, and `LeanOS.FrameWindowWords` (SC-FRAME-WINDOW-WORDS) proves
   that those words are `FrameCopyWindow.windowRoot` over a `Closed` root.
   The trusted step is again reading two printed definitions as the same.

   **Amendment (#604).** The first refactor landed for the PCI capability
   walker: `pci_collect_capabilities` returns its status and writes the
   result through an optional pointer, and nothing else changes. The third
   project,
   [`experiments/quickproof/pci-capabilities`](../../experiments/quickproof/pci-capabilities/README.md),
   proves two laws:
   - `capabilities_adversarial`: against a device that may fail any read or
     answer anything, the walker reads only the function's conventional
     space, at most 4 + 48 times, rejects exactly the invalid arguments,
     names every failure, and on OK publishes exactly the list it read;
   - `capabilities_complete`: a fixed, well-formed list of up to 48 headers
     is published whole.

   The walker's specification is parameterized by an abstract device
   protocol, so one proof serves both laws. Its seam is with the callers, not
   with Lean: they consume the published headers as the observations
   describe. The other helpers of refactor 1 still return structs:
   enumeration, the command executor, the power, AF and express
   observations, the final admission check and the MADT consumer.

   **Amendment (#606).** Enumeration got the same refactor:
   `pci_enumerate_segment` returns its status and writes the result through
   an optional pointer, and nothing else changes. The fourth project,
   [`experiments/quickproof/pci-enumeration`](../../experiments/quickproof/pci-enumeration/README.md),
   proves one law, `enumeration_exact`. Against a device that may fail any
   read or answer anything, the scan reads exactly in bus, device, function
   order: each identity dword, then the other fifteen dwords of each of the
   first sixteen functions found. It rejects exactly a NULL callback or
   snapshot, names the first failed read or the seventeenth function, and
   on OK publishes exactly the functions found as the device answered them.
   The law's device keeps its own copy of what it answered, so the one law
   gives both safety and completeness. The capability project, which pins
   the enumeration header too, was re-verified at the refactor. The other
   helpers of refactor 1 still return structs: the command executor, the
   power, AF and express observations, the final admission check and the
   MADT consumer.

   **Amendment (#608).** The MADT consumer got the same refactor:
   `qotom_bind_validated_madt_entries` returns its status and writes the
   result through a pointer, every exit through one publishing helper, and
   nothing else changes. The fifth project,
   [`experiments/quickproof/madt-consumer`](../../experiments/quickproof/madt-consumer/README.md),
   has its seam with the Lean code the consumer calls. Its law,
   `consumer_obligations`, replaces the three Lean exports the consumer calls
   with an adversarial Lean that answers anything and checks every call. The
   consumer meets the caller obligations of the MADT review against every
   such Lean: the exact calls in order, the answers carried unchanged, the
   first rejection final, and a topology published only on the finish's
   acceptance. The specification is parameterized by an abstract oracle,
   like the device protocols of the PCI projects. The trusted step is
   reading the law's protocol, the review table and the Lean theorems of
   `LeanOS.QotomMadtStream` as the same. The other helpers of refactor 1,
   none of them in a booted kernel, still return structs: the command
   executor, the power, AF and express observations and the final admission
   check.

   **Amendment (#614).** The ACPI root and table copy of `boot_allocate`
   got refactor 1. It ended every check in the `noreturn` `handoff_fail`,
   returned structs by value and used kernel globals. Now it is
   `include/acpi_table_copy.h`:
   - the physical copy is a callback;
   - the storage comes in as arguments;
   - each check returns its own status, which `acpi_table_copy_require`
     maps to the reason the check gave before.

   The sixth project,
   [`experiments/quickproof/acpi-table-copy`](../../experiments/quickproof/acpi-table-copy/README.md),
   has two adversaries in its law, `table_copy_exact`: a firmware whose
   every copy may fail or write any bytes, and a Lean that answers anything.
   Both check every call. Against all of them, the pipeline:
   - copies only within its storage, at most 64 KiB per table;
   - replays every copied byte through the generated copy stream;
   - meets the copy sequence's caller obligations;
   - publishes a MADT only from complete copies whose envelopes and checksums
     pass.

   The aperture copy itself stays a trusted boundary. The proof also shows
   that eight of the pipeline's checks cannot fail, because each tests what
   the pipeline itself just computed. They stay in the code as defense in
   depth.

   **Amendment (#617).** The canonical MADT admission of `boot_allocate`
   got the same refactor. Three kernel helpers called `handoff_fail`
   directly and read the copy through the kernel's `struct copied_acpi_sdt`.
   They moved into `include/madt_generated_admission.h`. Each check now
   returns its own status, which `madt_generated_require` maps to the reason
   the check gave before.

   The seventh project,
   [`experiments/quickproof/madt-generated-admission`](../../experiments/quickproof/madt-generated-admission/README.md),
   has an adversarial Lean in its law, `admission_exact`, that answers
   anything and checks every call. Against every such Lean, each of the
   header's four functions:
   - makes exactly the envelope, entry-stream and admission calls the exports
     require, in order;
   - carries the answers unchanged;
   - returns the status that the first rejecting answer decides;
   - writes the APIC ID only on OK.

   With the sixth project, both headers between the firmware's tables and
   the admitted APIC ID are now proved against any firmware and any Lean.
   Two parts stay outside the proofs:
   - the aperture copy;
   - the kernel's calls of the two headers and its mapping from statuses to
     reasons, which `scripts/check-boot-handoff-stream.sh` checks on the
     source.

   **Amendment (#624).** The Multiboot2 handoff copy and decoder of
   `boot_allocate` got the same refactor. The copy read physical memory
   through the identity map, every check ended in `handoff_fail`, the
   decoder copied 41-word states by value, and the projection wrote kernel
   globals. They moved into `include/boot_handoff_decode.h`:
   - the physical read and the projection's entry record are callbacks;
   - the decoder alternates between two caller states, so no state is copied
     and the header has no `volatile` access;
   - each check returns its own status, which `boot_handoff_require` maps to
     the reason the check gave before.

   The eighth project,
   [`experiments/quickproof/boot-handoff-decode`](../../experiments/quickproof/boot-handoff-decode/README.md),
   has an adversarial bootloader and an adversarial Lean in its law,
   `handoff_decode_exact`. Each answers anything and checks every call.
   Against every such pair, the header:
   - reads the information's first eight bytes once, and each chunk of the
     extent once and in order;
   - copies a chunk only once the copy stream accepts it;
   - asks each decoder transition about exactly the state, offset and chunk
     it carries;
   - returns the status that the first rejecting answer decides;
   - writes only the copy's accepted chunks, the bitmaps, the two states and
     its records.

   Three parts stay outside the proof:
   - the physical read and the entry record themselves;
   - the kernel's mapping from statuses to reasons, which
     `scripts/check-boot-handoff-stream.sh` checks on the source;
   - the frame selection after the decoder, which is the ninth project's
     (#627).

   **Amendment (#627).** The frame selection, scrub and publication of
   `boot_allocate` got the same refactor. Every check ended in
   `handoff_fail`, each candidate's decoded state was returned by value and
   copied with volatile loads, and the scrub was a volatile zero-then-read
   loop over physical memory. They moved into
   `include/boot_frame_selection.h`, as seven steps:
   - the candidate decoder and the scrub are callbacks, so the header has no
     physical access and no `volatile`;
   - the selection decodes candidates into one caller state until one is
     accepted, and the frame-budget scan into a second, so no state is
     copied;
   - each condition of each check returns its own status, which
     `boot_frame_require` maps to the reason the check gave before;
   - the production mutation fixtures keep their places between the steps.

   The ninth project,
   [`experiments/quickproof/boot-frame-selection`](../../experiments/quickproof/boot-frame-selection/README.md),
   has an adversarial candidate decoder, scrub and Lean in its law,
   `frame_selection_exact`. Each answers anything and checks every call.
   Against every such triple, the header:
   - selects exactly the first candidate every answer accepts, and stops at
     the first decoder rejection;
   - scrubs once, exactly the selected frame, and only after every
     cross-check accepted it;
   - asks for the authority result only after the scrub succeeded;
   - returns the status of the first failed check;
   - writes only its results, and every other word keeps its value.

   With projects 6 to 8, this covers `boot_allocate` from the handoff to the
   published frame. Three parts stay outside the proof:
   - that the kernel's decoder is project 8's, and what its scrub does to
     physical memory;
   - the kernel's mapping from statuses to reasons and the fixtures' places,
     which `scripts/check-boot-handoff-stream.sh` checks on the source;
   - what the Lean answers mean, which the theorems of
     `LeanOS.BootMemoryMapStreamAuthority` state.

## License

QuickProof is under the PolyForm Noncommercial License 1.0.0. Its toolchain
includes CompCert, under the INRIA Non-Commercial License (commercial use needs
a licence from AbsInt). LeanOS is Apache-2.0. The experiment directories hold
only files written for LeanOS (C harnesses, models, Coq proof sources), under
LeanOS's license. Running `qp verify` uses QuickProof and CompCert under their
own licenses. A required CI check would make every contributor and downstream
user depend on noncommercial software, so the lane stays optional:
`scripts/check-quickproof.sh` runs the published Docker image on demand. Only
the pin check above runs in ordinary CI.

## TCB of a QuickProof result

In addition to what the experiment's spec says, and as QuickProof's own
`docs/GUARANTEES.md` lists:

- Coq 8.20.1, VST 2.15 and CompCert 3.15's Clight semantics. VST's adequacy
  theorem is not yet instantiated for QuickProof's environment, and every
  theorem rests on 13 axioms (standard ones and VST's malloc library).
- `clightgen` and QuickProof's translation scripts and `qp verify`.
- The deviations: `-Dvolatile=` (VST cannot reason about volatile accesses),
  the wrapper unit that gives the header's static functions external names,
  and the model of each Lean export.
- The gap between CompCert's C and the GCC/Clang build LeanOS ships. The theorem
  covers the source, not the compiled kernel. It is single-threaded and
  partial-correctness, and the kernel's interrupts and the physical address
  of the aperture are outside it.

## Consequences

- One handwritten kernel component has a machine-checked theorem about its
  C. It covers every bootloader buffer and every printed byte sequence. A
  Lean-proved predicate is load-bearing in it: with an arbitrary selector, the
  writer's memory safety does not hold.
- A change to `include/boot_text_console.h`, `LeanOS/BootTextConsole.lean`, or
  the experiment's files fails the pin check until the QuickProof project is
  re-checked and the pins updated. A change to `valid` also fails the Lean
  build: `bootTextSurfaceC_spec` states the conjunction, and the emitted AST
  and pinned statement must be regenerated.
- Proof cost is dominated by VST mechanics. The pilot took 2,251 lines of Coq
  for about 150 lines of C under test, written by AI agents in a few hours of
  wall-clock time with four agents in parallel. `qp verify` checks it in
  9 minutes. The Lean refinement of the same seam checks in 2 seconds. The
  experiment README has the breakdown.
