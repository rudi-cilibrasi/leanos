# QuickProof pilot: the early boot text console (#597)

This experiment proves two properties of LeanOS's handwritten
[`include/boot_text_console.h`](../../../include/boot_text_console.h) with
[QuickProof](https://github.com/genproof/quickproof-public) v0.1.0 (Coq 8.20.1,
VST 2.15, CompCert 3.15). The header is the Multiboot2 tag-chain parser and VGA
text writer that the kernel runs before PCI quarantine (`kernel.c`:
`initialize_early_text`, `serial_putc`). The theorems are about the C source
under CompCert's semantics for x86-64, for every input the laws allow. The
decision record is [ADR 0030](../../../docs/adr/0030-quickproof-handwritten-c-evidence-lane.md).

## The laws

Each law is a C program in [`project/harness/`](project/harness/). Its first
comment states the claim, and that comment, not this summary, is what a reader
must review.

- **`boot_text_console_safe`.** Take a Multiboot2 information buffer of up to
  16 MiB with any contents, passed with its exact length.
  - `boot_text_parse` reads only inside the buffer and returns 0 or 1.
  - When it returns 1, the stored geometry is one the Lean selector
    `leanos_boot_text_surface` accepts, and its surface fits in the 32 KiB
    aperture.
  - With a window of exactly that surface (`height * pitch` bytes, any prior
    contents), `boot_text_enable` succeeds, and every later `boot_text_putc` of
    any byte, for any number of bytes, writes only inside the window and keeps
    `row < height` and `column <= width`.
  - Every byte other than CR/LF is displayed in the cell just before the cursor:
    printable ASCII as itself, anything else as `?`, attribute 7.
  - CR returns to column 0 of the same row. LF goes to column 0 of the next
    row, or of the last row when the cursor is already on it.
- **`boot_text_parse_complete`.** The buffer is well-formed and has exactly
  this shape: the header; up to two other tags, of any type but 0 and 8 and
  any size from 8 to 64 bytes; a framebuffer tag of 32 to 64 bytes; the end
  tag; with `available` equal to the total. For every geometry the selector
  accepts, in such a buffer, the parser accepts and returns exactly that
  geometry. Buffers with more tags or other layouts, as GRUB's real handoff
  has, are not covered by this law.

Not claimed: termination, the physical placement of the aperture, interrupt
reentrancy, scrolled and cleared cell contents, the column step of a printable
byte beyond `column >= 1`, and anything about the compiled kernel
(CompCert's C is not GCC's). [`project/DEVIATIONS.md`](project/DEVIATIONS.md)
lists every difference between the proved program and the kernel's build.

## The seam with Lean

The writer's memory safety depends on a Lean-decided predicate: with a
selector that accepts any geometry, `boot_text_console_safe` is false. Each
tool proves the half of the seam it can reach, and both state the same
conjunction:

| Side | Theorem | Statement |
| --- | --- | --- |
| Lean, the emitted C of the export | `LeanOS.Refinement.BootTextConsoleC.bootTextSurfaceC_spec` (SC-BOOT-TEXT-SURFACE-REFINEMENT) | `call bootTextSurfaceC [kind, bits, address, pitch, width, height] = some (if kind.toNat = 2 ∧ bits.toNat = 16 ∧ address.toNat = 753664 ∧ 0 < width.toNat ∧ width.toNat ≤ 160 ∧ 0 < height.toNat ∧ height.toNat ≤ 64 ∧ pitch.toNat % 2 = 0 ∧ 2 * width.toNat ≤ pitch.toNat ∧ pitch.toNat ≤ 512 then 1 else 0)` |
| Coq, the model the laws link | `ModelProof.body_surface` with `valid_geo_iff` | `leanos_boot_text_surface` returns `if valid_geo … then 1 else 0`, and `valid_geo … = true ↔ kind = 2 ∧ bits = 16 ∧ address = 753664 ∧ 0 < width <= 160 ∧ 0 < height <= 64 ∧ pitch mod 2 = 0 ∧ 2 * width <= pitch ∧ pitch <= 512` |

## Results

`qp verify` on a fresh clone: **PASS** ([`VERIFY.md`](VERIFY.md)).

| Theorem | Result | Axioms |
| --- | --- | --- |
| `boot_text_console_safe` | PROVED | 13: standard + VST malloc |
| `boot_text_parse_complete` | PROVED | 13: standard + VST malloc |
| `suite` (both, with one specification per function) | PROVED | 13: standard + VST malloc |

The statements and `whole_prog` are identical to the frozen contract, and the
regenerated Clight is identical to the committed Clight. The proof sources
contain no `Admitted`, `admit`, `Axiom`, `Parameter` or `Conjecture`.

What it took (development machine, 12 CPUs):

| Item | Measure |
| --- | --- |
| C under test | 111 lines of `boot_text_console.h`, plus the 25-line model and 3 wrappers; 2 laws, 130 lines |
| Coq written | 2,251 lines in 12 files. The function specifications are shared by both laws (`ConsoleSpecs.v`), and each function has one body proof. |
| Largest pieces | `boot_text_parse` 343 lines (functional: it computes `parse_model`, a Coq function of the tag walk); law 2's `main` and buffer model 405 + 281 lines; law 1's `main` 377 lines |
| `qp check` | about 25 s: 3,000 native runs and 20 interpreter runs per law, 40 mutants (`CHECK.md`, `CHECK-NOTES.md`) |
| `qp verify` | 9 min, about 2.4 GB peak |
| Who wrote it | AI agents (Claude Opus 5.5 in Claude Code), as QuickProof intends. One session wrote the laws, the shared specifications and the small bodies. Four parallel agents then wrote parse, display, and each law's `main` against those fixed specifications, in 30 minutes to 2 hours each (display 30 min, parse 49 min, each law's `main` about 1¾ h). No specification needed changing. A person reviews the laws, `DEVIATIONS.md` and the model, not the Coq. |

The Lean side checks in about 2 s. `bootTextSurfaceC_refines` is one
`csym_refine` call, and the naturals restatement and the aperture corollary
take a few lines each. Both use only `propext`, `Classical.choice` and
`Quot.sound`.

## Coverage survey (the rest of the handwritten C)

`qp lint` and `qp audit` on call-only harnesses, at `ee64a79`:

| Code | Lines | As written | What would open it |
| --- | --- | --- | --- |
| `include/boot_text_console.h` | 111 | proved here | `-Dvolatile=` (D1) |
| PCI enumeration, capabilities, command executor, express/pending observation, MADT consumer | about 650 | `clightgen` refuses 11 functions that return structs by value | results through out-parameters |
| `include/qotom_copy_root_builder.h`, `include/frame_copy_window.h` | 318 | 13 pointer-to-integer casts (each table entry embeds the next table's address) and 3 struct assignments | take the tables' physical addresses as integers; copy fields |
| `boot/kernel.c` | 11,254 | 135 inline-assembly sites, 225 `volatile`, MMIO and port I/O on globals | out of scope beyond extracted helpers |

CompCert's reference interpreter, without any proof, runs four of LeanOS's
existing hosted tests (`pci-capabilities`, `pci-power-observation`,
`qotom-pcie-pending`, `qotom-broadcom-d3`) to their end with no undefined
behaviour in CompCert's semantics (`scripts/check-compcert-interp.sh`). On
`qotom-copy-root-builder` it stops at `<ptr source+4096> | 7U`, which is the
idiom the audit names.

## Reproducing

```sh
scripts/check-quickproof.sh --check boot-text-console
```

This needs Docker. It runs the published image
(`ghcr.io/genproof/quickproof`, pinned by digest), makes a QuickProof
workspace whose upstream is this checkout at the pinned commit, runs `qp check`,
assembles the frozen contract, copies [`proof/`](proof/) over it and runs
`qp verify`. With `--check`, it fails on any native, interpreter or lint
finding, or on fewer killed mutants than `CHECK.md`.
`scripts/check-quickproof-pins.sh` runs in `scripts/check.sh`. It fails when
the header, `LeanOS/BootTextConsole.lean`, or any file of `project/` or
`proof/` differs from `pins.tsv`. A change to what the theorems depend on
therefore cannot pass without a re-check and a pin update.

## Files

- `project/`: the QuickProof project. It holds `project.conf` (the pins),
  `quickproof.conf`, the two laws, `env.c` and `env/` (input distributions for
  the native and interpreter runs only), `patch/` (the wrapper unit, the
  model of the Lean export and the ABI shim) and `DEVIATIONS.md`.
- `proof/src/`: the Coq proof sources written for this project; everything
  else in the proof repository is regenerated by `qp assemble`.
- `CHECK.md`, `CHECK-NOTES.md`: the report of `qp check` and its reading.
- `pins.tsv`: the files the theorems depend on and their hashes (regenerate
  with `scripts/check-quickproof-pins.sh --update` after a re-check).

QuickProof is under the PolyForm Noncommercial License 1.0.0 and its toolchain
includes CompCert under the INRIA Non-Commercial License. The files here were
written for LeanOS and are under its license. Running them uses QuickProof
under its own.
