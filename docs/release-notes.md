# LeanOS experimental image

This is an experimental research artifact, not a production operating system
or a claim of binary-level verification. The Lean proof gate establishes
model-level theorems and rejects unapproved proof and trusted-code escapes.
Compilation and the QEMU smoke test provide tested integration behavior only.

The release-blocking QEMU evidence is recorded in `EMULATOR_EVIDENCE.json`
against the versioned `EMULATOR_EVIDENCE_MATRIX.tsv`. The manifest binds the
tested source revision, tool inventory, exact QEMU commands, expected result
classes, and hashes of every mandatory scenario's image, ELF, serial log, and
runner log. Controlled-rejection and fail-stop entries are integration tests,
not Lean proofs or claims of compiler or binary refinement.

The trusted computing base and unproved boundary include Lean code generation,
generated C, GCC, GNU assembler and linker, GRUB, the boot assembly and C shim,
the linker script, SeaBIOS, QEMU, x86-64 hardware semantics, Multiboot2, the
16550 UART, and the debug-exit device contract. The connection from the proved
Lean model through generated code to the released machine image is not proved.
For extended-state denial this inventory specifically includes CPUID and
CR0/CR4 reads, #UD/#NM priority and delivery, probe decoding, vector 6/7 entry
and cleanup assembly, generated scalar dispatch, peer restore, and transcript
inspection. The five canaries cover representative x87, MMX, SSE, SSE2, and
AVX instructions only; they do not enumerate XSAVE state or qualify hardware.
See `docs/boot-image.md` and ADRs 0001 and 0002 in the tagged source tree for
the complete scope, assumptions, and experimental evidence.
