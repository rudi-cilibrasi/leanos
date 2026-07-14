# LeanOS experimental image

This is an experimental research artifact, not a production operating system
or a claim of binary-level verification. The Lean proof gate establishes
model-level theorems and rejects unapproved proof and trusted-code escapes.
Compilation and the QEMU smoke test provide tested integration behavior only.

The trusted computing base and unproved boundary include Lean code generation,
generated C, GCC, GNU assembler and linker, GRUB, the boot assembly and C shim,
the linker script, SeaBIOS, QEMU, x86-64 hardware semantics, Multiboot2, the
16550 UART, and the debug-exit device contract. The connection from the proved
Lean model through generated code to the released machine image is not proved.
See `docs/boot-image.md` and ADRs 0001 and 0002 in the tagged source tree for
the complete scope, assumptions, and experimental evidence.
