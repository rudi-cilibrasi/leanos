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
The vector-14 path additionally carries a version-one canonical page-fault
snapshot binding supported error bits, CR2/page, saved frame,
subject/address-space/CR3, and paging controls before policy; x86 delivery,
error-word/CR2 ordering, and assembly sampling remain trusted.
The gated release bundle retains separate supervisor-read, read-only-write,
and NX-execute fault ISOs, final ELFs and maps, serial transcripts, complete
19-word canonical snapshots, final disassemblies, page-table plans, and exact
entry-policy reports. The write case executes a real CPL3 store into a present
read-only user leaf and verifies an unchanged target canary before the common
peer restore. The NX case writes a fixed payload into A's present user
writable, non-executable stack leaf and branches to it, binding hardware error
word 21, execute access, CR2, saved RIP, live leaf, generated dispatch, cleanup,
and peer survival. An unexpected executable mapping follows an independent
guest-error payload instead of producing a false containment pass.

The matrix also retains two fail-stop images through the same production
snapshot/generated-policy adapter: one injects a controlled reserved bit into
the selected live leaf before a real CPL3 access, and one changes a single
expected-walk permission bit while retaining the hardware error, CR2, saved
RIP, and live walk. Each requires a typed absorbing terminal record and the
independent fatal debug-exit status; containment, cleanup, survivor dispatch,
user return, and normal success are forbidden. The release retains their ISOs,
ELFs, maps, disassemblies, policy reports, page-table plans, serial logs, and
terminal records. These tests do not establish binary refinement.
For extended-state denial this inventory specifically includes CPUID and
CR0/CR4 reads, #UD/#NM priority and delivery, probe decoding, vector 6/7 entry
and cleanup assembly, generated scalar dispatch, peer restore, and transcript
inspection. The five canaries cover representative x87, MMX, SSE, SSE2, and
AVX instructions only; they do not enumerate XSAVE state or qualify hardware.
See `docs/boot-image.md` and ADRs 0001 and 0002 in the tagged source tree for
the complete scope, assumptions, and experimental evidence.
