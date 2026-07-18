# ADR 0010: Guarded privilege-entry stack and checked byte budget

- Status: Accepted
- Date: 2026-07-18

## Decision

The ordinary CPL3 privilege-entry stack uses a linker-owned, page-aligned 4 KiB
absent lower guard followed by a 16 KiB usable interval. Stack growth is toward
lower addresses; all intervals are half-open, and the exclusive upper bound is
the sole value installed in `TSS.rsp0`. The usable leaves are writable only by
the supervisor and are non-executable. The guard has no leaf in either admitted
boot root. Distinct reservation identities keep both regions separate from page
tables, descriptor state, IST1, generated state, saved contexts, and user
mappings while permitting their intentional containment by the loaded image.

Every reviewed ordinary-entry path shares one byte-budget contract. It includes
the three- or five-word hardware frame, hardware error shape, fifteen saved
registers, dummy/alignment slots, transitive compiler-reported stack use, return
validation, and a 4 KiB safety margin. The image is compiled with
`-mno-red-zone`, `-mgeneral-regs-only`, and `-fstack-usage`; CI pins Ubuntu's GCC
13 package and GNU binutils 2.42. Unknown or dynamic usage, VLA/`alloca`, an
unresolved indirect edge, recursion, a changed assembly save count, an
unreviewed reachable contributor, or an over-budget result rejects the build.

The entry policy assumes the existing single-CPU interrupt-masking and nested-
entry rules. It does not introduce per-operation stacks or permit recovery from
exhaustion. The lower guard protects the architectural/stub prefix that executes
before normalization; later authorization carries the canonical identity,
bounds, top, required bytes, and checked remaining bytes in the one normalized
record.

## Proof and checked evidence

`LeanOS.PrivilegeEntryStack` models guarded layout validity and natural-number
byte accounting. It proves that accepted authorization names the exact stack
identity, half-open bounds, and canonical top, preserves the supplied composite
state, and satisfies `remaining + required = usable`. It also proves that an
insufficient request yields a typed fatal result with the composite state
unchanged. `SC-PRIVILEGE-ENTRY-STACK` advertises only the accepted model result;
it does not claim that a concrete image refines the model.

The image gate separately checks linker sections and symbols, both generated
page-table plans, live-page decoding, the reviewed unmapping instruction, final
ELF direct/tail-call reachability, assembly push counts, and compiler `.su`
reports. CI retains the raw reports, reviewed call graph, per-path budget and
margin, ELF symbols, disassembly, extracted edges, and final-ELF verdict. Normal
and preemption QEMU runs retain bounded stack-paint high-water records for a
real recovered CPL3 page fault and for the exercised syscall or
timer/context-switch path.

High-water painting is diagnostic only: a write matching the paint word can be
missed and the scan is cumulative rather than path-isolated. Kernel-origin
diagnostic faults remain on the active boot stack rather than switching through
`rsp0`, so this ordinary-stack evidence makes no claim about their high-water
use. It neither contributes authority nor replaces the static gate. Controlled
ordinary-stack exhaustion through IST1, including
the required adversarial runner rejections and terminal evidence, remains future
integration work.

## Trusted computing base and claim limit

The concrete boundary trusts GCC's stack-usage reports and code generation,
binutils, the reviewed call graph and checking scripts, assembly, linker script,
generated C, boot page-table construction, x86-64 frame construction and stack
switching, exception delivery, QEMU/TCG, firmware, and hardware. Compiler
reports, disassembly, page-table decoding, and QEMU observations are checked
evidence, not proofs of those components or a model-to-binary refinement.

The stable claim is limited to the Lean authorization model under its explicit
layout, reservation, entry-shape, and accepted-result assumptions. It does not
establish general C memory safety, arbitrary nesting, NMI or machine-check
behavior, SMP or per-CPU stacks, stack recovery, timing, or correctness of the
final binary.
