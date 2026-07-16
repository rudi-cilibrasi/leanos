# ADR 0007: Double-fault IST fail-stop slice

- Status: Accepted
- Date: 2026-07-15

## Decision

Vector 8 uses IST1, whose linker-owned region consists of one unmapped 4 KiB
guard page immediately below a page-aligned 16 KiB stack. The TSS points at the
exclusive stack end. No other gate uses IST1. Both bounded boot address spaces
map the stack supervisor-writable and non-executable and explicitly clear the
guard leaf before the TSS and IDT are loaded. The stack and guard remain inside
the boot-image reservation already passed to the allocation model.

The vector-8 assembly entry masks interrupts, clears AC and the direction flag,
checks that its hardware frame is in the IST bounds, checks two bounded
canaries, and verifies the architectural error code is zero. It does not call
C, push values, allocate, format, recover, or execute `iretq`. Success and
failure each emit one fixed terminal record and leave through distinct
debug-exit values; neither path returns.

The dedicated probe disables the ordinary controlled fault probes by entering
before them. It sets RSP to the boundary above the unmapped guard and raises a
real general-protection exception by loading an invalid segment selector. The
present vector-13 IST0 gate cannot push its frame, causing a page fault during
contributory-exception delivery and therefore vector 8. A separately built
negative image leaves the guard mapped and must reach the vector-13 terminal
failure path instead of vector 8. The normal image does not invoke this probe
and retains its exact existing success protocol.

## Evidence

`scripts/check-image-policy.sh` checks the vector-8/IST1 source construction,
the unique IST1 gate, linker bounds, allocated writable non-executable section
flags, guard-page clearing in both page tables, required symbols, and the
absence of calls, pushes, and `iretq` in the terminal stub. The normal and probe
ELFs, maps, serial logs, QEMU command/version, and exit status are retained by
CI.

`scripts/run-double-fault.sh` accepts exactly one typed vector-8 record with
error code zero, IST1 range/canary evidence, the declared unusable ordinary
stack, no return, and debug-exit status 37. Controlled fixtures reject a direct
handler claim, vector 14, wrong IST or RSP evidence, ordinary-stack use,
duplicates, a forged pass/final record, a return claim, guest rejection, reset,
and timeout. The ordinary QEMU scenario remains a separate gate.

The typed reason is the machine-boundary spelling of
`LeanOS.FailStop.FatalReason.doubleFault`. The model's
`double_fault_escalation` theorem proves that its documented bounded nested
page-fault state maps to that reason, while `fatal_atomicity`,
`fatal_clears_copy_override`, and `halted_terminal_non_resumption` preserve the
frozen state, clear the copy override, and prohibit later accepted operations
or context restoration. The concrete #GP/#PF construction is deliberately not
claimed to refine that bounded page-fault/page-fault model combination.

## Trusted computing base and claim limit

This slice adds the IST/TSS/IDT and paging setup, vector-8 and probe assembly,
linker layout, fixed serial/debug-exit path, image-policy and runner scripts,
and QEMU's exception and device emulation to the reviewed TCB. The compiler,
linker, GRUB, scripts, QEMU/TCG, x86-64 exception classification and delivery,
IST switching, page-table walks, serial port, debug-exit device, firmware, and
hardware remain trusted. The assembly and emitted record are not generated
from or checked against the Lean model.

The narrow claim is that QEMU exercised one bounded fail-stop double-fault path
on IST1 and the repository checks inspected the associated construction. It
does not verify x86 delivery, prove the assembly or binary, establish behavior
for other exception combinations, or qualify real hardware. Recovery, crash
dumps, unwinding, general panic logging, other dedicated ISTs, SMP, nested
interrupts, and continuation after terminal entry remain out of scope.
