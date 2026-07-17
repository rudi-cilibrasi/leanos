# ADR 0009: Scheduler-driven blocking IPC boot slice

- Status: Accepted
- Date: 2026-07-17

## Decision and evidence

The deterministic image starts receiver B in CPL3. B invokes blocking receive
on empty endpoint 10, and the kernel accepts the generated
`leanos_blocking_ipc_demo` block witness before saving B's complete register and
return frame. B is then non-runnable; assembly installs a fresh A frame and A's
CR3. A sends the two fixed payload words under kernel-owned caller identity 1.
Generated send/wake and dispatch witnesses must agree before exactly one ready
insertion is recorded and B's saved frame and CR3 are restored. B can complete
only after checking the exact payload and trusted sender word, followed by the
generated delivery witness.

The version-10 serial protocol is exact and ordered. Host fixtures reject an
omitted block, the old fixed handoff, a wrong address-space binding, a missing
or duplicate wake, delivery theft, a forged summary, guest failure, and hang.
The common 75-vector corpus is evaluated in Lean, replayed through hosted
generated C, and replayed in the guest before this machine path.

## Claims and trusted computing base

Lean proves that the four accepted scalar encodings agree with the concrete
composite blocking-IPC and scheduler transitions. It proves atomic reservation,
the receiver is non-runnable and absent from the ready queue after blocking,
the sender is selected, wakeup makes the receiver runnable with exactly one
ready entry and one reserved completion, trusted provenance, and exact delivery
for the modeled scenario. QEMU tests one corresponding machine execution; it does not prove
assembly, generated C, compiler, linker, page tables, CR3/TLB behavior, or x86
execution refines the Lean model.

TCB additions are the generated `BlockingIPC.c` adapter, its scalar ABI, the C
phase gate and protected saved-context globals, the `int 0x80` block/send/
delivery numbers, assembly frame copies and CR3 changes, the serial protocol and
host checker, and the existing compiler/linker/GRUB/QEMU/x86 contracts. The
single-core path assumes interrupts remain masked while each C/assembly state
transition is committed. No new `unsafe`, `extern`, FFI declaration, axiom,
constant, `sorry`, or `admit` is introduced.
