# ADR 0004: Two-subject IPC integration slice

- Status: Accepted
- Date: 2026-07-14

## Decision

The image boots two ring-3 subjects in distinct four-level page tables. Each
address space marks only its own code and stack leaves user-accessible; kernel
frames, page tables, IDT, TSS, and entry stack remain supervisor-only. A fixed
schedule runs sender A, switches CR3 and the kernel-owned caller identity, then
runs receiver B. There is no scheduler or concurrency claim.

The generated `leanos_ipc_demo` witness exposes fixed-width, pointer-free send
and receive results from the endpoint model. A has send authority only and B
has receive authority only. The C mailbox is a deliberately narrow foreign
adapter: it records sender identity from kernel context, ignores the supplied
sender word, and transfers no capability. The version-3 serial protocol and
debug-exit status test this exact path, including both direction denials,
payload/provenance agreement, handoff, and final resumption.

## Proof and evidence boundary

`LeanOS.IPCSyscall` proves model-level invariant preservation, unchanged state
for typed rejection, and that accepted send and delivered receive authority use
the trusted caller. The endpoint model supplies delivery-provenance lemmas.
`./scripts/check.sh` checks those proofs and rejects proof escapes. QEMU and the
ELF policy scan test the generated-code and machine integration; they do not
prove C/assembly refinement, page-table behavior, context switching, or the
kernel binary.

The TCB additions are the two page-table constructors and CR3 switch, saved
register/exception-frame handling, fixed C mailbox and endpoint initialization,
generated IPC C, linker layout, serial oracle, compiler/linker, GRUB, QEMU/TCG,
and x86-64 semantics. A defect in any may forge caller selection, provenance,
isolation, or the trace. DMA, speculation, covert channels, general scheduling,
blocking IPC, capability transfer, arbitrary faults, and liveness are excluded.

## Supervisor enforcement

The completed leaf policy is activated with CR0.WP in the final paging-enable
write. After vector 14 and the TSS are installed, CR4.SMEP is enabled and read
back. Two one-shot CPL0 probes then require exact fatal page faults: error code
3 and CR2 at a kernel-text byte for a supervisor write, and error code 17 and
CR2/RIP at subject A's user-text entry for a supervisor instruction fetch. The
handler advances only these exact boot phases; every mismatch and every other
kernel fault remains fatal. The exact transcript and guest debug-exit status
prevent a forged or missing PASS record from succeeding.

`LeanOS.X86PageTable` proves the reviewed policy is W^X and, assuming modeled
x86 permission semantics, that WP rejects the supervisor write and SMEP rejects
the supervisor fetch while CPL3 execution remains permitted. The ELF/linker
inspection and QEMU TCG probes are structured integration evidence, not a proof
of assembly, control-register writes, fault delivery, QEMU, or processor
semantics. Those items, plus the compiler/linker and the exact probe handler,
remain in the TCB. SMEP CPU support is required; SMAP is deliberately out of
scope.
