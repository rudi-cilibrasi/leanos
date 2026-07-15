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
