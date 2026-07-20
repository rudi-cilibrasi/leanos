# Fatal exception fail-stop model

`LeanOS.FailStop` is the authoritative composite execution latch around the
interrupt classifier. Its modes are `running`, `handling` a kernel-owned active
entry, and `halted` with a typed record. Entry and completion are explicit. A
normal syscall entry classification, timer event, incoming wrong-origin
rejection, or contained CPL3 page fault returns to `running`; the contained
fault still atomically applies the existing whole-subject cleanup policy.
Outgoing user return is a distinct `completeUserReturn` transaction: validation
failure records its purpose and reason, freezes every composite subsystem, and
enters the same absorbing halt gate. Kernel page faults and unsupported vectors
also halt.
The kernel-owned SMAP copy override is cleared on every entry and remains clear
after a fatal transition, so an interrupted diagnostic or copy window cannot
leak privileged access into a later context.

The bounded escalation policy models a page fault raised while handling a page
fault as a double fault. Every other exception during handling is forbidden
nested entry and halts. This is deliberately not Intel's complete exception
combination table. The halt record publishes only the reason, the kernel-owned
active entry, and incoming vector/origin diagnostics. Lifecycle, capabilities,
mappings, scheduler identity, saved context, mailbox, and resources remain the
pre-fault `core`; fatal atomicity proves that freeze.

Vector 2 has a separate terminal path. `dispatchNmi` consumes only the exact
accepted `InterruptEntry.normalizeNmi` result (or retains its typed rejection),
and is admitted from both `running` and every `handling` state. It never calls
ordinary entry completion, user-fault containment, scheduling, CR3/return
selection, or an operation-specific handler. An accepted NMI records the
prior mode plus the trusted normalized origin, active CR3, and IST2 identity;
it preserves the current subject/address-space/kernel-stack projection and
clears both return authority and the SMAP copy override. The composite theorem
freezes every business subsystem and absorbs all later operations.

If the state is already halted, another modeled NMI returns the identical
record and cannot manufacture a later snapshot. This sequential rule assumes
that a second physical NMI is blocked until architectural NMI return; no such
return exists in the model. It is not a statement about arbitrary machine
instruction interleavings or partially committed implementation mutations.

The composite state places scheduler/preemption, syscall virtual memory, IPC,
capability, mapping, and subject-lifecycle state under the same execution latch.
`Operation` carries each subsystem's typed inputs, and `gate` invokes the real
subsystem transition internally; callers cannot supply an arbitrary post-state.
Once halted it returns the identical composite state and rejects every
operation. `halted_terminal_non_resumption` proves this for one composite step,
and the absorption theorem extends it to arbitrary typed operation suffixes, so
neither a CPL3 return nor an accepted mutation or trusted context restoration
can occur.
Attacker registers are absent from active-entry identity and cannot change
classification, escalation, diagnostics, or the terminal latch. A kernel fault
cannot be classified as user containment.

Executable examples cover valid syscall return, contained user page fault,
timer delivery, kernel fault, unsupported vector, modeled double fault,
attempted restart, and attempted syscall/timer/IPC/lifecycle operations after
halt. A negative theorem
exhibits why the previous action-only fatal result was insufficient: its
unchanged state could immediately accept a valid syscall return.

## Diagnostic and trusted boundary

Boot-only WP/SMEP recovery remains a pre-runtime diagnostic behavior outside
this model. It must be disabled before subjects run and does not refine
`halted`; production fatal entry has no clear or restart transition.

These are Lean model proofs, not proof that x86 delivers an exception or NMI
into the model. IDT/TSS/IST setup, NMI delivery/blocking/coalescing and frame
construction, assembly entry/exit, exception delivery, compiler, generated
code, firmware, QEMU, and hardware remain trusted. No `unsafe`,
`extern`, FFI declaration, axiom, or constant is added.
