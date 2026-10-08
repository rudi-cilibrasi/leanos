# Ring-3 ABI as it exists today

This page describes what a ring-3 subject can do on the current boot images.
There is **no stable ABI**: no libc, no fork, no dynamic loading, no
general-purpose syscall layer. Every syscall below is part of a scripted,
scenario-scoped vocabulary. The table is generated from
`scripts/syscall-numbers.tsv`, and `scripts/check-userspace-abi.py` keeps the
table, the page and `boot/kernel.c` in agreement.

## Entry and registers

A subject enters the kernel with `int $0x80` through a DPL3 gate (ADR 0003,
[privilege-entry-control.md](privilege-entry-control.md)). The syscall number is
in `rax` and the arguments are in `rbx`, `rcx`, `rdx` and `rsi` (the transfer
scenarios read a fourth argument from `rsi`). The kernel's word comes back in
`rax`. Some scenarios also hand a subject the two IPC payload words in
`rax`/`rbx` when it is woken. `SYSCALL`/`SYSENTER` are denied
([fast-entry denial](privilege-entry-control.md)).

## Syscall numbers

Each number is accepted only in the listed scenario image, from the listed
subject, at one scripted step of that scenario. The same number can mean
different things in different images (for example 20). None of these numbers
match the abstract `LeanOS.Syscall` vocabulary (map 0, unmap 1, access-check 2,
[syscall-model.md](syscall-model.md)). That vocabulary is a model, not this
ABI.

<!-- syscall-table:start -->
| Number | Scenario image | Subject | Meaning |
| --- | --- | --- | --- |
| 1 | canonical (blocking-ipc, preemption) | 1 | first entry of A: yield into the preemption script |
| 2 | canonical (blocking-ipc, preemption) | 2 | B's authorized syscall; arms the timer |
| 3 | canonical (blocking-ipc, preemption) | 1, 2 | register-canary failure report (stops the machine) |
| 4 | canonical (blocking-ipc, preemption) | 1 | bounded user copy: RBX=direction, RCX=address, RDX=length |
| 5 | canonical (blocking-ipc, preemption) | 1 | final resumed-context check after preemption |
| 6 | canonical (blocking-ipc, preemption) | 1 | resume probe (returns the preemption phase) |
| 7 | canonical (blocking-ipc, preemption) | 2 | block on endpoint 10 (empty) |
| 7 | ipc-stream, device-service | 2 | block on endpoint 10 |
| 8 | canonical (blocking-ipc, preemption) | 1 | send on endpoint 10 (RBX, RCX = payload) |
| 8 | ipc-stream, device-service | 1 | send one event on endpoint 10 |
| 9 | canonical (blocking-ipc, preemption) | 2 | report the delivered payload |
| 9 | ipc-stream, device-service | 2 | echo the delivered event |
| 7 | three-subject | 3 | C blocks on endpoint 12 |
| 8 | three-subject | 1 | A sends one word on endpoint 12 (RBX, RCX = payload) |
| 9 | three-subject | 3 | C reports the delivered word (final record) |
| 10 | canonical (blocking-ipc, preemption) | 2 | capability reuse: use the initial handle |
| 11 | canonical (blocking-ipc, preemption) | 2 | capability reuse: replay the stale handle (rejected) |
| 12 | canonical (blocking-ipc, preemption) | 2 | capability reuse: use the fresh handle |
| 13 | extended-state family | 2 | peer entry after the denied extended-state instruction; reports CR0/CR4 state |
| 14 | fault-containment family | 2 | peer report after the contained fault |
| 15 | entry-adversarial | 2 | peer report after the adversarial entry attempts |
| 16 | direct-port family | 2 | peer report after the denied port access |
| 17 | divide-error, breakpoint | 2 | peer report after the contained integer fault |
| 19 | fault-stale-translation | 2 | stale-translation probe: check the runtime mapping before invalidation |
| 20 | fault-stale-translation | 1 | stale-translation probe: subject A after the unmap |
| 20 | frame-budget | 1 | frame-budget script step |
| 21 | frame-budget | 1, 2 | frame-budget script step |
| 22 | frame-budget | 1, 2 | frame-budget script step |
| 23 | frame-budget | 1, 2 | frame-budget script step |
| 24 | frame-budget | 1, 2 | frame-budget script step |
| 25 | frame-budget | 1, 2 | frame-budget script step |
| 26 | capability-transfer | 1 | sealed transfer: offer |
| 27 | capability-transfer | 2 | sealed transfer: reject the sealed handle before receipt |
| 28 | capability-transfer | 2 | sealed transfer: accept |
| 29 | capability-transfer | 2 | sealed transfer: delegated send |
| 30 | capability-transfer | 2 | sealed transfer: excess-right denial |
| 31 | inflight-revocation | 1, 2 | in-flight revocation script step |
| 32 | inflight-revocation | 1, 2 | in-flight revocation script step |
| 33 | inflight-revocation | 1, 2 | in-flight revocation script step |
| 34 | inflight-revocation | 1, 2 | in-flight revocation script step |
| 35 | inflight-revocation | 1, 2 | in-flight revocation script step |
| 36 | inflight-revocation | 1, 2 | in-flight revocation script step |
| 37 | inflight-revocation | 1, 2 | in-flight revocation script step |
| 38 | inflight-revocation | 1, 2 | in-flight revocation script step |
| 39 | inflight-revocation | 1, 2 | in-flight revocation script step |
| 40 | inflight-revocation | 1, 2 | in-flight revocation script step |
| 60 | ipc-stream, device-service | 1 | next event (device-service: the next key from the bound device program) |
| 61 | ipc-stream, device-service | 1 | end of stream (final record) |
| 62 | three-subject | 2 | B's single run from its initial context reports its register canaries (RBX, RCX) |
| 70 | notify-reply | 1 | signal notification 20 with RBX bits (the script signals 5) |
| 71 | notify-reply | 2 | wait on notification 20 (blocks until signalled) |
| 72 | notify-reply | 1 | call endpoint 10 with RBX; creates a one-shot reply capability for the caller |
| 73 | notify-reply | 2 | report the woken notification bits (RBX) |
| 74 | notify-reply | 2 | receive on endpoint 10 (blocks until the call) |
| 75 | notify-reply | 2 | reply through the one-shot reply capability with RBX; a second reply is rejected |
| 76 | notify-reply | 1 | report the delivered reply word (final record) |
| 77 | notify-reply | 2 | report the rejected second reply and block |
<!-- syscall-table:end -->

## Errors

There is no error-return convention. A syscall at the wrong step, from the
wrong subject, or with unexpected arguments stops the machine with a
`LEANOS/3 FINAL status=FAIL reason=...` record (fail-stop). A few scenarios
return scenario-specific words, which the subject's script checks: the
capability-reuse stale replay returns 0, and the device-service "next key" call
returns 0 at the end of the stream. The `0xff01`–`0xff06` words in
`LeanOS/BoundaryVocabulary.lean` are a kernel-internal Lean↔C ABI, not a user
ABI.

## Capabilities and handles

A subject's authority is its capability slots
([capability-model.md](capability-model.md)). The kinds are `memory`,
`addressSpace` and `endpoint`. The rights are `read`, `write`, `send`,
`receive`, `grant` and `revoke`, restricted per kind by
`Capability.rightsValid`. Device capabilities are a separate layer
(`LeanOS.DeviceCapability`), and so are notifications and one-shot reply
capabilities (`LeanOS.NotifyReply`, #471). A reply capability exists only
between a `call` and its reply, names that caller's generation, and cannot be
copied; the `notify-reply` image exercises syscalls 70–77 against that model's
generated witness. A handle word is a 16-bit slot plus a 48-bit
generation ([capability-handles.md](capability-handles.md)). A stale
generation is rejected.

## What does not exist

- no fork, clone or spawn syscall (ADR 0010);
- no libc and no dynamic loading: subjects are linked into the image;
- no stable syscall numbering;
- no general error codes.
