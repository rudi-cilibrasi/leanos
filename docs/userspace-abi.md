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
| 7 | ipc-stream, device-service, ahci-service | 2 | block on endpoint 10 |
| 8 | canonical (blocking-ipc, preemption) | 1 | send on endpoint 10 (RBX, RCX = payload) |
| 8 | ipc-stream, device-service, ahci-service | 1 | send one event on endpoint 10 (ahci-service: RBX = sector dword, RCX = its sequence number from 1) |
| 9 | canonical (blocking-ipc, preemption) | 2 | report the delivered payload |
| 9 | ipc-stream, device-service, ahci-service | 2 | report the delivered event; the kernel checks it equals what A sent (ipc-stream also echoes it, device-service does not; ahci-service also checks the sequence number and folds the dword into the sector digest) |
| 7 | three-subject | 3 | C blocks on endpoint 12 |
| 8 | three-subject | 1 | A sends one word on endpoint 12 (RBX, RCX = payload) |
| 9 | three-subject | 3 | C reports the delivered word (final record) |
| 7 | example-subject | 1, 3 | C (built from subjects/example) blocks forever on endpoint 13; A receives C's word on endpoint 12 |
| 8 | example-subject | 3 | C sends one word on endpoint 12 |
| 9 | example-subject | 1 | A reports the delivered word (final record) |
| 62 | example-subject | 2 | B's single run from its initial context, as in three-subject |
| 7 | fault-handler | 3 | C (built from subjects/fault-handler) blocks on fault endpoint 14 for its record, then forever on endpoint 13 |
| 62 | fault-handler | 2 | B's first run from its initial context, as in three-subject |
| 63 | fault-handler | 2 | B continues from its saved context after A's fault was handled; reports its canaries (final record) |
| 64 | fault-handler | 3 | C reports the fault record it received (RBX class word, RCX faulting subject, RDX address) |
| 65 | fault-handler | 3 | C answers the fault: RBX decision (1 = terminate), RCX faulting subject, RDX endpoint 14 |
| 7 | timer-server | 3 | C (built from subjects/timer-server) blocks receiving on endpoint 12; woken with RAX count or expiry bits, RBX word, RCX sender (0 = kernel expiry) |
| 8 | timer-server | 1, 2 | call the timer server on endpoint 12 (RBX count); A is resumed with the server's reply word; refused without the endpoint capability (0x302) |
| 62 | timer-server | 2 | B reports its canaries and its two refusals (RDX, 16 bits each), then spins with interrupts enabled |
| 90 | timer-server | 1, 2, 3 | arm the one-shot PIT for RBX counts through the timer capability (1 accepted; 0x102 no timer capability; 0x202 outside 1..65535) |
| 91 | timer-server | 3 | C replies RBX to the calling client and blocks receiving on endpoint 12 (RDX) |
| 92 | timer-server | 3 | C signals client RBX's wake notification (RDX 13) with bits RCX |
| 93 | timer-server | 1 | A waits on its wake notification 13 (RDX); resumed with its wake bits |
| 94 | timer-server | 1 | A reports the server's three replies (RBX, 16 bits each) and its wake bits (RCX) (final record) |
| 7 | frame-server | 3 | C (built from subjects/frame-server) blocks on endpoint 12 for its first request; woken with the request (RAX) and the kernel-attested client (RBX) |
| 62 | frame-server | 2 | B's first run from its initial context, as in three-subject |
| 90 | frame-server | 1, 2 | request to the frame server on endpoint 12 (RDX): RBX 1 asks for a frame (answer: its page address, or the typed rejection 0x100), RBX 2 releases the client's budget (A only; A never runs again) |
| 91 | frame-server | 3 | C's decision for the pending request, checked against the generated witness: RBX op (1 grant, 2 refuse over budget, 3 refuse pool exhausted, 5 revoke) with rights << 8, RCX client, RDX pool frame; C then blocks on endpoint 12 for the next request |
| 93 | frame-server | 2 | B reports the first and last byte of its republished frame (RBX, RCX) and its address (RDX) (final record) |
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
| 60 | ahci-service | 1, 2 | next sector dword from the bound AHCI program (sequence number in the high half; 0 = end, after the release scrub), for the device-capability holder A only; B's one attempt before it first blocks is refused (no device capability, returns all ones) |
| 61 | ipc-stream, device-service | 1 | end of stream (final record) |
| 61 | ahci-service | 1 | end of stream: A's final check of the 128 deliveries, the refusal and the release (final record with the sector digest) |
| 62 | three-subject | 2 | B's single run from its initial context reports its register canaries (RBX, RCX) |
| 7 | keyboard-echo | 3 | C, the echo server, blocks for the next key on its receive-only endpoint capability (slot in RDX); B's attempt is refused |
| 8 | keyboard-echo | 1 | A sends one key to C on its send-only endpoint capability (slot in RDX, RBX = key, RCX = 1); B's attempt is refused |
| 60 | keyboard-echo | 1, 3 | next key from the bound device program, for the device-capability holder A only; C's attempt is refused (no device capability) |
| 61 | keyboard-echo | 1 | A's final check of the key, delivery and console counts (final record) |
| 62 | keyboard-echo | 2 | B reports its canaries and its three refused attempts |
| 70 | keyboard-echo | 1, 2, 3 | console write of RBX's byte through the console capability in slot RDX (C only); A's and B's attempts are refused |
| 71 | keyboard-echo | 1, 2, 3 | console read through the console capability in slot RDX (C only; poll only: 256 when empty) |
| 7 | network-subject | 3 | C (built from subjects/net) blocks on endpoint 12 (RDX) for the next frame; woken with its length (RAX), sequence number (RBX) and the delivery flag (RCX) |
| 8 | network-subject | 1 | A sends the frame's length (RBX) and sequence number (RCX) to C on endpoint 12 (RDX); never the frame |
| 60 | network-subject | 1, 3 | next frame from the bound frame-source program, for the device-capability holder A only: sequence number in the high half, length in the low half (0 = end); C's attempt is refused (no device capability: bit 63 or 7) |
| 61 | network-subject | 1 | A's final check of the frame, copy, reply and edge counts (final record) |
| 62 | network-subject | 2 | B reports its canaries and its refused frame fetch (RDX) |
| 64 | network-subject | 1, 2, 3 | frame fetch: copy the pending frame into the caller's buffer at RBX, checked against the generated witness leanos_frame_copy_check (C only, the whole range inside C's own page); returns the length, or bit 63 or the reason |
| 65 | network-subject | 3 | frame send: copy RCX bytes (14-1514) at RBX out as the reply, under the same check; returns 0, or bit 63 or the reason |
| 70 | notify-reply | 1 | signal notification 20 with RBX bits (the script signals 5) |
| 71 | notify-reply | 2 | wait on notification 20 (blocks until signalled) |
| 72 | notify-reply | 1 | call endpoint 10 with RBX; creates a one-shot reply capability for the caller |
| 73 | notify-reply | 2 | report the woken notification bits (RBX) |
| 74 | notify-reply | 2 | receive on endpoint 10 (blocks until the call) |
| 75 | notify-reply | 2 | reply through the one-shot reply capability with RBX; a second reply is rejected |
| 76 | notify-reply | 1 | report the delivered reply word (final record) |
| 77 | notify-reply | 2 | report the rejected second reply and block |
| 7 | console-server | 3 | C blocks on its receive-only endpoint capability (slot in RDX); B's attempt is refused |
| 8 | console-server | 1 | A sends on its send-only endpoint capability (slot in RDX, RBX = payload); B's attempt is refused |
| 61 | console-server | 1 | A's final check of the console counts (final record) |
| 62 | console-server | 2 | B reports its canaries and its three refused attempts |
| 70 | console-server | 1, 2, 3 | console write of RBX's byte through the console capability in slot RDX; refused without it |
| 71 | console-server | 1, 2, 3 | console read through the console capability in slot RDX (poll only: 256 when empty); refused without it |
| 7 | endpoint-directory | 1, 2, 3 | receive through the receive capability in slot RDX: C on its request endpoint 12, B on its endpoint 14; A's attempt through its send-only slot is refused |
| 8 | endpoint-directory | 1 | A sends RBX through the resolved send-only capability in slot RDX, waking B |
| 9 | endpoint-directory | 2 | B reports the delivered word and its preserved R12 canary (final record) |
| 80 | endpoint-directory | 2 | register: delegate the capability in slot RDX, attenuated to rights RCX, to the directory under the name RBX |
| 81 | endpoint-directory | 1 | call the directory through slot RDX with the name RBX; the answer is the installed slot or the typed miss 0x100 |
| 82 | endpoint-directory | 3 | reply through the one-shot reply capability with a copy of slot RBX attenuated to rights RCX (0xff and 0 for none), then receive through slot RDX |
| 83 | endpoint-directory | 3 | describe the last received message: its kind and, for a registration, the directory slot and rights |
<!-- syscall-table:end -->

## Errors

There is no error-return convention. A syscall at the wrong step, from the
wrong subject, or with unexpected arguments stops the machine with a
`LEANOS/3 FINAL status=FAIL reason=...` record (fail-stop). A few scenarios
return scenario-specific words, which the subject's script checks: the
capability-reuse stale replay returns 0, and the device-service "next key" call
returns 0 at the end of the stream. In the `console-server` and
`keyboard-echo` images a refused capability request changes nothing and
returns `1 | reason << 8` ([console-server.md](console-server.md)). The
`keyboard-echo` image adds reason 7: a device request (60) from a subject
without the device capability. The `ahci-service` image returns all ones
to B's device request (60), which it refuses for the same reason, and
returns each sector dword to A with its sequence number in the high half, so
that only 0 ends the stream. The `0xff01`–`0xff06` words in
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
generation is rejected. The `endpoint-directory` image (#485) names
endpoint capabilities by a slot of the caller's own table and resolves a
64-bit name to a send-only copy through a ring-3 directory
([endpoint-directory.md](endpoint-directory.md)).

## What does not exist

- no fork, clone or spawn syscall (ADR 0010);
- no libc and no dynamic loading: subjects are linked into the image;
- no stable syscall numbering;
- no general error codes.
