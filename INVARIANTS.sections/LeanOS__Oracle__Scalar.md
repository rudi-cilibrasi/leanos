# Oracle rows for system calls, messaging, and scheduling

The opening block of the oracle: the boot entry point, the demonstration system call and messaging calls, timer preemption, boot memory allocation, return to user mode, blocking message passing, and capability-slot reuse. This block starts at corpus row 0, so a position here is a corpus row. The theorems confirm each scenario's accepted and refused answers.

- `boot_decoder_roundtrip_cold` — Encoding the boot model's cold starting state yields the number zero, the word the boot adapter starts from.
- `boot_accept_agrees` — The one well-formed boot command in the corpus is accepted.
- `every_rejection_agrees` — Every deliberately bad boot, system-call, and messaging row in the opening block is rejected with the answer zero.
- `syscall_accept_agrees` — The well-formed system-call row is accepted.
- `ipc_scenario_agrees` — In the four-row messaging scenario, the sender may send but not receive and the receiver may receive but not send, with each accepted step producing its exact word.
- `preemption_scenario_agrees` — The genuine timer tick and the resume each produce their exact program-switch words, while a masked interrupt, a wrong interrupt number, and a forged claim about the current program all produce nothing.
- `resumable_scenario_agrees` — Switching between the two suspended programs restores each one's exact saved descriptor and register markers, and a mismatched descriptor is refused.
- `user_return_scenario_agrees` — All four legitimate return-to-user rows are accepted, and every one of the 24 corrupted variants — bad addresses, wrong selectors, forbidden flag bits, stale identities, out-of-bounds code or stack, and more — is rejected.
- `blocking_ipc_scenario_agrees` — The four-step blocking hand-off (receiver blocks, sender wakes it, it is dispatched, the message is delivered) produces its exact event words, the wrong-caller, wrong-phase, and forged-payload rows produce nothing, and the eleven remaining hostile rows each produce a nonzero rejection word.
- `capability_reuse_scenario_agrees` — Every row of the capability-slot reuse story produces its exact expected word: stale and fresh handles are told apart at each stage, the forged and malformed rows produce nothing, and the exhaustion and boundary rows behave exactly as modeled.
