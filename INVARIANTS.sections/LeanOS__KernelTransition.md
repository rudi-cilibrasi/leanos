# The kernel's very first state machine

This file models the simplest possible version of the kernel: a machine that starts "cold" and can be initialized exactly once, with every other request refused. Its theorems establish the project's first three claims: the machine is predictable, it stays healthy through every step, and refusals change nothing. A final theorem ties the tiny numeric entry point actually called at boot back to this explicit model.

- `initialState_wellFormed` — The state the kernel starts in passes its own health check: a cold kernel whose generation counter reads zero.
- `transition_deterministic` — Given the same state and the same command, the kernel's step always produces exactly the same outcome; there is no hidden randomness or choice.
- `transition_preserves_wellFormed` — No matter what command arrives, stepping from a healthy state always lands in a healthy state.
- `rejected_state_unchanged` — Whenever the kernel rejects a command, the state afterwards is exactly the state before; a refusal changes nothing.
- `bootTransition_agrees` — The fixed-width numeric entry point actually called at boot gives, for every valid state and any command word, exactly the answer the explicit model prescribes.
