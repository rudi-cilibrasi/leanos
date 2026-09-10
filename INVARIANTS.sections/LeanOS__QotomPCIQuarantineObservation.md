# Qotom command and readback trace observations

These proofs describe accepted recorded operations. They do not establish that hardware performed the operations or that DMA has been contained.

- `checkStep_preserves_step` — A successful individual check retains the exact supplied write and readback record.
- `checkSteps_preserves_steps` — Successful checking of a sequence preserves all input records in order.
- `check_preserves_trace` — The final accepted witness retains the complete caller-supplied trace unchanged.
- `witnessed_command_zero` — Each step in an accepted witness has a decoded zero Command readback.
- `witnessed_write_is_command_word` — Each witnessed write specifies offset four, width two and value zero.
- `order_has_fifteen_functions` — The proposed complete inventory order contains fifteen functions.
- `witness_has_fifteen_steps` — Every accepted trace witness contains fifteen steps.
