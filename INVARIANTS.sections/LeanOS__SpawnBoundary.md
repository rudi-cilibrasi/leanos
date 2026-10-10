# Spawn at the boot image's command boundary

This section puts the spawn commands, the commands that give memory to a child or end it, and the memory commands into the boot image's stateful command dispatcher, a fixed table that the boot image's code is generated from. Each state number names the complete kernel state reached by replaying earlier kernel steps from a fixed starting state, and each table row is proved to be exactly one kernel step on that state. User programs still cannot spawn: this is a test boundary, not a system call.

- `toNat_ofNat_of_lt` — Bookkeeping: a number that fits in a 64-bit word survives the round trip into a word and back.
- `ofNat_ne_zero` — Bookkeeping: a positive number that fits in a 64-bit word becomes a nonzero word.
- `decodeFamily_encodeFamily` — Every command of the family whose numbers fit the argument words, with a nonzero spawn word and frame count, decodes back to exactly itself.
- `decodeChild_spawn` — Bookkeeping: words that the child-command decoder reads as a spawn are words the spawn decoder reads as that same request.
- `decodeChild_not_kernel` — Bookkeeping: the child-command decoder never produces the kernel's own grant or withdrawal of spawn permission.
- `encodeFamily_decodeFamily` — Any words that decode to a command are exactly the standard encoding of that command, so each command has only one encoding.
- `memoryErrorCode_injective` — No two memory refusal reasons share a code.
- `childStatus_accepted_or_rejected` — A child-command result is reported either with the accepted status or as a refusal.
- `memoryStatus_accepted_or_rejected` — A memory-command result is reported either with the accepted status or as a typed refusal.
- `familyStep_state` — Every command of the family is one step of the kind the whole-trace accounting theorem covers.
- `familyStep_stutter` — A refused spawn, child, or memory command leaves the whole kernel state exactly as it was.
- `decodeState_encodeState` — Every spawn-family state number reads back as exactly its state.
- `encodeState_injective` — Different spawn-family states have different state numbers.
- `runFamily_append` — Bookkeeping: replaying a list of commands and then one more is the same as replaying the longer list.
- `okIs_iff` — Bookkeeping: the success check used by the table checks means exactly "decoded to this value".
- `edges_dispatch` — For every row of the table, the generated dispatcher answers with exactly that row's reply and value words, and the reply reads back as the row's next state and status.
- `edges_decode` — Every row's command words decode to exactly that row's command.
- `edges_shape` — Every row either replays one more command from the same starting state, or is a refused spawn, child, or memory command that keeps its state.
- `edges_model` — On the complete state each row starts from, the kernel step gives exactly the row's status and value words.
- `edge_refines` — Each table row is exactly one kernel step: on the complete state the row's state number names, the step returns the complete state its next state number names, with the row's status and value.
- `dispatcher_refines` — For every table row: the words decode to the row's command, the generated dispatcher answers with the row's reply and value, and that answer is exactly the kernel step on the named state.
- `edges_rejections_stay` — Exactly the accepted rows move to a new state; every refused row stays where it was.
- `rejected_edge_unchanged` — Every refused row keeps both its state number and the whole kernel state, so a failed spawn, grant, termination, or memory request leaves nothing behind.
- `edges_match_hosted_oracle` — For every spawn, memory-grant, and end-child row, the separate hosted Lean test boundary reports the same status and value words as the boot dispatcher.
