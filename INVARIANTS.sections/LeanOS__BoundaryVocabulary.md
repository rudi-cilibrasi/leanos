# The one list of names the C code may use for kernel states, commands, and replies

The kernel's generated C boundary talks in numbers: every canonical state, command, typed reply, flush authorization, and error is a fixed 64-bit word. This file is the single Lean-owned list that gives those words their C names, and every word in it is computed by calling the same encoder or canonical-edge table that the dispatcher proofs use, so the C constants are generated from the model rather than typed in by hand. The theorems below check that the list is sound (no two states, replies, or errors share a word) and complete (every constructor of every state, command, reply, and error family appears in it), so a token that the model can produce is never missing from the generated header and no header constant can silently name two different things.

- `state_words_nodup` — No two canonical state names in the vocabulary map to the same 64-bit word, so a state token identifies exactly one modeled state.
- `reply_words_nodup` — No two typed reply names map to the same control word, so a reply constant can never be mistaken for a different reply.
- `error_words_nodup` — The six closed error words are pairwise distinct.
- `state_count_is_state_tokens` — The generated state-count constant equals the number of state tokens listed, confirming the count is not stale prose but the list's actual size.
- `stateId_covered` — Every state of the basic eight-state dispatcher family has a token in the vocabulary.
- `mixedStateId_covered` — Every state of the mixed transfer/IPC/mapping family has a token in the vocabulary.
- `invalidationStateId_covered` — Every state of the invalidation publication sequence has a token in the vocabulary.
- `budgetStateId_covered` — Every frame-budget scenario state has a token in the vocabulary.
- `capabilityTransferBootStateId_covered` — Every state of the machine A-to-B capability-transfer trace has a token in the vocabulary.
- `inFlightRevocationStateId_covered` — Every state of the in-flight revocation trace has a token in the vocabulary.
- `commandId_covered` — Every basic-family command tag is listed among the generated command selectors.
- `mixedCommandId_covered` — Every mixed-family command tag is listed among the generated command selectors.
- `invalidationCommandId_covered` — Every invalidation command tag is listed among the generated command selectors.
- `capabilityTransferBootCommandId_covered` — Every boot-transfer command tag is listed among the generated command selectors.
- `inFlightRevocationCommandId_covered` — Every in-flight revocation command tag is listed among the generated command selectors.
- `budgetCommand_covered` — Every frame-budget command tag is listed among the generated command selectors.
- `mixedReplyId_covered` — Every mixed-family typed reply word is listed among the generated reply constants.
- `invalidationReplyId_covered` — Every invalidation typed reply word is listed among the generated reply constants.
- `inFlightRevocationReplyId_covered` — Every in-flight revocation typed reply word is listed among the generated reply constants.
- `capabilityTransferBootEdges_covered` — The control word of every canonical boot-transfer edge is listed among the generated reply constants.
- `decodeError_covered` — Every closed decode-error word is listed among the generated error constants.
