# The generated allocator decides like the allocator

For every possible thirteen state words and five command words, the generated fixed-width code gives the same reply as decoding the words and running the allocator.

- `decodeCommand_ok` — Five command words that decode are a spawn with decoded rights, a frame grant, a termination, an allocation, a release, a kernel grant, or a kernel withdrawal, each with its arguments taken straight from the words.
- `budget_toNat` — The generated subject-budget field is the decoded record's budget.
- `le_toNat` — Bookkeeping: comparing two words compares their values.
- `lt_toNat` — Bookkeeping: comparing two words compares their values.
- `decide_spawn` — The generated decision of a spawn gives exactly the allocator's status on the decoded record.
- `decide_grant` — The generated decision of a frame grant gives exactly the allocator's status.
- `decide_terminate` — The generated decision of a termination gives exactly the allocator's status.
- `memoryWordAt_zero_iff` — A parent memory slot's word is zero exactly when the decoded slot holds no memory.
- `decide_allocate` — The generated decision of a memory allocation gives exactly the allocator's status.
- `decide_release` — The generated decision of a memory release gives exactly the allocator's status.
- `decide_grantAuthority` — The generated decision of a kernel grant of spawn permission gives exactly the allocator's status, or the outside-the-representation word when the allocator declines to decide.
- `decide_revoke` — The generated decision of withdrawing spawn permission gives exactly the allocator's status.
- `decideW_spec` — For every decoded command, the generated decision is the allocator's status on the decoded record.
- `errorWord_ne_zero` — No dispatcher error word is zero.
- `canonical_words` — Bookkeeping: the generated canonical-words test is the specification's.
- `codeReply_spec` — For every thirteen state words and five command words, the generated reply word is exactly the specification's.
- `codeReply_accepted` — A reply of 0x01 means the state words were canonical, the command decoded, and the allocator accepted it.
