# The ring-3 spawn syscall only runs checked spawn steps

This section is about the system call a user program uses to create, feed, and end a child program. The kernel never interprets that call's numbers itself: a generated checker either refuses the call before anything happens, or matches it to exactly one step of the spawn table, and that step is proved to be one step of the kernel's spawn model on the complete state the kernel is in. Refusals and rejected steps change nothing.

- `syscallTag_cases` — Every system call number either names no spawn command or names one of the five public spawn commands.
- `syscall_never_kernel_command` — No system call number reaches the kernel-only commands: granting or withdrawing spawn permission, switching programs, or copying a permission.
- `canonical_iff_decodes` — The checker's quick test of the registers passes exactly when they are the one correct encoding of a command, and then that command is a public child or memory command.
- `edgeRows_eq` — Bookkeeping: the literal list of table rows is exactly the spawn table's edges written as numbers.
- `ite_mem` — Bookkeeping: if both branches of a choice are in a list, the chosen value is in the list.
- `spawnFamilyMiss_mem` — When a spawn-table input matches no row, the answer is one of the dispatcher's error words.
- `row_eq` — Bookkeeping: a matched table row means every input word equals the row's word.
- `ite_covered` — Bookkeeping: a property that holds for both branches of a choice holds for the choice.
- `spawnDispatchRaw_cases` — For every possible input, the generated spawn table answers either an error word or the reply of the one row whose state and command words are exactly that input.
- `toNat_le` — Bookkeeping: comparing two 64-bit words is comparing their numeric values.
- `dispatch_family` — For any state word of the spawn family, the generated dispatcher hands the call straight to the spawn table.
- `edgeRows_replies` — Every row's reply has the shape of an accepted or rejected step.
- `errorWords_not_replies` — No error word has the shape of a step's reply.
- `edge_of_row` — Every literal table row comes from an edge of the spawn table.
- `spawnSyscall_cases` — For every state, caller, number, and register values, the checker either returns one of its refusal words, or there is exactly one table edge at that state whose command words are the call's, the caller is the state's current program, and the checker returns that edge's reply.
- `edges_syscall_commands` — Every edge whose command a system call can name runs a public child or memory command.
- `stateActor_current` — For every state of the spawn table, the checker's idea of the current program is the one the complete kernel state records (checked by evaluation).
- `allStates_complete` — Bookkeeping: the list of the table's states contains every state.
- `stateActor_of_plan` — The same statement for one state at a time.
- `edges_reply_token` — The low bits of every edge's reply name the state the edge leads to.
- `spawnSyscall_refines` — When the checker answers with an edge, the call decodes to a public child or memory command, the caller is the current program of the complete state, the step is exactly the spawn model's step on that state, the state the kernel keeps afterwards names the step's result, and the returned value word is the step's.
- `spawnSyscall_rollback` — Every refusal keeps the kernel's state word, and every rejected step keeps both the state word and the complete kernel state.
- `spawnSyscall_trace` — Whatever a call does, the state the kernel keeps afterwards satisfies every kernel, resource, child-accounting, and no-grandchildren rule.
- `image_run` — The demonstration image's thirteen calls get exactly the replies and values its user program checks, and walk through the expected states, including a new child in the reused table slot and the old handle being refused.
- `image_model` — In the complete kernel states the demonstration passes through, the child table, the children's address spaces, and the holder of the shared frame are exactly what the demonstration's log reports (checked by evaluation).
