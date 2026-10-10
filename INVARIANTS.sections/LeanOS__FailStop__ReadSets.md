# What each kernel operation may read: checked read sets

Every kernel operation declares the parts of the kernel state it reads. The theorems here check those declarations: two kernel states that agree on everything an operation declares it reads get the same reply and agreeing results on everything it declares it writes. Together with the frame rule, the declared footprint therefore determines the entire result of each step.

- `CompositeState.returnPlanLive_eq` — Spelling out the definition: whether the compiled return plan still matches live memory depends only on the execution record and the virtual-memory state.
- `selectLiveReturnAuthority_eq_selectLiveExecution` — Choosing the return policy for the next return to a program replaces only the execution record, with a value computed from the execution record and the virtual-memory state.
- `liveReturnExecution_fold` — Spelling out the definition: the execution record checked by an outgoing return is computed from the execution record and the virtual-memory state alone.
- `dispatchIPC_reads` — A plain message send or receive reads only the execution record, the message state, and the sealed-transfer store, so two states that agree on those get the same reply and the same new message and transfer records.
- `applyOperation_reads` — Every ordinary kernel operation reads only what it declares: two states that agree on its declared reads end in states that agree on everything it declares it writes.
- `operationReply_reads` — The reply of every ordinary kernel operation depends only on the parts of the kernel state it declares it reads.
- `gate_reads` — The ordinary kernel gate reads only an operation's declared reads plus whether the kernel is running, busy, or halted: states that agree on those get the same result and agreeing written parts, on accepted, busy, and halted outcomes alike.
- `agreeOn_blockingWrites_of_view` — Bookkeeping: two states with the same scheduling, lifecycle, snapshot-bank, and blocking records agree on everything a blocking message operation may write.
- `BlockingViewRelated.of_map` — Bookkeeping: two fallible publication steps that give the same visible blocking records either fail with the same error or both succeed with matching blocking records.
- `restoreBlockingPeer_reads` — Handing the processor to the next scheduled program after a block reads only the blocking operation's declared parts, so two states that agree on them get the same outcome.
- `publishReleasedBlockingContext_reads` — Waking a released waiter reads only the blocking operation's declared parts, so two states that agree on them get the same outcome.
- `dispatchBlockingReceive_reads` — A blocking receive reads only its declared parts: two states that agree on them get the same reply and agreeing written parts.
- `dispatchBlockingSend_reads` — A blocking send reads only its declared parts: two states that agree on them get the same reply and agreeing written parts.
- `dispatchBlockingCancel_reads` — Cancelling a blocked wait reads only its declared parts: two states that agree on them get the same reply and agreeing written parts.
- `applyBlockingOperation_reads` — Every blocking message operation reads only what it declares: its reply and its written parts depend on nothing else.
- `blockingGate_reads` — The blocking gate reads only an operation's declared reads plus whether the kernel is running, busy, or halted.
- `drainDeferredCancellation_reads` — Draining a deferred cancellation reads only its declared parts: two states that agree on them get the same result and agreeing written parts.
- `applyAuthoritativeOperation_reads` — Every operation of the single authoritative gate, ordinary, blocking, or deferred drain, reads only what it declares: its reply and its written parts depend on nothing else.
- `authoritativeGate_reads` — The single authoritative kernel gate reads only an operation's declared reads plus whether the kernel is running, busy, or halted: states that agree on those get the same result and agreeing written parts.
