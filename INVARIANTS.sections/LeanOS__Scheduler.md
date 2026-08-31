# Taking turns on the processor

The scheduler decides which program (subject) runs next, keeping the others in a bounded waiting queue and rotating through them in round-robin order. These theorems guarantee that every refused request leaves the kernel untouched, that every operation keeps the scheduler's bookkeeping sound, that only live, runnable programs with their own address space are ever handed the processor, and that no waiting program can be starved: each one gets its turn within one bounded round.

- `add_rejected_unchanged` — Whenever the scheduler refuses to add a subject to the queue, the state is left exactly as it was.
- `remove_rejected_unchanged` — Whenever the scheduler refuses to remove a subject, the state is left exactly as it was.
- `select_rejected_unchanged` — Whenever selecting the next subject is refused, the state is left exactly as it was.
- `yield_rejected_unchanged` — Whenever a yield (the running subject giving up its turn) is refused, the state is left exactly as it was.
- `tick_rejected_unchanged` — Whenever a timer tick is refused, the state is left exactly as it was.
- `terminateCurrent_rejected_unchanged` — Whenever terminating the running subject is refused, the state is left exactly as it was.
- `add_preserves_wellFormed` — Adding a subject to the queue always keeps every scheduler bookkeeping rule intact: no duplicates, the queue within its fixed capacity, and only live, runnable subjects with their own address space queued.
- `remove_preserves_wellFormed` — Removing a subject always keeps those same bookkeeping rules intact.
- `selectNext_preserves_wellFormed` — Selecting the next subject to run always keeps the bookkeeping rules intact.
- `yield_preserves_wellFormed` — A yield — the running subject going to the back of the queue and the head taking over — always keeps the bookkeeping rules intact.
- `tick_preserves_wellFormed` — A timer tick, which is exactly one round-robin yield, always keeps the bookkeeping rules intact.
- `terminateCurrent_preserves_wellFormed` — Terminating the running subject always keeps the bookkeeping rules intact.
- `dispatch_context_safe` — The identity and address space handed to a newly dispatched subject are exactly the ones the scheduler selected — that subject and an address space it owns — and neither value can be supplied from outside as an argument.
- `dispatch_selects_live_runnable` — In a well-formed scheduler, whichever subject is selected to run is guaranteed to be live and runnable.
- `termination_cleanup` — Terminating a subject scrubs it from the scheduler completely: it is no longer in the waiting queue and can no longer be the running subject.
- `bounded_progress_position` — Every subject in the queue sits at a definite position strictly below the scheduler's fixed capacity, and since each scheduling step consumes one queue head, that position bounds how many steps stand between the subject and the processor.
- `bounded_round_robin_selection` — Every continuously runnable queued subject appears in the dispatch order within the fixed capacity — no one can be pushed back forever.
- `many_selected_within_one_round` — A concrete, machine-checked run: with three subjects queued and the scheduler ticking along, each of the three is dispatched within a single round.
