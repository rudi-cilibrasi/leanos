# The closed register leak

Until this change, three answers the kernel gave the observer carried another program's complete saved registers: the answer to its timer switch carried the next program's registers, the answer to a send that woke a waiting program carried that program's registers, and the answer to cancelling a wait carried the cancelled program's registers. The running kernel never handed those registers to the caller; the leak was in the model's record of the answer. The answers now name a program and nothing else. These theorems show that the named program is one every observer already sees, keep a record of what the old answers carried, and check, on the standard sample boot plan, that the old answers differed between two runs the observer cannot tell apart while the new ones agree.

- `yield_accepted_current` — When a round-robin yield picks a program, that program becomes the scheduled one.
- `switch_restored_current` — A context switch makes exactly the program whose snapshot it restores the scheduled one.
- `resume_reply_names_scheduled` — When the kernel reports a completed switch to a program, that program is the scheduled one afterwards, which every observer sees; the answer carries none of its registers.
- `legacyResume_owner` — The old switch answer was the program the new answer names, together with that program's saved snapshot.
- `facts_sample` — The kernel's evaluator confirms every concrete fact about the example runs on the standard sample boot plan.
- `facts_of_compile` — For the compiled sample plan, every concrete fact holds.
- `facts_parts` — Bookkeeping: the combined check splits into its named facts.
- `preempt_pair` — The two runs that switch to program 1 and back with different saved registers meet every condition of the privacy theorems.
- `blocked_pair` — The two runs that park program 1 with different registers meet every condition.
- `legacy_replies_leaked` — The old answers to the observer's timer switch, its waking send, and its wait cancellation differed between those indistinguishable runs, because they carried program 1's saved registers.
- `register_channel_closed_on_pairs` — The new answers to the same three operations are equal in both runs.
