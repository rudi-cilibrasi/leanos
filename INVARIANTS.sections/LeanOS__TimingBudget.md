# Closing two timing channels

How long the kernel takes to answer can leak information even when the answer itself does not. ADR 0028 decides which of these timing differences LeanOS closes, which it accepts and names the source of, and which it leaves out of scope. This file states the two it closes. First, a request about another program is refused by a check that reads only what everyone can see, and the reply is held back until a fixed number of processor cycles after the request came in, so every such refusal leaves at the same moment. Second, programs are not allowed to read the processor's cycle counter at all, so they have no fine clock to time the kernel with. Nothing here is about real time: how many cycles a step takes is whatever the hardware takes, and the model only says how the moment of the reply follows from it.

- `subjectWord_some_toNat` — Bookkeeping: the number used to name a program is its identity plus one, as long as that fits in 64 bits.
- `subjectWord_some_ne_zero` — Bookkeeping: the number naming a program is never zero, the number that means "no program".
- `subjectWord_some_inj` — Bookkeeping: two programs get the same number only if they are the same program.
- `crossSubjectRefusal_agrees` — The generated refusal check, given the kernel's mode, the running program and the named program as numbers, refuses exactly when the kernel model's gate refuses the request as a request about another program.
- `departure_not_early` — A reply that is held back to a budget never leaves before that budget has passed.
- `departure_fixed` — Two held-back replies whose work fits within the budget leave at exactly the same moment, however much work each one did.
- `departure_within` — A held-back reply whose work fits within the budget leaves exactly when the budget runs out.
- `departure_overrun` — A reply whose work takes longer than the budget leaves when its work is done.
- `refusal_fixed_budget` — Two kernel states that agree on the mode and the running program refuse the same request about another program in the same way, change nothing, and — when the work fits the budget — reply at the same moment, whatever the state of the program the request names.
- `refusal_words_public` — The refusal check gets the same three numbers in any two kernel states that agree on the mode and the running program, so it cannot answer differently between them.
- `clock_controls_deny_user_counters` — Every processor control setting that the kernel accepts before returning to a program makes the cycle counter and the performance counters unreadable from that program, under the processor manual's description of those instructions.
- `clock_controls_require_tsd` — A control setting that leaves the cycle counter readable by programs, as firmware usually leaves it, is refused.
