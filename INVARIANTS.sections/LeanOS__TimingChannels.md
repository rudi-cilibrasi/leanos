# The check that refuses a request about another program

When a running program asks the kernel to act on a different program — for example to end it, or to put something in its table — the kernel refuses (ADR 0025). This file is the small generated check the timing-channels kernel image calls for that decision. It takes only three numbers every program can already see: whether the kernel is running normally, which program is running, and which program the request names. So it cannot look at anything about the other program, and the refusal cannot depend on it. The check answers one fixed refusal word or a word that lets the request through.

- `crossSubjectRefusal_cases` — The check only ever answers the refusal word or the pass word.
- `refusedWord_ne_passWord` — The refusal word and the pass word are different, so the two answers cannot be confused.
- `crossSubjectRefusal_refused` — The check refuses only when the kernel is running normally, some program is running, and the request names a different program than the running one.
- `crossSubjectRefusal_own` — A request that names the running program itself, or names no program at all, is never refused.
