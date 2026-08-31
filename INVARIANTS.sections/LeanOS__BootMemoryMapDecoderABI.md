# The decoder's question-and-answer interface

This small file is the question-and-answer interface that lets ordinary compiled C code replay the boot memory-map decoder on one immutable byte buffer and read the outcome one number at a time. Its two theorems pin down the basics: answers are stable, and a rejected buffer can never masquerade as an accepted one.

- `query_deterministic` — Bookkeeping: asking the same question about the same buffer twice always returns the same answer.
- `rejection_has_no_accepted_status` — Whenever the decoder rejects a buffer, the status question answers rejected, never accepted.
