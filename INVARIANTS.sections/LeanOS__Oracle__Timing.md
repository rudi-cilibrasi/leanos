# Oracle rows for the cross-subject refusal check

The oracle rows for the check that refuses a request about another program, which the build replays against the generated C code.

- `timing_refusal_vectors_expected` — The expected answers of the refusal check's rows are exactly the listed words: refusals for the two requests about another program and for the largest program number, and the pass word for a request about the running program itself, a request naming no program, no running program, a kernel that is busy, stopped or in an unknown mode, and the largest numbers.
