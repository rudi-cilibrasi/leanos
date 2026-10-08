# The range check the running kernel uses before copying user memory

Before the kernel copies bytes in or out of a program, it checks the requested range: not too long, no wrap-around, inside the lower half of the address space, owned by the calling program, mapped, writable if the copy writes, and belonging to a program that has not been replaced. The running kernel now asks a small piece of generated code for that answer instead of a hand-written C function. This file defines that generated check and the exact model situation it stands for: the first program's text mapped read-only and its stack mapped read-write, page by page.

- `copyPolicy_agrees_grid` — On a grid of 540 boundary cases (lengths 0 to 17, addresses at and around every edge of the text and stack, the top of the address space and the canonical limit, reads and writes, the right and wrong program, and current and replaced programs), the generated check gives exactly the answer of the model's range validation.
