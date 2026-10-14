# How the system-call exit picks its path

When a program's system call finishes, the kernel's hand-written exit code chooses how to leave: hand the answer back to the caller, or save the caller and switch to another program. It used to choose by looking at the answer itself and comparing it with a few fixed numbers, so a program that got the kernel to answer with one of those numbers could push the exit onto the wrong path. The choice now comes from a separate word that only the kernel writes. These theorems describe the exit's chain of comparisons as data, the same chain the build checks against the finished kernel, and show that only that kernel-written word decides the path.

- `code_injective` — No two paths share a selector number.
- `run_reads_rdx_only` — A chain of comparisons that only ever looks at the selector register gives the same result for any two states with the same selector, whatever else differs.
- `dispatch_reads_selector_only` — The kernel's exit chain looks only at the selector: not at the answer, and not at any register the calling program left behind.
- `dispatch_function_of_step_path` — The path taken depends only on the path the kernel chose for the step, never on the answer word or on the caller's saved registers.
- `run_ladder_code` — When the selector holds a path's number, the chain picks that path if this kernel image handles it and stops the machine otherwise.
- `dispatch_enter` — A step whose chosen path the image handles leaves by exactly that path.
- `dispatch_unhandled_fail_stop` — A step whose chosen path the image does not handle stops the machine instead of guessing.
- `dispatch_unknown_selector_fail_stop` — A selector that is no path's number stops the machine.
- `former_magic_inert` — An answer equal to any of the old fixed numbers leaves by the path the kernel chose, as any other answer would.
- `former_magic_reply_returns` — In particular, an ordinary answer equal to one of the old numbers goes back to the caller.
- `legacy_reply_steered` — A record of the old behaviour: comparing the answer itself sent an ordinary answer equal to each old number onto a switch path instead of back to the caller.
