# The kernel's spawn words follow the kernel model exactly

The kernel keeps the spawn family's state as the thirteen words of the allocator's record and answers the ring-3 spawn system calls with generated functions over those words. This file shows that on the words of every kernel state the allocator describes, every call that is not refused is exactly one step of the kernel model's spawn or memory gate on that state: the same status, the same value, and the words of the resulting state, which the allocator still describes. Refusals and rejections change nothing, the starting words are the starting state's, and so along every sequence of calls the kernel's words stay the words of the model state the same steps reach.

- `family_bounded` — The record of every kernel state the allocator describes is within the allocator's bounds.
- `syscallTag_cases` — A system call number names either nothing or one of the five spawn-family commands.
- `syscallTag_not_kernel` — No system call number names the kernel's grant or revocation of the spawn right.
- `registersCanonical_iff` — For a spawn-family number, the register check passes exactly when the command words decode, and then they decode to a public child or memory command.
- `refusalOf_zero` — A call that is not refused has well-formed state words, comes from the parent, uses a spawn-family number, and has well-formed registers.
- `syscall_code` — A call that is not refused runs the generated step functions on its command words.
- `syscall_refused` — A refused call returns its refusal word and a zero value and keeps every state word.
- `toCommand_familyCommandOf` — Translating an allocator command to a kernel-model command and back gives the same command.
- `syscall_refines` — On the words of every kernel state the allocator describes, a call that is not refused decodes to a public child or memory command, comes from the current program, and returns exactly the status and value of one step of the kernel model's gate on that state, with the words of the resulting state, which the allocator still describes.
- `syscall_rollback` — On those words, a refused call or a rejected step keeps every word, returns a zero value, and leaves the model state unchanged.
- `kernel_refines` — The kernel's own commands on those words, including its grant of the spawn right and its ending of a child, are likewise exactly one step of the kernel model's gate.
- `seed_refines` — The starting words are the words of the family's starting state, for every boot plan, and that state is one the allocator describes.
- `syscall_preserves` — Every call keeps the kernel's words the words of a state the allocator describes.
- `syscallTrace_refines` — Along every sequence of calls from the start, the kernel's words are the words of the model state the same gate steps reach, and the allocator describes that state.
- `syscall_spec` — For every input, the generated call functions compute the specification: the refusal checks in order, then reading the words, running the allocator, and writing the words back.
- `kernel_spec` — For every input, the generated kernel-command functions compute the same specification.
