# The brief window when the kernel may touch program memory

Modern processors have a safety catch that normally stops the kernel from accidentally reading or writing a program's memory; the kernel must deliberately lift an override flag to do so. These theorems show that LeanOS lifts that flag only inside a single, tightly bounded copy operation: every byte of the request is checked before the flag goes up, the one copy is the only thing done while it is up, and the flag is guaranteed to be back down on every way out, success or failure. Even while the flag is up, it grants no more than the checked request needed, and it never turns read permission into write permission.

- `openWindow_validated` — A window can only open when the flag was down beforehand and the whole requested range had already passed every check; the opened state is the old state with nothing changed except the raised flag.
- `openWindow_sets_ac` — Spelling out the definition: a successfully opened window has the override flag up, which is exactly what the copy step needs.
- `closed_encoded_user_access_denied` — While the window is closed, the processor's safety catch blocks the kernel from touching any page of program memory, for reading and for writing alike.
- `openWindow_encoded_read_allowed` — An open, fully pre-checked window supplies exactly the state needed for the kernel to read a mapped page of program memory.
- `openWindow_encoded_write_allowed` — The override never amplifies permission: even with the window open, the kernel can write a page of program memory only if that page was marked writable in the first place.
- `copyFrom_clears_ac` — After any copy out of a program's memory, accepted or refused, the override flag is down again; no path leaves it up.
- `copyTo_clears_ac` — After any copy into a program's memory, accepted or refused, the override flag is likewise down again.
- `copyFrom_accepted_validated` — An accepted copy out of a program's memory can only have happened after the entire range passed validation with read permission; there is no unchecked path to acceptance.
- `copyTo_accepted_validated` — An accepted copy into a program's memory can only have happened after the entire range passed validation with write permission.
- `copyFrom_rejected_memory_unchanged` — A refused copy-out is stopped before the window ever opens, so neither the program's memory nor the kernel's buffers change at all.
- `copyTo_rejected_memory_unchanged` — A refused copy-in is likewise stopped before the window opens, leaving both memory domains exactly as they were.
