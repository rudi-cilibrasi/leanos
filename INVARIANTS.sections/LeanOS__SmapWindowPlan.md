# The two code windows that may touch user memory

Only two short stretches of the kernel's hand-written machine code are allowed to read or write a program's memory: one copies bytes in from the program, the other copies bytes out. Each one switches on a processor flag (AC) that permits the access, copies, and switches it off again. These theorems treat each window as a fixed list of instructions, the same list the build checks byte for byte against the finished kernel, and show that the window is always closed again before it returns.

- `copyBody_acSafe` — The shared instruction list of both windows passes the check: it returns, it switches the access flag off before restoring the saved flags and before returning, it touches program memory only while the flag is on, and only its copy instruction can be interrupted by a fault.
- `windows_acSafe` — Both named windows, copy-in and copy-out, pass that same check.
- `windows_ret_closed` — Every way either window returns normally leaves the access flag switched off.
- `windows_access_inside` — Program memory is touched only while the access flag is on.
- `windows_fault_exit` — The only way out of a window other than returning is a fault in the copy instruction, with the flag still on; the kernel's interrupt entry code, checked separately, switches it off.
- `copyBody_encoding` — The window's instructions encode to exactly the sixteen bytes the build expects to find in the kernel.
- `copyBody_label_offsets` — The three named points inside each window sit at bytes 2, 3 and 11, where the build expects the labels.
