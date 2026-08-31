# The hardware page tables that enforce memory permissions

The processor decides every memory access by walking a page table, a hardware data structure that says which addresses a program may read, write, or execute. This file models how the kernel builds those tables from its own mapping records and proves the hardware view never grants more than the records allow. It also proves a fixed reviewed memory layout keeps user programs out of every kernel region, and that the processor's extra protections (write-protect, no-execute, SMEP, SMAP) draw exactly the intended lines.

- `classify_deterministic` — Bookkeeping: the hardware-walk classifier gives the same answer every time for the same table, page, and access.
- `encoded_structurally_valid` — Every page table the kernel builds from its mapping records is structurally sound: all its entries are present, marked as user pages, have their reserved bits clear, and point at physical frames within the machine's range.
- `encoded_unmapped_denied` — A page with no mapping record produces a table entry that simply is not there, so the hardware walk refuses the access as not-present.
- `encoded_supervisor_impossible` — Every entry in a table built for a user program is a user entry; no kernel-only page can ever appear in it.
- `encoded_owned` — Every entry in a built table traces back to a live mapping record whose memory object currently owns exactly that physical frame.
- `read_refines_translate` — Whenever the caller owns the address space and its mapping permits reading, the hardware walk and the kernel's own abstract translation return the very same physical frame.
- `write_not_amplified` — A mapping that does not grant write permission produces a table through which writing is refused; the hardware never amplifies what the record allowed.
- `encoded_nx` — Every page in a built table refuses instruction execution, so a user program can never run code out of mapped data memory.
- `encoded_read_result` — A read through any entry of a built table returns exactly the physical frame that entry records, never some other frame.
- `distinct_spaces_separated` — Whenever two address spaces map the same page number to different physical frames, their hardware walks give different answers: the spaces are genuinely separate.
- `policy_table_structurally_valid` — Each single-page table built from the reviewed memory-layout policy is structurally sound whenever its page and frame are within the machine's range.
- `policy_wx_exclusive` — No region in the reviewed layout is both writable and executable; every region gives up at least one of the two.
- `kernel_text_policy` — Spelling out the definition: the kernel-code entry is exactly the one the reviewed policy prescribes for kernel code.
- `kernel_data_policy` — Spelling out the definition: the kernel-data entry is exactly the one the reviewed policy prescribes for kernel data.
- `user_text_policy` — Spelling out the definition: the user-code entry is exactly the one the reviewed policy prescribes for user code.
- `user_stack_policy` — Spelling out the definition: the user-stack entry is exactly the one the reviewed policy prescribes for user stacks.
- `kernel_text_attributes` — Kernel code is invisible to user programs, read-only, and executable.
- `kernel_writable_region_attributes` — Kernel data, kernel stacks, and the page tables themselves are invisible to user programs, writable, and never executable.
- `supervisor_device_region_attributes` — The device-register window and the DMA-remapping tables are invisible to user programs, writable, and never executable.
- `user_text_attributes` — User code is visible to user programs, read-only, and executable.
- `user_stack_attributes` — User stacks are visible to user programs, writable, and never executable.
- `cpl3_kernel_text_denied` — A user-mode program is refused every kind of access, whether read, write, or execute, to the kernel-code region.
- `cpl3_kernel_data_denied` — A user-mode program is refused every kind of access to the kernel-data region.
- `cpl3_kernel_stack_denied` — A user-mode program is refused every kind of access to the kernel-stack region.
- `cpl3_page_tables_denied` — A user-mode program is refused every kind of access to the page tables themselves, so it can never rewrite its own permissions.
- `cpl3_mmio_window_denied` — A user-mode program is refused every kind of access to the device-register window.
- `cpl3_remapping_tables_denied` — A user-mode program is refused every kind of access to the DMA-remapping tables that control what devices may touch.
- `wp_protects_kernel_text` — With the write-protect control on, even the kernel itself cannot write over its own code.
- `smep_protects_user_text` — With the SMEP control on, the kernel is refused when it tries to execute code from a user page.
- `smap_requires_override` — With the SMAP control on and no explicit override raised, the kernel is refused when it tries to read user memory.
