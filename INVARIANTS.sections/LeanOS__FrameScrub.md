# Wiping memory before it changes hands

Physical memory is recycled: a frame released by one program is later handed to another. If the kernel forgot to erase it first, the new owner could read the old owner's secrets. These theorems guarantee that a frame is completely wiped before its new owner can see it, that the wipe touches nothing else, and that a refused request changes nothing at all.

- `scrubFrame_target` — Wiping a frame really does reset every byte inside that frame to the clean initial value.
- `scrubFrame_other` — Wiping one frame changes no byte of any other frame.
- `allocate_rejected_unchanged` — Whenever an allocation request is refused, the kernel's state is left exactly as it was.
- `allocation_lifecycle_accepted` — A stepping-stone fact used by later theorems: when this model accepts an allocation, the underlying memory-ownership model accepted it too.
- `allocation_publishes_scrubbed` — By the time a newly allocated frame becomes visible to its new owner, every byte in it has been wiped clean — no matter what firmware or a previous owner left behind.
- `allocation_publishes_owned` — A successful allocation ties the new memory object to a physical frame that the allocator records as belonging to exactly that object.
- `release_rejected_unchanged` — Whenever a release request is refused, the kernel's state is left exactly as it was.
- `release_preserves_bytes` — Giving a frame back never touches its contents: release withdraws the right to use the frame but neither clears nor changes a single byte, and never relies on what those bytes are.
- `read_fresh_zero` — A program reading from its brand-new, never-yet-written frame always sees the clean initial value — never leftover data from anyone else.
