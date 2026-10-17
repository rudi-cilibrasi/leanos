# The spawn allocator in thirteen words

This section is about the fixed-width form of the allocator record that the kernel can hold: thirteen 64-bit words.

- `Words.ofList_toList` — Bookkeeping: the thirteen state words read back from their list form are the same words.
