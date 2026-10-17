# Bounded allocator records encode exactly

The spawn allocator's record is stored as thirteen 64-bit words. Earlier files show that well-formed words read back as a record and re-encode to the same words. This file shows the other direction: every record within the allocator's bounds encodes to well-formed words that read back as the same record, so the generated word functions run on such a record are exactly the allocator's step.

- `generationReserved_value` — Bookkeeping: the reserved generation is 2^48 − 1.
- `wordBound_value` — Bookkeeping: the word bound is 2^64.
- `frameBound_value` — Bookkeeping: the frame bound is 2^16.
- `children_four` — A bounded record's child table is exactly its four child entries, in slot order.
- `memory_two` — A bounded record's memory table is exactly its parent slots 2 and 3.
- `childAt_mem` — A child entry the record reports in some slot is one of its child-table entries.
- `memoryAt_mem` — A memory identity the record reports in some slot is one of its memory-table entries.
- `charge_le_chargeSum` — A child's charge is at most the total charged to all children.
- `decodeChild_encodeChild` — One child entry of a bounded record encodes to a well-formed word that reads back as the same entry and carries its charge in the low sixteen bits.
- `decodeMemory_encodeMemory` — One memory entry of a bounded record encodes to a word that reads back as the same entry.
- `decodeAuthority_encodeAuthority` — The spawn generation a bounded record holds encodes to a word that reads back as the same generation.
- `frames_toNat` — The word holding the subject budget and the parent's frames does not overflow for a bounded record.
- `decode_encode` — A bounded record's words read back as exactly that record.
- `encode_canonical` — A bounded record's words are well formed.
- `code_step` — On a bounded record's words, the generated reply, value and successor functions return exactly the allocator step's status, value and the words of its next record, for every command the allocator decides.
