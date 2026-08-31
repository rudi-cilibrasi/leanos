# Decoding the firmware's raw memory-map bytes

At boot, firmware leaves a block of raw bytes in memory describing which parts of RAM exist and what they are for. This file's theorems cover the decoder that turns those bytes into the kernel's typed boot memory map: every read is checked against the buffer's bounds, and every accepted result carries built-in evidence tracing each field back to the exact bytes it was read from. Together they guarantee that nothing the kernel later trusts about memory can appear in the decoded result unless the corresponding bytes were actually present, in bounds, and well-formed — and that a rejected buffer produces nothing at all.

- `readLEAux_drop` — Bookkeeping: reading a number out of the byte buffer gives the same answer whether the reader counts from the start of the whole buffer or first discards the bytes before the read position.
- `readLEAux_take` — Bookkeeping: bytes beyond the ones being read never affect the value read, so trimming the buffer down to exactly the bytes needed changes nothing.
- `readLE_drop_take` — Reading a fixed-width number gives the same value whether the decoder reads it in place inside the full buffer or from the exact slice cut out at that position.
- `readU64_drop_take` — An eight-byte value reads identically from the full buffer at its offset and from the isolated eight-byte chunk, which is what lets the chunk-by-chunk stream replay agree with the full decoder.
- `low32Word_ofNat` — The machine-word operation for taking the low 32 bits of a 64-bit value agrees exactly with the decoder's arithmetic version, for every value that fits in 64 bits.
- `high32Word_ofNat` — The machine-word operation for taking the high 32 bits of a 64-bit value agrees exactly with the decoder's arithmetic version, for every value that fits in 64 bits.
- `readByte_lt_byteLimit` — Bookkeeping: any single byte the decoder successfully reads is a value below 256.
- `readLEAux_lt_factor` — A stepping-stone fact used by later theorems: a multi-byte read always produces a value within the numeric bound implied by how many bytes it read.
- `readU64_lt_wordLimit` — Every successful checked eight-byte read produces a value that fits in a 64-bit machine word without any truncation.
- `readLEAux_succeeds` — A stepping-stone fact used by later theorems: whenever enough bytes remain in the buffer, the multi-byte read never fails.
- `readU64_succeeds_of_length` — Whenever at least eight bytes are available, the checked eight-byte read always succeeds, no matter what values those bytes hold.
- `memoryKind_usable_word` — A memory entry is classified as usable exactly when firmware tagged it with type one; no other type code can ever produce a usable classification.
- `decodeEntries_constructs_traversal` — Whenever the decoder accepts a run of memory-map entries, it also produces a step-by-step record proving every field of every entry was read and checked from the source bytes, so no entry can appear without that evidence.
- `successfulEntryDecodeTraversal_length` — Bookkeeping: the entry-by-entry decoding record covers exactly the advertised number of entries, no more and no fewer.
- `successfulTagDecodeTraversal_offset_lt_total` — Every step of a successful walk through the firmware's tags starts at a complete tag header lying strictly inside the advertised data, so nothing is ever read past the end.
- `successfulTagDecodeTraversal_afterMap_shape` — Once the single memory-map tag has been consumed, the rest of a successful walk can only contain irrelevant tags followed by the closing end tag, and their sizes are recorded so the original order can be reconstructed.
- `extractMemoryMap_ignored_around` — Irrelevant tags sitting before or after the one well-formed memory-map tag never change the entry list extracted from it.
- `successfulTagDecodeTraversal_extracts_entry_traversal_aux` — A stepping-stone fact used by the next theorem: for a tag walk that has so far seen only irrelevant tags, the entry list the extractor returns is backed by an entry-by-entry record of the bytes actually read.
- `successfulTagDecodeTraversal_extracts_entry_traversal` — The entry list extracted from a successful tag walk is exactly the one whose bytes were read and checked, entry by entry, from the source buffer.
- `decodeTags_constructs_traversal` — Whenever the tag decoder accepts, it constructs the complete step-by-step certificate of its walk through the bytes, introducing no second parser and no extra assumption.
- `successfulRichDecodeTraversal_entries_source` — The decoding certificate ties the entry list in the final result to the specific memory-map bytes that were walked, not merely to some entry list decoded somewhere in the stream.
- `decode_functional` — Bookkeeping: decoding the same input twice always gives the same result.
- `successful_decode_constructs_traversal` — Every accepted decode, of any input whatsoever, comes with the full byte-walk certificate; no test fixture, shortcut, or caller-supplied value can substitute for it.
- `accepted_input_header` — An accepted result keeps the exact identifying header values of its input: the same boot signature, the same address, and a recorded size equal to the byte buffer's actual length.
- `accepted_input_scalar_header` — The input behind every accepted decode meets all the entry conditions of the chunk-by-chunk streaming parser: correct boot signature, aligned addresses, and in-range sizes.
- `accepted_infoAddress_at_least_page` — Every accepted result records an information address of at least 4 KiB, closing a gap where the decoder could otherwise accept a low address that the streaming replay would necessarily reject.
- `accepted_handoff_valid` — Bookkeeping: the typed handoff inside every accepted result passes the independent handoff validator, which returns exactly the decoded entries.
- `validateHandoff_extractMemoryMap` — Whenever the handoff validator accepts, the entry list it returns is exactly the one extracted from the memory-map tag; none of the earlier shape checks can substitute a different list.
- `accepted_within_bounds` — Bookkeeping: every accepted result stays inside the fixed size limits on total bytes, tag count, and entry count.
- `accepted_entries_valid` — Bookkeeping: the entries of every accepted result pass the separate per-entry checks, so none has zero length or an address range that wraps around.
- `rejected_has_no_handoff` — Whenever decoding is rejected, no handoff value is produced at all.
- `accepted_pipeline_has_handoff` — Whenever the combined decode-then-normalize pipeline succeeds, decoding produced a result and normalization accepted that same result's handoff; the pipeline cannot succeed unless both stages succeeded on the same data.
- `rejected_pipeline_has_no_normalized` — Whenever the combined pipeline rejects, it produces no normalized result at all.
