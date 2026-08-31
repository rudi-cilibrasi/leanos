# Streaming the memory-map bytes in fixed chunks

To feed the firmware's byte buffer to generated machine code without allocating any memory, the kernel uses a simple stream protocol: bind a stream to one buffer, then hand over the bytes in small fixed chunks, each accepted only at exactly the next expected position. This file's theorems guarantee the protocol cannot be confused: an accepted step advances by exactly the bytes it consumed and stays bound to the same buffer, a completed or failed stream accepts nothing further, and the standard chunking of any buffer reproduces that buffer byte for byte.

- `init_deterministic` — Bookkeeping: initializing a stream with the same values twice always gives the same answer.
- `step_deterministic` — Bookkeeping: taking one stream step with the same inputs twice always gives the same answer.
- `accepted_step_advances_exactly` — Every accepted stream step advances the stream's position by exactly the number of bytes in the chunk it consumed.
- `accepted_step_preserves_stream` — An accepted step never changes which buffer the stream is bound to or the total number of bytes it expects.
- `accepted_step_exposes_exact_chunk` — An accepted step reports back exactly the chunk value and byte count it was given, nothing else.
- `accepted_step_terminal_iff_extent` — A step reports the stream as complete exactly when the bytes consumed so far reach the buffer's full declared size.
- `rejected_step_has_rejected_status` — Whenever any of a step's checks fail, the step reports a rejected status.
- `completed_replay_rejects` — Feeding another chunk to a stream that has already completed is always rejected, no matter what the chunk contains.
- `rejection_exposes_no_chunk` — A rejected step exposes no chunk data at all.
- `modelStep_continuity` — In the exact reference model of the protocol, every accepted step keeps the same buffer identity and total size and advances by exactly the chunk's length.
- `replay_continuity` — Any successful replay of several chunks stays bound to one buffer and advances by exactly the sum of the accepted chunk sizes.
- `canonicalChunks_length` — The standard chunking of a buffer has exactly one chunk for every complete eight-byte word in it.
- `canonicalChunksAux_get?_source` — Every position in the standard chunking is exactly the eight-byte slice at the matching offset in the source buffer, with its offset and final-chunk marker fixed by its position, so a later refinement can never pair a source read with the wrong chunk.
- `canonicalChunks_get?_source` — Public form of the previous fact: each aligned offset names exactly one standard chunk carrying the source bytes, stream identity, offset, and final-chunk bit fixed by the immutable input.
- `canonicalChunks_reconstruct` — Gluing the standard chunks back together reproduces the original buffer exactly, for every aligned buffer rather than just tested examples.
- `canonicalChunks_replay` — Replaying the standard chunks of any nonempty aligned buffer keeps one identity and size, consumes every byte exactly once, and ends in the complete state.
