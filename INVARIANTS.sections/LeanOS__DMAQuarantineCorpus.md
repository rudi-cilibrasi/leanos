# Replayable test records for the DMA watchdog

LeanOS's DMA quarantine is a watchdog that halts the whole machine if a device's control settings ever differ from the snapshot accepted at boot. This file freezes a small table of six replayable test records — two short runs of the watchdog, each step recorded with its starting state, operation, ending state, and verdict as fixed-width numbers — so outside tools can re-run the exact same steps and compare answers word for word. The theorems pin down the table's exact size, shape, verdicts, and step-to-step continuity, guaranteeing the published records are an unbroken, faithful replay of the watchdog's behavior.

- `encodeControlState_fixed_width` — Whenever a watchdog control state encodes successfully, the encoded record has exactly the advertised fixed number of words.
- `encodeOperation_fixed_width` — Whenever an operation encodes successfully, its record likewise has exactly the advertised fixed width.
- `encodeRuntimeResult_length` — Every verdict encodes to exactly one word.
- `corpus_shape` — The published table contains exactly six records.
- `corpus_fixed_width` — Every record in the table has exactly the advertised widths for its before-state, operation, after-state, and verdict fields.
- `changed_trace_result_sequence` — The "changed control" run ends exactly as advertised: an ordinary step and a faithful re-observation both continue, observing a tampered control register halts the machine fatally, and the follow-up step answers "already halted".
- `invalid_trace_result_sequence` — The "invalid control" run ends exactly as advertised: observing a flipped bus-master bit halts the machine fatally as invalid, and the follow-up observation answers "already halted".
- `changed_trace_continuous` — In the first run, each record's after-state is exactly the next record's before-state, so there are no hidden steps between records.
- `invalid_trace_continuous` — In the second run, the first record's after-state is exactly the second record's before-state.
