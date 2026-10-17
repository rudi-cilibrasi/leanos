# Oracle rows for loading spawned programs

The oracle rows for the run-time loader, with the facts tying their expected words to the kernel model. The spawn family's own rows moved to the hosted spawn-allocator corpus when the fixed spawn table was removed.

- `loader_vectors_expected` — The expected answers of the loader's rows are exactly the listed source answers and decisions.
- `loader_trace_replies` — Along the loader demo's requests, the loader's answers are: undo the load claimed from outside the reserved area, refuse the stale request, load the code in place, copy the data, start, and refuse the two requests after the start.
- `loader_trace_vectors_expected` — The demo-trace test rows expect exactly those numeric answers.
- `loader_trace_vectors_model` — Each demo-trace test row's expected answer is the model's own answer for the loader state the row describes.
- `loader_trace_rollback_idle` — After the failed load, the demo's loader is exactly the loader before the first child was created.
- `loader_trace_contents` — In the demo, the started child reads a code byte from the file, a data byte copied from the file, and a zero just past the data's file size.
