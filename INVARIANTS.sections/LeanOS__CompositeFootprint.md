# Naming what each composite operation may touch

This vocabulary gives each authoritative composite-state projection a stable finite name and lets later operation integrations declare what they read and write. Its first lemmas establish the frame-discipline foundations without changing any operation or gate: the vocabulary is complete, unread projections cannot be written, read-only projections remain frame-eligible, and literal preservation obligations compose across sequential steps.

- `Projection.mem_all` — Every named composite-state projection occurs in the explicit finite vocabulary, so footprint declarations cannot silently range over an incomplete hand-written subset.
- `Footprint.unread_is_untouched` — If an operation footprint does not read a projection, the writes-are-reads discipline guarantees that it also leaves that projection untouched.
- `Footprint.untouched_not_written` — An untouched projection is not written, including the important case where an operation reads it without changing it.
- `frames_of_eq` — Whenever a projection's before and after values are literally equal, its generic frame obligation is satisfied.
- `frames_trans` — Projection frame obligations compose across two sequential steps, so preserving an untouched projection through each step also preserves it through their composition.
