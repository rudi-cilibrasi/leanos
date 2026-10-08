# The shared recipe for whole-run privacy proofs

These theorems state, once and for any system, the recipe that the scheduler privacy model and the full kernel privacy model both follow. A system runs one step at a time and, after each step, either says nothing to an observer or announces one event to it. If quiet steps never change what the observer sees, and announced steps leave the observer seeing exactly what the event says, then whole finite runs can be compared by their announced events alone.

- `replays_of_unwinding` — The two per-step promises — a quiet step changes nothing the observer sees, and an announced step leaves the observer seeing exactly what it announced — together give the one-step replay guarantee.
- `run_replays` — Given the one-step guarantee, the observer's view at the end of any finite run equals its starting view with the run's announced events replayed onto it in order.
- `finite_trace_lowEquiv` — The general privacy theorem: two finite runs that start indistinguishable to an observer and announce the same events end indistinguishable to it, even if they took different numbers and kinds of quiet steps; runs that never finish are not covered.
