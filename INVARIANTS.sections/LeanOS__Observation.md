# What one program can see, and what a single hidden step cannot change

These theorems set up the basic privacy story for a single kernel operation. Each program (a "subject") has a declared view of the system: whether it is alive, which capabilities it holds, its own bytes, any explicitly shared bytes, its memory mappings, the kernel's latest reply to it, its incoming messages, and the scheduler's publicly visible choice. A step is called "silent" for an observer only when its entire footprint belongs to some unrelated program — shared-memory writes, resource allocation, and scheduling are deliberately never silent. The theorems guarantee that silent steps are invisible: an observer's view is exactly the same before and after them.

- `View.ext` — Bookkeeping: two observer views that agree on every declared item — liveness, held rights, private bytes, shared bytes, mappings, latest reply, deliveries, and the scheduler's choice — are one and the same view.
- `silent_observe_unchanged` — Whenever a step is silent for an observer, that observer's entire view of the system is exactly the same after the step as before it, no matter what the step did elsewhere.
- `silent_steps_lowEquiv` — Whenever two system states look identical to an observer, they still look identical after each side takes any step of its own choosing that is silent for that observer — the two steps need not be the same.
- `silent_steps_equal_reply` — In particular, after any such pair of silent steps, the kernel reply the observer sees is exactly equal on both sides.
