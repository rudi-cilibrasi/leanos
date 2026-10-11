# The revocation-history leak is inside the full view

The earlier record shows two runs the ordinary view cannot tell apart, after which revoking a tree of the observer's own permission cancels the handover pending on its endpoint in one run only. The difference was hidden history: in one run the offered permission descends from the observer's own, in the other from another program's. That history is the observer's revocation authority, and the full view contains it. On the standard sample boot plan the kernel evaluates the two runs' extra authority and finds it different, so the pair is not fully indistinguishable, and the per-step guarantee covers revocation for every pair that is.

- `facts_sample` — On the standard sample boot plan, the two runs' extra authority differs.
- `facts_of_compile` — The same holds for the plan the sample input compiles to.
- `revokeSubtree_own_closed` — The pair on which revoking a tree of the observer's own permission leaked is not fully indistinguishable.
