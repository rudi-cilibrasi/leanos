# The spawn family's dispatcher states obey the whole-trace rules

This section shows that every state the spawn family's dispatcher table names is reached by a sequence of kernel steps that the whole-trace accounting theorem covers, starting from a state that satisfies every kernel and resource rule. So every rule that theorem guarantees holds at every one of those states.

- `authoritative_issuers_frameBudgets_unsupported` — None of the kernel's core rules looks at the identity counters or the frame budgets.
- `familySeed_authoritativeRuntimeWellFormed` — Every starting state of the family satisfies the kernel's core rules, because it differs from the dispatcher's checked starting state only in parts those rules never read.
- `dispatcherSeed_issuedSubjects` — Bookkeeping: in the dispatcher's starting state, exactly subjects 1 and 2 have ever been issued.
- `dispatcherSeed_issuedObject` — Bookkeeping: in the dispatcher's starting state, exactly objects 1, 2, 10, and 20 have ever been issued as memory, and objects 1 and 2 as address spaces.
- `familySeed_resourceRuntimeWellFormed` — Every starting state of the family satisfies every resource rule as well, as long as its identity counters are above everything already issued and inside the allowed range.
- `familySeed_childAccounting` — Every starting state with no recorded children satisfies the child-accounting rules.
- `familySeed_spawnTree` — Every starting state with no children, no spawn permission, and no recorded parents satisfies the rule that children never have children.
- `seedState_familySeed` — Each of the four starting states (the main one and the three with one counter at its limit) is such a starting state.
- `runFamily_runChildSteps` — Replaying the family's commands is the same as running the corresponding steps of the whole-trace theorem.
- `toStep_admissible` — Every command of the family meets the whole-trace theorem's precondition in every state.
- `admissibleAlong_family` — Every replayed command list meets the precondition along its whole length.
- `spawn_boundary_trace` — Every state the family's tokens name satisfies all kernel, resource, child-accounting, and no-grandchildren rules; frame use stays within each limit; each parent's live children stay within its budget and its use plus its children's limits within its entitlement; no frame outside the starting commitment is committed; and no subject identity is created twice or reused.
