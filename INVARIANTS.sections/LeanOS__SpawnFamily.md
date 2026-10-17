# The spawn family's commands, starting states and whole runs

The spawn family's commands are spawn, giving frames to a child, ending a child, the parent's memory commands, the kernel's grant and withdrawal of the right to spawn, and two dispatcher-only commands (a timer switch and a capability copy). This section fixes their word encoding and how their results become status and value words, defines one step of the family and a whole run of steps, and proves that the family's starting states satisfy the kernel's invariants and that every run from them keeps all of the whole-run guarantees.

- `toNat_ofNat_of_lt` — Bookkeeping: a number that fits in a 64-bit word survives the round trip into a word and back.
- `ofNat_ne_zero` — Bookkeeping: a positive number that fits in a 64-bit word becomes a nonzero word.
- `decodeFamily_encodeFamily` — Every command of the family whose numbers fit the argument words, with a nonzero spawn word and frame count, decodes back to exactly itself.
- `decodeChild_spawn` — Bookkeeping: words that the child-command decoder reads as a spawn are words the spawn decoder reads as that same request.
- `decodeChild_not_kernel` — Bookkeeping: the child-command decoder never produces the kernel's own grant or withdrawal of spawn permission.
- `encodeFamily_decodeFamily` — Any words that decode to a command are exactly the standard encoding of that command, so each command has only one encoding.
- `memoryErrorCode_injective` — No two memory refusal reasons share a code.
- `childStatus_accepted_or_rejected` — A child-command result is reported either with the accepted status or as a refusal.
- `memoryStatus_accepted_or_rejected` — A memory-command result is reported either with the accepted status or as a typed refusal.
- `familyStep_state` — Every command of the family is one step of the kind the whole-trace accounting theorem covers.
- `familyStep_stutter` — A refused spawn, child, or memory command leaves the whole kernel state exactly as it was.
- `runFamily_append` — Bookkeeping: replaying a list of commands and then one more is the same as replaying the longer list.
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
- `family_trace` — Every state the spawn family reaches from any of its starting states, by any list of its commands, satisfies the kernel's authority, resource, child-accounting and spawn-tree invariants; frame usage stays within each limit; every parent's live children stay within its child budget, and its usage plus its children's limits within its entitlement; no frame outside the starting commitments becomes committed; and no subject identity is created twice or reused along the way.
