# Per-program memory budgets

Each program (subject) is admitted at boot with a fixed budget: a set of memory frames that only it may be charged for. These theorems guarantee that no program can ever use more than its budget, that one program exhausting its budget can never starve or block another, that budgets themselves can never be transferred, forged, or grown, and that when a program is terminated its frames — and only its frames — return to the free pool.

- `usage_le_limit` — A subject's count of frames in use can never exceed the number of frames set aside for it; usage always stays within the budget.
- `commitments_disjoint` — Each budgeted frame belongs to exactly one subject's budget: whenever the records charge a frame to two subjects, they are the same subject.
- `allocate_rejected_unchanged` — Whenever an allocation request is refused, for any reason, the kernel's state is left exactly as it was.
- `release_rejected_unchanged` — Whenever a release request is refused, the kernel's state is left exactly as it was.
- `terminate_rejected_unchanged` — Whenever a termination request is refused, the kernel's state is left exactly as it was.
- `allocation_charge_confined` — An accepted allocation is always paid for out of the requesting subject's own budget: the frame handed over was one admitted for that subject, and it is now recorded as owned by the new memory object.
- `allocation_other_usage_unchanged` — One subject's allocation never changes any other subject's usage count.
- `peer_available_not_budgetExhausted` — A subject that still has a free frame in its own budget can never be turned away with an out-of-memory answer, no matter how much its peers have consumed.
- `available_allocation_accepted` — Whenever the routine conditions hold — the subject is live, the destination slot is valid and empty, the object name is unused, and the subject still has a free budgeted frame — the allocation is guaranteed to succeed; peers running out of memory cannot make it fail.
- `release_preserves_commitment` — Releasing a frame never changes the boot-time budget partition itself: which frames belong to which subject's budget stays fixed.
- `terminate_preserves_commitment` — Terminating a subject also leaves the budget partition untouched — repeated cleanup can never mint new budget for anyone.
- `termination_frees_charged_frame` — When a subject is terminated, every budgeted frame it was using is returned to the free pool.
- `termination_preserves_other_frame` — Terminating one subject leaves every frame outside that subject's budget in exactly the state it was in before.
