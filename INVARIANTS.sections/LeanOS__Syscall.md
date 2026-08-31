# The kernel's front door for program requests

When a program asks the kernel to do something — map memory into its view, unmap it, or check an access — it may only pass plain numbers; who is asking and which memory space is active is established by the kernel itself, never by those numbers. These theorems guarantee that no crafted request can impersonate another program, mint new permissions, or corrupt the kernel's records, and that every refused request leaves everything exactly as it was.

- `accepted_map_resolves_exact` — A memory-mapping request is accepted only after the number the program supplied was verified to name a real, current memory permission in that caller's own permission book.
- `decode_deterministic` — Every incoming request has exactly one interpretation: the same numbers always mean the same operation.
- `attacker_words_cannot_change_caller` — Nothing in a request's numbers can change who the kernel treats as the caller; identity comes only from the kernel's own trusted record.
- `map_capabilities_unchanged` — Mapping memory never changes anyone's permissions.
- `unmap_capabilities_unchanged` — Unmapping memory never changes anyone's permissions.
- `dispatchDecoded_capabilities_unchanged` — No decoded request of any kind changes anyone's permissions.
- `dispatch_capabilities_unchanged` — The complete request path, from raw numbers to final answer, changes nobody's permissions.
- `dispatch_authority_provenance` — Any authority a program holds after a request, it already held before — requests never grant power.
- `dispatchDecoded_preserves_lifecycleWellFormed` — Every decoded request keeps the kernel's composite records consistent.
- `dispatch_preserves_lifecycleWellFormed` — Every request, accepted or refused, keeps the kernel's composite records consistent.
- `dispatch_rejected_unchanged` — Every refusal — including "I do not understand this request" — leaves the state completely untouched.
- `nonowner_dispatchDecoded_unchanged` — A program that does not own the active memory space cannot alter it: any such request leaves the state untouched.
- `syscallDemo_authorized_agrees` — Bookkeeping: the tiny accept-or-reject demo exported for the boot test gives the same answer as the full model on the reviewed accepted request.
- `syscallDemo_rejected_agrees` — Bookkeeping: the demo also gives the same answer as the full model on the reviewed unknown-request refusal.
