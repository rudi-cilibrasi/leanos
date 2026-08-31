# One public step that pairs every revocation with its exact flush

This file defines the single public step through which the kernel changes address translations: unmapping a page, reducing its permissions, releasing a memory object, destroying an address space, or switching to another one. Each accepted step returns both the new state and the exact cache flush the machine must perform, and each target is derived from checked kernel records rather than attacker-supplied words. The theorems guarantee that rejected requests do nothing and demand nothing, that the demanded flush is determined entirely by the checked request, and that the state each accepted step returns already has every affected translation gone.

- `rejected_inert` — A rejected step preserves the complete state and demands no cache flush at all; only the always-accepted address-space switch can never be rejected.
- `unmap_accepted_effect` — An accepted unmap demands the flush of exactly the requested address space and page, whatever the prior state was, so an attacker cannot swap in a different target.
- `protect_accepted_effect` — An accepted permission reduction demands the flush of exactly the requested address space and page.
- `release_accepted_effect` — An accepted memory release demands the reviewed complete flush of the whole cache.
- `virtual_destroy_accepted_lookup` — An accepted address-space destruction can only arise from a capability actually found in the caller's records, so the retired identity is the one the checked handle named.
- `tlb_destroy_accepted_lookup` — A stepping-stone fact used by later theorems: the same found-capability guarantee holds for the cache-level destruction operation.
- `destroy_accepted_effect` — An accepted destruction demands the flush of exactly the address space named by the checked capability the kernel itself looked up, never one taken from an attacker's word.
- `switch_effect` — An address-space switch is always accepted and always demands the reviewed complete flush.
- `unmap_wrong_owner_inert` — A program that does not own an address space cannot unmap anything in it: the step is refused, the state is unchanged, and no flush of that page is demanded.
- `protect_wrong_owner_inert` — Likewise for permission changes: a non-owner's request is refused and changes nothing, so it can never flush another program's page.
- `applyEffect_page_absent` — Performing the single-page flush on any cache leaves the named page unfindable there.
- `applyEffect_space_absent` — Performing the address-space flush on any cache leaves every page of that space unfindable.
- `applyEffect_flush_absent` — Performing the complete flush leaves nothing findable in the cache at all.
- `accepted_unmap_target_absent` — The state an accepted unmap returns already has the affected page absent from the cache: the revocation is done before the step hands back control.
- `accepted_protect_target_absent` — The state an accepted permission reduction returns already has the affected page absent from the cache.
- `accepted_release_all_absent` — The state an accepted release returns has an entirely empty cache, so no stale lookup for the retired object can succeed.
- `accepted_release_flushed` — Stated directly on the cache itself: after an accepted release, the list of cached translations is empty, so no retired frame is reachable through a stale hit before reuse.
- `accepted_destroy_space_absent` — The state an accepted destruction returns has every translation of the retired address space absent from the cache.
- `step_preserves_coherent` — Every step, accepted or rejected, keeps the cache within its fixed size bound.
