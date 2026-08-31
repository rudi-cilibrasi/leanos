# The address-translation cache and revocation before return

The TLB is the processor's shortcut cache for address translations, and a stale entry left in it is the classic way a program keeps reaching memory the kernel has already taken away. These theorems guarantee that the modeled cache stays within its fixed size, that a cached entry alone can never authorize an access (every hit is re-checked against the current page table), and that every operation that revokes memory (unmap, permission reduction, release, destroy) removes the matching cache entries before it returns to the caller.

- `erase_key_length` — Bookkeeping: removing one page's entry never makes the cache larger.
- `erase_space_length` — Bookkeeping: removing all of one address space's entries never makes the cache larger.
- `insert_bounded` — Inserting an entry always leaves the cache at or below its fixed capacity, evicting as needed.
- `fill_rejected_unchanged` — Bookkeeping: this simply restates that a rejected cache fill reports exactly its rejection.
- `invalidate_page_absent` — After a page's entry is erased, looking that page up in the cache finds nothing, whatever the access context.
- `invalidate_space_absent` — After an address space's entries are erased, no lookup within that address space finds anything.
- `access_success_current` — Every successful access happens in a currently active address space and is confirmed by a fresh walk of the current page table returning the same frame; a cached entry by itself never authorizes anything.
- `successful_access_owned` — Every successful access traces back to a live mapping record whose memory object currently owns the very frame that was returned.
- `access_preserves_coherent` — A successful access leaves the cache within its fixed size bound.
- `fill_preserves_coherent` — A successful cache fill leaves the cache within its fixed size bound.
- `invalidate_page_preserves_coherent` — Invalidating one page keeps the cache within its size bound.
- `invalidate_space_preserves_coherent` — Invalidating one address space keeps the cache within its size bound.
- `switch_coherent` — Switching to another address space empties the cache entirely, so the size bound holds trivially.
- `release_accepted_coherent` — An accepted memory release leaves the cache within its size bound.
- `unmap_accepted_coherent` — An accepted unmap leaves the cache within its size bound.
- `protect_accepted_coherent` — An accepted permission reduction leaves the cache within its size bound.
- `protect_accepted_preserves_virtual_lifecycleWellFormed` — An accepted permission reduction preserves the entire authoritative bookkeeping invariant of the mapping and object-lifetime records carried inside the cache state.
- `destroy_accepted_coherent` — An accepted address-space destruction leaves the cache within its size bound.
- `unmap_rejected_unchanged` — A rejected unmap changes nothing at all: cache and records are exactly as before.
- `release_rejected_unchanged` — A rejected release changes nothing at all.
- `protect_rejected_unchanged` — A rejected permission change changes nothing at all.
- `protect_active` — Bookkeeping: a permission change never alters which address space is currently active.
- `protect_virtual_memory` — Bookkeeping: a permission change never alters the memory-object records.
- `protect_virtual_owner` — Bookkeeping: a permission change never alters who owns which address space.
- `destroy_rejected_unchanged` — A rejected destruction changes nothing at all.
- `unmap_revokes_before_return` — By the time an accepted unmap returns to its caller, the unmapped page's cached translation is already gone.
- `release_revokes_before_return` — By the time an accepted release returns, the cache is completely empty: no lookup of any page in any address space succeeds.
- `protect_revokes_before_return` — By the time an accepted permission reduction returns, the affected page's cached translation is already gone, so the old broader permission cannot be reused.
- `destroy_revokes_before_return` — By the time an accepted address-space destruction returns, every cached translation belonging to the destroyed space is already gone.
