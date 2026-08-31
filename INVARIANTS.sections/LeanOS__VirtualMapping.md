# Address spaces, page mappings, and capability-bounded translation

This file models how programs get named views of memory: each address space belongs to exactly one program, its pages map to memory objects with read/write permissions, and every bit of authority comes from a held capability. The theorems guarantee that translation succeeds only for the owner, backed by live authority; that mapping a page can never grant more than the capability allowed; and that creating, destroying, and revoking address spaces and objects is exact and complete without disturbing anyone else's memory.

- `setMapping_restrict_permissions_preserves_lifecycleWellFormed` — Replacing one live mapping's permissions with a smaller-but-nonempty set preserves the entire bookkeeping invariant: the object, owner, frame binding, and every capability record stay exactly as they were.
- `map_rejected_unchanged` — A rejected mapping request changes nothing at all.
- `unmap_rejected_unchanged` — A rejected unmap request changes nothing at all.
- `release_rejected_unchanged` — A rejected release request changes nothing at all.
- `translated_current_frame` — A successful translation returns the physical frame currently bound to a live mapping's object, which the allocator confirms that object still owns.
- `translated_selected_mapping` — A successful translation goes only through the requested address space's own page entry, only for that space's owner, and only when the mapping's permissions allow the requested kind of access.
- `translated_capability_authority` — In a well-formed state, every successful translation is still backed by a capability the address-space owner currently holds for exactly that object and kind of access.
- `other_subject_cannot_translate` — A program can never translate addresses in an address space owned by a different program; the request always fails.
- `map_permission_authority` — An accepted mapping grants read or write only if the acting program's capability already carried that same right; mapping never amplifies authority.
- `map_preserves_wellFormed` — Installing a mapping keeps the state well formed: every mapping still names a live, owned frame backed by real authority.
- `map_memory` — Bookkeeping: installing a mapping never alters the underlying memory-object records.
- `map_owner` — Bookkeeping: installing a mapping never alters who owns which address space.
- `unmap_preserves_wellFormed` — Removing a mapping keeps the state well formed.
- `unmap_memory` — Bookkeeping: removing a mapping never alters the underlying memory-object records.
- `unmap_owner` — Bookkeeping: removing a mapping never alters who owns which address space.
- `map_preserves_lifecycleWellFormed` — Installing a mapping also preserves the stronger lifetime invariant tying capabilities, issued identifiers, and address-space owners together.
- `unmap_preserves_lifecycleWellFormed` — Removing a mapping also preserves that stronger lifetime invariant.
- `memory_release_preserves_subjects` — A stepping-stone fact used by later theorems: releasing a memory object never changes which programs exist.
- `create_rejected_unchanged` — A rejected address-space creation changes nothing at all.
- `destroy_rejected_unchanged` — A rejected address-space destruction changes nothing at all.
- `cleared_address_space` — Spelling out the definition: after its mappings are cleared, an address space has no mapping at any page.
- `created_fresh_empty_root` — An accepted creation uses an identifier never issued before, records it in the permanent issuance history, makes the caller the owner, installs exactly one root capability for the new space, and starts with no mappings whatsoever.
- `destroyed_complete_cleanup` — An accepted destruction retires the address space entirely: its owner record is gone, the object is gone, all of its mappings are gone, and no capability held by anyone still names it.
- `destroy_preserves_other_address_space` — Destroying one address space leaves every other address space's owner and every one of its mappings exactly as they were.
- `clear_address_space_preserves_other` — Clearing one address space's mappings leaves every other address space's mappings untouched.
- `invalidated_object_mapping` — Invalidating a memory object removes every mapping, in any address space, that names that object.
- `release_preserves_unrelated_mapping` — An accepted release keeps intact every mapping that names a different object; only the retired object's mappings disappear.
