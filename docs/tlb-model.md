# Single-core TLB model

`LeanOS.TLB` models a finite 16-entry translation cache keyed by address-space
identity and virtual page. Each entry records its access context and classified
physical frame. Every cache hit is revalidated against the current encoded
page-table walk before use. Thus effective U/S, R/W, NX, CR0.WP, SMEP, SMAP,
AC, live object binding, and allocator ownership are checked at access time.

The model is sequential and uses eager invalidation. `mutatePage` and `unmap`
publish the page-table change and remove the page's translations atomically.
Destruction removes all entries for that identity. Release conservatively
flushes the complete cache while publishing lifecycle-produced tables. CR3
switch also flushes everything; there are no PCIDs or global mappings. This is
costlier than selective release invalidation but makes publication order clear.

Lean proves successful accesses agree with a current privileged page-table
classification and current allocator ownership. It also proves affected keys
are absent when accepted unmap returns, accepted release leaves no cache hit,
cache capacity is invariant under fill and invalidation, and every rejected
unmap, release, or destruction leaves the complete cache/model state unchanged.
Executable examples exercise repeated page invalidation, space invalidation,
switch-away/back flushing, and the negative constructions. The negative
witnesses show that clearing a PTE without invalidation retains stale cache data
and that omitting address-space identity aliases equal virtual pages; the normal
access path rejects stale data because of current-walk revalidation.

We assume x86 effective-permission semantics, that serializing CR3 reload
without PCID invalidates modeled non-global translations, and that INVLPG has
completed for the named linear page before return on this single core. We also
assume page-table stores and invalidation are ordered as the atomic transition.
The ISA guarantees, compiler, assembly, QEMU, and hardware are trusted, not
proved. SMP shootdowns, PCID, global/huge pages, nested paging, speculation,
replacement performance, and concurrent mutation are outside scope.
