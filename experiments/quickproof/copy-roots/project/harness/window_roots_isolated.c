/* Law window_roots_isolated.  For every source root at any physical address with any contents; any closed,
   fetch and send storage at any physical addresses; an inventory of up to 16 frames of any values, passed with
   any count; any window (base, limit and first alias slot, any values); and any prior first-build record and
   built flag, frame_window_build (window_build):
     1. returns FRAME_WINDOW_OK exactly when
        - each of the four physical addresses is nonzero, a multiple of 4096 and at most 2^52 - 45056, and
          the four 45056-byte physical ranges are pairwise disjoint;
        - the window has the reviewed geometry (LeanOS.FrameCopyWindow.geometryOk): base is a multiple of
          4096, base < limit <= 16 MiB, limit - base is one or two pages, and the alias slots
          slot .. slot + pages - 1 lie in 1..4095;
        - the source's non-leaf entries name its own tables at its physical address (as in copy_roots_exact);
        - the count is 1..16 and those frames are distinct and below 2^40;
        - every frame of the window is in the inventory and the source leaf at every alias slot is 0;
        - when built is nonzero, first already holds this build's inventory size, removed and other present
          leaf counts;
     2. when it returns OK:
        - the closed, fetch and send roots each name their own tables at their physical addresses: PML4[0]
          its PDPT, PDPT[0] its page directory and directory entries 0..7 its eight page tables, each with
          flags 7, and every other non-leaf entry 0;
        - for every page p, with s the source leaf: the closed leaf is 0 when s is present and its frame
          (bits 12..51) is in the inventory, and s otherwise; at an alias slot p, the fetch leaf is
          ((base >> 12) + (p - slot)) << 12 | present | writable | NX and the send leaf the same without
          writable; at every other page both equal the closed leaf;
        - the source's leaves are unchanged, built is nonzero, and first's inventory size, removed and other
          present leaf counts are this build's.
   These leaves are the word form of the hypotheses of LeanOS.FrameCopyWindow's isolation theorems:
   LeanOS.FrameWindowWords proves that the closed leaves decode to a Closed root for the inventory and the
   fetch and send leaves to windowRoot of it, writable and read-only.  That each physical address is where
   its storage is, and that the inventory is complete, are the caller's obligations.  Not claimed:
   termination (partial correctness). */
#include "quickproof.h"
#include "roots_api.h"

#define ROOT_BYTES UINT64_C(45056)

static int member(uint64_t frame, const uint64_t *frames, size_t n) {
    for (size_t i = 0; i < n; ++i)
        if (frames[i] == frame)
            return 1;
    return 0;
}

static int phys_ok(uint64_t a) {
    return a != 0 && a % 4096u == 0 && a <= (UINT64_C(1) << 52) - ROOT_BYTES;
}

/* Of two addresses phys_ok accepts, so neither sum wraps. */
static int apart(uint64_t a, uint64_t b) {
    return a + ROOT_BYTES <= b || b + ROOT_BYTES <= a;
}

static uint64_t table(uint64_t phys, uint64_t k) {
    return (phys + 4096u * k) | 7u;
}

/* r's non-leaf entries name its own tables at phys, with the bits of `ignore` ignored where the source
   check ignores Accessed. */
static int tables_at(const struct qotom_root_pages *r, uint64_t phys, uint64_t ignore) {
    if ((r->pml4[0] & ~ignore) != table(phys, 1) || (r->pdpt[0] & ~ignore) != table(phys, 2))
        return 0;
    for (size_t i = 1; i < 512; ++i)
        if (r->pml4[i] != 0 || r->pdpt[i] != 0)
            return 0;
    for (size_t i = 0; i < 512; ++i)
        if ((r->pd[i] & ~ignore) != (i < 8 ? table(phys, 3 + i) : 0))
            return 0;
    return 1;
}

static int inventory_ok(const uint64_t *frames, size_t n) {
    if (n < 1 || n > 16)
        return 0;
    for (size_t i = 0; i < n; ++i) {
        if (frames[i] >= (UINT64_C(1) << 40))
            return 0;
        for (size_t j = i + 1; j < n; ++j)
            if (frames[i] == frames[j])
                return 0;
    }
    return 1;
}

/* LeanOS.FrameCopyWindow.geometryOk. */
static int geometry_ok(uint64_t base, uint64_t limit, uint64_t slot) {
    return base % 4096u == 0 && base < limit && limit <= UINT64_C(0x1000000) &&
        (limit - base == 4096u || limit - base == 8192u) &&
        slot != 0 && slot <= 4096u && slot + (limit - base) / 4096u <= 4096u;
}

int main(void) {
    struct qotom_root_pages source, closed, fetch, send;
    uint64_t frames[16];
    uint64_t kept[QOTOM_ROOT_LEAVES];
    struct frame_window w;
    struct qotom_root_build_result first;
    int built;

    uint64_t source_phys = nondet_size(), closed_phys = nondet_size();
    w.fetch = &fetch;
    w.send = &send;
    w.fetch_phys = nondet_size();
    w.send_phys = nondet_size();
    for (size_t i = 0; i < 512; ++i) {
        source.pml4[i] = nondet_size();
        source.pdpt[i] = nondet_size();
        source.pd[i] = nondet_size();
    }
    for (size_t i = 0; i < QOTOM_ROOT_LEAVES; ++i) {
        source.pt[i] = nondet_size();
        kept[i] = source.pt[i];
    }
    size_t n = nondet_size();
    for (size_t i = 0; i < 16; ++i)
        frames[i] = nondet_size();
    w.base = nondet_size();
    w.limit = nondet_size();
    w.slot = nondet_size();
    first.protected_count = nondet_size();
    first.removed_aliases = nondet_size();
    first.retained_present = nondet_size();
    first.alias_count = nondet_size();
    built = (int)nondet_u32();

    int valid = phys_ok(source_phys) && phys_ok(closed_phys) && phys_ok(w.fetch_phys) &&
        phys_ok(w.send_phys) && apart(source_phys, closed_phys) && apart(source_phys, w.fetch_phys) &&
        apart(source_phys, w.send_phys) && apart(closed_phys, w.fetch_phys) &&
        apart(closed_phys, w.send_phys) && apart(w.fetch_phys, w.send_phys) &&
        geometry_ok(w.base, w.limit, w.slot) && tables_at(&source, source_phys, QOTOM_ROOT_ACCESSED) &&
        inventory_ok(frames, n);
    uint64_t pages = (w.limit - w.base) / 4096u;
    if (valid) {
        for (uint64_t i = 0; i < pages; ++i)
            if (!member((w.base >> 12) + i, frames, n) || source.pt[w.slot + i] != 0)
                valid = 0;
    }
    uint64_t removed = 0, retained = 0;
    if (valid) {
        for (size_t p = 0; p < QOTOM_ROOT_LEAVES; ++p) {
            uint64_t s = source.pt[p];
            if ((s & QOTOM_ROOT_PRESENT) != 0 && member((s & QOTOM_ROOT_ADDRESS_MASK) >> 12, frames, n))
                ++removed;
            else if ((s & QOTOM_ROOT_PRESENT) != 0)
                ++retained;
        }
        if (built != 0 && (first.protected_count != n || first.removed_aliases != removed ||
                           first.retained_present != retained))
            valid = 0;
    }

    enum frame_window_status status = window_build(&source, source_phys, &closed, closed_phys, frames, n,
        &w, &first, &built);
    qp_assert((status == FRAME_WINDOW_OK) == valid);
    if (status != FRAME_WINDOW_OK)
        return 0;

    qp_assert(tables_at(&closed, closed_phys, 0));
    qp_assert(tables_at(&fetch, w.fetch_phys, 0));
    qp_assert(tables_at(&send, w.send_phys, 0));
    for (size_t p = 0; p < QOTOM_ROOT_LEAVES; ++p) {
        uint64_t s = source.pt[p];
        qp_assert(s == kept[p]);
        int gone = (s & QOTOM_ROOT_PRESENT) != 0 && member((s & QOTOM_ROOT_ADDRESS_MASK) >> 12, frames, n);
        uint64_t c = gone ? 0 : s;
        qp_assert(closed.pt[p] == c);
        if (p >= w.slot && p < w.slot + pages) {
            uint64_t alias = (((w.base >> 12) + (p - w.slot)) << 12) | QOTOM_ROOT_PRESENT | QOTOM_ROOT_NX;
            qp_assert(fetch.pt[p] == (alias | QOTOM_ROOT_WRITABLE));
            qp_assert(send.pt[p] == alias);
        } else {
            qp_assert(fetch.pt[p] == c);
            qp_assert(send.pt[p] == c);
        }
    }
    qp_assert(built != 0);
    qp_assert(first.protected_count == n && first.removed_aliases == removed &&
              first.retained_present == retained);
    return 0;
}
