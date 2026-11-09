/* Law window_scan_exact.  For any root and closed root at any physical addresses with any contents, an
   inventory of n <= 16 frames of any values, any window (base, limit and first alias slot, any values) and
   writable 0 or 1, frame_window_root_exact (window_root_exact) changes nothing and returns 1 exactly when
     - both roots' non-leaf entries name their own tables at their physical addresses: PML4[0] its PDPT,
       PDPT[0] its page directory, directory entries 0..7 its eight page tables, each with flags 7 and the
       Accessed bit ignored; directory entries 8..511 are 0 but for the Accessed bit, and every other PML4 and
       PDPT entry is 0;
     - no present closed leaf has a frame (bits 12..51) in the inventory;
     - with pages = (limit - base) / 4096, the root's leaf at every page p with slot <= p < slot + pages is
       ((base >> 12) + (p - slot)) << 12 | present | NX, plus writable when writable is 1, and at every other
       page it equals the closed leaf (all in uint64_t arithmetic);
   and 0 otherwise.  The Qotom production image runs this scan over the roots frame_window_build made
   (hardware/lab/qotom-production-network.c.inc), as frame_window_build itself does.  Not claimed:
   termination (partial correctness). */
#include "quickproof.h"
#include "roots_api.h"

static int member(uint64_t frame, const uint64_t *frames, size_t n) {
    for (size_t i = 0; i < n; ++i)
        if (frames[i] == frame)
            return 1;
    return 0;
}

static uint64_t table(uint64_t phys, uint64_t k) {
    return (phys + 4096u * k) | 7u;
}

static int tables_at(const struct qotom_root_pages *r, uint64_t phys) {
    if ((r->pml4[0] & ~QOTOM_ROOT_ACCESSED) != table(phys, 1) ||
        (r->pdpt[0] & ~QOTOM_ROOT_ACCESSED) != table(phys, 2))
        return 0;
    for (size_t i = 1; i < 512; ++i)
        if (r->pml4[i] != 0 || r->pdpt[i] != 0)
            return 0;
    for (size_t i = 0; i < 512; ++i)
        if ((r->pd[i] & ~QOTOM_ROOT_ACCESSED) != (i < 8 ? table(phys, 3 + i) : 0))
            return 0;
    return 1;
}

static void root_fill(struct qotom_root_pages *r) {
    for (size_t i = 0; i < 512; ++i) {
        r->pml4[i] = nondet_size();
        r->pdpt[i] = nondet_size();
        r->pd[i] = nondet_size();
    }
    for (size_t i = 0; i < QOTOM_ROOT_LEAVES; ++i)
        r->pt[i] = nondet_size();
}

static void root_copy(struct qotom_root_pages *d, const struct qotom_root_pages *s) {
    for (size_t i = 0; i < 512; ++i) {
        d->pml4[i] = s->pml4[i];
        d->pdpt[i] = s->pdpt[i];
        d->pd[i] = s->pd[i];
    }
    for (size_t i = 0; i < QOTOM_ROOT_LEAVES; ++i)
        d->pt[i] = s->pt[i];
}

static int root_same(const struct qotom_root_pages *a, const struct qotom_root_pages *b) {
    for (size_t i = 0; i < 512; ++i)
        if (a->pml4[i] != b->pml4[i] || a->pdpt[i] != b->pdpt[i] || a->pd[i] != b->pd[i])
            return 0;
    for (size_t i = 0; i < QOTOM_ROOT_LEAVES; ++i)
        if (a->pt[i] != b->pt[i])
            return 0;
    return 1;
}

int main(void) {
    struct qotom_root_pages root, root0, closed, closed0;
    uint64_t frames[16];
    struct frame_window w;

    uint64_t root_phys = nondet_size(), closed_phys = nondet_size();
    root_fill(&root);
    root_fill(&closed);
    size_t n = nondet_size();
    qp_assume(n <= 16);
    for (size_t i = 0; i < 16; ++i)
        frames[i] = nondet_size();
    w.fetch = &root;
    w.send = &root;
    w.fetch_phys = root_phys;
    w.send_phys = root_phys;
    w.base = nondet_size();
    w.limit = nondet_size();
    w.slot = nondet_size();
    int writable = nondet_u8() & 1;
    root_copy(&root0, &root);
    root_copy(&closed0, &closed);

    int expect = tables_at(&root, root_phys) && tables_at(&closed, closed_phys);
    uint64_t pages = (w.limit - w.base) / 4096u;
    for (size_t p = 0; p < QOTOM_ROOT_LEAVES; ++p) {
        uint64_t c = closed.pt[p];
        if ((c & QOTOM_ROOT_PRESENT) != 0 && member((c & QOTOM_ROOT_ADDRESS_MASK) >> 12, frames, n))
            expect = 0;
        uint64_t want = c;
        if (p >= w.slot && p < w.slot + pages)
            want = (((w.base >> 12) + (p - w.slot)) << 12) | QOTOM_ROOT_PRESENT | QOTOM_ROOT_NX |
                (writable ? QOTOM_ROOT_WRITABLE : 0);
        if (root.pt[p] != want)
            expect = 0;
    }

    int got = window_root_exact(&root, root_phys, &closed, closed_phys, frames, n, &w, writable);
    qp_assert(got == expect);
    qp_assert(root_same(&root, &root0));
    qp_assert(root_same(&closed, &closed0));
    return 0;
}
