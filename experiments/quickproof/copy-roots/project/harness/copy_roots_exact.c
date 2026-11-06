/* Law copy_roots_exact.  For every source root at any physical address with any contents; any closed and copy
   storage at any physical addresses with any prior contents; an inventory of up to 16 frames of any values,
   passed with any count; up to 2 aliases of any values, passed with any count; any prior result record; and
   each of the six pointer arguments either its object or NULL, qotom_build_copy_roots (roots_build):
     1. returns QOTOM_ROOT_BUILD_OK exactly when every argument is valid:
        - no pointer is NULL;
        - each physical address is nonzero, a multiple of 4096 and at most 2^52 - 45056, and the three
          45056-byte physical ranges are pairwise disjoint;
        - the source's non-leaf entries name its own tables at its physical address: PML4[0] its PDPT and
          PDPT[0] its page directory, directory entries 0..7 its eight page tables, each with flags 7 and the
          Accessed bit ignored; directory entries 8..511 are 0 but for the Accessed bit, and every other PML4
          and PDPT entry is 0;
        - the count is 1..16 and those frames are distinct and below 2^40;
        - the alias count is 1..2, and each alias has a page below 4096 whose source leaf is 0, a frame of
          the inventory and writable 0 or 1, with pages distinct and frames distinct across aliases;
     2. returns one of the five statuses, and never changes the source;
     3. when it returns anything but OK, changes neither root nor the result record;
     4. when it returns OK:
        - each root's non-leaf entries name its own tables at its physical address in the same way, with
          flags exactly 7, and all its other non-leaf entries are 0;
        - for every page p, with s the source leaf: the closed leaf is 0 when s is present and its frame
          (bits 12..51) is in the inventory, and s otherwise; the copy leaf at an alias's page is
          frame << 12 | present | NX, with writable added when the alias's writable is 1, and the closed
          leaf everywhere else;
        - the result holds the count, the number of removed leaves, the number of other present leaves and
          the alias count.
   That each physical address is where its storage is (qotom_root_phys on the identity-mapped kernel) is the
   caller's obligation, and so is the separation of the result record from the roots, which distinct C
   objects have.  Not claimed: termination (partial correctness). */
#include "quickproof.h"
#include "roots_api.h"

#define ROOT_BYTES UINT64_C(45056)

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

static int aliases_ok(const struct qotom_copy_alias *a, size_t m, const struct qotom_root_pages *source,
                      const uint64_t *frames, size_t n) {
    if (m < 1 || m > 2)
        return 0;
    for (size_t i = 0; i < m; ++i) {
        if (a[i].page >= QOTOM_ROOT_LEAVES || source->pt[a[i].page] != 0 ||
            !member(a[i].frame, frames, n) || a[i].writable > 1)
            return 0;
        for (size_t j = i + 1; j < m; ++j)
            if (a[i].page == a[j].page || a[i].frame == a[j].frame)
                return 0;
    }
    return 1;
}

int main(void) {
    struct qotom_root_pages source, source0, closed, closed0, copy, copy0;
    uint64_t frames[16];
    struct qotom_copy_alias aliases[2];
    struct qotom_root_build_result result;

    uint64_t source_phys = nondet_size(), closed_phys = nondet_size(), copy_phys = nondet_size();
    root_fill(&source);
    root_fill(&closed);
    root_fill(&copy);
    size_t n = nondet_size();
    for (size_t i = 0; i < 16; ++i)
        frames[i] = nondet_size();
    size_t m = nondet_size();
    for (size_t i = 0; i < 2; ++i) {
        aliases[i].page = nondet_size();
        aliases[i].frame = nondet_size();
        aliases[i].writable = nondet_size();
    }
    result.protected_count = nondet_size();
    result.removed_aliases = nondet_size();
    result.retained_present = nondet_size();
    result.alias_count = nondet_size();
    uint64_t r0 = result.protected_count, r1 = result.removed_aliases;
    uint64_t r2 = result.retained_present, r3 = result.alias_count;
    root_copy(&source0, &source);
    root_copy(&closed0, &closed);
    root_copy(&copy0, &copy);

    const struct qotom_root_pages *source_arg = nondet_u8() == 0 ? NULL : &source;
    struct qotom_root_pages *closed_arg = nondet_u8() == 0 ? NULL : &closed;
    struct qotom_root_pages *copy_arg = nondet_u8() == 0 ? NULL : &copy;
    const uint64_t *frames_arg = nondet_u8() == 0 ? NULL : frames;
    const struct qotom_copy_alias *aliases_arg = nondet_u8() == 0 ? NULL : aliases;
    struct qotom_root_build_result *result_arg = nondet_u8() == 0 ? NULL : &result;

    int valid = source_arg != NULL && closed_arg != NULL && copy_arg != NULL && frames_arg != NULL &&
        aliases_arg != NULL && result_arg != NULL &&
        phys_ok(source_phys) && phys_ok(closed_phys) && phys_ok(copy_phys) &&
        apart(source_phys, closed_phys) && apart(source_phys, copy_phys) && apart(closed_phys, copy_phys) &&
        tables_at(&source, source_phys, QOTOM_ROOT_ACCESSED) && inventory_ok(frames, n) &&
        aliases_ok(aliases, m, &source, frames, n);

    enum qotom_root_build_status status = roots_build(source_arg, source_phys, closed_arg, closed_phys,
        copy_arg, copy_phys, frames_arg, n, aliases_arg, m, result_arg);

    qp_assert((status == QOTOM_ROOT_BUILD_OK) == valid);
    qp_assert(status >= QOTOM_ROOT_BUILD_OK && status <= QOTOM_ROOT_BUILD_ALIAS);
    qp_assert(root_same(&source, &source0));
    if (status != QOTOM_ROOT_BUILD_OK) {
        qp_assert(root_same(&closed, &closed0));
        qp_assert(root_same(&copy, &copy0));
        qp_assert(result.protected_count == r0 && result.removed_aliases == r1 &&
                  result.retained_present == r2 && result.alias_count == r3);
        return 0;
    }
    qp_assert(tables_at(&closed, closed_phys, 0));
    qp_assert(tables_at(&copy, copy_phys, 0));
    uint64_t removed = 0, retained = 0;
    for (size_t p = 0; p < QOTOM_ROOT_LEAVES; ++p) {
        uint64_t s = source.pt[p];
        int gone = (s & QOTOM_ROOT_PRESENT) != 0 && member((s & QOTOM_ROOT_ADDRESS_MASK) >> 12, frames, n);
        uint64_t want = gone ? 0 : s;
        qp_assert(closed.pt[p] == want);
        uint64_t copy_want = want;
        for (size_t k = 0; k < m; ++k)
            if (aliases[k].page == p)
                copy_want = (aliases[k].frame << 12) | QOTOM_ROOT_PRESENT | QOTOM_ROOT_NX |
                    (aliases[k].writable == 1 ? QOTOM_ROOT_WRITABLE : 0);
        qp_assert(copy.pt[p] == copy_want);
        if (gone)
            ++removed;
        else if ((s & QOTOM_ROOT_PRESENT) != 0)
            ++retained;
    }
    qp_assert(result.protected_count == n && result.removed_aliases == removed &&
              result.retained_present == retained && result.alias_count == m);
    return 0;
}
