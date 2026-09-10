#ifndef LEANOS_EXPERIMENT_COPY_BINDING_H
#define LEANOS_EXPERIMENT_COPY_BINDING_H
#include "operands.h"

/* Immutable observations of at most two pages in one address space. A trusted
 * collector must reconcile shared object/frame records, capture the actual
 * subject walk, and retain ownership and mappings through transfer. These
 * fields are observations, not independently forgeable authorization tokens.
 * No hardware access, snapshot collection or lifetime locking occurs here. */
struct copy_binding_page {
    uint64_t page, object, read, write, memory_kind;
    uint64_t bound, frame, allocated, allocation_object;
    uint64_t ancestors[3], leaf;
};
struct copy_binding_snapshot {
    uint64_t address_space, owner_present, owner, page_count;
    struct copy_binding_page pages[2];
};
struct copy_bound_locations {
    struct copy_location locations[16];
    uint64_t count;
};
enum copy_binding_result {
    COPY_BIND_OK, COPY_BIND_TOO_LONG, COPY_BIND_OVERFLOW, COPY_BIND_NONCANONICAL,
    COPY_BIND_ADDRESS_SPACE, COPY_BIND_OWNER, COPY_BIND_UNMAPPED,
    COPY_BIND_PERMISSION, COPY_BIND_KIND, COPY_BIND_RETIRED, COPY_BIND_ALLOCATOR,
    COPY_BIND_ALIAS, COPY_BIND_HARDWARE, COPY_BIND_SNAPSHOT, COPY_BIND_STORAGE
};

/* Restricted 4-KiB word encoding: P/RW/US, A/D and address bits; leaf NX.
 * Unsupported flags/large pages are rejected. This 52-bit encoding limit is
 * not a processor MAXPHYADDR admission check or an ancestor-link proof. */
static inline int copy_binding_walk(const struct copy_binding_page *page,
                                     unsigned write) {
    uint64_t common = CONSTRUCT_ADDRESS_MASK | UINT64_C(0x67);
    for (size_t j = 0; j < 3; ++j) {
        uint64_t word = page->ancestors[j];
        if ((word & ~common) || (word & 5) != 5 || (write && !(word & 2)))
            return 0;
    }
    uint64_t word = page->leaf;
    return !(word & ~(common | (UINT64_C(1) << 63))) &&
        (word & 5) == 5 && (!write || (word & 2)) &&
        page->frame < (UINT64_C(1) << 40) &&
        ((word & CONSTRUCT_ADDRESS_MASK) >> 12) == page->frame;
}

static inline enum copy_binding_result copy_binding_validate(
        const struct copy_binding_snapshot *snapshot,
        uint64_t caller, uint64_t address_space, uint64_t start, uint64_t length,
        unsigned write, struct copy_bound_locations *output) {
    if (length > 16) return COPY_BIND_TOO_LONG;
    if (!output) return COPY_BIND_STORAGE;
    if (write > 1) return COPY_BIND_SNAPSHOT;
    if (length) {
        /* Model overflow is end > 2^64, not end == 2^64. */
        if (length - 1 > UINT64_MAX - start) return COPY_BIND_OVERFLOW;
        uint64_t limit = UINT64_C(1) << 47;
        if (start >= limit || length > limit - start) return COPY_BIND_NONCANONICAL;
        if (!snapshot || !construct_disjoint(output, sizeof(*output),
                                               snapshot, sizeof(*snapshot)))
            return COPY_BIND_STORAGE;
        if (snapshot->page_count > 2) return COPY_BIND_SNAPSHOT;
        for (size_t i = 0; i < snapshot->page_count; ++i)
            for (size_t j = 0; j < i; ++j)
                {
                    const struct copy_binding_page *a = &snapshot->pages[i];
                    const struct copy_binding_page *b = &snapshot->pages[j];
                    if (a->page == b->page) return COPY_BIND_SNAPSHOT;
                    /* Object bindings and allocator ownership are global
                     * functions, not independent per-page assertions. */
                    if (a->object == b->object &&
                        (a->memory_kind != b->memory_kind || a->bound != b->bound ||
                         (a->bound && a->frame != b->frame)))
                        return COPY_BIND_SNAPSHOT;
                    if (a->bound && b->bound && a->frame == b->frame &&
                        (a->allocated != b->allocated ||
                         (a->allocated && a->allocation_object != b->allocation_object)))
                        return COPY_BIND_SNAPSHOT;
                }
        if (snapshot->address_space != address_space || !snapshot->owner_present)
            return COPY_BIND_ADDRESS_SPACE;
        if (snapshot->owner != caller) return COPY_BIND_OWNER;
    }
    /* Volatile scratch prevents freestanding compiler runtime memory calls. */
    volatile struct copy_location locations[16];
    size_t indices[16];
    for (size_t i = 0; i < length; ++i) {
        uint64_t page = (start + i) >> 12;
        size_t j = 0;
        while (j < snapshot->page_count && snapshot->pages[j].page != page) ++j;
        if (j == snapshot->page_count) return COPY_BIND_UNMAPPED;
        const struct copy_binding_page *mapping = &snapshot->pages[j];
        if (!(write ? mapping->write : mapping->read)) return COPY_BIND_PERMISSION;
        if (!mapping->memory_kind) return COPY_BIND_KIND;
        if (!mapping->bound) return COPY_BIND_RETIRED;
        if (!mapping->allocated || mapping->allocation_object != mapping->object)
            return COPY_BIND_ALLOCATOR;
        for (size_t k = 0; k < i; ++k)
            if (locations[k].frame == mapping->frame && ((start + k) >> 12) != page)
                return COPY_BIND_ALIAS;
        locations[i].frame = mapping->frame;
        locations[i].offset = (start + i) & 4095;
        indices[i] = j;
    }
    /* Match the model: all policy checks precede every hardware comparison. */
    for (size_t i = 0; i < length; ++i)
        if (!copy_binding_walk(&snapshot->pages[indices[i]], write))
            return COPY_BIND_HARDWARE;
    for (size_t i = 0; i < 16; ++i) {
        output->locations[i].frame = i < length ? locations[i].frame : 0;
        output->locations[i].offset = i < length ? locations[i].offset : 0;
    }
    output->count = length;
    return COPY_BIND_OK;
}
#endif
