#ifndef LEANOS_EXPERIMENT_COPY_ROOT_CONSTRUCT_H
#define LEANOS_EXPERIMENT_COPY_ROOT_CONSTRUCT_H

#include <stddef.h>
#include <stdint.h>

/* Unpublished 4-KiB leaf-array construction only. Callers provide valid,
 * immutable input storage and exclusive writable output storage. Neither the
 * inventory's completeness nor ancestors, CR3, TLBs or live closure is proved
 * here. The bounded virtual domain matches the existing 16-MiB fixture.
 * No caller may publish the output unless construction returns CONSTRUCT_OK.
 */
#define CONSTRUCT_LEAVES 4096u
#define CONSTRUCT_FRAMES 16u
#define CONSTRUCT_ADDRESS_MASK UINT64_C(0x000ffffffffff000)

struct construct_required {
    uint64_t page;
    uint64_t leaf;
};

enum construct_result {
    CONSTRUCT_OK,
    CONSTRUCT_BOUNDS,
    CONSTRUCT_STORAGE,
    CONSTRUCT_REQUIRED,
    CONSTRUCT_PROTECTED
};

/* Subtraction avoids wrapping an end address. Empty ranges cannot overlap. */
static inline int construct_disjoint(const void *a, size_t an,
                                     const void *b, size_t bn) {
    uintptr_t x = (uintptr_t)a, y = (uintptr_t)b;
    return an == 0 || bn == 0 || (x <= y ? y - x >= an : x - y >= bn);
}

static inline int construct_protected(uint64_t leaf, const uint64_t *frames,
                                      size_t count) {
    uint64_t frame = (leaf & CONSTRUCT_ADDRESS_MASK) >> 12;
    for (size_t i = 0; i < count; ++i)
        if (frame == frames[i]) return 1;
    return 0;
}

static inline enum construct_result construct_closed_leaves(
        const uint64_t source[CONSTRUCT_LEAVES],
        uint64_t target[CONSTRUCT_LEAVES],
        const uint64_t *frames, size_t frame_count,
        const struct construct_required *required, size_t required_count) {
    if (frame_count > CONSTRUCT_FRAMES || required_count > CONSTRUCT_LEAVES)
        return CONSTRUCT_BOUNDS;
    if (!source || !target || (frame_count && !frames) ||
        (required_count && !required)) return CONSTRUCT_STORAGE;
    if (!construct_disjoint(target, CONSTRUCT_LEAVES * sizeof(*target),
                            source, CONSTRUCT_LEAVES * sizeof(*source)) ||
        !construct_disjoint(target, CONSTRUCT_LEAVES * sizeof(*target),
                            frames, frame_count * sizeof(*frames)) ||
        !construct_disjoint(target, CONSTRUCT_LEAVES * sizeof(*target),
                            required, required_count * sizeof(*required)))
        return CONSTRUCT_STORAGE;
    for (size_t i = 0; i < frame_count; ++i)
        if (frames[i] >= (UINT64_C(1) << 40)) return CONSTRUCT_BOUNDS;
    for (size_t i = 0; i < required_count; ++i) {
        uint64_t page = required[i].page, leaf = required[i].leaf;
        if (page >= CONSTRUCT_LEAVES) return CONSTRUCT_BOUNDS;
        if (!(leaf & 1) || source[page] != leaf) return CONSTRUCT_REQUIRED;
        if (construct_protected(leaf, frames, frame_count))
            return CONSTRUCT_PROTECTED;
    }
    /* All possible rejection checks precede the first output write. Removal
     * uses the physical address, independently of the U/S permission bit.
     * Preserved entries retain every bit, including existing absent guards.
     */
    for (size_t page = 0; page < CONSTRUCT_LEAVES; ++page)
        target[page] = construct_protected(source[page], frames, frame_count)
            ? 0 : source[page];
    return CONSTRUCT_OK;
}
#endif
