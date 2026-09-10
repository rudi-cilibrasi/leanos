#ifndef LEANOS_EXPERIMENT_COPY_OPERANDS_H
#define LEANOS_EXPERIMENT_COPY_OPERANDS_H

#include "construct.h"

/* Projection of an ALREADY VALIDATED, immutable location list. This function
 * supplies no subject, permission, lifetime or mapping authority. The caller
 * must hold that authority and the kernel buffer stable until transfer ends.
 * Output is unpublished kernel-owned storage, not a live page table. */
struct copy_location { uint64_t frame, offset; };
struct copy_operand { uint64_t source, destination; };
struct copy_plan {
    uint64_t leaves[2];
    struct copy_operand operands[16];
    uint64_t count;
};
enum copy_plan_result {
    COPY_PLAN_OK, COPY_PLAN_BOUNDS, COPY_PLAN_STORAGE,
    COPY_PLAN_OCCUPIED, COPY_PLAN_UNPROTECTED, COPY_PLAN_FRAMES
};

/* This initial concrete projection uses two pages within the existing 16-MiB
 * fixture arena. Zero-length requests still check the reserved slots, as does
 * UserCopyAliases.prepare. Rejections leave all output bytes unchanged. */
static inline enum copy_plan_result copy_plan_prepare(
        const struct copy_location *locations, size_t count,
        const uint64_t *protected_frames, size_t protected_count,
        uint64_t base_page, const uint64_t closed_slots[2],
        uint64_t kernel_buffer, unsigned copy_out, struct copy_plan *output) {
    if (count > 16 || protected_count > CONSTRUCT_FRAMES || copy_out > 1 ||
        base_page >= CONSTRUCT_LEAVES - 1 ||
        kernel_buffer >= UINT64_C(0x1000000) ||
        count > UINT64_C(0x1000000) - kernel_buffer)
        return COPY_PLAN_BOUNDS;
    if (!output || !closed_slots || (count && !locations) ||
        (protected_count && !protected_frames)) return COPY_PLAN_STORAGE;
    if (!construct_disjoint(output, sizeof(*output), locations,
                            count * sizeof(*locations)) ||
        !construct_disjoint(output, sizeof(*output), protected_frames,
                            protected_count * sizeof(*protected_frames)) ||
        !construct_disjoint(output, sizeof(*output), closed_slots,
                            2 * sizeof(*closed_slots))) return COPY_PLAN_STORAGE;
    /* Require canonical absent words; do not silently discard software data. */
    if (closed_slots[0] || closed_slots[1]) return COPY_PLAN_OCCUPIED;
    /* A trusted kernel buffer must not itself name either temporary alias. */
    uint64_t alias_start = base_page << 12;
    if (count && kernel_buffer < alias_start + 8192 &&
        kernel_buffer + count > alias_start) return COPY_PLAN_STORAGE;
    for (size_t i = 0; i < protected_count; ++i)
        if (protected_frames[i] >= (UINT64_C(1) << 40))
            return COPY_PLAN_BOUNDS;
    /* Explicit volatile scratch accesses keep this freestanding projection
     * independent of compiler-generated memset/memcpy runtime calls. */
    volatile struct copy_plan plan;
    plan.leaves[0] = 0;
    plan.leaves[1] = 0;
    for (size_t i = 0; i < 16; ++i) {
        plan.operands[i].source = 0;
        plan.operands[i].destination = 0;
    }
    uint64_t frames[2] = {0};
    size_t frame_count = 0;
    for (size_t i = 0; i < count; ++i) {
        uint64_t frame = locations[i].frame, offset = locations[i].offset;
        if (frame >= (UINT64_C(1) << 40) || offset >= 4096)
            return COPY_PLAN_BOUNDS;
        size_t j = 0;
        while (j < protected_count && protected_frames[j] != frame) ++j;
        if (j == protected_count) return COPY_PLAN_UNPROTECTED;
        j = 0;
        while (j < frame_count && frames[j] != frame) ++j;
        if (j == frame_count) {
            if (frame_count == 2) return COPY_PLAN_FRAMES;
            frames[frame_count++] = frame;
            plan.leaves[j] = (frame << 12) | UINT64_C(0x8000000000000001) |
                             (copy_out ? 2 : 0);
        }
        uint64_t alias = ((base_page + j) << 12) + offset;
        plan.operands[i].source = copy_out ? kernel_buffer + i : alias;
        plan.operands[i].destination = copy_out ? alias : kernel_buffer + i;
    }
    output->leaves[0] = plan.leaves[0];
    output->leaves[1] = plan.leaves[1];
    for (size_t i = 0; i < 16; ++i) {
        output->operands[i].source = plan.operands[i].source;
        output->operands[i].destination = plan.operands[i].destination;
    }
    output->count = count;
    return COPY_PLAN_OK;
}
#endif
