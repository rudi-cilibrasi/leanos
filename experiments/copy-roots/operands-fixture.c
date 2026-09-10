/* Fixture-only authority: two linked data pages and a fixed byte pattern.
 * Production must obtain these locations from whole-request validation. */
#include "binding.h"
extern uint64_t leaves_a[CONSTRUCT_LEAVES], leaves_b[CONSTRUCT_LEAVES];
extern char value_a[], value_b[], transfer_buffer[];
extern struct copy_operand transfer_operands[16];

int prepare_fixture_operands(unsigned copy_out, uint64_t requested) {
    /* The oversize helper-negative case deliberately passes 17 against a
     * valid 16-byte plan. The helper must reject before dereferencing it. */
    size_t count = requested > 16 ? 16 : (size_t)requested;
    uint64_t frames[] = {(uintptr_t)value_a >> 12, (uintptr_t)value_b >> 12};
    /* Synthetic subject/object observation for the isolated fixture. This
     * is not a collector for production roots or live object ownership. */
    struct copy_binding_snapshot snapshot;
    snapshot.address_space = 7;
    snapshot.owner_present = 1;
    snapshot.owner = 0;
    snapshot.page_count = 2;
    for (size_t i = 0; i < 2; ++i) {
        snapshot.pages[i].page = i;
        snapshot.pages[i].object = 10 + i;
        snapshot.pages[i].read = 1;
        snapshot.pages[i].write = 1;
        snapshot.pages[i].memory_kind = 1;
        snapshot.pages[i].bound = 1;
        snapshot.pages[i].frame = frames[i];
        snapshot.pages[i].allocated = 1;
        snapshot.pages[i].allocation_object = 10 + i;
        for (size_t j = 0; j < 3; ++j) snapshot.pages[i].ancestors[j] = 7;
        snapshot.pages[i].leaf = (frames[i] << 12) | 7 | (UINT64_C(1) << 63);
    }
    struct copy_bound_locations bound;
    int binding = copy_binding_validate(&snapshot, 0, 7, 4088, count, copy_out, &bound);
    if (binding != COPY_BIND_OK) return binding;
    uint64_t slots[] = {leaves_b[0x700], leaves_b[0x701]};
    struct copy_plan plan;
    int result = copy_plan_prepare(bound.locations, bound.count, frames, 2, 0x700, slots,
                                   (uintptr_t)transfer_buffer + 8, copy_out, &plan);
    if (result != COPY_PLAN_OK) return result;
    for (size_t i = 0; i < 16; ++i) transfer_operands[i] = plan.operands[i];
    leaves_a[0x700] = plan.leaves[0];
    leaves_a[0x701] = plan.leaves[1];
    return 0;
}
