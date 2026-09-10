/* Fixture-only authority: two linked data pages and a fixed byte pattern.
 * Production must obtain these locations from whole-request validation. */
#include "operands.h"
extern uint64_t leaves_a[CONSTRUCT_LEAVES], leaves_b[CONSTRUCT_LEAVES];
extern char value_a[], value_b[], transfer_buffer[];
extern struct copy_operand transfer_operands[16];

int prepare_fixture_operands(unsigned copy_out, uint64_t requested) {
    /* The oversize helper-negative case deliberately passes 17 against a
     * valid 16-byte plan. The helper must reject before dereferencing it. */
    size_t count = requested > 16 ? 16 : (size_t)requested;
    uint64_t frames[] = {(uintptr_t)value_a >> 12, (uintptr_t)value_b >> 12};
    struct copy_location locations[16];
    for (size_t i = 0; i < count; ++i)
        locations[i] = (struct copy_location){frames[i < 8 ? 0 : 1],
                                             i < 8 ? 4088 + i : i - 8};
    uint64_t slots[] = {leaves_b[0x700], leaves_b[0x701]};
    struct copy_plan plan;
    int result = copy_plan_prepare(locations, count, frames, 2, 0x700, slots,
                                   (uintptr_t)transfer_buffer + 8, copy_out, &plan);
    if (result != COPY_PLAN_OK) return result;
    for (size_t i = 0; i < 16; ++i) transfer_operands[i] = plan.operands[i];
    leaves_a[0x700] = plan.leaves[0];
    leaves_a[0x701] = plan.leaves[1];
    return 0;
}
