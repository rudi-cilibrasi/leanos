#include "operands.h"
#include <assert.h>
#include <stdio.h>
#include <string.h>

int main(void) {
    const uint64_t frames[] = {17, 19, 23};
    uint64_t slots[2] = {0};
    struct copy_location locations[16];
    for (size_t i = 0; i < 16; ++i)
        locations[i] = (struct copy_location){i < 8 ? 19 : 17,
                                             i < 8 ? 4088 + i : i - 8};
    struct copy_plan plan;
    for (unsigned out = 0; out < 2; ++out) {
        assert(copy_plan_prepare(locations, 16, frames, 3, 0x700, slots,
                                 0x200000, out, &plan) == COPY_PLAN_OK);
        assert(plan.count == 16);
        assert(plan.leaves[0] == ((UINT64_C(19) << 12) |
               UINT64_C(0x8000000000000001) | (out ? 2 : 0)));
        assert(plan.leaves[1] == ((UINT64_C(17) << 12) |
               UINT64_C(0x8000000000000001) | (out ? 2 : 0)));
        for (size_t i = 0; i < 16; ++i) {
            assert(plan.operands[i].source == (out ? 0x200000 + i : 0x700ff8 + i));
            assert(plan.operands[i].destination == (out ? 0x700ff8 + i : 0x200000 + i));
        }
    }
    struct copy_plan poison;
    memset(&poison, 0xa5, sizeof(poison));
#define REJECT(expected, ...) do { \
    plan = poison; \
    assert(copy_plan_prepare(__VA_ARGS__, &plan) == (expected)); \
    assert(memcmp(&plan, &poison, sizeof(plan)) == 0); \
} while (0)
    REJECT(COPY_PLAN_BOUNDS, locations, 17, frames, 3, 0x700, slots, 0x200000, 0);
    REJECT(COPY_PLAN_BOUNDS, locations, 16, frames, 3, 4095, slots, 0x200000, 0);
    REJECT(COPY_PLAN_BOUNDS, locations, 16, frames, 3, 0x700, slots, UINT64_MAX, 0);
    REJECT(COPY_PLAN_BOUNDS, locations, 16, frames, 3, 0x700, slots, 0xfffff8, 0);
    REJECT(COPY_PLAN_BOUNDS, locations, 16, frames, 3, 0x700, slots, 0x200000, 2);
    REJECT(COPY_PLAN_STORAGE, locations, 16, frames, 3, 0x700, slots, 0x700fff, 0);
    REJECT(COPY_PLAN_STORAGE, NULL, 16, frames, 3, 0x700, slots, 0x200000, 0);
    REJECT(COPY_PLAN_STORAGE, locations, 16, frames, 3, 0x700, plan.leaves, 0x200000, 0);
    slots[1] = 2;
    REJECT(COPY_PLAN_OCCUPIED, locations, 16, frames, 3, 0x700, slots, 0x200000, 0);
    slots[1] = 0;
    locations[15].offset = 4096;
    REJECT(COPY_PLAN_BOUNDS, locations, 16, frames, 3, 0x700, slots, 0x200000, 0);
    locations[15].offset = 7;
    locations[15].frame = 29;
    REJECT(COPY_PLAN_UNPROTECTED, locations, 16, frames, 3, 0x700, slots, 0x200000, 0);
    locations[15].frame = 23;
    REJECT(COPY_PLAN_FRAMES, locations, 16, frames, 3, 0x700, slots, 0x200000, 0);
    assert(copy_plan_prepare(NULL, 0, NULL, 0, 0x700, slots, 0, 0, &plan) == COPY_PLAN_OK);
    assert(plan.count == 0 && plan.leaves[0] == 0 && plan.leaves[1] == 0);
    puts("copy operand plan: PASS");
}
