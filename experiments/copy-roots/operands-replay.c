#include "operands.h"
#include <inttypes.h>
#include <stdio.h>
int main(void) {
    size_t count;
    unsigned out;
    uint64_t base, buffer;
    int read;
    while ((read = scanf("%zu %u %" SCNu64 " %" SCNu64, &count, &out, &base, &buffer)) == 4) {
        if (count > 16) return 2;
        struct copy_location locations[16];
        uint64_t frames[16], slots[2] = {0};
        for (size_t i = 0; i < count; ++i) {
            if (scanf("%" SCNu64 " %" SCNu64, &locations[i].frame, &locations[i].offset) != 2) return 2;
            frames[i] = locations[i].frame;
        }
        struct copy_plan plan;
        if (copy_plan_prepare(locations, count, frames, count, base, slots,
                              buffer, out, &plan) != COPY_PLAN_OK) return 3;
        printf("%" PRIu64 " %" PRIu64, plan.leaves[0], plan.leaves[1]);
        for (size_t i = 0; i < count; ++i)
            printf(" %" PRIu64 " %" PRIu64, plan.operands[i].source, plan.operands[i].destination);
        putchar('\n');
    }
    return read == EOF ? 0 : 2;
}
