/* Test-only decimal-word bridge for comparison with the compiled Lean model. */
#include "construct.h"
#include <inttypes.h>
#include <stdio.h>
static uint64_t source[CONSTRUCT_LEAVES], target[CONSTRUCT_LEAVES], frames[CONSTRUCT_FRAMES];
static struct construct_required required[CONSTRUCT_LEAVES];
int main(void) {
    size_t fc, rc;
    int read;
    while ((read = scanf("%zu %zu", &fc, &rc)) == 2) {
        if (fc > CONSTRUCT_FRAMES || rc > CONSTRUCT_LEAVES) return 2;
        for (size_t i = 0; i < fc; ++i)
            if (scanf("%" SCNu64, &frames[i]) != 1) return 2;
        for (size_t i = 0; i < rc; ++i)
            if (scanf("%" SCNu64 " %" SCNu64, &required[i].page, &required[i].leaf) != 2) return 2;
        for (size_t i = 0; i < CONSTRUCT_LEAVES; ++i) {
            if (scanf("%" SCNu64, &source[i]) != 1) return 2;
            target[i] = UINT64_MAX;
        }
        enum construct_result result = construct_closed_leaves(source, target, frames, fc, required, rc);
        if (result != CONSTRUCT_OK) {
            for (size_t i = 0; i < CONSTRUCT_LEAVES; ++i)
                if (target[i] != UINT64_MAX) return 3;
            puts("0");
        } else {
            printf("1");
            for (size_t i = 0; i < CONSTRUCT_LEAVES; ++i) printf(" %" PRIu64, target[i]);
            putchar('\n');
        }
    }
    return read == EOF ? 0 : 2;
}
