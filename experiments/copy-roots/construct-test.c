#include "construct.h"
#include <assert.h>
#include <stdio.h>
#include <string.h>

static uint64_t source[CONSTRUCT_LEAVES], target[CONSTRUCT_LEAVES];
static const uint64_t poison = UINT64_C(0xdeadbeefbad0cafe);
static void reset(void) {
    for (size_t i = 0; i < CONSTRUCT_LEAVES; ++i) {
        source[i] = ((uint64_t)i << 12) | 3;
        target[i] = poison;
    }
    source[99] = 0; /* absent guard */
    source[200] = UINT64_C(0x8000000000004063); /* supervisor alias, NX/A/D */
    source[4095] = 0x5007; /* final slot: user alias */
}
static void unchanged(void) {
    for (size_t i = 0; i < CONSTRUCT_LEAVES; ++i) assert(target[i] == poison);
}
int main(void) {
    uint64_t frames[] = {4, 5};
    struct construct_required required[] = {{8, 0x8003}, {4094, 0xffe003}};
    reset();
    assert(construct_closed_leaves(source, target, frames, 2, required, 2) == CONSTRUCT_OK);
    assert(target[4] == 0 && target[5] == 0 && target[200] == 0 && target[4095] == 0);
    assert(target[99] == 0 && target[8] == 0x8003 && target[4094] == 0xffe003);
    for (size_t i = 0; i < CONSTRUCT_LEAVES; ++i)
        if (i != 4 && i != 5 && i != 200 && i != 4095) assert(target[i] == source[i]);
    assert(source[200] == UINT64_C(0x8000000000004063));
    reset();
    required[1] = (struct construct_required){4, 0x4003};
    assert(construct_closed_leaves(source, target, frames, 2, required, 2) == CONSTRUCT_PROTECTED);
    unchanged();
    required[1] = (struct construct_required){99, 0x63003};
    assert(construct_closed_leaves(source, target, frames, 2, required, 2) == CONSTRUCT_REQUIRED);
    unchanged();
    required[1] = (struct construct_required){8, 0x8001};
    assert(construct_closed_leaves(source, target, frames, 2, required, 2) == CONSTRUCT_REQUIRED);
    unchanged();
    required[1] = (struct construct_required){4096, 3};
    assert(construct_closed_leaves(source, target, frames, 2, required, 2) == CONSTRUCT_BOUNDS);
    unchanged();
    assert(construct_closed_leaves(source, target, frames, 17, required, 0) == CONSTRUCT_BOUNDS);
    assert(construct_closed_leaves(source, target, frames, 2, required, 4097) == CONSTRUCT_BOUNDS);
    unchanged();
    frames[1] = UINT64_C(1) << 40;
    assert(construct_closed_leaves(source, target, frames, 2, required, 0) == CONSTRUCT_BOUNDS);
    unchanged();
    frames[1] = 5;
    assert(construct_closed_leaves(source, source, frames, 2, required, 0) == CONSTRUCT_STORAGE);
    assert(source[200] == UINT64_C(0x8000000000004063));
    assert(construct_closed_leaves(source, target, target, 2, required, 0) == CONSTRUCT_STORAGE);
    unchanged();
    assert(construct_closed_leaves(source, target, NULL, 1, NULL, 0) == CONSTRUCT_STORAGE);
    unchanged();
    assert(construct_closed_leaves(source, target, NULL, 0, NULL, 0) == CONSTRUCT_OK);
    assert(memcmp(source, target, sizeof(source)) == 0);
    puts("closed leaf construction: aliases, preservation, rejection atomicity and bounds PASS");
}
