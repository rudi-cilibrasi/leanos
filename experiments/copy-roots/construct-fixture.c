/* QEMU-only adapter: freeze a source snapshot, require the complete linked
 * fixture image except its two protected data pages, then construct root B.
 * Hardware A/D bits may change in root A; they are not authorization inputs.
 * The immutable snapshot itself is never installed as a hardware table.
 */
#include "construct.h"
extern uint64_t leaves_a[CONSTRUCT_LEAVES], leaves_b[CONSTRUCT_LEAVES];
extern char value_a[], value_b[], fixture_image_start[], fixture_image_end[];
static uint64_t snapshot[CONSTRUCT_LEAVES];
static struct construct_required required[CONSTRUCT_LEAVES];

int construct_fixture_root(void) {
    uint64_t frames[] = {(uintptr_t)value_a >> 12, (uintptr_t)value_b >> 12};
    size_t first = (uintptr_t)fixture_image_start >> 12;
    size_t last = ((uintptr_t)fixture_image_end + 4095) >> 12;
    size_t count = 0;
    if (last > CONSTRUCT_LEAVES || first >= last) return 1;
    for (size_t page = 0; page < CONSTRUCT_LEAVES; ++page)
        snapshot[page] = ((volatile uint64_t *)leaves_a)[page];
    for (size_t page = first; page < last; ++page) {
        if (page == frames[0] || page == frames[1]) continue;
        /* Fixture bootstrap permits exactly identity present/writable leaves.
         * Do not derive permission authority from an arbitrary source word. */
        uint64_t expected = ((uint64_t)page << 12) | 3;
        if ((snapshot[page] & ~UINT64_C(0x60)) != expected) return 2;
        required[count++] = (struct construct_required){page, snapshot[page]};
    }
    return construct_closed_leaves(snapshot, leaves_b, frames, 2, required, count);
}
