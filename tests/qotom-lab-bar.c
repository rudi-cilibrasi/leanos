#include <assert.h>
#include <stdint.h>
#include "qotom-lab-bar.h"

/* The admission restated in 64-bit arithmetic: a memory BAR, 32-bit or 64-bit
   with a zero upper half, whose base is a multiple of 4 KiB and aligned to the
   window, and whose pages lie in [2 GiB, 0xfec00000). */
static int reference(uint32_t raw, uint32_t upper, uint32_t window, uint32_t pages) {
    uint64_t base = raw & ~UINT64_C(0xf);
    unsigned type = raw & 0xfu;
    int memory = type == 0 || (type == 4 && upper == 0);
    return memory && base % 4096 == 0 && (base & (window - 1u)) == 0 &&
           base >= UINT64_C(0x80000000) && base + UINT64_C(4096) * pages <= UINT64_C(0xfec00000);
}

/* The check both windows of hardware/lab/qotom-wifi.c.inc made before, for
   the cases below that it got wrong. */
static int before(uint32_t raw, uint32_t upper, uint32_t window) {
    uint32_t type = raw & 0xfu, base = raw & ~UINT32_C(0xf);
    return !((type != 0 && !(type == 4 && upper == 0)) || (base & (window - 1u)) != 0 ||
             base < UINT32_C(0x80000000) || base > UINT32_C(0xfec00000));
}

static const uint32_t windows[] = {0x200, 0x400, 0x800, 0x1000, 0x2000, 0x4000, 0x8000, 0x10000};

static void sweep(uint64_t from, uint64_t to, uint32_t step) {
    for (uint64_t base = from; base < to; base += step)
        for (unsigned w = 0; w < sizeof windows / sizeof windows[0]; ++w)
            for (uint32_t pages = 1; pages <= 16; ++pages)
                for (uint32_t type = 0; type < 16; ++type)
                    for (uint32_t upper = 0; upper < 2; ++upper) {
                        uint32_t raw = (uint32_t)base | type;
                        assert(lab_dev_bar_admitted(raw, upper, windows[w], pages) ==
                               reference(raw, upper, windows[w], pages));
                    }
}

int main(void) {
    /* The profiles' BARs as captured, and the q35 device lab's: admitted. */
    assert(lab_dev_bar_admitted(0xd0916000u, 0, 0x800, 1));       /* AHCI ABAR, 2 KiB window */
    assert(lab_dev_bar_admitted(0xd0916000u | 4u, 0, 0x800, 1));  /* the same, as a 64-bit BAR */
    assert(lab_dev_bar_admitted(0xfebf0000u, 0, 0x10000, 16));    /* a 64 KiB window ending at the hole's end */
    assert(lab_dev_bar_admitted(0x80000000u, 0, 0x1000, 1));
    /* A 2 KiB window at an odd 2 KiB boundary: the leaf would map the page
       below the device's registers. The check before admitted it. */
    assert(before(0xd0916800u, 0, 0x800) && !lab_dev_bar_admitted(0xd0916800u, 0, 0x800, 1));
    assert(before(0xd0916200u, 0, 0x200) && !lab_dev_bar_admitted(0xd0916200u, 0, 0x200, 1));
    /* The I/O APIC's page, and a window that runs into it: admitted before. */
    assert(before(0xfec00000u, 0, 0x1000) && !lab_dev_bar_admitted(0xfec00000u, 0, 0x1000, 1));
    assert(before(0xfebff000u, 0, 0x1000) && !lab_dev_bar_admitted(0xfebff000u, 0, 0x2000, 2));
    assert(lab_dev_bar_admitted(0xfebff000u, 0, 0x1000, 1));
    /* Outside the hole, prefetchable, I/O, 64-bit above 4 GiB: rejected. */
    assert(!lab_dev_bar_admitted(0x7ffff000u, 0, 0x1000, 1));
    assert(!lab_dev_bar_admitted(0xfee00000u, 0, 0x1000, 1));
    assert(!lab_dev_bar_admitted(0xd0900008u, 0, 0x1000, 1));
    assert(!lab_dev_bar_admitted(0xd0900001u, 0, 0x1000, 1));
    assert(!lab_dev_bar_admitted(0xd0900004u, 1, 0x1000, 1));
    assert(!lab_dev_bar_admitted(0xd0900002u, 0, 0x1000, 1));
    /* Every base in steps of 512 bytes at both ends of the hole and around a
       captured BAR, against the reference. */
    sweep(UINT64_C(0x7fff0000), UINT64_C(0x80011000), 0x200);
    sweep(UINT64_C(0xd0900000), UINT64_C(0xd0921000), 0x200);
    sweep(UINT64_C(0xfebe0000), UINT64_C(0xfec11000), 0x200);
    sweep(UINT64_C(0xfff00000), UINT64_C(0x100000000), 0x200);
    return 0;
}
