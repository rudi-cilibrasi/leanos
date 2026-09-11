#ifndef LEANOS_LAB_QOTOM_ECAM_ROOT_H
#define LEANOS_LAB_QOTOM_ECAM_ROOT_H
#include <stdint.h>

/* Trusted views of the compiled boot arrays, not pointers decoded from device
 * input. The native caller must bind each view to its identity physical address
 * and keep all arrays stable during validation and the aperture transaction. */
struct lab_ecam_root_view {
    const volatile uint64_t *root, *pdpt, *pd;
    volatile uint64_t *pt;
    uint64_t root_address, pdpt_address, pd_address, pt_address;
};

static inline int lab_ecam_root_matches(const struct lab_ecam_root_view *v,
                                        uint64_t active_root, uint64_t window) {
    if (!v || !v->root || !v->pdpt || !v->pd || !v->pt ||
        !window || window >= UINT64_C(0x1000000) || (window & 4095u) ||
        active_root != v->root_address) return 0;
    const uint64_t starts[4] = {v->root_address, v->pdpt_address,
                                v->pd_address, v->pt_address};
    const uint64_t lengths[4] = {4096, 4096, 4096, 32768};
    for (unsigned i = 0; i < 4; ++i) {
        if (!starts[i] || (starts[i] & 4095u) ||
            starts[i] > UINT64_C(0x1000000) - lengths[i] ||
            (window >= starts[i] && window < starts[i] + lengths[i])) return 0;
        for (unsigned j = 0; j < i; ++j)
            if (starts[i] < starts[j] + lengths[j] &&
                starts[j] < starts[i] + lengths[i]) return 0;
    }
    const uint64_t accessed = 0x20;
    if ((v->root[0] & ~accessed) != (v->pdpt_address | 7u) ||
        (v->pdpt[0] & ~accessed) != (v->pd_address | 7u)) return 0;
    for (unsigned i = 1; i < 512; ++i)
        if (v->root[i] || v->pdpt[i]) return 0;
    for (unsigned i = 0; i < 512; ++i) {
        uint64_t expected = i < 8 ? (v->pt_address + i * 4096u) | 7u : 0;
        uint64_t actual = v->pd[i];
        if (i < 8) actual &= ~accessed;
        if (actual != expected) return 0;
    }
    for (unsigned i = 0; i < 4096; ++i) {
        uint64_t leaf = v->pt[i];
        uint64_t frame = leaf & UINT64_C(0x000ffffffffff000);
        if ((leaf & 1u) && frame >= UINT64_C(0xe0000000) &&
            frame < UINT64_C(0xf0000000)) return 0;
    }
    return (v->pt[window / 4096u] & ~UINT64_C(0x60)) ==
        (window | UINT64_C(0x8000000000000003));
}
#endif
