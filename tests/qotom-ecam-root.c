#include <assert.h>
#include <stdio.h>
#include "qotom-ecam-root.h"
static uint64_t root[512], pdpt[512], pd[512], pt[4096];
int main(void) {
    struct lab_ecam_root_view v = {root, pdpt, pd, pt, 0x100000, 0x101000,
                                   0x102000, 0x103000};
    const uint64_t window = 0x200000;
    root[0] = v.pdpt_address | 7;
    pdpt[0] = v.pd_address | 7;
    for (unsigned i = 0; i < 8; ++i) pd[i] = (v.pt_address + i * 4096) | 7;
    for (unsigned i = 0; i < 4096; ++i)
        pt[i] = (uint64_t)i * 4096 | UINT64_C(0x8000000000000003);
#define ACCEPT() lab_ecam_root_matches(&v, 0x100000, window)
    assert(ACCEPT());
    root[0] |= 0x20; pdpt[0] |= 0x20; pd[0] |= 0x20;
    pt[window / 4096] |= 0x60;
    assert(ACCEPT());
    /* Every possible present alias is rejected, including the last leaf. */
    for (unsigned i = 0; i < 4096; ++i) {
        uint64_t saved = pt[i];
        pt[i] = UINT64_C(0xe0000001); assert(!ACCEPT());
        pt[i] = UINT64_C(0xeffff001); assert(!ACCEPT());
        pt[i] = saved;
    }
    for (unsigned i = 1; i < 512; ++i) {
        root[i] = 1; assert(!ACCEPT()); root[i] = 0;
        pdpt[i] = 1; assert(!ACCEPT()); pdpt[i] = 0;
    }
    for (unsigned i = 0; i < 512; ++i) {
        uint64_t saved = pd[i];
        pd[i] ^= 0x80; assert(!ACCEPT()); /* Huge page or unexpected entry. */
        pd[i] = saved;
    }
    for (unsigned bit = 0; bit < 64; ++bit) {
        if (bit == 5 || bit == 6) continue;
        pt[window / 4096] ^= UINT64_C(1) << bit;
        assert(!ACCEPT());
        pt[window / 4096] ^= UINT64_C(1) << bit;
    }
    assert(!lab_ecam_root_matches(&v, 0x101000, window));
    assert(!lab_ecam_root_matches(&v, 0x100000, v.pt_address + 7 * 4096));
    assert(!lab_ecam_root_matches(&v, 0x100000, window + 1));
    assert(!lab_ecam_root_matches(0, 0x100000, window));
    struct lab_ecam_root_view bad = v;
    bad.pt_address = 0xff9000; assert(!lab_ecam_root_matches(&bad, 0x100000, window));
    bad = v; bad.pt_address = v.pd_address;
    assert(!lab_ecam_root_matches(&bad, 0x100000, window));
    bad = v; bad.pt = 0; assert(!lab_ecam_root_matches(&bad, 0x100000, window));
    assert(ACCEPT());
    puts("ECAM root: bounded ancestors, aperture storage and all alias positions PASS");
}
