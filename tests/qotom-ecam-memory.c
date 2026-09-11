#include <assert.h>
#include <stdio.h>
#include "qotom-ecam-memory.h"

int main(void) {
    const struct lab_ecam_controls captured = {
        UINT64_C(0x0007040600070406), UINT64_C(0x8001001f),
        UINT64_C(0x150000), UINT64_C(0x68), UINT64_C(0xd00), 2
    };
    assert(lab_ecam_controls_match(&captured, 0x150000));
    assert(!lab_ecam_controls_match(0, 0x150000));
    const uint64_t roots[] = {0, 0x150001, 0x151000, 0x1000000, UINT64_MAX};
    for (unsigned i = 0; i < sizeof(roots)/sizeof(roots[0]); ++i)
        assert(!lab_ecam_controls_match(&captured, roots[i]));
    for (unsigned bit = 0; bit < 64; ++bit) {
        struct lab_ecam_controls c = captured;
        c.pat ^= UINT64_C(1) << bit;
        assert(!lab_ecam_controls_match(&c, 0x150000));
        c = captured; c.cr3 ^= UINT64_C(1) << bit;
        assert(!lab_ecam_controls_match(&c, 0x150000));
    }
    const unsigned cr0_bits[] = {0, 16, 29, 30, 31};
    const unsigned cr4_bits[] = {5, 7, 12, 17};
    const unsigned efer_bits[] = {8, 10, 11};
    for (unsigned i = 0; i < sizeof(cr0_bits)/sizeof(cr0_bits[0]); ++i) {
        struct lab_ecam_controls c = captured; c.cr0 ^= UINT64_C(1) << cr0_bits[i];
        assert(!lab_ecam_controls_match(&c, 0x150000));
    }
    for (unsigned i = 0; i < sizeof(cr4_bits)/sizeof(cr4_bits[0]); ++i) {
        struct lab_ecam_controls c = captured; c.cr4 ^= UINT64_C(1) << cr4_bits[i];
        assert(!lab_ecam_controls_match(&c, 0x150000));
    }
    for (unsigned i = 0; i < sizeof(efer_bits)/sizeof(efer_bits[0]); ++i) {
        struct lab_ecam_controls c = captured; c.efer ^= UINT64_C(1) << efer_bits[i];
        assert(!lab_ecam_controls_match(&c, 0x150000));
    }
    for (unsigned bit = 9; bit <= 17; bit += 8) {
        struct lab_ecam_controls c = captured; c.rflags |= UINT64_C(1) << bit;
        assert(!lab_ecam_controls_match(&c, 0x150000));
    }
    for (uint64_t page = 0; page < 65536; ++page) {
        uint64_t frame = UINT64_C(0xe0000000) + page * 4096;
        for (unsigned offset = 0; offset <= 252; offset += 4) {
            uint64_t leaf = 0;
            assert(lab_ecam_read_leaf(frame + offset, &leaf));
            assert((leaf & UINT64_C(0x000ffffffffff000)) == frame);
            assert((leaf & 0xfff) == 0x19); /* present, PWT, PCD; no RW/U/PS/global */
            assert(leaf >> 63 == 1);
        }
    }
    const uint64_t bad[] = {0, 0xdfffffff, 0xe0000001, 0xe0000100,
                            0xe0000ffc, 0xf0000000, UINT64_MAX};
    for (unsigned i = 0; i < sizeof(bad)/sizeof(bad[0]); ++i) {
        uint64_t leaf = 42;
        assert(!lab_ecam_read_leaf(bad[i], &leaf) && leaf == 42);
    }
    assert(!lab_ecam_read_leaf(0xe0000000, 0));
    puts("Qotom ECAM controls and 4194304 supervisor read-only NX/UC leaves PASS");
}
