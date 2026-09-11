#include <assert.h>
#include <stdio.h>
#include "qotom-ecam-arm.h"
static uint64_t root[512], pdpt[512], pd[512], pt[4096];
static unsigned observations, invalidations, loads, reject_observation;
static struct lab_ecam_controls observed = {
    .pat=UINT64_C(0x0007040600070406), .cr0=0x80010001,
    .cr3=0x100000, .cr4=0x20, .efer=0xd00, .rflags=2
};
static int controls(void *unused, struct lab_ecam_controls *out) {
    (void)unused;
    ++observations;
    *out = observed;
    if (observations == reject_observation) out->cr3 += 4096;
    return 1;
}
static void invalidate(void *unused, uint64_t address) {
    (void)unused; (void)address; ++invalidations;
}
static int load(void *unused, uint64_t address, uint32_t *out) {
    (void)unused; (void)address; ++loads; *out = 0x0f008086; return 1;
}
static void fault(void *unused) { (void)unused; assert(0); }
int main(void) {
    struct lab_ecam_root_view v = {root, pdpt, pd, pt,
                                   0x100000, 0x101000, 0x102000, 0x103000};
    root[0] = v.pdpt_address | 7; pdpt[0] = v.pd_address | 7;
    for (unsigned i = 0; i < 8; ++i) pd[i] = (v.pt_address + i * 4096) | 7;
    for (unsigned i = 0; i < 4096; ++i)
        pt[i] = (uint64_t)i * 4096 | UINT64_C(0x8000000000000003);
    struct lab_ecam_window w = {.controls=controls, .invalidate=invalidate,
                                .load32=load, .fault=fault};
#define ARM() lab_ecam_arm(&w, &v, lab_ecam_expected_tables, LAB_ECAM_FIRMWARE_TABLE_COUNT, 0x200000)
    assert(ARM());
    assert(w.armed == 1 && w.leaf == &pt[512] && w.root == v.root_address);
    assert(observations == 2 && !loads && !invalidations);
    uint64_t saved = pt[512];
    uint32_t value = 42;
    assert(lab_ecam_window_read(&w, 0xe0000000, &value));
    assert(value == 0x0f008086 && pt[512] == saved && loads == 1 && invalidations == 2);
    /* A bad firmware snapshot revokes the previous arm without any access. */
    unsigned prior = observations;
    assert(!lab_ecam_arm(&w, &v, lab_ecam_expected_tables, 0, 0x200000));
    assert(observations == prior && !w.armed && !w.leaf && !w.root && !w.window);
    value = 42;
    assert(!lab_ecam_window_read(&w, 0xe0000000, &value) && value == 42);
    assert(loads == 1 && invalidations == 2);
    for (unsigned n = 1; n <= 2; ++n) {
        reject_observation = observations + n;
        assert(!ARM()); assert(!w.armed && !w.leaf);
    }
    reject_observation = 0;
    pt[4095] = 0xe0000001;
    assert(!ARM() && !w.armed);
    pt[4095] = UINT64_C(0x8000000000fff003);
    assert(ARM());
    w.load32 = 0;
    prior = observations;
    assert(!ARM() && observations == prior && !w.armed);
    assert(loads == 1 && invalidations == 2 && pt[512] == saved);
    puts("ECAM arm: firmware/root/control composition, revocation and transaction PASS");
}
