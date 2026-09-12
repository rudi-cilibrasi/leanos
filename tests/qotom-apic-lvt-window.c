#include <assert.h>
#include <setjmp.h>
#include <stdio.h>
#include <string.h>
#include "qotom-apic-lvt-window.h"

static uint64_t table[4096], saved, mapped;
static struct lab_qotom_lvt_window window;
static unsigned control_calls, invalidations, loads, faults;
static unsigned fail_load;
static int bad_control, leaf_interference, restore_interference;
static jmp_buf terminal;

static int controls(void *opaque, struct lab_ecam_controls *out) {
    assert(opaque == &window);
    ++control_calls;
    *out = (struct lab_ecam_controls){UINT64_C(0x0007040600070406),
        UINT64_C(0x8001001f), UINT64_C(0x150000), UINT64_C(0x68),
        UINT64_C(0xd00), UINT64_C(2)};
    if (bad_control && control_calls >= 3) out->rflags |= UINT64_C(0x200);
    if (control_calls == 4) assert(table[1024] == saved && invalidations == 2);
    return 1;
}

static void invalidate(void *opaque, uint64_t address) {
    assert(opaque == &window && address == UINT64_C(0x400000));
    ++invalidations;
    if (invalidations == 1) assert(table[1024] == mapped && loads == 0);
    else {
        assert(invalidations == 2 && table[1024] == saved);
        if (restore_interference) table[1024] ^= 2;
    }
}

static int load32(void *opaque, uint64_t address, uint32_t *value) {
    assert(opaque == &window && invalidations == 1 &&
           (table[1024] & ~UINT64_C(0x20)) == mapped);
    ++loads;
    const unsigned odd = address == UINT64_C(0x400360);
    assert(address == UINT64_C(0x400350) || odd);
    *value = odd ? UINT32_C(0x10400) : UINT32_C(0x10700);
    table[1024] |= UINT64_C(0x20);
    if (leaf_interference && loads == 4) table[1024] |= 2;
    return fail_load != loads;
}

static void fault(void *opaque) {
    assert(opaque == &window && invalidations == 2);
    ++faults;
    longjmp(terminal, 1);
}

static void reset(void) {
    memset(table, 0, sizeof(table));
    for (size_t page = 0; page < 4096; ++page)
        table[page] = page * UINT64_C(4096) | UINT64_C(0x8000000000000003);
    saved = table[1024] |= UINT64_C(0x60);
    mapped = QOTOM_LOCAL_APIC_BASE | UINT64_C(0x8000000000000019);
    control_calls = invalidations = loads = faults = fail_load = 0;
    bad_control = leaf_interference = restore_interference = 0;
    window = (struct lab_qotom_lvt_window){
        .opaque=&window, .controls=controls, .invalidate=invalidate,
        .load32=load32, .fault=fault};
}

static void arm(void) {
    assert(lab_qotom_lvt_arm(&window, table, 4096, UINT64_C(0x150000),
        UINT64_C(0x400000), QOTOM_IA32_APIC_BASE));
    assert(window.armed == 1 && window.leaf == &table[1024] && control_calls == 2);
}

int main(void) {
    struct lab_qotom_lvt_sample sample;
    reset(); arm();
    assert(lab_qotom_lvt_read(&window, &sample));
    assert(sample.lint0_first == UINT32_C(0x10700));
    assert(sample.lint1_first == UINT32_C(0x10400));
    assert(sample.lint0_second == sample.lint0_first &&
           sample.lint1_second == sample.lint1_first);
    assert(table[1024] == saved && loads == 4 && invalidations == 2 &&
           control_calls == 4 && !faults);

    for (unsigned failed = 1; failed <= 4; ++failed) {
        reset(); arm(); fail_load = failed;
        sample = (struct lab_qotom_lvt_sample){1,2,3,4};
        assert(!lab_qotom_lvt_read(&window, &sample));
        assert(!sample.lint0_first && !sample.lint1_first &&
               !sample.lint0_second && !sample.lint1_second);
        assert(table[1024] == saved && invalidations == 2 && !faults);
    }
    reset(); arm(); bad_control = 1;
    assert(!lab_qotom_lvt_read(&window, &sample));
    assert(!invalidations && !loads);
    reset(); arm(); leaf_interference = 1;
    if (!setjmp(terminal)) {
        (void)lab_qotom_lvt_read(&window, &sample);
        assert(!"aperture interference returned");
    }
    assert(faults == 1 && table[1024] == saved);
    reset(); arm(); restore_interference = 1;
    if (!setjmp(terminal)) {
        (void)lab_qotom_lvt_read(&window, &sample);
        assert(!"failed restoration returned");
    }
    assert(faults == 1);

    reset();
    assert(!lab_qotom_lvt_arm(&window, table, 4095, UINT64_C(0x150000),
        UINT64_C(0x400000), QOTOM_IA32_APIC_BASE));
    assert(!window.armed);
    reset();
    assert(!lab_qotom_lvt_arm(&window, table, 4096, UINT64_C(0x150000),
        UINT64_C(0x400000), QOTOM_LOCAL_APIC_BASE));
    reset(); table[1024] ^= 4;
    assert(!lab_qotom_lvt_arm(&window, table, 4096, UINT64_C(0x150000),
        UINT64_C(0x400000), QOTOM_IA32_APIC_BASE));
    for (size_t alias = 0; alias < 4096; ++alias) {
        reset(); table[alias] = QOTOM_LOCAL_APIC_BASE | 1;
        assert(!lab_qotom_lvt_arm(&window, table, 4096, UINT64_C(0x150000),
            UINT64_C(0x400000), QOTOM_IA32_APIC_BASE));
        assert(!window.armed);
    }
    reset(); arm();
    assert(!lab_qotom_lvt_arm(&window, NULL, 4096, UINT64_C(0x150000),
        UINT64_C(0x400000), QOTOM_IA32_APIC_BASE));
    assert(!window.armed && window.leaf == NULL);
    reset();
    assert(!lab_qotom_lvt_read(&window, &sample));
    assert(!lab_qotom_lvt_read(NULL, &sample));
    assert(!lab_qotom_lvt_read(&window, NULL));
    puts("Qotom APIC LVT window: exact UC reads, alias exclusion, restoration and terminal interference PASS");
}
