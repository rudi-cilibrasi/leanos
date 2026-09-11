#include <assert.h>
#include <setjmp.h>
#include <stdio.h>
#include <string.h>
#include "qotom-ecam-window.h"

static struct lab_ecam_window window;
static uint64_t leaf, saved, mapped;
static uint32_t output;
static unsigned control_calls, invalidations, loads, faults;
static int pre_bad, post_bad, load_failed, leaf_interference, restore_interference;
static jmp_buf terminal;

static int controls(void *opaque, struct lab_ecam_controls *c) {
    assert(opaque == &window && output == 42);
    ++control_calls;
    *c = (struct lab_ecam_controls){UINT64_C(0x0007040600070406),
        UINT64_C(0x8001001f), 0x150000, 0x68, 0xd00, 2};
    if ((control_calls == 1 && pre_bad) || (control_calls == 2 && post_bad))
        c->cr3 += 4096;
    if (control_calls == 2) assert(leaf == saved && invalidations == 2);
    return 1;
}

static void invalidate(void *opaque, uint64_t address) {
    assert(opaque == &window && address == 0x400000 && output == 42);
    ++invalidations;
    if (invalidations == 1) assert(leaf == mapped && loads == 0);
    else {
        assert(invalidations == 2 && leaf == saved && loads == 1);
        if (restore_interference) leaf ^= 2;
    }
}

static int load32(void *opaque, uint64_t address, uint32_t *value) {
    assert(opaque == &window && address == 0x4000fc);
    assert(invalidations == 1 && loads == 0 && output == 42 && leaf == mapped);
    ++loads;
    leaf |= 0x20; /* Hardware may set Accessed, but not Dirty for this read. */
    if (leaf_interference) leaf |= 2;
    *value = 0x12345678;
    return !load_failed;
}

static void fault(void *opaque) {
    assert(opaque == &window && output == 42 && invalidations == 2);
    ++faults;
    longjmp(terminal, 1);
}

static void reset(void) {
    saved = leaf = UINT64_C(0x8000000000400063);
    assert(lab_ecam_read_leaf(0xe00000fc, &mapped));
    output = 42;
    control_calls = invalidations = loads = faults = 0;
    pre_bad = post_bad = load_failed = leaf_interference = restore_interference = 0;
    window = (struct lab_ecam_window){&leaf, 0x150000, 0x400000, 1,
                                     &window, controls, invalidate, load32, fault};
}

int main(void) {
    reset();
    assert(lab_ecam_window_read(&window, 0xe00000fc, &output));
    assert(output == 0x12345678 && leaf == saved && control_calls == 2 && !faults);
    reset(); load_failed = 1;
    assert(!lab_ecam_window_read(&window, 0xe00000fc, &output));
    assert(output == 42 && leaf == saved && control_calls == 2 && !faults);
    reset(); pre_bad = 1;
    assert(!lab_ecam_window_read(&window, 0xe00000fc, &output));
    assert(leaf == saved && !invalidations && !loads && output == 42);
    reset(); leaf ^= 4;
    assert(!lab_ecam_window_read(&window, 0xe00000fc, &output));
    assert(!invalidations && !loads && output == 42);
    reset(); window.armed = 0;
    assert(!lab_ecam_window_read(&window, 0xe00000fc, &output));
    assert(!control_calls && !invalidations && !loads);
    reset();
    assert(!lab_ecam_window_read(0, 0xe00000fc, &output));
    assert(!lab_ecam_window_read(&window, 0xe00000fc, 0));
    assert(!lab_ecam_window_read(&window, 0xe0000100, &output));
    assert(!control_calls && !invalidations && !loads);
    /* These paths must terminate after cleanup, never return a read result. */
    reset(); post_bad = 1;
    if (!setjmp(terminal)) {
        (void)lab_ecam_window_read(&window, 0xe00000fc, &output);
        assert(!"post-read root change returned");
    }
    assert(faults == 1 && leaf == saved);
    reset(); leaf_interference = 1;
    if (!setjmp(terminal)) {
        (void)lab_ecam_window_read(&window, 0xe00000fc, &output);
        assert(!"interfered aperture returned");
    }
    assert(faults == 1 && leaf == saved);
    reset(); restore_interference = 1;
    if (!setjmp(terminal)) {
        (void)lab_ecam_window_read(&window, 0xe00000fc, &output);
        assert(!"failed restoration returned");
    }
    assert(faults == 1 && output == 42);
    puts("Qotom ECAM window: ordered invalidation, private read, exact restore and terminal rejection PASS");
}
