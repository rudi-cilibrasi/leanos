#include <assert.h>
#include <setjmp.h>
#include <stdio.h>
#include <string.h>
#include "qotom-xhci-ext-window.h"

static struct lab_xhci_ext_window window;
static uint64_t leaf, saved, mapped, selected = 0xd0908008;
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
    assert(opaque == &window && address == 0x400000 + (selected & 4095));
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
    assert(lab_xhci_ext_read_leaf(0xd0908008, &mapped));
    output = 42;
    control_calls = invalidations = loads = faults = 0;
    pre_bad = post_bad = load_failed = leaf_interference = restore_interference = 0;
    window = (struct lab_xhci_ext_window){&leaf, 0x150000, 0x400000, 1,
                                     &window, controls, invalidate, load32, fault};
}

int main(void) {
    reset();
    assert(lab_xhci_ext_window_read(&window, 0xd0908008, &output));
    assert(output == 0x12345678 && leaf == saved && control_calls == 2 && !faults);
    reset(); load_failed = 1;
    assert(!lab_xhci_ext_window_read(&window, 0xd0908008, &output));
    assert(output == 42 && leaf == saved && control_calls == 2 && !faults);
    reset(); pre_bad = 1;
    assert(!lab_xhci_ext_window_read(&window, 0xd0908008, &output));
    assert(leaf == saved && !invalidations && !loads && output == 42);
    reset(); leaf ^= 4;
    assert(!lab_xhci_ext_window_read(&window, 0xd0908008, &output));
    assert(!invalidations && !loads && output == 42);
    reset(); window.armed = 0;
    assert(!lab_xhci_ext_window_read(&window, 0xd0908008, &output));
    assert(!control_calls && !invalidations && !loads);
    reset();
    assert(!lab_xhci_ext_window_read(0, 0xd0908008, &output));
    assert(!lab_xhci_ext_window_read(&window, 0xd0908008, 0));
    assert(!lab_xhci_ext_window_read(&window, 0xe0000100, &output));
    assert(!control_calls && !invalidations && !loads);
    /* These paths must terminate after cleanup, never return a read result. */
    reset(); post_bad = 1;
    if (!setjmp(terminal)) {
        (void)lab_xhci_ext_window_read(&window, 0xd0908008, &output);
        assert(!"post-read root change returned");
    }
    assert(faults == 1 && leaf == saved);
    reset(); leaf_interference = 1;
    if (!setjmp(terminal)) {
        (void)lab_xhci_ext_window_read(&window, 0xd0908008, &output);
        assert(!"interfered aperture returned");
    }
    assert(faults == 1 && leaf == saved);
    reset(); restore_interference = 1;
    if (!setjmp(terminal)) {
        (void)lab_xhci_ext_window_read(&window, 0xd0908008, &output);
        assert(!"failed restoration returned");
    }
    assert(faults == 1 && output == 42);
    for (unsigned offset = 0; offset <= 0x10004; ++offset) {
        uint64_t candidate = 42;
        uint64_t address = UINT64_C(0xd0900000) + offset;
        int accepted = lab_xhci_ext_read_leaf(address, &candidate);
        assert(accepted == (offset >= 0x8000 && offset <= 0xfffc && !(offset & 3)));
        assert(candidate == (accepted ? ((address & ~UINT64_C(4095)) |
            UINT64_C(0x8000000000000019)) : 42));
        reset();
        if (accepted) {
            selected = address;
            mapped = candidate;
            assert(lab_xhci_ext_window_read(&window, selected, &output));
            assert(output == 0x12345678 && leaf == saved && invalidations == 2);
        } else {
            assert(!lab_xhci_ext_window_read(&window, address, &output));
            assert(output == 42 && leaf == saved && !loads && !invalidations);
        }
    }
    uint64_t rejected = 42;
    assert(!lab_xhci_ext_read_leaf(UINT64_MAX, &rejected) && rejected == 42);
    assert(!lab_xhci_ext_read_leaf(0xd0908000, NULL));
    puts("Qotom XHCI extended window: ordered invalidation, private read, exact restore and terminal rejection PASS");
}
