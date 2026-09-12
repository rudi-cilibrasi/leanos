#include <assert.h>
#include <setjmp.h>
#include <stdio.h>
#include <string.h>
#include "qotom-realtek-state-window.h"

static struct lab_realtek_state_window window;
static uint64_t leaf, saved, mapped;
static uint32_t output;
static uint8_t selected_bus=1;
static uint64_t requested;
static uint8_t requested_width=4;
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

static int load(void *opaque, uint64_t address, uint8_t width, uint32_t *value) {
    assert(opaque == &window && address == 0x400000+(requested&4095) && width==requested_width);
    assert(invalidations == 1 && loads == 0 && output == 42 && leaf == mapped);
    ++loads;
    leaf |= 0x20; /* Hardware may set Accessed, but not Dirty for this read. */
    if (leaf_interference) leaf |= 2;
    *value = width==1?0x78:(width==2?0x5678:0x12345678);
    return !load_failed;
}

static void fault(void *opaque) {
    assert(opaque == &window && output == 42 && invalidations == 2);
    ++faults;
    longjmp(terminal, 1);
}

static void reset(void) {
    saved = leaf = UINT64_C(0x8000000000400063);
    assert(lab_realtek_state_read_leaf(selected_bus,requested, requested_width, &mapped));
    output = 42;
    control_calls = invalidations = loads = faults = 0;
    pre_bad = post_bad = load_failed = leaf_interference = restore_interference = 0;
    window = (struct lab_realtek_state_window){&leaf, 0x150000, 0x400000, 1, selected_bus,
                                     &window, controls, invalidate, load, fault};
}

static void run(void) {
    requested=qotom_realtek_bar(selected_bus)+0x40;requested_width=4;
    assert(pci_enumerate_segment(NULL,NULL,NULL).status==PCI_ENUMERATION_INVALID_ARGUMENT);
    reset();
    assert(lab_realtek_state_window_read(&window, requested, 4, &output));
    assert(output == 0x12345678 && leaf == saved && control_calls == 2 && !faults);
    reset(); load_failed = 1;
    assert(!lab_realtek_state_window_read(&window, requested, 4, &output));
    assert(output == 42 && leaf == saved && control_calls == 2 && !faults);
    reset(); pre_bad = 1;
    assert(!lab_realtek_state_window_read(&window, requested, 4, &output));
    assert(leaf == saved && !invalidations && !loads && output == 42);
    reset(); leaf ^= 4;
    assert(!lab_realtek_state_window_read(&window, requested, 4, &output));
    assert(!invalidations && !loads && output == 42);
    reset(); window.armed = 0;
    assert(!lab_realtek_state_window_read(&window, requested, 4, &output));
    assert(!control_calls && !invalidations && !loads);
    reset();
    assert(!lab_realtek_state_window_read(0, requested, 4, &output));
    assert(!lab_realtek_state_window_read(&window, requested, 4, 0));
    assert(!lab_realtek_state_window_read(&window, 0xe0000100, 4, &output));
    assert(!control_calls && !invalidations && !loads);
    for(unsigned missing=0;missing<5;++missing) {
        reset();
        if(missing==0)window.controls=NULL;
        if(missing==1)window.invalidate=NULL;
        if(missing==2)window.load=NULL;
        if(missing==3)window.fault=NULL;
        if(missing==4)window.leaf=NULL;
        assert(!lab_realtek_state_window_read(&window,requested,requested_width,&output));
        assert(output==42 && leaf==saved && !control_calls && !invalidations && !loads);
    }
    const uint64_t bad_windows[]={0,0x400001,0x1000000,UINT64_MAX};
    for(unsigned i=0;i<4;++i) {
        reset();window.window=bad_windows[i];
        assert(!lab_realtek_state_window_read(&window,requested,requested_width,&output));
        assert(output==42 && leaf==saved && !control_calls && !invalidations && !loads);
    }
    /* These paths must terminate after cleanup, never return a read result. */
    reset(); post_bad = 1;
    if (!setjmp(terminal)) {
        (void)lab_realtek_state_window_read(&window, requested, 4, &output);
        assert(!"post-read root change returned");
    }
    assert(faults == 1 && leaf == saved);
    reset(); leaf_interference = 1;
    if (!setjmp(terminal)) {
        (void)lab_realtek_state_window_read(&window, requested, 4, &output);
        assert(!"interfered aperture returned");
    }
    assert(faults == 1 && leaf == saved);
    reset(); restore_interference = 1;
    if (!setjmp(terminal)) {
        (void)lab_realtek_state_window_read(&window, requested, 4, &output);
        assert(!"failed restoration returned");
    }
    assert(faults == 1 && output == 42);
    for (unsigned offset=0;offset<4096;++offset)for(unsigned width=0;width<=8;++width) {
        uint64_t candidate=42;
        int accepted=lab_realtek_state_read_leaf(selected_bus,qotom_realtek_bar(selected_bus)+offset,width,&candidate);
        int valid=(offset==0x37 && width==1) || (offset==0x3c && width==2) ||
            ((offset==0x40 || offset==0x44) && width==4);
        assert(accepted==valid);
        assert(candidate==(accepted?(qotom_realtek_bar(selected_bus)|UINT64_C(0x8000000000000019)):42));
    }
    uint64_t candidate=42;
    assert(!lab_realtek_state_read_leaf(selected_bus,UINT64_MAX,4,&candidate) && candidate==42);
    assert(!lab_realtek_state_read_leaf(selected_bus,qotom_realtek_bar(selected_bus)-1,1,&candidate) && candidate==42);
    assert(!lab_realtek_state_read_leaf(selected_bus,qotom_realtek_bar(selected_bus)+8,4,NULL));
    const unsigned offsets[]={0x37,0x3c,0x40,0x44},widths[]={1,2,4,4};
    for(unsigned i=0;i<4;++i) {
        requested=qotom_realtek_bar(selected_bus)+offsets[i];requested_width=widths[i];reset();
        assert(lab_realtek_state_window_read(&window,requested,requested_width,&output));
        uint32_t expected=requested_width==1?0x78:(requested_width==2?0x5678:0x12345678);
        assert(output==expected && leaf==saved && loads==1 && invalidations==2);
        for(unsigned width=0;width<=8;++width)if(width!=requested_width) {
            reset();assert(!lab_realtek_state_window_read(&window,requested,width,&output));
            assert(output==42 && leaf==saved && !loads && !invalidations && !control_calls);
        }
    }
    reset();
    window.bus=selected_bus==1?3:1;
    assert(!lab_realtek_state_window_read(&window,requested,requested_width,&output));
    assert(!control_calls && !loads && !invalidations && output==42);
    for (unsigned bus=0;bus<256;++bus) if(bus!=1 && bus!=3) {
        reset();window.bus=(uint8_t)bus;
        assert(!lab_realtek_state_window_read(&window,requested,requested_width,&output));
        assert(!control_calls && !loads && !invalidations && output==42);
    }
}

int main(void) {
    selected_bus=1;run();selected_bus=3;run();
    puts("PASS Realtek window: both bound endpoints, exact widths, rejected cross-endpoint reads, restoration and terminal interference");
}
