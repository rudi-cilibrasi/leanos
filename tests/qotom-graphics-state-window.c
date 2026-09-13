#include <assert.h>
#include <setjmp.h>
#include <stdio.h>
#include "qotom-graphics-state-window.h"
static struct lab_graphics_state_window window;
static uint64_t leaf,saved,mapped,requested;static uint32_t output;
static unsigned controls_count,invalidations,loads,faults;
static int pre_bad,post_bad,load_fail,leaf_bad,restore_bad;static jmp_buf terminal;
static int controls(void *opaque,struct lab_ecam_controls *out) {
    assert(opaque==&window);++controls_count;
    *out=(struct lab_ecam_controls){0x0007040600070406,0x8001001f,0x150000,0x68,0xd00,2};
    if((controls_count==1&&pre_bad)||(controls_count==2&&post_bad))out->cr3^=4096;
    return 1;
}
static void invalidate(void *opaque,uint64_t address) {
    assert(opaque==&window && address==0x400000);++invalidations;
    if(invalidations==2 && restore_bad)leaf^=2;
}
static int load32(void *opaque,uint64_t address,uint32_t *value) {
    assert(opaque==&window && address==0x400000+(requested&4095));++loads;
    leaf|=0x20;if(leaf_bad)leaf|=2;*value=0x12345678;return !load_fail;
}
static void fault(void *opaque) { assert(opaque==&window);++faults;longjmp(terminal,1); }
static void reset(unsigned engine,unsigned reg) {
    assert(qotom_graphics_state_address(engine,reg,&requested));
    saved=leaf=UINT64_C(0x8000000000400063);assert(lab_graphics_state_read_leaf(requested,&mapped));
    output=42;controls_count=invalidations=loads=faults=0;
    pre_bad=post_bad=load_fail=leaf_bad=restore_bad=0;
    window=(struct lab_graphics_state_window){&leaf,0x150000,0x400000,1,&window,
        controls,invalidate,load32,fault};
}
int main(void) {
    (void)pci_enumerate_segment;
    for(unsigned engine=0;engine<3;++engine)for(unsigned reg=0;reg<5;++reg) {
        reset(engine,reg);assert(lab_graphics_state_window_read(&window,requested,&output));
        assert(output==0x12345678 && leaf==saved && controls_count==2 &&
               invalidations==2 && loads==1 && !faults);
    }
    reset(0,0);load_fail=1;assert(!lab_graphics_state_window_read(&window,requested,&output));
    assert(output==42 && leaf==saved && invalidations==2);
    reset(0,0);pre_bad=1;assert(!lab_graphics_state_window_read(&window,requested,&output));
    assert(!loads && !invalidations && output==42);
    reset(0,0);window.armed=0;assert(!lab_graphics_state_window_read(&window,requested,&output));
    reset(0,0);assert(!lab_graphics_state_window_read(NULL,requested,&output));
    assert(!lab_graphics_state_window_read(&window,requested,NULL));
    assert(!lab_graphics_state_window_read(&window,QOTOM_GRAPHICS_BAR0,&output));
    for(unsigned which=0;which<3;++which) {
        reset(0,0);if(which==0)post_bad=1;if(which==1)leaf_bad=1;if(which==2)restore_bad=1;
        if(!setjmp(terminal)) {
            (void)lab_graphics_state_window_read(&window,requested,&output);assert(!"interference returned");
        }
        assert(faults==1 && (which==2?leaf!=saved:leaf==saved));
    }
    uint64_t value=42;assert(!lab_graphics_state_read_leaf(UINT64_MAX,&value) && value==42);
    assert(!lab_graphics_state_read_leaf(requested,NULL));
    puts("PASS graphics MMIO window: exact three pages, read-only UC mapping, cleanup and terminal interference");
}
