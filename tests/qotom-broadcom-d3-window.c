#include <assert.h>
#include <setjmp.h>
#include <stdio.h>
#include "qotom-broadcom-d3-window.h"

static struct lab_broadcom_d3_window w;
static uint64_t leaf,saved;
static unsigned stores,invalidations,controls_count;
static int pre_bad,post_bad,store_failed,leaf_bad,restore_bad;
static jmp_buf terminal;
static int controls(void *p,struct lab_ecam_controls *c) {
    assert(p==&w && !w.armed);++controls_count;
    *c=(struct lab_ecam_controls){0x0007040600070406,0x8001001f,0x150000,0x68,0xd00,2};
    if((controls_count&1?pre_bad:post_bad))c->cr3+=4096;
    return 1;
}
static void invalidate(void *p,uint64_t address) {
    assert(p==&w && address==0x400000 && !w.armed);++invalidations;
    if(invalidations&1)assert(leaf==UINT64_C(0x80000000e020001b));
    else {assert(leaf==saved);if(restore_bad)leaf^=2;}
}
static int store16(void *p,uint64_t address,uint16_t value) {
    assert(p==&w && !w.armed);++stores;
    if(stores==1)assert(address==0x400004 && value==0);
    else assert(stores==2 && address==0x400044 && value==QOTOM_BROADCOM_PMCSR_D3HOT);
    leaf|=0x60;if(leaf_bad)leaf^=4;return !store_failed;
}
static void fault(void *p) {assert(p==&w && !w.armed);longjmp(terminal,1);}
static void reset(void) {
    leaf=saved=UINT64_C(0x8000000000400063);
    stores=invalidations=controls_count=0;
    pre_bad=post_bad=store_failed=leaf_bad=restore_bad=0;
    w=(struct lab_broadcom_d3_window){&leaf,0x150000,0x400000,1,0,
        &w,controls,invalidate,store16,fault};
}
static int command(void) {return lab_broadcom_d3_window_write(&w,2,0,0,4,0);}
static int d3(void) {return lab_broadcom_d3_window_write(&w,2,0,0,0x44,QOTOM_BROADCOM_PMCSR_D3HOT);}
int main(void) {
    (void)pci_enumerate_segment;
    reset();assert(command() && w.armed==1 && w.stage==1 && stores==1);
    assert(d3() && !w.armed && w.stage==1 && stores==2 && invalidations==4 && leaf==saved);
    assert(!d3() && stores==2);
    reset();assert(!d3() && !w.armed && !stores && !controls_count);
    reset();store_failed=1;assert(!command() && !w.armed && stores==1 && leaf==saved);
    reset();assert(command());store_failed=1;assert(!d3() && !w.armed && stores==2);
    for(unsigned field=0;field<5;++field)for(unsigned value=0;value<256;++value) {
        unsigned valid[]={2,0,0,4,0};if(value==valid[field])continue;
        reset();valid[field]=value;
        assert(!lab_broadcom_d3_window_write(&w,valid[0],valid[1],valid[2],valid[3],valid[4]));
        assert(!w.armed && !stores && !controls_count);
    }
    for(unsigned value=1;value<65536;++value) {
        reset();assert(!lab_broadcom_d3_window_write(&w,2,0,0,4,(uint16_t)value));
        assert(!w.armed && !stores);
    }
    for(volatile unsigned which=0;which<3;++which) {
        reset();post_bad=which==0;leaf_bad=which==1;restore_bad=which==2;
        if(!setjmp(terminal)){(void)command();assert(!"interference returned");}
        assert(stores==1 && !w.armed && invalidations==2);
    }
    reset();assert(command());controls_count=0;
    for(volatile unsigned which=0;which<3;++which) {
        if(which){reset();assert(command());controls_count=0;}
        post_bad=which==0;leaf_bad=which==1;restore_bad=which==2;
        if(!setjmp(terminal)){(void)d3();assert(!"interference returned");}
        assert(stores==2 && !w.armed);
    }
    reset();w.armed=0;assert(!command());
    assert(!lab_broadcom_d3_window_write(NULL,2,0,0,4,0));
    for(unsigned missing=0;missing<5;++missing) {
        reset();
        if(missing==0)w.controls=0;
        if(missing==1)w.invalidate=0;
        if(missing==2)w.store16=0;
        if(missing==3)w.fault=0;
        if(missing==4)w.leaf=0;
        assert(!command() && !w.armed && !stores);
    }
    const uint64_t bad[]={0,0x400001,0x1000000,UINT64_MAX};
    for(unsigned i=0;i<4;++i){reset();w.window=bad[i];assert(!command() && !stores);}
    puts("PASS Broadcom D3 window: exact ordered Command/PMCSR stores and terminal interference");
}
