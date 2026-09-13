#include <assert.h>
#include <setjmp.h>
#include <stdio.h>
#include "qotom-txe-bme-window.h"
static struct lab_txe_bme_window w;
static uint64_t leaf,saved;
static unsigned stores,invalidations,controls_count;
static int pre_bad,post_bad,store_failed,leaf_bad,restore_bad;
static jmp_buf terminal;
static int controls(void *p,struct lab_ecam_controls *c) {
    assert(p==&w && !w.armed);++controls_count;
    *c=(struct lab_ecam_controls){0x0007040600070406,0x8001001f,0x150000,0x68,0xd00,2};
    if((controls_count==1&&pre_bad)||(controls_count==2&&post_bad))c->cr3+=4096;
    if(controls_count==2)assert(leaf==saved && invalidations==2);
    return 1;
}
static void invalidate(void *p,uint64_t a) {
    assert(p==&w && a==0x400000 && !w.armed);++invalidations;
    if(invalidations==1)assert(leaf==UINT64_C(0x80000000e00d001b) && !stores);
    else {assert(invalidations==2 && leaf==saved && stores==1);if(restore_bad)leaf^=2;}
}
static int store16(void *p,uint64_t a,uint16_t v) {
    assert(p==&w && a==0x400004 && v==0x102 && !w.armed);
    assert(!stores && invalidations==1);++stores;leaf|=0x60;
    if(leaf_bad)leaf^=4;
    return !store_failed;
}
static void fault(void *p) {assert(p==&w && invalidations==2 && !w.armed);longjmp(terminal,1);}
static void reset(void) {
    leaf=saved=UINT64_C(0x8000000000400063);stores=invalidations=controls_count=0;
    pre_bad=post_bad=store_failed=leaf_bad=restore_bad=0;
    w=(struct lab_txe_bme_window){&leaf,0x150000,0x400000,1,&w,
        controls,invalidate,store16,fault};
}
static int request(void){return lab_txe_bme_window_write(&w,0,26,0,4,0x102);}
int main(void) {
    reset();assert(request() && stores==1 && leaf==saved && controls_count==2);
    assert(!request() && stores==1);
    reset();store_failed=1;assert(!request() && stores==1 && leaf==saved);
    reset();pre_bad=1;assert(!request() && !stores && !invalidations);
    reset();leaf^=4;assert(!request() && !stores && !invalidations);
    for(unsigned field=0;field<5;++field)for(unsigned value=0;value<256;++value) {
        unsigned valid[5]={0,26,0,4,0x102};if(value==(valid[field]&255))continue;
        reset();valid[field]=value;
        assert(!lab_txe_bme_window_write(&w,(uint8_t)valid[0],(uint8_t)valid[1],
            (uint8_t)valid[2],(uint8_t)valid[3],(uint16_t)valid[4]));
        assert(!w.armed&&!stores&&!controls_count);
    }
    for(unsigned v=0;v<65536;++v)if(v!=0x102) {
        reset();assert(!lab_txe_bme_window_write(&w,0,26,0,4,(uint16_t)v));
        assert(!w.armed&&!stores&&!controls_count);
    }
    for(unsigned which=0;which<3;++which) {
        reset();post_bad=which==0;leaf_bad=which==1;restore_bad=which==2;
        if(!setjmp(terminal)){(void)request();assert(!"interference returned");}
        assert(stores==1&&!w.armed&&invalidations==2);
    }
    reset();w.armed=0;assert(!request());
    assert(!lab_txe_bme_window_write(NULL,0,26,0,4,0x102));
    for(unsigned missing=0;missing<5;++missing) {
        reset();
        if(!missing)w.controls=NULL;
        if(missing==1)w.invalidate=NULL;
        if(missing==2)w.store16=NULL;
        if(missing==3)w.fault=NULL;
        if(missing==4)w.leaf=NULL;
        assert(!request()&&!stores&&!controls_count&&!invalidations);
    }
    const uint64_t bad[4]={0,0x400001,0x1000000,UINT64_MAX};
    for(unsigned i=0;i<4;++i){reset();w.window=bad[i];assert(!request()&&!controls_count);}
    puts("PASS TXE BME window: exact 0102 word request, consumed authority, restore and terminal interference");
}
