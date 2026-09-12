#include <assert.h>
#include <stdio.h>
#include "qotom-xhci-semaphore-arm.h"
static uint64_t root[512],pdpt[512],pd[512],pt[4096];
static unsigned loads, invalidations;
static int controls(void *ctx,struct lab_ecam_controls *out) {
    (void)ctx;
    *out=(struct lab_ecam_controls){0x0007040600070406,0x80010001,0x100000,0x20,0xd00,2};return 1;
}
static void invalidate(void *ctx,uint64_t a) {(void)ctx;(void)a;++invalidations;}
static int load(void *ctx,uint64_t a,uint32_t v) {(void)ctx;(void)a;(void)v;++loads;return 0;}
static void fault(void *ctx) {(void)ctx;assert(0);}
int main(void) {
    assert(pci_enumerate_segment(NULL,NULL,NULL).status==PCI_ENUMERATION_INVALID_ARGUMENT);
    struct lab_ecam_root_view v={root,pdpt,pd,pt,0x100000,0x101000,0x102000,0x103000};
    root[0]=v.pdpt_address|7;pdpt[0]=v.pd_address|7;
    for(unsigned i=0;i<8;++i)pd[i]=(v.pt_address+i*4096)|7;
    for(unsigned i=0;i<4096;++i)pt[i]=((uint64_t)i*4096)|UINT64_C(0x8000000000000003);
    struct pci_enumeration_header h={.device=20,.words={0x0f358086,0x406,0x0c03300e,0,0xd0900004}};
    struct qotom_xhci_capabilities caps = {{0x01000080,0x07000820,0x84000054,
        0x0200000a,0x200077c1,0x3000,0x2000}};
    struct qotom_xhci_legacy prior={.count=6,.legacy_offset=0x8460,.control_status=0x2001,
        .headers={{0x8000,0x02000802},{0x8020,0x03000802},{0x8040,0x00010cc1},
                  {0x8070,0x0000fcc0},{0x8460,0x00010801},{0x8480,0x0005000a}}};
    enum qotom_xhci_legacy_status status=QOTOM_XHCI_LEGACY_OK;
    struct lab_xhci_semaphore_window w={.controls=controls,.invalidate=invalidate,.store32=load,.fault=fault};
#define ARM() lab_xhci_semaphore_arm(&w,&v,lab_ecam_expected_tables,LAB_ECAM_FIRMWARE_TABLE_COUNT,0x200000,&h,&caps,status,&prior)
    assert(ARM() && w.armed && w.leaf==&pt[512]);
    for(unsigned i=0;i<4096;++i) {
        uint64_t saved=pt[i];pt[i]=QOTOM_XHCI_BAR|1;
        assert(!ARM() && !w.armed && !w.leaf && !w.root && !w.window);
        pt[i]=saved;
    }
    assert(ARM());
    h.words[4]^=0x1000;assert(!ARM() && !w.armed);h.words[4]^=0x1000;
    h.words[1]&=~2u;assert(!ARM() && !w.armed);h.words[1]|=2;
    assert(ARM());root[1]=7;assert(!ARM() && !w.armed);root[1]=0;
    for(unsigned page=0;page<16;++page) {
        uint64_t saved=pt[600];pt[600]=(QOTOM_XHCI_BAR+page*4096)|1;
        assert(!ARM() && !w.armed);pt[600]=saved;
    }
    for(unsigned bit=0;bit<32;++bit) {
        assert(ARM());h.words[5]=UINT32_C(1)<<bit;assert(!ARM() && !w.armed);h.words[5]=0;
    }
    for(unsigned i=0;i<4096;++i) {
        uint64_t saved=pt[i];pt[i]=UINT64_C(0xe00a0001);
        assert(!ARM() && !w.armed);pt[i]=saved;
    }
    for (unsigned word=0; word<7; ++word) {
        for (unsigned bit=0; bit<32; ++bit) {
            assert(ARM());
            caps.words[word] ^= UINT32_C(1)<<bit;
            assert(!ARM() && !w.armed && !w.leaf && !w.root && !w.window);
            caps.words[word] ^= UINT32_C(1)<<bit;
        }
    }
    assert(ARM());
    assert(!lab_xhci_semaphore_arm(&w,&v,lab_ecam_expected_tables,
        LAB_ECAM_FIRMWARE_TABLE_COUNT,0x200000,&h,NULL,status,&prior));
    assert(!w.armed && !w.leaf && !w.root && !w.window);
    for(unsigned entry=0;entry<6;++entry)for(unsigned bit=0;bit<32;++bit) {
        assert(ARM());prior.headers[entry].raw^=UINT32_C(1)<<bit;
        assert(!ARM() && !w.armed);prior.headers[entry].raw^=UINT32_C(1)<<bit;
        assert(ARM());prior.headers[entry].offset^=UINT32_C(1)<<bit;
        assert(!ARM() && !w.armed);prior.headers[entry].offset^=UINT32_C(1)<<bit;
    }
    for(unsigned bit=0;bit<32;++bit) {
        assert(ARM());prior.control_status^=UINT32_C(1)<<bit;
        assert(!ARM() && !w.armed);prior.control_status^=UINT32_C(1)<<bit;
        assert(ARM());prior.legacy_offset^=UINT32_C(1)<<bit;
        assert(!ARM() && !w.armed);prior.legacy_offset^=UINT32_C(1)<<bit;
    }
    for(unsigned count=0;count<=49;++count) {
        if(count==6)continue;
        assert(ARM());prior.count=count;
        assert(!ARM() && !w.armed);prior.count=6;
    }
    for(unsigned i=1;i<=QOTOM_XHCI_LEGACY_FINAL;++i) {
        assert(ARM());status=(enum qotom_xhci_legacy_status)i;
        assert(!ARM() && !w.armed);status=QOTOM_XHCI_LEGACY_OK;
    }
    assert(ARM());
    assert(!lab_xhci_semaphore_arm(&w,&v,lab_ecam_expected_tables,
        LAB_ECAM_FIRMWARE_TABLE_COUNT,0x200000,&h,&caps,status,NULL));
    assert(!w.armed && !w.leaf && !w.root && !w.window);
    assert(!loads && !invalidations);
    puts("PASS xHCI semaphore arm: exact BAR, all 4096 aliases rejected, no device access, failed rearm revoked");
}
