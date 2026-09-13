#include <assert.h>
#include <stdio.h>
#include <string.h>
#include "qotom-txe-bme-arm.h"
static uint64_t root[512],pdpt[512],pd[512],pt[4096];
static unsigned stores,invalidations,controls_count,reject_control;
static int controls(void *p,struct lab_ecam_controls *out) {
    (void)p;++controls_count;
    *out=(struct lab_ecam_controls){0x0007040600070406,0x80010001,0x100000,0x20,0xd00,2};
    if(controls_count==reject_control)out->cr3^=4096;
    return 1;
}
static void invalidate(void *p,uint64_t a){(void)p;(void)a;++invalidations;}
static int store(void *p,uint64_t a,uint16_t v){(void)p;(void)a;(void)v;++stores;return 0;}
static void fault(void *p){(void)p;assert(0);}
int main(void) {
    (void)pci_enumerate_segment;
    memset(root,0,sizeof root);memset(pdpt,0,sizeof pdpt);memset(pd,0,sizeof pd);
    struct lab_ecam_root_view view={root,pdpt,pd,pt,0x100000,0x101000,0x102000,0x103000};
    root[0]=view.pdpt_address|7;pdpt[0]=view.pd_address|7;
    for(unsigned i=0;i<8;++i)pd[i]=(view.pt_address+i*4096)|7;
    for(unsigned i=0;i<4096;++i)pt[i]=((uint64_t)i*4096)|UINT64_C(0x8000000000000003);
    struct pci_enumeration_header h={.device=26,.words={0x0f188086,0x00100106,
        0x1080000e,0x10,0xd0500000,0xd0400000,0,0,0,0,0,0x0f188086,0,0x80,0,0x1ff}};
    struct qotom_txe_status_observation prior={0x1f0000d5,0x69000000};
    struct lab_txe_bme_window w={.controls=controls,.invalidate=invalidate,
        .store16=store,.fault=fault};
#define ARM() lab_txe_bme_arm(&w,&view,lab_ecam_expected_tables, \
        LAB_ECAM_FIRMWARE_TABLE_COUNT,0x200000,&h,QOTOM_TXE_OK,&prior)
#define CLEARED() (!w.armed&&!w.leaf&&!w.root&&!w.window)
    assert(ARM()&&w.armed&&w.leaf==&pt[512]);
    for(unsigned i=0;i<4096;++i) {
        assert(ARM());uint64_t saved=pt[i];pt[i]=UINT64_C(0xe00d0001);
        assert(!ARM()&&CLEARED());pt[i]=saved;
    }
    const unsigned words[4]={0,1,2,3};
    const uint32_t masks[4]={UINT32_MAX,65535,UINT32_MAX,0x00ff0000};
    for(unsigned n=0;n<4;++n)for(unsigned bit=0;bit<32;++bit) {
        assert(ARM());h.words[words[n]]^=UINT32_C(1)<<bit;
        if(masks[n]&(UINT32_C(1)<<bit))assert(!ARM()&&CLEARED());else assert(ARM());
        h.words[words[n]]^=UINT32_C(1)<<bit;
    }
    for(unsigned s=1;s<=6;++s) {
        assert(ARM());assert(!lab_txe_bme_arm(&w,&view,lab_ecam_expected_tables,
            LAB_ECAM_FIRMWARE_TABLE_COUNT,0x200000,&h,(enum qotom_txe_status)s,&prior)&&CLEARED());
    }
    assert(ARM());assert(!lab_txe_bme_arm(&w,&view,lab_ecam_expected_tables,
        LAB_ECAM_FIRMWARE_TABLE_COUNT,0x200000,&h,QOTOM_TXE_OK,NULL)&&CLEARED());
    for(unsigned n=1;n<=2;++n){assert(ARM());reject_control=controls_count+n;
        assert(!ARM()&&CLEARED());reject_control=0;}
    assert(ARM());root[1]=7;assert(!ARM()&&CLEARED());root[1]=0;
    struct lab_ecam_firmware_table changed[LAB_ECAM_FIRMWARE_TABLE_COUNT];
    memcpy(changed,lab_ecam_expected_tables,sizeof changed);changed[0].address^=4;
    assert(ARM());assert(!lab_txe_bme_arm(&w,&view,changed,
        LAB_ECAM_FIRMWARE_TABLE_COUNT,0x200000,&h,QOTOM_TXE_OK,&prior)&&CLEARED());
    assert(ARM());w.controls=NULL;assert(!ARM()&&CLEARED());w.controls=controls;
    assert(ARM());w.invalidate=NULL;assert(!ARM()&&CLEARED());w.invalidate=invalidate;
    assert(ARM());w.store16=NULL;assert(!ARM()&&CLEARED());w.store16=store;
    assert(ARM());w.fault=NULL;assert(!ARM()&&CLEARED());w.fault=fault;
    assert(ARM());assert(!lab_txe_bme_arm(&w,NULL,lab_ecam_expected_tables,
        LAB_ECAM_FIRMWARE_TABLE_COUNT,0x200000,&h,QOTOM_TXE_OK,&prior)&&CLEARED());
    assert(!lab_txe_bme_arm(NULL,&view,lab_ecam_expected_tables,
        LAB_ECAM_FIRMWARE_TABLE_COUNT,0x200000,&h,QOTOM_TXE_OK,&prior));
    assert(!stores&&!invalidations);
    puts("PASS TXE BME arm: exact endpoint and prior, every ECAM alias and revoked rearm");
}
