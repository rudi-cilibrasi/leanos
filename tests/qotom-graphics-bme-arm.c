#include <assert.h>
#include <stdio.h>
#include <string.h>
#include "qotom-graphics-bme-arm.h"
static uint64_t root[512],pdpt[512],pd[512],pt[4096];
static unsigned stores,invalidations,controls_count,reject_control;
static int controls(void *context,struct lab_ecam_controls *out) {
    (void)context;++controls_count;
    *out=(struct lab_ecam_controls){0x0007040600070406,0x80010001,0x100000,0x20,0xd00,2};
    if(controls_count==reject_control)out->cr3^=4096;
    return 1;
}
static void invalidate(void *context,uint64_t address){(void)context;(void)address;++invalidations;}
static int store(void *context,uint64_t address,uint16_t value){(void)context;(void)address;(void)value;++stores;return 0;}
static void fault(void *context){(void)context;assert(0);}
int main(void) {
    (void)pci_enumerate_segment;
    memset(root,0,sizeof root);memset(pdpt,0,sizeof pdpt);memset(pd,0,sizeof pd);
    struct lab_ecam_root_view view={root,pdpt,pd,pt,0x100000,0x101000,0x102000,0x103000};
    root[0]=view.pdpt_address|7;pdpt[0]=view.pd_address|7;
    for(unsigned i=0;i<8;++i)pd[i]=(view.pt_address+i*4096)|7;
    for(unsigned i=0;i<4096;++i)pt[i]=((uint64_t)i*4096)|UINT64_C(0x8000000000000003);
    struct pci_enumeration_header h={.device=2,.words={0x0f318086,0x00100007,
        0x0300000e,0,0xd0000000,0,0xc0000008,0,0x0000f081,0,0,0x0f318086,
        0,0xd0,0,0x110}};
    struct qotom_graphics_state prior={0};
    for(unsigned s=0;s<2;++s)for(unsigned e=0;e<3;++e)prior.words[s*15+e*5+4]=0x200;
    struct lab_graphics_bme_window w={.controls=controls,.invalidate=invalidate,
        .store16=store,.fault=fault};
#define ARM() lab_graphics_bme_arm(&w,&view,lab_ecam_expected_tables, \
        LAB_ECAM_FIRMWARE_TABLE_COUNT,0x200000,&h,QOTOM_GRAPHICS_OK,&prior)
#define CLEARED() (!w.armed && !w.leaf && !w.root && !w.window)
    assert(ARM() && w.armed && w.leaf==&pt[512]);
    for(unsigned i=0;i<4096;++i) {
        assert(ARM());uint64_t saved=pt[i];pt[i]=UINT64_C(0xe0010001);
        assert(!ARM() && CLEARED());pt[i]=saved;
    }
    const unsigned words[11]={0,1,2,3,4,5,6,7,8,11,13};
    const uint32_t masks[11]={UINT32_MAX,65535,UINT32_MAX,0x00ff0000,
        UINT32_MAX,UINT32_MAX,UINT32_MAX,UINT32_MAX,UINT32_MAX,UINT32_MAX,UINT32_MAX};
    for(unsigned n=0;n<11;++n)for(unsigned bit=0;bit<32;++bit) {
        assert(ARM());h.words[words[n]]^=UINT32_C(1)<<bit;
        if(masks[n]&(UINT32_C(1)<<bit))assert(!ARM()&&CLEARED());else assert(ARM());
        h.words[words[n]]^=UINT32_C(1)<<bit;
    }
    for(unsigned status=1;status<=7;++status) {
        assert(ARM());assert(!lab_graphics_bme_arm(&w,&view,lab_ecam_expected_tables,
            LAB_ECAM_FIRMWARE_TABLE_COUNT,0x200000,&h,status,&prior)&&CLEARED());
    }
    for(unsigned mutation=0;mutation<4;++mutation) {
        assert(ARM());unsigned index=mutation==0?0:mutation==1?1:mutation==2?3:15;
        prior.words[index]^=1;
        assert(!ARM()&&CLEARED());prior.words[index]^=1;
    }
    for(unsigned n=1;n<=2;++n){assert(ARM());reject_control=controls_count+n;
        assert(!ARM()&&CLEARED());reject_control=0;}
    assert(ARM());root[1]=7;assert(!ARM()&&CLEARED());root[1]=0;
    struct lab_ecam_firmware_table changed[LAB_ECAM_FIRMWARE_TABLE_COUNT];
    memcpy(changed,lab_ecam_expected_tables,sizeof changed);changed[0].address^=4;
    assert(ARM());assert(!lab_graphics_bme_arm(&w,&view,changed,
        LAB_ECAM_FIRMWARE_TABLE_COUNT,0x200000,&h,QOTOM_GRAPHICS_OK,&prior)&&CLEARED());
    assert(ARM());w.controls=NULL;assert(!ARM()&&CLEARED());w.controls=controls;
    assert(ARM());w.invalidate=NULL;assert(!ARM()&&CLEARED());w.invalidate=invalidate;
    assert(ARM());w.store16=NULL;assert(!ARM()&&CLEARED());w.store16=store;
    assert(ARM());w.fault=NULL;assert(!ARM()&&CLEARED());w.fault=fault;
    assert(ARM());assert(!lab_graphics_bme_arm(&w,NULL,lab_ecam_expected_tables,
        LAB_ECAM_FIRMWARE_TABLE_COUNT,0x200000,&h,QOTOM_GRAPHICS_OK,&prior)&&CLEARED());
    assert(!lab_graphics_bme_arm(NULL,&view,lab_ecam_expected_tables,
        LAB_ECAM_FIRMWARE_TABLE_COUNT,0x200000,&h,QOTOM_GRAPHICS_OK,&prior));
    assert(!stores && !invalidations);
    puts("PASS graphics BME arm: exact endpoint, quiet prior, every ECAM alias and revoked rearm");
}
