#include <assert.h>
#include <stdio.h>
#include <string.h>
#include "qotom-rootport-bme-arm.h"
static uint64_t root[512],pdpt[512],pd[512],pt[4096];
static unsigned stores,invalidations,observations,reject_observation;
static int controls(void *ctx,struct lab_ecam_controls *out) {
    (void)ctx;++observations;
    *out=(struct lab_ecam_controls){0x0007040600070406,0x80010001,0x100000,0x20,0xd00,2};
    if(observations==reject_observation)out->cr3+=4096;
    return 1;
}
static void invalidate(void *ctx,uint64_t a){(void)ctx;(void)a;++invalidations;}
static int store(void *ctx,uint64_t a,uint16_t value){(void)ctx;(void)a;(void)value;++stores;return 0;}
static void fault(void *ctx){(void)ctx;assert(0);}
int main(void) {
    assert(pci_enumerate_segment(NULL,NULL,NULL).status==PCI_ENUMERATION_INVALID_ARGUMENT);
    struct lab_ecam_root_view v={root,pdpt,pd,pt,0x100000,0x101000,0x102000,0x103000};
    root[0]=v.pdpt_address|7;pdpt[0]=v.pd_address|7;
    for(unsigned i=0;i<8;++i)pd[i]=(v.pt_address+i*4096)|7;
    for(unsigned i=0;i<4096;++i)pt[i]=((uint64_t)i*4096)|UINT64_C(0x8000000000000003);
    struct pci_enumeration_header h={.device=28,.words={[0]=0x0f488086,[1]=7,[2]=0x0604000e,[3]=0x810010}};
    struct pci_express_observation prior={PCI_EXPRESS_OK,64,0x8000,0x100000};
    struct lab_rootport_bme_window w={.controls=controls,.invalidate=invalidate,.store16=store,.fault=fault};
#define ARM() lab_rootport_bme_arm(&w,&v,lab_ecam_expected_tables,LAB_ECAM_FIRMWARE_TABLE_COUNT,0x200000,&h,&prior)
#define CLEARED() (!w.armed && !w.leaf && !w.root && !w.window && !w.function)
    for(unsigned fn=0;fn<4;++fn){h.function=fn;h.words[0]=0x0f488086+fn*0x20000;
        assert(ARM() && w.armed && w.function==fn && w.leaf==&pt[512]);}
    h.function=0;h.words[0]=0x0f488086;
    for(unsigned fn=0;fn<4;++fn)for(unsigned i=0;i<4096;++i){
        assert(ARM());uint64_t saved=pt[i];pt[i]=(UINT64_C(0xe00e0000)+fn*4096)|1;
        assert(!ARM() && CLEARED());pt[i]=saved;
    }
    const uint32_t masks[]={UINT32_MAX,0xffff,UINT32_MAX,0xff0000};
    for(unsigned word=0;word<4;++word)for(unsigned bit=0;bit<32;++bit){
        assert(ARM());h.words[word]^=UINT32_C(1)<<bit;
        if(masks[word]&(UINT32_C(1)<<bit))assert(!ARM() && CLEARED());else assert(ARM());
        h.words[word]^=UINT32_C(1)<<bit;
    }
    for(unsigned bit=0;bit<32;++bit)for(unsigned field=0;field<2;++field){
        assert(ARM());uint32_t *p=field?&prior.device_control_status:&prior.device_capabilities;*p^=UINT32_C(1)<<bit;
        if(field && ((UINT32_C(1)<<bit)&0x1f0000))assert(ARM());else assert(!ARM() && CLEARED());
        *p^=UINT32_C(1)<<bit;
    }
    assert(ARM());prior.status=PCI_EXPRESS_NOT_PRESENT;assert(!ARM() && CLEARED());prior.status=PCI_EXPRESS_OK;
    assert(ARM());prior.offset=0;assert(!ARM() && CLEARED());prior.offset=64;
    assert(ARM());h.bus=1;assert(!ARM() && CLEARED());h.bus=0;
    assert(ARM());h.device=27;assert(!ARM() && CLEARED());h.device=28;
    assert(ARM());h.function=4;assert(!ARM() && CLEARED());h.function=0;
    for(unsigned n=1;n<=2;++n){assert(ARM());reject_observation=observations+n;assert(!ARM() && CLEARED());reject_observation=0;}
    assert(ARM());root[1]=7;assert(!ARM() && CLEARED());root[1]=0;
    struct lab_ecam_firmware_table changed[LAB_ECAM_FIRMWARE_TABLE_COUNT];
    memcpy(changed,lab_ecam_expected_tables,sizeof changed);changed[0].address^=4;
    assert(ARM());assert(!lab_rootport_bme_arm(&w,&v,changed,LAB_ECAM_FIRMWARE_TABLE_COUNT,0x200000,&h,&prior) && CLEARED());
    assert(ARM());w.controls=NULL;assert(!ARM() && CLEARED());w.controls=controls;
    assert(ARM());w.invalidate=NULL;assert(!ARM() && CLEARED());w.invalidate=invalidate;
    assert(ARM());w.store16=NULL;assert(!ARM() && CLEARED());w.store16=store;
    assert(ARM());w.fault=NULL;assert(!ARM() && CLEARED());w.fault=fault;
    assert(ARM());assert(!lab_rootport_bme_arm(&w,&v,lab_ecam_expected_tables,LAB_ECAM_FIRMWARE_TABLE_COUNT,0x200000,NULL,&prior) && CLEARED());
    assert(ARM());assert(!lab_rootport_bme_arm(&w,&v,lab_ecam_expected_tables,LAB_ECAM_FIRMWARE_TABLE_COUNT,0x200000,&h,NULL) && CLEARED());
    assert(ARM());assert(!lab_rootport_bme_arm(&w,NULL,lab_ecam_expected_tables,LAB_ECAM_FIRMWARE_TABLE_COUNT,0x200000,&h,&prior) && CLEARED());
    assert(!stores && !invalidations);puts("Root-port arm: four function bindings, ECAM aliases, failed rearm revocation and no device access PASS");
}
