#include <assert.h>
#include <stdio.h>
#include <string.h>
#include "qotom-realtek-bme-arm.h"
static uint64_t root[512],pdpt[512],pd[512],pt[4096];
static unsigned stores,invalidations,controls_count,reject_control;
static int controls(void *context,struct lab_ecam_controls *out) {
    (void)context;++controls_count;
    *out=(struct lab_ecam_controls){0x0007040600070406,0x80010001,0x100000,0x20,0xd00,2};
    if(controls_count==reject_control)out->cr3^=4096;
    return 1;
}
static void invalidate(void *context,uint64_t address){(void)context;(void)address;++invalidations;}
static int store(void *context,uint64_t address,uint16_t value) {
    (void)context;(void)address;(void)value;++stores;return 0;
}
static void fault(void *context){(void)context;assert(0);}
static void run(uint8_t bus) {
    memset(root,0,sizeof root);memset(pdpt,0,sizeof pdpt);memset(pd,0,sizeof pd);
    struct lab_ecam_root_view view={root,pdpt,pd,pt,0x100000,0x101000,0x102000,0x103000};
    root[0]=view.pdpt_address|7;pdpt[0]=view.pd_address|7;
    for(unsigned i=0;i<8;++i)pd[i]=(view.pt_address+i*4096)|7;
    for(unsigned i=0;i<4096;++i)pt[i]=((uint64_t)i*4096)|UINT64_C(0x8000000000000003);
    uint32_t bar=(uint32_t)qotom_realtek_bar(bus);
    struct pci_enumeration_header endpoint={.bus=bus,.words={
        [0]=0x816810ec,[1]=0x00100007,[2]=0x02000007,[3]=16,
        [6]=bar|4,[8]=(bar-0x4000)|12}};
    struct pci_enumeration_header bridge={.device=28,.function=bus-1,.words={
        [0]=bus==1?0x0f488086:0x0f4c8086,[1]=0x00100007,[2]=0x0604000e,
        [3]=0x00810010,[6]=(bus<<16)|(bus<<8),
        [8]=bus==1?0xd080d080:0xd060d060,[9]=0x0001fff1,[13]=0x40}};
    struct qotom_rootport_bme_result route={1,7,3};
    struct qotom_realtek_state prior={0x2f900d00,0,0,0x0002ff0e,0,0x2f900d00};
    struct lab_realtek_bme_window window={.controls=controls,.invalidate=invalidate,
        .store16=store,.fault=fault};
#define ARM() lab_realtek_bme_arm(&window,&view,lab_ecam_expected_tables, \
        LAB_ECAM_FIRMWARE_TABLE_COUNT,0x200000,&endpoint,&bridge, \
        QOTOM_ROOTPORT_OK,&route,QOTOM_REALTEK_OK,&prior)
#define CLEARED() (!window.armed && !window.leaf && !window.root && \
        !window.window && !window.bus)
    controls_count=reject_control=0;
    assert(ARM() && window.armed && window.bus==bus && window.leaf==&pt[512]);
    for(unsigned target=1;target<=3;target+=2)for(unsigned i=0;i<4096;++i) {
        assert(ARM());uint64_t saved=pt[i];pt[i]=(UINT64_C(0xe0000000)+((uint64_t)target<<20))|1;
        assert(!ARM() && CLEARED());pt[i]=saved;
    }
    const unsigned words[8]={0,1,2,3,6,7,8,9};
    const uint32_t masks[8]={UINT32_MAX,65535,UINT32_MAX,0x00ff0000,
        UINT32_MAX,UINT32_MAX,UINT32_MAX,UINT32_MAX};
    for(unsigned n=0;n<8;++n)for(unsigned bit=0;bit<32;++bit) {
        assert(ARM());endpoint.words[words[n]]^=UINT32_C(1)<<bit;
        if(masks[n]&(UINT32_C(1)<<bit))assert(!ARM() && CLEARED());else assert(ARM());
        endpoint.words[words[n]]^=UINT32_C(1)<<bit;
    }
    for(unsigned field=0;field<3;++field)for(unsigned bit=0;bit<32;++bit) {
        assert(ARM());((uint32_t *)&route)[field]^=UINT32_C(1)<<bit;
        assert(!ARM() && CLEARED());((uint32_t *)&route)[field]^=UINT32_C(1)<<bit;
    }
    for(unsigned status=1;status<=8;++status) {
        assert(ARM());assert(!lab_realtek_bme_arm(&window,&view,lab_ecam_expected_tables,
            LAB_ECAM_FIRMWARE_TABLE_COUNT,0x200000,&endpoint,&bridge,status,&route,
            QOTOM_REALTEK_OK,&prior) && CLEARED());
    }
    for(unsigned status=1;status<=9;++status) {
        assert(ARM());assert(!lab_realtek_bme_arm(&window,&view,lab_ecam_expected_tables,
            LAB_ECAM_FIRMWARE_TABLE_COUNT,0x200000,&endpoint,&bridge,QOTOM_ROOTPORT_OK,
            &route,status,&prior) && CLEARED());
    }
    for(unsigned n=1;n<=2;++n) {
        assert(ARM());reject_control=controls_count+n;assert(!ARM() && CLEARED());reject_control=0;
    }
    assert(ARM());root[1]=7;assert(!ARM() && CLEARED());root[1]=0;
    struct lab_ecam_firmware_table changed[LAB_ECAM_FIRMWARE_TABLE_COUNT];
    memcpy(changed,lab_ecam_expected_tables,sizeof changed);changed[0].address^=4;
    assert(ARM());assert(!lab_realtek_bme_arm(&window,&view,changed,
        LAB_ECAM_FIRMWARE_TABLE_COUNT,0x200000,&endpoint,&bridge,QOTOM_ROOTPORT_OK,
        &route,QOTOM_REALTEK_OK,&prior) && CLEARED());
    assert(ARM());window.controls=NULL;assert(!ARM() && CLEARED());window.controls=controls;
    assert(ARM());window.invalidate=NULL;assert(!ARM() && CLEARED());window.invalidate=invalidate;
    assert(ARM());window.store16=NULL;assert(!ARM() && CLEARED());window.store16=store;
    assert(ARM());window.fault=NULL;assert(!ARM() && CLEARED());window.fault=fault;
    assert(ARM());assert(!lab_realtek_bme_arm(&window,NULL,lab_ecam_expected_tables,
        LAB_ECAM_FIRMWARE_TABLE_COUNT,0x200000,&endpoint,&bridge,QOTOM_ROOTPORT_OK,
        &route,QOTOM_REALTEK_OK,&prior) && CLEARED());
    assert(!lab_realtek_bme_arm(NULL,&view,lab_ecam_expected_tables,
        LAB_ECAM_FIRMWARE_TABLE_COUNT,0x200000,&endpoint,&bridge,QOTOM_ROOTPORT_OK,
        &route,QOTOM_REALTEK_OK,&prior));
    assert(!stores && !invalidations);
#undef ARM
#undef CLEARED
}
int main(void) {
    (void)pci_enumerate_segment;run(1);run(3);
    puts("PASS Realtek BME arm: both endpoints, every ECAM alias, route/state binding, rejected rearm and no device access");
}
