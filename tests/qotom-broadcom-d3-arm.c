#include <assert.h>
#include <stdio.h>
#include <string.h>
#include "qotom-broadcom-d3-arm.h"

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
int main(void) {
    (void)pci_enumerate_segment;
    memset(root,0,sizeof root);memset(pdpt,0,sizeof pdpt);memset(pd,0,sizeof pd);
    struct lab_ecam_root_view view={root,pdpt,pd,pt,0x100000,0x101000,0x102000,0x103000};
    root[0]=view.pdpt_address|7;pdpt[0]=view.pd_address|7;
    for(unsigned i=0;i<8;++i)pd[i]=(view.pt_address+i*4096)|7;
    for(unsigned i=0;i<4096;++i)pt[i]=((uint64_t)i*4096)|UINT64_C(0x8000000000000003);
    struct pci_enumeration_header endpoint={.bus=2,.words={
        0x435314e4,0x00100006,0x02800001,0x10,0xd0700004,0,0,0,
        0,0,0,0x04d814e4,0,0x40,0,0x105}};
    struct pci_enumeration_header bridge={.device=28,.function=1,.words={
        0x0f4a8086,0x00100007,0x0604000e,0x00810010,0,0,0x00020200,
        0x200000f0,0xd070d070,0x0001fff1,0,0,0,0x40,0,0x00100205}};
    struct pci_capability_snapshot caps={.count=4,.headers={
        {0x40,0xce035801},{0x58,0x00784809},{0x48,0x0080d005},{0xd0,0x00010010}}};
    struct pci_express_observation pcie={PCI_EXPRESS_OK,0xd0,0x05908fa0,0x00190000};
    struct qotom_rootport_bme_result bme={1,7,3};
    struct qotom_pcie_pending_result pending={2,17};
    struct lab_broadcom_d3_window window={.controls=controls,.invalidate=invalidate,
        .store16=store,.fault=fault};
#define ARM() lab_broadcom_d3_arm(&window,&view,lab_ecam_expected_tables, \
        LAB_ECAM_FIRMWARE_TABLE_COUNT,0x200000,&endpoint,&bridge,&caps,&pcie, \
        QOTOM_ROOTPORT_OK,&bme,QOTOM_PCIE_PENDING_OK,&pending)
#define CLEARED() (!window.armed && !window.stage && !window.leaf && !window.root && !window.window)
    controls_count=reject_control=0;
    assert(ARM() && window.armed && !window.stage && window.leaf==&pt[512]);
    for(unsigned target=0;target<4;++target)for(unsigned i=0;i<4096;++i) {
        assert(ARM());uint64_t saved=pt[i];
        pt[i]=(UINT64_C(0xe0000000)+((uint64_t)target<<20))|1;
        assert(!ARM() && CLEARED());pt[i]=saved;
    }
    for(unsigned word=0;word<16;++word)for(unsigned bit=0;bit<32;++bit) {
        assert(ARM());endpoint.words[word]^=UINT32_C(1)<<bit;
        int relevant=word==0 || word==2 || word==4 || word==5 || word==11 || word==13 ||
            (word==1 && bit<16) || (word==3 && bit>=16 && bit<24);
        if(relevant)assert(!ARM() && CLEARED());else assert(ARM());
        endpoint.words[word]^=UINT32_C(1)<<bit;
    }
    for(unsigned word=0;word<16;++word)for(unsigned bit=0;bit<32;++bit) {
        assert(ARM());bridge.words[word]^=UINT32_C(1)<<bit;
        int relevant=word==0 || word==2 || word==6 || word==8 || word==9 || word==10 ||
            word==11 || (word==1&&bit<16) || (word==3&&bit>=16&&bit<24);
        if(relevant)assert(!ARM() && CLEARED());else assert(ARM());
        bridge.words[word]^=UINT32_C(1)<<bit;
    }
    for(unsigned i=0;i<4;++i)for(unsigned bit=0;bit<32;++bit) {
        assert(ARM());caps.headers[i].raw^=UINT32_C(1)<<bit;
        assert(!ARM() && CLEARED());caps.headers[i].raw^=UINT32_C(1)<<bit;
    }
    for(unsigned status=1;status<=8;++status) {
        assert(ARM());pcie.status=status;assert(!ARM() && CLEARED());pcie.status=PCI_EXPRESS_OK;
    }
    for(unsigned offset=0;offset<256;++offset)if(offset!=0xd0) {
        assert(ARM());pcie.offset=(uint8_t)offset;assert(!ARM() && CLEARED());pcie.offset=0xd0;
    }
    for(unsigned bit=0;bit<32;++bit) {
        assert(ARM());pcie.device_capabilities^=UINT32_C(1)<<bit;
        assert(!ARM() && CLEARED());pcie.device_capabilities^=UINT32_C(1)<<bit;
        assert(ARM());pcie.device_control_status^=UINT32_C(1)<<bit;
        assert(!ARM() && CLEARED());pcie.device_control_status^=UINT32_C(1)<<bit;
    }
    for(unsigned field=0;field<3;++field)for(unsigned bit=0;bit<32;++bit) {
        assert(ARM());((uint32_t *)&bme)[field]^=UINT32_C(1)<<bit;
        assert(!ARM() && CLEARED());((uint32_t *)&bme)[field]^=UINT32_C(1)<<bit;
    }
    for(unsigned field=0;field<2;++field)for(unsigned bit=0;bit<32;++bit) {
        assert(ARM());((uint32_t *)&pending)[field]^=UINT32_C(1)<<bit;
        int accepted=(field==0 && pending.polls>=2 && pending.polls<=100) ||
            (field==1 && pending.device_status==16);
        if(accepted)assert(ARM());else assert(!ARM() && CLEARED());
        ((uint32_t *)&pending)[field]^=UINT32_C(1)<<bit;
    }
    for(unsigned n=1;n<=2;++n) {
        assert(ARM());reject_control=controls_count+n;assert(!ARM() && CLEARED());reject_control=0;
    }
    assert(ARM());root[1]=7;assert(!ARM() && CLEARED());root[1]=0;
    struct lab_ecam_firmware_table changed[LAB_ECAM_FIRMWARE_TABLE_COUNT];
    memcpy(changed,lab_ecam_expected_tables,sizeof changed);changed[0].address^=4;
    assert(ARM());assert(!lab_broadcom_d3_arm(&window,&view,changed,
        LAB_ECAM_FIRMWARE_TABLE_COUNT,0x200000,&endpoint,&bridge,&caps,&pcie,
        QOTOM_ROOTPORT_OK,&bme,QOTOM_PCIE_PENDING_OK,&pending) && CLEARED());
    assert(ARM());window.controls=0;assert(!ARM() && CLEARED());window.controls=controls;
    assert(ARM());window.invalidate=0;assert(!ARM() && CLEARED());window.invalidate=invalidate;
    assert(ARM());window.store16=0;assert(!ARM() && CLEARED());window.store16=store;
    assert(ARM());window.fault=0;assert(!ARM() && CLEARED());window.fault=fault;
    assert(ARM());assert(!lab_broadcom_d3_arm(&window,0,lab_ecam_expected_tables,
        LAB_ECAM_FIRMWARE_TABLE_COUNT,0x200000,&endpoint,&bridge,&caps,&pcie,
        QOTOM_ROOTPORT_OK,&bme,QOTOM_PCIE_PENDING_OK,&pending) && CLEARED());
    assert(!lab_broadcom_d3_arm(0,&view,lab_ecam_expected_tables,
        LAB_ECAM_FIRMWARE_TABLE_COUNT,0x200000,&endpoint,&bridge,&caps,&pcie,
        QOTOM_ROOTPORT_OK,&bme,QOTOM_PCIE_PENDING_OK,&pending));
    assert(!stores && !invalidations);
    puts("PASS Broadcom D3 arm: exact endpoint/route/capability/quiet binding, aliases and rejected rearm");
}
