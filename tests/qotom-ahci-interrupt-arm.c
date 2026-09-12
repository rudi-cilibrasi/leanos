#include <assert.h>
#include <stdio.h>
#include <string.h>
#include "qotom-ahci-interrupt-arm.h"
static uint64_t root[512],pdpt[512],pd[512],pt[4096];
static unsigned stores, invalidations;
static int controls(void *ctx,struct lab_ecam_controls *out) {
    (void)ctx;
    *out=(struct lab_ecam_controls){0x0007040600070406,0x80010001,0x100000,0x20,0xd00,2};return 1;
}
static void invalidate(void *ctx,uint64_t a) {(void)ctx;(void)a;++invalidations;}
static int store(void *ctx,uint64_t a,uint32_t v) {(void)ctx;(void)a;(void)v;++stores;return 0;}
static void fault(void *ctx) {(void)ctx;assert(0);}
int main(void) {
    assert(pci_enumerate_segment(NULL,NULL,NULL).status==PCI_ENUMERATION_INVALID_ARGUMENT);
    struct lab_ecam_root_view v={root,pdpt,pd,pt,0x100000,0x101000,0x102000,0x103000};
    root[0]=v.pdpt_address|7;pdpt[0]=v.pd_address|7;
    for(unsigned i=0;i<8;++i)pd[i]=(v.pt_address+i*4096)|7;
    for(unsigned i=0;i<4096;++i)pt[i]=((uint64_t)i*4096)|UINT64_C(0x8000000000000003);
    struct pci_enumeration_header h={.device=19,.words={[0]=0x0f238086,[1]=7,[2]=0x0106010e,[9]=0xd0916000}};
    struct qotom_ahci_capabilities prior={0xc720ff01,0x80000002,2,0x10300,0x38};
    struct qotom_ahci_port stopped={6,0,0x50,0x123,0,0,6};
    struct lab_ahci_interrupt_window w={.controls=controls,.invalidate=invalidate,.store32=store,.fault=fault};
#define ARM() lab_ahci_interrupt_arm(&w,&v,lab_ecam_expected_tables,LAB_ECAM_FIRMWARE_TABLE_COUNT,0x200000,&h,QOTOM_AHCI_OK,&prior,QOTOM_AHCI_PORT_OK,&stopped)
    assert(ARM() && w.armed && w.leaf==&pt[512]);
    for(unsigned i=0;i<4096;++i) {
        uint64_t saved=pt[i];pt[i]=QOTOM_AHCI_BAR|1;
        assert(!ARM() && !w.armed && !w.leaf && !w.root && !w.window);
        pt[i]=saved;
    }
    assert(ARM());
    h.words[9]^=0x1000;assert(!ARM() && !w.armed);h.words[9]^=0x1000;
    h.words[1]&=~2u;assert(!ARM() && !w.armed);h.words[1]|=2;
    assert(ARM());root[1]=7;assert(!ARM() && !w.armed);root[1]=0;
    const unsigned words[]={0,1,2,3,9};
    const uint32_t masks[]={UINT32_MAX,2,UINT32_MAX,0x00ff0000,UINT32_MAX};
    for(unsigned i=0;i<5;++i)for(unsigned bit=0;bit<32;++bit) {
        assert(ARM());h.words[words[i]]^=1u<<bit;
        if(masks[i]&(1u<<bit)) assert(!ARM() && !w.armed && !w.leaf && !w.root && !w.window);
        else assert(ARM());
        h.words[words[i]]^=1u<<bit;
    }
    struct lab_ecam_firmware_table changed[LAB_ECAM_FIRMWARE_TABLE_COUNT];
    memcpy(changed,lab_ecam_expected_tables,sizeof changed);changed[0].address^=4;
    assert(ARM());
    assert(!lab_ahci_interrupt_arm(&w,&v,changed,LAB_ECAM_FIRMWARE_TABLE_COUNT,0x200000,&h,QOTOM_AHCI_OK,&prior,QOTOM_AHCI_PORT_OK,&stopped));
    assert(!w.armed && !w.leaf && !w.root && !w.window);
    assert(ARM());w.store32=NULL;assert(!ARM() && !w.armed && !w.leaf);w.store32=store;
    assert(ARM());h.bus=1;assert(!ARM() && !w.armed);h.bus=0;
    assert(ARM());h.device=20;assert(!ARM() && !w.armed);h.device=19;
    assert(ARM());h.function=1;assert(!ARM() && !w.armed);h.function=0;
    uint32_t *fields[]={&prior.capability,&prior.control,&prior.ports,&prior.version,&prior.extended};
    for(unsigned i=0;i<5;++i)for(unsigned bit=0;bit<32;++bit) {
        assert(ARM());*fields[i]^=1u<<bit;
        assert(!ARM() && !w.armed && !w.leaf && !w.root && !w.window);
        *fields[i]^=1u<<bit;
    }
    for(unsigned status=1;status<=6;++status) {
        assert(ARM());assert(!lab_ahci_interrupt_arm(&w,&v,lab_ecam_expected_tables,
            LAB_ECAM_FIRMWARE_TABLE_COUNT,0x200000,&h,status,&prior,QOTOM_AHCI_PORT_OK,&stopped));
        assert(!w.armed && !w.leaf && !w.root && !w.window);
    }
    uint32_t *port_fields[]={&stopped.command_before,&stopped.interrupt_enable,
        &stopped.task_file,&stopped.sata_status,&stopped.active,&stopped.issued,&stopped.command_after};
    for(unsigned i=0;i<7;++i)for(unsigned bit=0;bit<32;++bit) {
        assert(ARM());*port_fields[i]^=1u<<bit;
        assert(!ARM() && !w.armed && !w.leaf && !w.root && !w.window);
        *port_fields[i]^=1u<<bit;
    }
    for(unsigned status=1;status<=9;++status) {
        assert(ARM());assert(!lab_ahci_interrupt_arm(&w,&v,lab_ecam_expected_tables,
            LAB_ECAM_FIRMWARE_TABLE_COUNT,0x200000,&h,QOTOM_AHCI_OK,&prior,status,&stopped));
        assert(!w.armed && !w.leaf && !w.root && !w.window);
    }
    assert(!stores && !invalidations);
    puts("PASS AHCI arm: exact BAR, all 4096 aliases rejected, no device access, failed rearm revoked");
}
