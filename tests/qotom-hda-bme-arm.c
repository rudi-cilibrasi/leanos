#include <assert.h>
#include <stdio.h>
#include <string.h>
#include "qotom-hda-bme-arm.h"
static uint64_t root[512],pdpt[512],pd[512],pt[4096];
static unsigned stores, invalidations;
static int controls(void *ctx,struct lab_ecam_controls *out) {
    (void)ctx;
    *out=(struct lab_ecam_controls){0x0007040600070406,0x80010001,0x100000,0x20,0xd00,2};return 1;
}
static void invalidate(void *ctx,uint64_t a) {(void)ctx;(void)a;++invalidations;}
static int store(void *ctx,uint64_t a,uint16_t v) {(void)ctx;(void)a;(void)v;++stores;return 0;}
static void fault(void *ctx) {(void)ctx;assert(0);}
int main(void) {
    assert(pci_enumerate_segment(NULL,NULL,NULL).status==PCI_ENUMERATION_INVALID_ARGUMENT);
    struct lab_ecam_root_view v={root,pdpt,pd,pt,0x100000,0x101000,0x102000,0x103000};
    root[0]=v.pdpt_address|7;pdpt[0]=v.pd_address|7;
    for(unsigned i=0;i<8;++i)pd[i]=(v.pt_address+i*4096)|7;
    for(unsigned i=0;i<4096;++i)pt[i]=((uint64_t)i*4096)|UINT64_C(0x8000000000000003);
    struct pci_enumeration_header h={.device=27,.words={[0]=0x0f048086,[1]=6,[2]=0x0403000e,[4]=0xd0910004}};
    struct qotom_hda_observation prior={1,0x4401,0,1,0,1};
    struct qotom_hda_state stopped={0};
    for(unsigned i=0;i<8;++i)stopped.streams[i]=0x40000;
    struct lab_hda_bme_window w={.controls=controls,.invalidate=invalidate,.store16=store,.fault=fault};
#define ARM() lab_hda_bme_arm(&w,&v,lab_ecam_expected_tables,LAB_ECAM_FIRMWARE_TABLE_COUNT,0x200000,&h,QOTOM_HDA_OK,&prior,QOTOM_HDA_STATE_OK,&stopped)
    assert(ARM() && w.armed && w.leaf==&pt[512]);
    for(unsigned page=0;page<4;++page)for(unsigned i=0;i<4096;++i) {
        uint64_t saved=pt[i];pt[i]=(QOTOM_HDA_BAR+page*4096)|1;
        assert(!ARM() && !w.armed && !w.leaf && !w.root && !w.window);
        pt[i]=saved;
    }
    assert(ARM());
    h.words[4]^=0x1000;assert(!ARM() && !w.armed);h.words[4]^=0x1000;
    h.words[1]&=~2u;assert(!ARM() && !w.armed);h.words[1]|=2;
    assert(ARM());root[1]=7;assert(!ARM() && !w.armed);root[1]=0;
    const unsigned words[]={0,1,2,3,4,5};
    const uint32_t masks[]={UINT32_MAX,0xffff,UINT32_MAX,0x00ff0000,UINT32_MAX,UINT32_MAX};
    for(unsigned i=0;i<6;++i)for(unsigned bit=0;bit<32;++bit) {
        assert(ARM());h.words[words[i]]^=1u<<bit;
        if(masks[i]&(1u<<bit)) assert(!ARM() && !w.armed && !w.leaf && !w.root && !w.window);
        else assert(ARM());
        h.words[words[i]]^=1u<<bit;
    }
    struct lab_ecam_firmware_table changed[LAB_ECAM_FIRMWARE_TABLE_COUNT];
    memcpy(changed,lab_ecam_expected_tables,sizeof changed);changed[0].address^=4;
    assert(ARM());
    assert(!lab_hda_bme_arm(&w,&v,changed,LAB_ECAM_FIRMWARE_TABLE_COUNT,0x200000,&h,QOTOM_HDA_OK,&prior,QOTOM_HDA_STATE_OK,&stopped));
    assert(!w.armed && !w.leaf && !w.root && !w.window);
    assert(ARM());w.store16=NULL;assert(!ARM() && !w.armed && !w.leaf);w.store16=store;
    assert(ARM());h.bus=1;assert(!ARM() && !w.armed);h.bus=0;
    assert(ARM());h.device=20;assert(!ARM() && !w.armed);h.device=27;
    assert(ARM());h.function=1;assert(!ARM() && !w.armed);h.function=0;
    assert(ARM());w.controls=NULL;assert(!ARM() && !w.armed && !w.leaf);w.controls=controls;
    assert(ARM());w.invalidate=NULL;assert(!ARM() && !w.armed && !w.leaf);w.invalidate=invalidate;
    assert(ARM());w.fault=NULL;assert(!ARM() && !w.armed && !w.leaf);w.fault=fault;
    assert(ARM());
    assert(!lab_hda_bme_arm(&w,NULL,lab_ecam_expected_tables,LAB_ECAM_FIRMWARE_TABLE_COUNT,0x200000,&h,QOTOM_HDA_OK,&prior,QOTOM_HDA_STATE_OK,&stopped));
    assert(!w.armed && !w.leaf && !w.root && !w.window);
    assert(ARM());
    assert(!lab_hda_bme_arm(&w,&v,lab_ecam_expected_tables,LAB_ECAM_FIRMWARE_TABLE_COUNT,0x200000,NULL,QOTOM_HDA_OK,&prior,QOTOM_HDA_STATE_OK,&stopped));
    assert(!w.armed && !w.leaf && !w.root && !w.window);
    uint32_t *fields[]={&prior.control_before,&prior.capability,&prior.version_minor,
        &prior.version_major,&prior.interrupt,&prior.control_after};
    for(unsigned i=0;i<6;++i)for(unsigned bit=0;bit<32;++bit) {
        assert(ARM());*fields[i]^=1u<<bit;
        assert(!ARM() && !w.armed && !w.leaf && !w.root && !w.window);*fields[i]^=1u<<bit;
    }
    for(unsigned status=1;status<=9;++status) {
        assert(ARM());assert(!lab_hda_bme_arm(&w,&v,lab_ecam_expected_tables,
            LAB_ECAM_FIRMWARE_TABLE_COUNT,0x200000,&h,status,&prior,QOTOM_HDA_STATE_OK,&stopped));
        assert(!w.armed && !w.leaf && !w.root && !w.window);
    }
    assert(ARM());assert(!lab_hda_bme_arm(&w,&v,lab_ecam_expected_tables,
        LAB_ECAM_FIRMWARE_TABLE_COUNT,0x200000,&h,QOTOM_HDA_OK,NULL,QOTOM_HDA_STATE_OK,&stopped));
    assert(!w.armed && !w.leaf && !w.root && !w.window);
    uint32_t *state_fields[]={&stopped.corb,&stopped.rirb,&stopped.position,
        &stopped.streams[0],&stopped.streams[1],&stopped.streams[2],&stopped.streams[3],
        &stopped.streams[4],&stopped.streams[5],&stopped.streams[6],&stopped.streams[7]};
    for(unsigned i=0;i<11;++i)for(unsigned bit=0;bit<32;++bit) {
        assert(ARM());*state_fields[i]^=1u<<bit;
        assert(!ARM() && !w.armed && !w.leaf && !w.root && !w.window);*state_fields[i]^=1u<<bit;
    }
    for(unsigned status=1;status<=10;++status) {
        assert(ARM());assert(!lab_hda_bme_arm(&w,&v,lab_ecam_expected_tables,
            LAB_ECAM_FIRMWARE_TABLE_COUNT,0x200000,&h,QOTOM_HDA_OK,&prior,status,&stopped));
        assert(!w.armed && !w.leaf && !w.root && !w.window);
    }
    assert(ARM());assert(!lab_hda_bme_arm(&w,&v,lab_ecam_expected_tables,
        LAB_ECAM_FIRMWARE_TABLE_COUNT,0x200000,&h,QOTOM_HDA_OK,&prior,QOTOM_HDA_STATE_OK,NULL));
    assert(!w.armed && !w.leaf && !w.root && !w.window);
    assert(!stores && !invalidations);
    puts("PASS HDA BME arm: exact BAR, all 4096 aliases to all four resource pages rejected, no device access, failed rearm revoked");
}
