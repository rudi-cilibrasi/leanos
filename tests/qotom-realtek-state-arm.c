#include <assert.h>
#include <stdio.h>
#include <string.h>
#include "qotom-realtek-state-arm.h"
static uint64_t root[512],pdpt[512],pd[512],pt[4096];
static unsigned loads, invalidations,control_calls,bad_control;
static int control_failure;
static int controls(void *ctx,struct lab_ecam_controls *out) {
    (void)ctx;
    *out=(struct lab_ecam_controls){0x0007040600070406,0x80010001,0x100000,0x20,0xd00,2};
    ++control_calls;
    if(control_calls==bad_control) {
        if(control_failure)return 0;
        out->cr3^=4096;
    }
    return 1;
}
static void invalidate(void *ctx,uint64_t a) {(void)ctx;(void)a;++invalidations;}
static int load(void *ctx,uint64_t a,uint8_t width,uint32_t *v) {(void)ctx;(void)a;(void)width;(void)v;++loads;return 0;}
static void fault(void *ctx) {(void)ctx;assert(0);}
static void run(uint8_t selected_bus) {
    memset(root,0,sizeof root);memset(pdpt,0,sizeof pdpt);memset(pd,0,sizeof pd);
    assert(pci_enumerate_segment(NULL,NULL,NULL).status==PCI_ENUMERATION_INVALID_ARGUMENT);
    struct lab_ecam_root_view v={root,pdpt,pd,pt,0x100000,0x101000,0x102000,0x103000};
    root[0]=v.pdpt_address|7;pdpt[0]=v.pd_address|7;
    for(unsigned i=0;i<8;++i)pd[i]=(v.pt_address+i*4096)|7;
    for(unsigned i=0;i<4096;++i)pt[i]=((uint64_t)i*4096)|UINT64_C(0x8000000000000003);
    uint64_t bar=qotom_realtek_bar(selected_bus);
    struct pci_enumeration_header h={.bus=selected_bus,.words={
        [0]=0x816810ec,[1]=7,[2]=0x02000007,[3]=16,
        [6]=(uint32_t)bar|4,[8]=((uint32_t)bar-0x4000)|12}};
    struct lab_realtek_state_window w={.controls=controls,.invalidate=invalidate,.load=load,.fault=fault};
#define ARM() lab_realtek_state_arm(&w,&v,lab_ecam_expected_tables,LAB_ECAM_FIRMWARE_TABLE_COUNT,0x200000,&h)
    assert(ARM() && w.armed && w.bus==selected_bus && w.leaf==&pt[512]);
    for(unsigned page=0;page<5;++page)for(unsigned i=0;i<4096;++i) {
        uint64_t saved=pt[i];pt[i]=(bar-0x4000+page*4096)|1;
        assert(!ARM() && !w.armed && !w.leaf && !w.root && !w.window && !w.bus);
        pt[i]=saved;
    }
    assert(ARM());
    h.words[6]^=0x1000;assert(!ARM() && !w.armed);h.words[6]^=0x1000;
    h.words[1]&=~2u;assert(!ARM() && !w.armed);h.words[1]|=2;
    assert(ARM());root[1]=7;assert(!ARM() && !w.armed);root[1]=0;
    const unsigned words[]={0,1,2,3,6,7,8,9};
    const uint32_t masks[]={UINT32_MAX,65535,UINT32_MAX,0x00ff0000,UINT32_MAX,UINT32_MAX,UINT32_MAX,UINT32_MAX};
    for(unsigned i=0;i<8;++i)for(unsigned bit=0;bit<32;++bit) {
        assert(ARM());h.words[words[i]]^=1u<<bit;
        if(masks[i]&(1u<<bit)) assert(!ARM() && !w.armed && !w.leaf && !w.root && !w.window && !w.bus);
        else assert(ARM());
        h.words[words[i]]^=1u<<bit;
    }
    struct lab_ecam_firmware_table changed[LAB_ECAM_FIRMWARE_TABLE_COUNT];
    memcpy(changed,lab_ecam_expected_tables,sizeof changed);changed[0].address^=4;
    assert(ARM());
    assert(!lab_realtek_state_arm(&w,&v,changed,LAB_ECAM_FIRMWARE_TABLE_COUNT,0x200000,&h));
    assert(!w.armed && !w.leaf && !w.root && !w.window && !w.bus);
    assert(ARM());w.load=NULL;assert(!ARM() && !w.armed && !w.leaf);w.load=load;
    assert(ARM());h.bus=2;assert(!ARM() && !w.armed);h.bus=selected_bus;
    assert(ARM());h.device=20;assert(!ARM() && !w.armed);h.device=0;
    assert(ARM());h.function=1;assert(!ARM() && !w.armed);h.function=0;
    assert(ARM());w.controls=NULL;assert(!ARM() && !w.armed && !w.leaf);w.controls=controls;
    assert(ARM());w.invalidate=NULL;assert(!ARM() && !w.armed && !w.leaf);w.invalidate=invalidate;
    assert(ARM());w.fault=NULL;assert(!ARM() && !w.armed && !w.leaf);w.fault=fault;
    assert(ARM());
    assert(!lab_realtek_state_arm(&w,NULL,lab_ecam_expected_tables,LAB_ECAM_FIRMWARE_TABLE_COUNT,0x200000,&h));
    assert(!w.armed && !w.leaf && !w.root && !w.window && !w.bus);
    assert(ARM());
    assert(!lab_realtek_state_arm(&w,&v,lab_ecam_expected_tables,LAB_ECAM_FIRMWARE_TABLE_COUNT,0x200000,NULL));
    assert(!w.armed && !w.leaf && !w.root && !w.window && !w.bus);
    for(unsigned phase=1;phase<=2;++phase)for(unsigned failure=0;failure<=1;++failure) {
        assert(ARM());control_calls=0;bad_control=phase;control_failure=failure;
        assert(!ARM() && !w.armed && !w.leaf && !w.root && !w.window && !w.bus);
        assert(control_calls==phase);bad_control=0;
    }
    for(unsigned bus=0;bus<256;++bus)if(bus!=1 && bus!=3) {
        assert(ARM());h.bus=(uint8_t)bus;
        assert(!ARM() && !w.armed && !w.leaf && !w.root && !w.window && !w.bus);
        h.bus=selected_bus;
    }
    assert(!lab_realtek_state_arm(NULL,&v,lab_ecam_expected_tables,LAB_ECAM_FIRMWARE_TABLE_COUNT,0x200000,&h));
    assert(!loads && !invalidations);

}

int main(void) {
    run(1);run(3);
    puts("PASS Realtek arm: both bound BAR pairs, all 4096 aliases to five pages per endpoint rejected, no device access, rearm revoked");
}
