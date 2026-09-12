#include <assert.h>
#include <stdio.h>
#include "qotom-ehci-operational-arm.h"
static uint64_t root[512],pdpt[512],pd[512],pt[4096];
static unsigned loads, invalidations;
static int controls(void *ctx,struct lab_ecam_controls *out) {
    (void)ctx;
    *out=(struct lab_ecam_controls){0x0007040600070406,0x80010001,0x100000,0x20,0xd00,2};return 1;
}
static void invalidate(void *ctx,uint64_t a) {(void)ctx;(void)a;++invalidations;}
static int load(void *ctx,uint64_t a,uint32_t *v) {(void)ctx;(void)a;(void)v;++loads;return 0;}
static void fault(void *ctx) {(void)ctx;assert(0);}
int main(void) {
    assert(pci_enumerate_segment(NULL,NULL,NULL).status==PCI_ENUMERATION_INVALID_ARGUMENT);
    struct lab_ecam_root_view v={root,pdpt,pd,pt,0x100000,0x101000,0x102000,0x103000};
    root[0]=v.pdpt_address|7;pdpt[0]=v.pd_address|7;
    for(unsigned i=0;i<8;++i)pd[i]=(v.pt_address+i*4096)|7;
    for(unsigned i=0;i<4096;++i)pt[i]=((uint64_t)i*4096)|UINT64_C(0x8000000000000003);
    struct pci_enumeration_header h={.device=29,.words={0x0f348086,0x406,0x0c03200e,0,0xd0915000}};
    struct lab_ehci_operational_window w={.controls=controls,.invalidate=invalidate,.load32=load,.fault=fault};
    struct qotom_ehci_capabilities caps={0x1000020,0x200008,0x36881};
    struct qotom_ehci_smi_result prior={1,0x2000,0};
    enum qotom_ehci_smi_status status=QOTOM_EHCI_SMI_OBSERVED;
#define ARM() lab_ehci_operational_arm(&w,&v,lab_ecam_expected_tables,LAB_ECAM_FIRMWARE_TABLE_COUNT,0x200000,&h,&caps,status,&prior)
    assert(ARM() && w.armed && w.leaf==&pt[512]);
    for(unsigned i=0;i<4096;++i) {
        uint64_t saved=pt[i];pt[i]=QOTOM_EHCI_BAR|1;
        assert(!ARM() && !w.armed && !w.leaf && !w.root && !w.window);
        pt[i]=UINT64_C(0xe00e8000)|1;
        assert(!ARM() && !w.armed && !w.leaf && !w.root && !w.window);
        pt[i]=saved;
    }
    assert(ARM());
    h.words[4]^=0x1000;assert(!ARM() && !w.armed);h.words[4]^=0x1000;
    h.words[1]&=~2u;assert(!ARM() && !w.armed);h.words[1]|=2;
    assert(ARM());root[1]=7;assert(!ARM() && !w.armed);root[1]=0;
    for(unsigned bit=0;bit<32;++bit) {
        uint32_t mask=UINT32_C(1)<<bit;
        assert(ARM());caps.capbase^=mask;assert(!ARM() && !w.armed);caps.capbase^=mask;
        assert(ARM());caps.structural^=mask;assert(!ARM() && !w.armed);caps.structural^=mask;
        assert(ARM());caps.capability^=mask;assert(!ARM() && !w.armed);caps.capability^=mask;
        if(!(mask&QOTOM_EHCI_SMI_STATUS)) {
            assert(ARM());prior.after_control=mask;assert(!ARM() && !w.armed);prior.after_control=0;
        }
        if(!(mask&(QOTOM_EHCI_SMI_STATUS|QOTOM_EHCI_SMI_ENABLE))) {
            assert(ARM());prior.before_control|=mask;assert(!ARM() && !w.armed);prior.before_control=0x2000;
        }
    }
    assert(ARM());prior.write_attempted=0;assert(!ARM() && !w.armed);prior.write_attempted=1;
    assert(ARM());status=QOTOM_EHCI_SMI_READBACK;assert(!ARM() && !w.armed);status=QOTOM_EHCI_SMI_OBSERVED;
    prior.after_control=QOTOM_EHCI_SMI_STATUS;assert(ARM());
    assert(!lab_ehci_operational_arm(&w,&v,lab_ecam_expected_tables,0,0x200000,&h,&caps,status,&prior));
    assert(!w.armed && !w.leaf && !w.root && !w.window);
    assert(!loads && !invalidations);
    puts("PASS EHCI operational arm: exact BAR, all 4096 aliases rejected, no device access, failed rearm revoked");
}
