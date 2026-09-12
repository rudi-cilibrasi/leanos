#include <assert.h>
#include <stdio.h>
#include "qotom-xhci-bme-arm.h"
static uint64_t root[512],pdpt[512],pd[512],pt[4096];
static unsigned loads, invalidations;
static int controls(void *ctx,struct lab_ecam_controls *out) {
    (void)ctx;
    *out=(struct lab_ecam_controls){0x0007040600070406,0x80010001,0x100000,0x20,0xd00,2};return 1;
}
static void invalidate(void *ctx,uint64_t a) {(void)ctx;(void)a;++invalidations;}
static int load(void *ctx,uint64_t a,uint16_t v) {(void)ctx;(void)a;(void)v;++loads;return 0;}
static void fault(void *ctx) {(void)ctx;assert(0);}
int main(void) {
    assert(pci_enumerate_segment(NULL,NULL,NULL).status==PCI_ENUMERATION_INVALID_ARGUMENT);
    struct lab_ecam_root_view v={root,pdpt,pd,pt,0x100000,0x101000,0x102000,0x103000};
    root[0]=v.pdpt_address|7;pdpt[0]=v.pd_address|7;
    for(unsigned i=0;i<8;++i)pd[i]=(v.pt_address+i*4096)|7;
    for(unsigned i=0;i<4096;++i)pt[i]=((uint64_t)i*4096)|UINT64_C(0x8000000000000003);
    struct pci_enumeration_header h={.device=20,.words={0x0f358086,0x6,0x0c03300e,0,0xd0900004}};
    struct lab_xhci_bme_window w={.controls=controls,.invalidate=invalidate,.store16=load,.fault=fault};
    struct qotom_xhci_capabilities caps={{0x1000080,0x7000820,0x84000054,0x200000a,0x200077c1,0x3000,0x2000}};
    struct qotom_xhci_smi_result prior={1,0x2000,0};
    enum qotom_xhci_smi_status status=QOTOM_XHCI_SMI_OBSERVED;
    struct qotom_xhci_operational stopped={1,0,1};
    enum qotom_xhci_operational_status stopped_status=QOTOM_XHCI_OPERATIONAL_OK;
#define ARM() lab_xhci_bme_arm(&w,&v,lab_ecam_expected_tables,LAB_ECAM_FIRMWARE_TABLE_COUNT,0x200000,&h,&caps,status,&prior,stopped_status,&stopped)
    assert(ARM() && w.armed && w.leaf==&pt[512]);
    for(unsigned i=0;i<4096;++i) {
        uint64_t saved=pt[i];pt[i]=QOTOM_XHCI_BAR|1;
        assert(!ARM() && !w.armed && !w.leaf && !w.root && !w.window);
        pt[i]=UINT64_C(0xe00a0000)|1;
        assert(!ARM() && !w.armed && !w.leaf && !w.root && !w.window);
        pt[i]=saved;
    }
    assert(ARM());
    h.words[4]^=0x1000;assert(!ARM() && !w.armed);h.words[4]^=0x1000;
    h.words[1]&=~2u;assert(!ARM() && !w.armed);h.words[1]|=2;
    assert(ARM());root[1]=7;assert(!ARM() && !w.armed);root[1]=0;
    for(unsigned bit=0;bit<32;++bit) {
        uint32_t mask=UINT32_C(1)<<bit;
        for(unsigned i=0;i<7;++i) {
            assert(ARM());caps.words[i]^=mask;assert(!ARM() && !w.armed);caps.words[i]^=mask;
        }
        assert(ARM());prior.after_control=mask;assert(!ARM() && !w.armed);prior.after_control=0;
        assert(ARM());prior.before_control^=mask;assert(!ARM() && !w.armed);prior.before_control^=mask;
    }
    for(unsigned page=0;page<16;++page) {
        uint64_t saved=pt[600];pt[600]=(QOTOM_XHCI_BAR+page*4096)|1;
        assert(!ARM() && !w.armed);pt[600]=saved;
    }
    for(unsigned bit=0;bit<32;++bit) {
        assert(ARM());h.words[5]^=UINT32_C(1)<<bit;assert(!ARM() && !w.armed);h.words[5]^=UINT32_C(1)<<bit;
    }
    assert(ARM());prior.write_attempted=0;assert(!ARM() && !w.armed);prior.write_attempted=1;
    assert(ARM());status=QOTOM_XHCI_SMI_READBACK;assert(!ARM() && !w.armed);status=QOTOM_XHCI_SMI_OBSERVED;
    for(unsigned bit=0;bit<32;++bit) {
        uint32_t mask=UINT32_C(1)<<bit;
        assert(ARM());stopped.command^=mask;assert(!ARM() && !w.armed);stopped.command^=mask;
        assert(ARM());stopped.status_before^=mask;assert(!ARM() && !w.armed);stopped.status_before^=mask;
        assert(ARM());stopped.status_after^=mask;assert(!ARM() && !w.armed);stopped.status_after^=mask;
    }
    assert(ARM());stopped_status=QOTOM_XHCI_OPERATIONAL_FINAL;assert(!ARM() && !w.armed);stopped_status=QOTOM_XHCI_OPERATIONAL_OK;
    assert(ARM());h.words[1]=0x2;assert(!ARM() && !w.armed);h.words[1]=0x6;
    assert(ARM());
    assert(!lab_xhci_bme_arm(&w,&v,lab_ecam_expected_tables,0,0x200000,&h,&caps,status,&prior,stopped_status,&stopped));
    assert(!w.armed && !w.leaf && !w.root && !w.window);
    assert(!loads && !invalidations);
    puts("PASS XHCI BME arm: exact BAR, all 4096 aliases rejected, no device access, failed rearm revoked");
}
