#include <assert.h>
#include <stdio.h>
#include <string.h>
#include "../boot/qotom-xhci-smi.h"
static const struct pci_enumeration_header header={.device=20,.words={0x0f358086,6,0x0c03300e,0,0xd0900004,0}};
static const struct qotom_xhci_capabilities caps={{0x1000080,0x7000820,0x84000054,0x200000a,0x200077c1,0x3000,0x2000}};
static struct qotom_xhci_legacy previous;
static struct qotom_xhci_handoff_result prior;
static enum qotom_xhci_handoff_status prior_status;
static uint32_t ext[8192],final_extra,final_vendor,final_other;
static unsigned reads,writes,failed,first_reads;
static int write_failed,write_ignored,reassert,config_drift;
static int config(void *ctx,uint8_t b,uint8_t d,uint8_t f,uint8_t off,uint32_t *out) {
    (void)ctx;assert(!b && d==20 && !f && !(off&3) && off<=20);
    if(++reads==failed)return 0;
    *out=header.words[off/4];if(writes && config_drift && !off)*out^=1;return 1;
}
static int mmio(void *ctx,uint64_t a,uint32_t *out) {
    (void)ctx;assert(a>=QOTOM_XHCI_BAR && a<=QOTOM_XHCI_BAR+24 && !(a&3));
    if(++reads==failed)return 0;
    *out=caps.words[(a-QOTOM_XHCI_BAR)/4];return 1;
}
static int extended(void *ctx,uint64_t a,uint32_t *out) {
    (void)ctx;assert(a>=QOTOM_XHCI_BAR+0x8000 && a<=QOTOM_XHCI_BAR+0xfffc && !(a&3));
    if(++reads==failed)return 0;
    *out=ext[(a-QOTOM_XHCI_BAR-0x8000)/4];return 1;
}
static int write32(void *ctx,uint64_t a,uint32_t value) {
    (void)ctx;assert(a==UINT64_C(0xd0908464) && !value && !writes && reads==first_reads);
    ++writes;
    if(!write_ignored)ext[0x464/4]&=~QOTOM_XHCI_SMI_ENABLE;
    ext[0x464/4]|=final_extra;ext[16]^=final_vendor;ext[0]^=final_other;
    if(reassert)ext[0x460/4]|=0x10000;
    return !write_failed;
}
static void reset(void) {
    previous=(struct qotom_xhci_legacy){.count=6,.legacy_offset=0x8460,.control_status=0x2001,
        .headers={{0x8000,0x02000802},{0x8020,0x03000802},{0x8040,0x10cc1},
                  {0x8070,0xfcc0},{0x8460,0x10801},{0x8480,0x5000a}}};
    memset(ext,0,sizeof ext);
    for(unsigned i=0;i<previous.count;++i)ext[(previous.headers[i].offset-0x8000)/4]=previous.headers[i].raw;
    ext[0x460/4]=0x01000801;ext[0x464/4]=0x2000;ext[16]=0xcc1;
    prior=(struct qotom_xhci_handoff_result){.write_attempted=1,.polls=2,.last_support=0x01000801,.final_control=0x2000};
    prior_status=QOTOM_XHCI_HANDOFF_OBSERVED;
    reads=writes=failed=final_extra=final_vendor=final_other=0;first_reads=45;
    write_failed=write_ignored=reassert=config_drift=0;
}
static void maximum(void) {
    reset();previous.count=48;
    for(unsigned i=0;i<46;++i)previous.headers[i]=(struct qotom_xhci_ext_header){0x8000+4*i,0x102};
    previous.headers[45].raw=0x02|(((0x8460-previous.headers[45].offset)/4)<<8);
    previous.headers[46]=(struct qotom_xhci_ext_header){0x8460,0x10801};
    previous.headers[47]=(struct qotom_xhci_ext_header){0x8480,0x5000a};
    for(unsigned i=0;i<48;++i)ext[(previous.headers[i].offset-0x8000)/4]=previous.headers[i].raw;
    ext[0x460/4]=0x01000801;first_reads=87;
}
static struct qotom_xhci_smi_result out;
static void check(enum qotom_xhci_smi_status status) {
    memset(&out,0x55,sizeof out);
    assert(qotom_disable_xhci_smi(config,NULL,mmio,NULL,extended,NULL,write32,NULL,&header,&caps,&previous,prior_status,&prior,&out)==status);
    assert(reads<=174 && writes<=1 && out.write_attempted==writes);
    if(!writes)assert(!out.before_control && !out.after_control);
}
int main(void) {
    assert(pci_enumerate_segment(NULL,NULL,NULL).status==PCI_ENUMERATION_INVALID_ARGUMENT);
    for(unsigned subset=0;subset<32;++subset) {
        reset();uint32_t mask=(subset&1)|((subset&2)<<3)|((subset&28)<<11);
        ext[0x464/4]=prior.final_control=mask|QOTOM_XHCI_SMI_STATUS;
        check(QOTOM_XHCI_SMI_OBSERVED);
        assert(reads==90 && out.before_control==(mask|QOTOM_XHCI_SMI_STATUS) && out.after_control==QOTOM_XHCI_SMI_STATUS);
    }
    for(unsigned bit=0;bit<32;++bit) {
        uint32_t mask=UINT32_C(1)<<bit;
        if(mask&QOTOM_XHCI_SMI_STATUS) {
            reset();ext[0x464/4]|=mask;check(QOTOM_XHCI_SMI_OBSERVED);assert(out.after_control==mask);
            reset();final_extra=mask;check(QOTOM_XHCI_SMI_OBSERVED);assert(out.after_control==mask);
        }
        if(mask&QOTOM_XHCI_SMI_ENABLE) {
            reset();final_extra=mask;check(QOTOM_XHCI_SMI_READBACK);assert(out.after_control==mask);
        }
    }
    maximum();check(QOTOM_XHCI_SMI_OBSERVED);assert(reads==174);
    for(unsigned i=1;i<=174;++i) {maximum();failed=i;check(i<=87?QOTOM_XHCI_SMI_REFRESH:QOTOM_XHCI_SMI_FINAL);}
    reset();write_failed=1;check(QOTOM_XHCI_SMI_WRITE);assert(ext[0x464/4]==0 && !out.after_control);
    reset();write_failed=write_ignored=1;check(QOTOM_XHCI_SMI_WRITE);assert(ext[0x464/4]==0x2000);
    reset();write_ignored=1;check(QOTOM_XHCI_SMI_READBACK);assert(out.after_control==0x2000);
    reset();reassert=1;check(QOTOM_XHCI_SMI_FINAL);
    reset();config_drift=1;check(QOTOM_XHCI_SMI_FINAL);
    for(unsigned bit=0;bit<32;++bit) {
        uint32_t mask=UINT32_C(1)<<bit;
        reset();final_vendor=mask;
        check(mask&QOTOM_XHCI_CMDM_STATUS?QOTOM_XHCI_SMI_OBSERVED:QOTOM_XHCI_SMI_FINAL);
        if(mask&(QOTOM_XHCI_SMI_ENABLE|QOTOM_XHCI_SMI_STATUS))continue;
        reset();ext[0x464/4]|=mask;check(QOTOM_XHCI_SMI_STATE);
        reset();prior.final_control|=mask;check(QOTOM_XHCI_SMI_PRIOR);assert(!reads);
        reset();final_extra=mask;check(QOTOM_XHCI_SMI_READBACK);
    }
    reset();final_other=0x10000;check(QOTOM_XHCI_SMI_FINAL);
    reset();ext[0x460/4]|=0x10000;check(QOTOM_XHCI_SMI_STATE);
    reset();ext[0x464/4]^=1;check(QOTOM_XHCI_SMI_STATE);
    reset();previous.headers[0].raw^=0x10000;check(QOTOM_XHCI_SMI_STATE);
    reset();prior_status=QOTOM_XHCI_HANDOFF_FINAL;check(QOTOM_XHCI_SMI_PRIOR);assert(!reads);
    reset();prior.polls=101;check(QOTOM_XHCI_SMI_PRIOR);
    reset();prior.polls=0;check(QOTOM_XHCI_SMI_PRIOR);
    reset();prior.write_attempted=0;check(QOTOM_XHCI_SMI_PRIOR);
    reset();prior.last_support^=0x10000;check(QOTOM_XHCI_SMI_PRIOR);
    reset();prior.verify_kind=1;check(QOTOM_XHCI_SMI_PRIOR);
    reset();prior.verify_index=1;check(QOTOM_XHCI_SMI_PRIOR);
    reset();prior.verify_expected=1;check(QOTOM_XHCI_SMI_PRIOR);
    reset();prior.verify_observed=1;check(QOTOM_XHCI_SMI_PRIOR);
    reset();previous.count=49;check(QOTOM_XHCI_SMI_PRIOR);
    reset();previous.count=0;check(QOTOM_XHCI_SMI_PRIOR);
    reset();previous.legacy_offset=0x8464;check(QOTOM_XHCI_SMI_PRIOR);
    reset();assert(qotom_disable_xhci_smi(NULL,NULL,mmio,NULL,extended,NULL,write32,NULL,&header,&caps,&previous,prior_status,&prior,&out)==QOTOM_XHCI_SMI_ARGUMENT);
    assert(!reads && !writes && !out.write_attempted && !out.before_control && !out.after_control);
    puts("PASS xHCI SMI disable: all enable combinations, 174 read-failure positions, live status, ownership drift and exact zero DWORD write");
}
