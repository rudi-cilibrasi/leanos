#include <assert.h>
#include <stdio.h>
#include <string.h>
#include "../boot/qotom-xhci-operational.h"
static const struct pci_enumeration_header header={.device=20,.words={0x0f358086,6,0x0c03300e,0,0xd0900004,0}};
static const struct qotom_xhci_capabilities caps={{0x1000080,0x7000820,0x84000054,0x200000a,0x200077c1,0x3000,0x2000}};
static struct qotom_xhci_legacy previous;
static struct qotom_xhci_smi_result prior;
static enum qotom_xhci_smi_status prior_status;
static uint32_t ext[8192],samples[3],final_extra,final_vendor,final_other;
static unsigned reads,ops,failed,first_reads;
static int reassert,config_drift;
static int config(void *ctx,uint8_t b,uint8_t d,uint8_t f,uint8_t off,uint32_t *out) {
    (void)ctx;assert(!b && d==20 && !f && !(off&3) && off<=20);
    if(++reads==failed)return 0;
    *out=header.words[off/4];if(ops && config_drift && !off)*out^=1;return 1;
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
static int operational(void *ctx,uint64_t a,uint32_t *out) {
    (void)ctx;assert(ops<3 && a==QOTOM_XHCI_BAR+(ops==1?0x80:0x84));
    assert(reads==first_reads+ops);++ops;
    if(++reads==failed)return 0;
    *out=samples[ops-1];
    if(ops==3) {
        ext[0x464/4]|=final_extra;ext[16]^=final_vendor;ext[0]^=final_other;
        if(reassert)ext[0x460/4]|=0x10000;
    }
    return 1;
}
static void reset(void) {
    previous=(struct qotom_xhci_legacy){.count=6,.legacy_offset=0x8460,.control_status=0x2001,
        .headers={{0x8000,0x02000802},{0x8020,0x03000802},{0x8040,0x10cc1},
                  {0x8070,0xfcc0},{0x8460,0x10801},{0x8480,0x5000a}}};
    memset(ext,0,sizeof ext);
    for(unsigned i=0;i<previous.count;++i)ext[(previous.headers[i].offset-0x8000)/4]=previous.headers[i].raw;
    ext[0x460/4]=0x01000801;ext[0x464/4]=0;ext[16]=0xcc1;
    prior=(struct qotom_xhci_smi_result){1,0x2000,0};
    prior_status=QOTOM_XHCI_SMI_OBSERVED;
    reads=ops=failed=final_extra=final_vendor=final_other=0;first_reads=45;
    reassert=config_drift=0;samples[0]=samples[2]=1;samples[1]=0;
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
static struct qotom_xhci_operational out;
static void check(enum qotom_xhci_operational_status status) {
    memset(&out,0x55,sizeof out);
    assert(qotom_collect_xhci_operational(config,NULL,mmio,NULL,extended,NULL,operational,NULL,
        &header,&caps,&previous,prior_status,&prior,&out)==status);
    assert(reads<=177 && ops<=3);
    if(status)assert(!out.command && !out.status_before && !out.status_after);
}
int main(void) {
    assert(pci_enumerate_segment(NULL,NULL,NULL).status==PCI_ENUMERATION_INVALID_ARGUMENT);
    reset();check(QOTOM_XHCI_OPERATIONAL_OK);assert(reads==93 && ops==3 && out.status_before==1 && !out.command && out.status_after==1);
    maximum();check(QOTOM_XHCI_OPERATIONAL_OK);assert(reads==177);
    for(unsigned i=1;i<=177;++i) {
        maximum();failed=i;
        check(i<=87?QOTOM_XHCI_OPERATIONAL_REFRESH:i<=90?QOTOM_XHCI_OPERATIONAL_READ:QOTOM_XHCI_OPERATIONAL_FINAL);
    }
    for(unsigned i=0;i<3;++i) {
        reset();samples[i]=UINT32_MAX;check(QOTOM_XHCI_OPERATIONAL_ABSENT);assert(ops==i+1);
    }
    reset();samples[0]=0x800;check(QOTOM_XHCI_OPERATIONAL_NOT_READY);assert(ops==1);
    reset();samples[2]=0x800;check(QOTOM_XHCI_OPERATIONAL_NOT_READY);assert(ops==3);
    reset();samples[0]=0x10;samples[1]=0xd;samples[2]=1;check(QOTOM_XHCI_OPERATIONAL_OK);
    assert(out.status_before==0x10 && out.command==0xd && out.status_after==1);
    for(unsigned bit=0;bit<32;++bit) {
        uint32_t mask=UINT32_C(1)<<bit;
        reset();final_vendor=mask;
        check(mask&QOTOM_XHCI_CMDM_STATUS?QOTOM_XHCI_OPERATIONAL_OK:QOTOM_XHCI_OPERATIONAL_FINAL);
        reset();ext[0x464/4]=mask;
        check(mask&QOTOM_XHCI_SMI_STATUS?QOTOM_XHCI_OPERATIONAL_OK:QOTOM_XHCI_OPERATIONAL_STATE);
        reset();final_extra=mask;
        check(mask&QOTOM_XHCI_SMI_STATUS?QOTOM_XHCI_OPERATIONAL_OK:QOTOM_XHCI_OPERATIONAL_FINAL);
        reset();prior.after_control=mask;
        check(mask&QOTOM_XHCI_SMI_STATUS?QOTOM_XHCI_OPERATIONAL_OK:QOTOM_XHCI_OPERATIONAL_PRIOR);
    }
    reset();config_drift=1;check(QOTOM_XHCI_OPERATIONAL_FINAL);
    reset();reassert=1;check(QOTOM_XHCI_OPERATIONAL_FINAL);
    reset();final_other=0x10000;check(QOTOM_XHCI_OPERATIONAL_FINAL);
    reset();ext[0x460/4]|=0x10000;check(QOTOM_XHCI_OPERATIONAL_STATE);
    reset();previous.headers[0].raw^=0x10000;check(QOTOM_XHCI_OPERATIONAL_STATE);
    reset();prior_status=QOTOM_XHCI_SMI_FINAL;check(QOTOM_XHCI_OPERATIONAL_PRIOR);assert(!reads);
    reset();prior.write_attempted=0;check(QOTOM_XHCI_OPERATIONAL_PRIOR);
    reset();prior.before_control=2;check(QOTOM_XHCI_OPERATIONAL_PRIOR);
    reset();previous.count=49;check(QOTOM_XHCI_OPERATIONAL_PRIOR);
    reset();previous.count=0;check(QOTOM_XHCI_OPERATIONAL_PRIOR);
    reset();previous.legacy_offset=0x8464;check(QOTOM_XHCI_OPERATIONAL_PRIOR);
    uint64_t address=0;
    for(uint32_t off=0;off<0x10000;++off) {
        assert(!!qotom_xhci_operational_address(0x01000080,off,&address)==(off==0 || off==4));
        if(off==0 || off==4)assert(address==QOTOM_XHCI_BAR+0x80+off);
    }
    for(unsigned bit=0;bit<32;++bit)assert(!qotom_xhci_operational_address(0x01000080^(UINT32_C(1)<<bit),0,&address));
    assert(!qotom_xhci_operational_address(0x01000080,0,NULL));
    reset();assert(qotom_collect_xhci_operational(NULL,NULL,mmio,NULL,extended,NULL,operational,NULL,
        &header,&caps,&previous,prior_status,&prior,&out)==QOTOM_XHCI_OPERATIONAL_ARGUMENT);
    assert(!reads && !ops && !out.command && !out.status_before && !out.status_after);
    puts("PASS xHCI operational observation: all177 read failures, exact status-command-status order, CNR guards, complete refresh and zero failed output");
}
