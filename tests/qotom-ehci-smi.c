#include <assert.h>
#include <stdio.h>
#include <string.h>
#include "../boot/qotom-ehci-smi.h"
static struct pci_enumeration_header header={.device=29,.words={0x0f348086,0x406,0x0c03200e,0,0xd0915000}};
static struct qotom_ehci_capabilities caps={0x1000020,0x200008,0x36881};
static struct qotom_ehci_handoff_result prior;
static uint32_t words[64],final_extra;
static unsigned reads,writes,failed;
static int write_failed,write_ignored,reassert;
static enum qotom_ehci_handoff_status prior_status;
static int config(void *ctx,uint8_t b,uint8_t d,uint8_t f,uint8_t off,uint32_t *out) {
    (void)ctx;assert(!b && d==29 && !f && !(off&3));
    if(++reads==failed)return 0;
    *out=words[off/4];return 1;
}
static int mmio(void *ctx,uint64_t a,uint32_t *out) {
    (void)ctx;if(++reads==failed)return 0;
    if(a==QOTOM_EHCI_BAR)*out=caps.capbase;
    else if(a==QOTOM_EHCI_BAR+4)*out=caps.structural;
    else {assert(a==QOTOM_EHCI_BAR+8);*out=caps.capability;}
    return 1;
}
static int write32(void *ctx,uint8_t b,uint8_t d,uint8_t f,uint8_t off,uint32_t value) {
    (void)ctx;assert(!b && d==29 && !f && off==0x6c && value==0 && reads==10 && !writes);
    ++writes;
    if(!write_ignored)words[27]&=~QOTOM_EHCI_SMI_ENABLE;
    words[27]|=final_extra;
    if(reassert)words[26]|=0x10000;
    return !write_failed;
}
static void reset(void) {
    memset(words,0,sizeof words);memcpy(words,header.words,sizeof header.words);
    words[26]=0x1000001;words[27]=0x2000;
    prior=(struct qotom_ehci_handoff_result){1,1,0x1000001,0x2000};
    prior_status=QOTOM_EHCI_HANDOFF_OBSERVED;
    reads=writes=failed=final_extra=0;write_failed=write_ignored=reassert=0;
}
static struct qotom_ehci_smi_result out;
static void check(enum qotom_ehci_smi_status status) {
    memset(&out,0x55,sizeof out);
    assert(qotom_disable_ehci_smi(config,NULL,mmio,NULL,write32,NULL,&header,&caps,prior_status,&prior,&out)==status);
    assert(reads<=114 && writes<=1 && out.write_attempted==writes);
    if(!writes)assert(!out.before_control && !out.after_control);
}
int main(void) {
    assert(pci_enumerate_segment(NULL,NULL,NULL).status==PCI_ENUMERATION_INVALID_ARGUMENT);
    for(unsigned subset=0;subset<512;++subset) {
        reset();uint32_t mask=(subset&63)|((subset&448)<<7);
        words[27]=prior.final_control=mask|QOTOM_EHCI_SMI_STATUS;
        check(QOTOM_EHCI_SMI_OBSERVED);
        assert(reads==20 && out.before_control==(mask|QOTOM_EHCI_SMI_STATUS) && out.after_control==QOTOM_EHCI_SMI_STATUS);
    }
    reset();words[27]|=0x80000;check(QOTOM_EHCI_SMI_OBSERVED);assert(out.after_control==0x80000);
    for(unsigned i=1;i<=20;++i) {reset();failed=i;check(i<=10?QOTOM_EHCI_SMI_REFRESH:QOTOM_EHCI_SMI_FINAL);}
    reset();write_failed=1;check(QOTOM_EHCI_SMI_WRITE);assert(writes==1 && words[27]==0 && !out.after_control);
    reset();write_ignored=1;check(QOTOM_EHCI_SMI_READBACK);assert(out.after_control==0x2000);
    reset();reassert=1;check(QOTOM_EHCI_SMI_FINAL);
    for(unsigned bit=0;bit<32;++bit) {
        uint32_t mask=UINT32_C(1)<<bit;
        if(mask&(QOTOM_EHCI_SMI_ENABLE|QOTOM_EHCI_SMI_STATUS))continue;
        reset();words[27]|=mask;check(QOTOM_EHCI_SMI_STATE);
        reset();prior.final_control|=mask;check(QOTOM_EHCI_SMI_PRIOR);assert(!reads);
        reset();final_extra=mask;check(QOTOM_EHCI_SMI_READBACK);
    }
    reset();words[26]|=0x10000;check(QOTOM_EHCI_SMI_STATE);
    reset();words[27]^=1;check(QOTOM_EHCI_SMI_STATE);
    reset();prior_status=QOTOM_EHCI_HANDOFF_TIMEOUT;check(QOTOM_EHCI_SMI_PRIOR);assert(!reads);
    reset();prior.polls=101;check(QOTOM_EHCI_SMI_PRIOR);
    reset();prior.write_attempted=0;check(QOTOM_EHCI_SMI_PRIOR);
    reset();assert(qotom_disable_ehci_smi(NULL,NULL,mmio,NULL,write32,NULL,&header,&caps,prior_status,&prior,&out)==QOTOM_EHCI_SMI_ARGUMENT);
    assert(!reads && !writes && !out.write_attempted && !out.before_control && !out.after_control);
    puts("PASS EHCI SMI disable: all enable combinations, retained status bits, refresh/readback failures and one zero dword write");
}
