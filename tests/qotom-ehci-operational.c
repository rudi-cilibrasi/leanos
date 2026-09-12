#include <assert.h>
#include <stdio.h>
#include <string.h>
#include "../boot/qotom-ehci-operational.h"
static const struct pci_enumeration_header header={.device=29,.words={0x0f348086,0x406,0x0c03200e,0,0xd0915000}};
static struct qotom_ehci_capabilities caps;
static struct qotom_ehci_smi_result prior;
static enum qotom_ehci_smi_status prior_status;
static uint32_t words[64],samples[4];
static unsigned reads,op_reads,failed;
static int final_owner,final_enable,final_bar,final_caps;
static int config(void *ctx,uint8_t b,uint8_t d,uint8_t f,uint8_t off,uint32_t *out) {
    (void)ctx;assert(!b && d==29 && !f && !(off&3));
    if(++reads==failed)return 0;
    *out=words[off/4];
    if(op_reads==4) {
        if(final_owner && off==0x68)*out|=0x10000;
        if(final_enable && off==0x6c)*out|=0x2000;
        if(final_bar && off==0x10)*out^=0x1000;
    }
    return 1;
}
static int capability(void *ctx,uint64_t a,uint32_t *out) {
    (void)ctx;if(++reads==failed)return 0;
    if(a==QOTOM_EHCI_BAR)*out=0x1000020;
    else if(a==QOTOM_EHCI_BAR+4)*out=0x200008;
    else {assert(a==QOTOM_EHCI_BAR+8);*out=0x36881;}
    if(op_reads==4 && final_caps)*out^=1;
    return 1;
}
static int operational(void *ctx,uint64_t a,uint32_t *out) {
    (void)ctx;const unsigned offsets[4]={0x20,0x24,0x28,0x60};
    assert(op_reads<4 && a==QOTOM_EHCI_BAR+offsets[op_reads]);
    assert(reads==10+op_reads);
    if(++reads==failed)return 0;
    *out=samples[op_reads++];return 1;
}
static void reset(void) {
    memset(words,0,sizeof words);memcpy(words,header.words,sizeof header.words);
    words[26]=0x1000001;words[27]=0;
    caps=(struct qotom_ehci_capabilities){0x1000020,0x200008,0x36881};
    prior=(struct qotom_ehci_smi_result){1,0x2000,0};prior_status=QOTOM_EHCI_SMI_OBSERVED;
    reads=op_reads=failed=0;final_owner=final_enable=final_bar=final_caps=0;
    samples[0]=0x80001;samples[1]=0x8000;samples[2]=0x3f;samples[3]=1;
}
static void check(enum qotom_ehci_operational_status expected) {
    struct qotom_ehci_operational out;memset(&out,0x55,sizeof out);
    assert(qotom_collect_ehci_operational(config,NULL,capability,NULL,operational,NULL,
        &header,&caps,prior_status,&prior,&out)==expected);
    assert(reads<=118 && op_reads<=4);
    if(expected==QOTOM_EHCI_OPERATIONAL_OK) {
        assert(reads==24 && op_reads==4);
        assert(out.command==samples[0] && out.status==samples[1] && out.interrupt_enable==samples[2] && out.configured==samples[3]);
    } else assert(!out.command && !out.status && !out.interrupt_enable && !out.configured);
}
int main(void) {
    assert(pci_enumerate_segment(NULL,NULL,NULL).status==PCI_ENUMERATION_INVALID_ARGUMENT);
    reset();check(QOTOM_EHCI_OPERATIONAL_OK);
    for(unsigned i=1;i<=24;++i) {
        reset();failed=i;
        check(i<=10?QOTOM_EHCI_OPERATIONAL_REFRESH:i<=14?QOTOM_EHCI_OPERATIONAL_READ:QOTOM_EHCI_OPERATIONAL_FINAL);
    }
    for(unsigned i=0;i<4;++i) {
        reset();samples[i]=UINT32_MAX;check(QOTOM_EHCI_OPERATIONAL_ABSENT);
        for(unsigned bit=0;bit<32;++bit) {
            reset();samples[i]=UINT32_C(1)<<bit;check(QOTOM_EHCI_OPERATIONAL_OK);
        }
    }
    reset();final_owner=1;check(QOTOM_EHCI_OPERATIONAL_FINAL);
    reset();final_enable=1;check(QOTOM_EHCI_OPERATIONAL_FINAL);
    reset();final_bar=1;check(QOTOM_EHCI_OPERATIONAL_FINAL);
    reset();final_caps=1;check(QOTOM_EHCI_OPERATIONAL_FINAL);
    reset();words[26]|=0x10000;check(QOTOM_EHCI_OPERATIONAL_STATE);assert(!op_reads);
    reset();words[27]|=0x2000;check(QOTOM_EHCI_OPERATIONAL_STATE);assert(!op_reads);
    reset();words[4]^=0x1000;check(QOTOM_EHCI_OPERATIONAL_REFRESH);assert(!op_reads);
    reset();words[27]=QOTOM_EHCI_SMI_STATUS;check(QOTOM_EHCI_OPERATIONAL_OK);
    for(unsigned bit=0;bit<32;++bit) {
        uint32_t mask=UINT32_C(1)<<bit;
        reset();caps.capbase^=mask;check(QOTOM_EHCI_OPERATIONAL_PRIOR);assert(!reads);
        reset();caps.structural^=mask;check(QOTOM_EHCI_OPERATIONAL_PRIOR);assert(!reads);
        reset();caps.capability^=mask;check(QOTOM_EHCI_OPERATIONAL_PRIOR);assert(!reads);
        if(!(mask&QOTOM_EHCI_SMI_STATUS)) {
            reset();prior.after_control=mask;check(QOTOM_EHCI_OPERATIONAL_PRIOR);assert(!reads);
        }
        if(!(mask&(QOTOM_EHCI_SMI_STATUS|QOTOM_EHCI_SMI_ENABLE))) {
            reset();prior.before_control|=mask;check(QOTOM_EHCI_OPERATIONAL_PRIOR);assert(!reads);
        }
    }
    reset();prior_status=QOTOM_EHCI_SMI_READBACK;check(QOTOM_EHCI_OPERATIONAL_PRIOR);assert(!reads);
    reset();prior.write_attempted=0;check(QOTOM_EHCI_OPERATIONAL_PRIOR);assert(!reads);
    for(unsigned length=0;length<256;++length)for(unsigned off=0;off<4096;++off) {
        uint64_t a=UINT64_MAX;
        int valid=length==32 && (off==0 || off==4 || off==8 || off==0x40);
        assert(qotom_ehci_operational_address(0x1000000|length,off,&a)==valid);
        assert(a==(valid?QOTOM_EHCI_BAR+length+off:UINT64_MAX));
    }
    assert(!qotom_ehci_operational_address(0x1000020,0,NULL));
    struct qotom_ehci_operational out={1,2,3,4};reset();
    assert(qotom_collect_ehci_operational(NULL,NULL,capability,NULL,operational,NULL,
        &header,&caps,prior_status,&prior,&out)==QOTOM_EHCI_OPERATIONAL_ARGUMENT);
    assert(!reads && !out.command && !out.status && !out.interrupt_enable && !out.configured);
    puts("PASS EHCI operational observation: exact derived addresses, every read failure, ownership/SMI drift and zero failed publication");
}
