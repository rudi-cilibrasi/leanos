#include <assert.h>
#include <stdio.h>
#include <string.h>
#include "../boot/qotom-ehci-bme.h"
static struct pci_enumeration_header header;
static const struct qotom_ehci_capabilities caps={0x1000020,0x200008,0x36881};
static const struct qotom_ehci_smi_result smi={1,0x2000,0};
static struct qotom_ehci_operational prior;
static uint32_t words[64];
static unsigned reads,writes,failed,op_reads;
static int ignored,write_failed,reassert,changed,change_final;
static enum qotom_ehci_operational_status prior_status;
static int config(void *ctx,uint8_t b,uint8_t d,uint8_t f,uint8_t off,uint32_t *out) {
    (void)ctx;assert(!b && d==29 && !f && !(off&3));
    if(++reads==failed)return 0;
    *out=words[off/4];
    if(reassert && reads==51)*out|=4;
    return 1;
}
static int capability(void *ctx,uint64_t a,uint32_t *out) {
    (void)ctx;if(++reads==failed)return 0;
    if(a==QOTOM_EHCI_BAR)*out=caps.capbase;
    else if(a==QOTOM_EHCI_BAR+4)*out=caps.structural;
    else {assert(a==QOTOM_EHCI_BAR+8);*out=caps.capability;}
    return 1;
}
static int operational(void *ctx,uint64_t a,uint32_t *out) {
    (void)ctx;if(++reads==failed)return 0;
    const unsigned offsets[4]={0x20,0x24,0x28,0x60};
    unsigned i=op_reads++%4;assert(a==QOTOM_EHCI_BAR+offsets[i]);
    const uint32_t values[4]={0x80000,0x1000,0,0};*out=values[i];
    if(changed && (!change_final || writes) && i==0)*out|=1;
    return 1;
}
static int write16(void *ctx,uint8_t b,uint8_t d,uint8_t f,uint8_t off,uint16_t value) {
    (void)ctx;assert(!b && d==29 && !f && off==4 && value==0x402 && reads==25 && !writes);
    ++writes;if(!ignored)words[1]=(words[1]&0xffff0000)|value;
    return !write_failed;
}
static void reset(void) {
    header=(struct pci_enumeration_header){.device=29,.words={0x0f348086,0x406,0x0c03200e,0,0xd0915000}};
    memset(words,0,sizeof words);memcpy(words,header.words,sizeof header.words);
    words[26]=0x1000001;words[27]=0;
    prior=(struct qotom_ehci_operational){0x80000,0x1000,0,0};prior_status=QOTOM_EHCI_OPERATIONAL_OK;
    reads=writes=failed=op_reads=0;ignored=write_failed=reassert=changed=change_final=0;
}
static struct qotom_ehci_bme_result out;
static void check(enum qotom_ehci_bme_status expected) {
    memset(&out,0x55,sizeof out);
    assert(qotom_clear_ehci_bme(config,NULL,capability,NULL,operational,NULL,write16,NULL,
        &header,&caps,QOTOM_EHCI_SMI_OBSERVED,&smi,prior_status,&prior,&out)==expected);
    assert(reads<=239 && writes<=1 && out.attempted==writes);
    if(!writes)assert(!out.before_command && !out.after_command);
    else assert(out.before_command==0x406);
}
int main(void) {
    assert(pci_enumerate_segment(NULL,NULL,NULL).status==PCI_ENUMERATION_INVALID_ARGUMENT);
    reset();check(QOTOM_EHCI_BME_OK);assert(reads==51 && writes==1 && out.after_command==0x402);
    for(unsigned i=1;i<=51;++i) {
        reset();failed=i;check(i<=24?QOTOM_EHCI_BME_REFRESH:i==25?QOTOM_EHCI_BME_COMMAND:
            i==26?QOTOM_EHCI_BME_READBACK:QOTOM_EHCI_BME_FINAL);
    }
    reset();ignored=1;check(QOTOM_EHCI_BME_READBACK);assert(out.after_command==0x406);
    reset();write_failed=1;check(QOTOM_EHCI_BME_WRITE);assert((words[1]&0xffff)==0x402 && !out.after_command);
    reset();reassert=1;check(QOTOM_EHCI_BME_FINAL);assert(out.after_command==0x406);
    reset();changed=1;check(QOTOM_EHCI_BME_STATE);assert(!writes);
    reset();changed=change_final=1;check(QOTOM_EHCI_BME_FINAL);
    for(unsigned bit=0;bit<32;++bit) {
        uint32_t mask=UINT32_C(1)<<bit;
        reset();prior.command^=mask;check(QOTOM_EHCI_BME_PRIOR);assert(!reads);
        reset();prior.status^=mask;check(QOTOM_EHCI_BME_PRIOR);assert(!reads);
        reset();prior.interrupt_enable=mask;check(QOTOM_EHCI_BME_PRIOR);assert(!reads);
        reset();prior.configured=mask;check(QOTOM_EHCI_BME_PRIOR);assert(!reads);
        if(bit<16) {
            reset();words[1]^=mask;check(bit==1?QOTOM_EHCI_BME_REFRESH:QOTOM_EHCI_BME_COMMAND);assert(!writes);
        } else {
            reset();words[1]|=mask;check(QOTOM_EHCI_BME_OK);assert(words[1]==(mask|0x402));
        }
    }
    reset();words[26]|=0x10000;check(QOTOM_EHCI_BME_REFRESH);
    reset();words[27]=0x2000;check(QOTOM_EHCI_BME_REFRESH);
    reset();prior_status=QOTOM_EHCI_OPERATIONAL_FINAL;check(QOTOM_EHCI_BME_PRIOR);
    reset();header.words[1]=0x402;check(QOTOM_EHCI_BME_PRIOR);
    reset();assert(qotom_clear_ehci_bme(NULL,NULL,capability,NULL,operational,NULL,write16,NULL,
        &header,&caps,QOTOM_EHCI_SMI_OBSERVED,&smi,prior_status,&prior,&out)==QOTOM_EHCI_BME_ARGUMENT);
    assert(!reads && !writes && !out.attempted && !out.before_command && !out.after_command);
    puts("PASS EHCI BME clear: all pinned read failures, stopped-state refresh, word-only preservation and ambiguous writes");
}
