#include <assert.h>
#include <stdio.h>
#include <string.h>
#include "../boot/qotom-ehci-handoff.h"
static struct pci_enumeration_header initial={.device=29,.words={0x0f348086,0x406,0x0c03200e,0,0xd0915000}};
static struct qotom_ehci_capabilities caps={0x1000020,0x200008,0x36881};
static struct qotom_ehci_legacy_snapshot previous;
static uint32_t words[64];
static unsigned reads,writes,delays,release_at,fail_read,fail_delay,mutation_at;
static uint32_t mutation;
static int fail_write,final_drift;
static uint32_t final_support_xor;
static int config(void *ctx,uint8_t b,uint8_t d,uint8_t f,uint8_t off,uint32_t *v) {
    (void)ctx;assert(!b && d==29 && !f && !(off&3));
    if(++reads==fail_read)return 0;
    if(writes && delays>=release_at && off==0) {
        if(final_drift)return 0;
        words[26]^=final_support_xor;
    }
    *v=words[off/4];return 1;
}
static int mmio(void *ctx,uint64_t a,uint32_t *v) {
    (void)ctx;if(++reads==fail_read)return 0;
    if(a==QOTOM_EHCI_BAR)*v=caps.capbase;
    else if(a==QOTOM_EHCI_BAR+4)*v=caps.structural;
    else {assert(a==QOTOM_EHCI_BAR+8);*v=caps.capability;}
    return 1;
}
static int write_byte(void *ctx,uint8_t b,uint8_t d,uint8_t f,uint8_t off,uint8_t v) {
    (void)ctx;assert(!b && d==29 && !f && off==0x6b && v==1 && !writes);
    assert(reads==10);++writes;
    words[26]|=0x01000000; /* Failure may still have changed hardware. */
    return !fail_write;
}
static int delay(void *ctx,uint32_t ms) {
    (void)ctx;assert(ms==10 && writes==1);++delays;
    if(delays==fail_delay)return 0;
    if(delays==release_at)words[26]&=~UINT32_C(0x10000);
    if(delays==mutation_at)words[26]^=mutation;
    return 1;
}
static void reset(void) {
    memset(words,0,sizeof words);memcpy(words,initial.words,sizeof initial.words);
    words[26]=0x10001;words[27]=0x82005;
    previous=(struct qotom_ehci_legacy_snapshot){.count=1,.legacy_offset=104,.control_status=0x82005,.headers={{104,0x10001}}};
    reads=writes=delays=fail_read=fail_delay=mutation_at=0;
    release_at=1;mutation=final_support_xor=0;fail_write=final_drift=0;
}
static struct qotom_ehci_handoff_result out;
static void check(enum qotom_ehci_handoff_status expected) {
    memset(&out,0x55,sizeof out);
    assert(qotom_request_ehci_handoff(config,NULL,mmio,NULL,write_byte,NULL,delay,NULL,&initial,&caps,&previous,&out)==expected);
    assert(reads<=214 && writes<=1 && delays<=100 && out.polls<=100);
    assert(out.write_attempted==writes);
    if(expected!=QOTOM_EHCI_HANDOFF_OBSERVED)assert(!out.final_control);
}
int main(void) {
    assert(pci_enumerate_segment(NULL,NULL,NULL).status==PCI_ENUMERATION_INVALID_ARGUMENT);
    for(unsigned i=1;i<=100;++i) {
        reset();release_at=i;check(QOTOM_EHCI_HANDOFF_OBSERVED);
        assert(out.polls==i && delays==i && out.last_support==0x1000001 && out.final_control==0x82005);
    }
    reset();release_at=101;check(QOTOM_EHCI_HANDOFF_TIMEOUT);assert(out.polls==100 && out.last_support==0x1010001);
    for(unsigned i=1;i<=10;++i) {reset();fail_read=i;check(QOTOM_EHCI_HANDOFF_REFRESH);assert(!writes && !delays);}
    for(unsigned i=1;i<=100;++i) {
        reset();release_at=101;fail_read=10+i;check(QOTOM_EHCI_HANDOFF_READ);assert(out.polls==i);
        reset();release_at=101;fail_delay=i;check(QOTOM_EHCI_HANDOFF_DELAY);assert(out.polls==i-1);
    }
    for(unsigned i=12;i<=21;++i) {reset();fail_read=i;check(QOTOM_EHCI_HANDOFF_FINAL);}
    for(unsigned bit=0;bit<32;++bit) {
        if(bit==16)continue;
        reset();mutation_at=1;mutation=UINT32_C(1)<<bit;check(QOTOM_EHCI_HANDOFF_CHANGED);
    }
    reset();fail_write=1;check(QOTOM_EHCI_HANDOFF_WRITE);assert(writes==1 && !delays && words[26]==0x1010001);
    reset();final_drift=1;check(QOTOM_EHCI_HANDOFF_FINAL);
    for(unsigned bit=0;bit<32;++bit) {
        reset();final_support_xor=UINT32_C(1)<<bit;check(QOTOM_EHCI_HANDOFF_FINAL);
    }
    reset();previous.count=49;check(QOTOM_EHCI_HANDOFF_DRIFT);
    reset();previous.headers[0].raw^=0x100;check(QOTOM_EHCI_HANDOFF_DRIFT);
    reset();previous.control_status^=1;check(QOTOM_EHCI_HANDOFF_DRIFT);
    const uint32_t bad[]={1,0x1000001,0x1010001,0x2010001,0x81010001};
    for(unsigned i=0;i<sizeof bad/sizeof bad[0];++i) {
        reset();words[26]=previous.headers[0].raw=bad[i];check(QOTOM_EHCI_HANDOFF_INITIAL);assert(!writes);
    }
    reset();
    assert(qotom_request_ehci_handoff(NULL,NULL,mmio,NULL,write_byte,NULL,delay,NULL,&initial,&caps,&previous,&out)==QOTOM_EHCI_HANDOFF_ARGUMENT);
    assert(!out.write_attempted && !out.polls && !out.last_support && !out.final_control && !reads);
    puts("PASS bounded EHCI handoff: every release, read failure, delay failure, timeout, drift and exact byte write");
}
