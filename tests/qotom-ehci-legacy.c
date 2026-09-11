#include <assert.h>
#include <stdio.h>
#include <string.h>
#include "../boot/qotom-ehci-legacy.h"
static uint32_t words[64];
static unsigned reads;
static int failed=-1;
static uint32_t mmio_drift;
static struct pci_enumeration_header initial={.device=29,.words={0x0f348086,0x406,0x0c03200e,0,0xd0915000}};
static struct qotom_ehci_capabilities previous={0x1000020,8,0x6800};
static int config(void *ctx,uint8_t b,uint8_t d,uint8_t f,uint8_t off,uint32_t *v) {
    (void)ctx;assert(!b && d==29 && !f && !(off&3));++reads;
    if(off==failed)return 0;
    *v=words[off/4];return 1;
}
static int mmio(void *ctx,uint64_t a,uint32_t *v) {
    (void)ctx;++reads;
    if(a==QOTOM_EHCI_BAR)*v=previous.capbase;
    else if(a==QOTOM_EHCI_BAR+4)*v=previous.structural;
    else {assert(a==QOTOM_EHCI_BAR+8);*v=previous.capability ^ mmio_drift;}
    return 1;
}
static struct qotom_ehci_legacy_snapshot out;
static void check(enum qotom_ehci_legacy_status status) {
    reads=0;memset(&out,0x55,sizeof out);
    assert(qotom_collect_ehci_legacy(config,NULL,mmio,NULL,&initial,&previous,&out)==status);
    assert(reads<=57);
    if(status!=QOTOM_EHCI_LEGACY_OK)assert(!out.count && !out.legacy_offset && !out.control_status);
}
int main(void) {
    assert(pci_enumerate_segment(NULL,NULL,NULL).status==PCI_ENUMERATION_INVALID_ARGUMENT);
    memcpy(words,initial.words,sizeof initial.words);
    words[0x68/4]=0x01010001;words[0x6c/4]=0x12340000;
    check(QOTOM_EHCI_LEGACY_OK);
    assert(reads==10 && out.count==1 && out.legacy_offset==0x68 && out.control_status==0x12340000);
    failed=0x6c;check(QOTOM_EHCI_LEGACY_READ);failed=0x68;check(QOTOM_EHCI_LEGACY_READ);failed=-1;
    words[0x6c/4]=UINT32_MAX;check(QOTOM_EHCI_LEGACY_ABSENT);
    for(unsigned pointer=1;pointer<256;++pointer) {
        if(pointer>=64 && !(pointer&3))continue;
        previous.capability=pointer<<8;check(QOTOM_EHCI_LEGACY_POINTER);assert(reads==8);
    }
    previous.capability=64<<8;
    for(unsigned i=0;i<48;++i)words[16+i]=2|((i==47?0:68+i*4)<<8);
    check(QOTOM_EHCI_LEGACY_OK);assert(out.count==48 && reads==56 && !out.legacy_offset);
    for(unsigned i=0;i<48;++i) {
        failed=64+i*4;check(QOTOM_EHCI_LEGACY_READ);failed=-1;
        uint32_t saved=words[16+i];words[16+i]=2|(64<<8);check(QOTOM_EHCI_LEGACY_CYCLE);words[16+i]=saved;
    }
    words[16]=1|(68<<8);words[17]=2;check(QOTOM_EHCI_LEGACY_OVERLAP);
    words[16]=1|(72<<8);words[18]=1;check(QOTOM_EHCI_LEGACY_DUPLICATE);
    words[16]=0;check(QOTOM_EHCI_LEGACY_ID);words[16]=255;check(QOTOM_EHCI_LEGACY_ID);
    previous.capability=252<<8;words[63]=1;check(QOTOM_EHCI_LEGACY_POINTER);
    previous.capability=0;check(QOTOM_EHCI_LEGACY_OK);assert(!out.count && !out.legacy_offset);
    words[0]^=1;check(QOTOM_EHCI_LEGACY_REFRESH);words[0]^=1;
    mmio_drift=0x100;check(QOTOM_EHCI_LEGACY_DRIFT);mmio_drift=0;
    assert(reads==8);
    assert(qotom_collect_ehci_legacy(NULL,NULL,mmio,NULL,&initial,&previous,&out)==QOTOM_EHCI_LEGACY_ARGUMENT);
    assert(qotom_collect_ehci_legacy(config,NULL,mmio,NULL,&initial,NULL,&out)==QOTOM_EHCI_LEGACY_ARGUMENT);
    assert(qotom_collect_ehci_legacy(config,NULL,mmio,NULL,&initial,&previous,NULL)==QOTOM_EHCI_LEGACY_ARGUMENT);
    /* A valid backward link is not a cycle. */
    previous.capability=104<<8;words[26]=2|(64<<8);words[16]=1;words[17]=0;
    check(QOTOM_EHCI_LEGACY_OK);assert(out.count==2 && out.legacy_offset==64);
    puts("PASS EHCI extended list: bounded traversal, pointer failures, cycles, overlap, duplicates and private failure output");
}
