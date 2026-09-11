#include <assert.h>
#include <stdio.h>
#include "../boot/qotom-ehci-capabilities.h"
static uint32_t config_words[5] = {0x0f348086,0x406,0x0c03200e,0,0xd0915000};
static uint32_t mmio_words[3] = {0x01000020,4,0x6800};
static unsigned config_calls, mmio_calls;
static int fail_config=-1,fail_mmio=-1;
static int config_read(void *ctx,uint8_t b,uint8_t d,uint8_t f,uint8_t off,uint32_t *out) {
    (void)ctx; assert(b==0 && d==29 && f==0 && off%4==0 && off<=16);
    ++config_calls;
    if (off/4==fail_config) return 0;
    *out=config_words[off/4];return 1;
}
static int mmio_read(void *ctx,uint64_t address,uint32_t *out) {
    (void)ctx;
    assert(config_calls==5 && address==QOTOM_EHCI_BAR+4*mmio_calls);
    unsigned i=mmio_calls++;
    if ((int)i==fail_mmio) return 0;
    *out=mmio_words[i];return 1;
}
static struct pci_enumeration_header initial={.bus=0,.device=29,.function=0,
    .words={0x0f348086,0x406,0x0c03200e,0,0xd0915000}};
static void check(enum qotom_ehci_status expected) {
    config_calls=mmio_calls=0;
    struct qotom_ehci_capabilities out={123,456,789};
    assert(qotom_collect_ehci_capabilities(config_read,NULL,mmio_read,NULL,&initial,&out)==expected);
    if (expected==QOTOM_EHCI_OK)
        assert(out.capbase==mmio_words[0] && out.structural==mmio_words[1] && out.capability==mmio_words[2]);
    else assert(!out.capbase && !out.structural && !out.capability);
}
int main(void) {
    assert(pci_enumerate_segment(NULL,NULL,NULL).status==PCI_ENUMERATION_INVALID_ARGUMENT);
    check(QOTOM_EHCI_OK);assert(config_calls==5 && mmio_calls==3);
    for (int i=0;i<5;++i) {fail_config=i;check(QOTOM_EHCI_CONFIG_READ);assert(!mmio_calls);}
    fail_config=-1;
    const uint32_t masks[5]={1,2,1,0x10000,0x1000};
    for (int i=0;i<5;++i) {config_words[i]^=masks[i];check(QOTOM_EHCI_DRIFT);assert(!mmio_calls);config_words[i]^=masks[i];}
    for (int i=0;i<3;++i) {
        fail_mmio=i;check(QOTOM_EHCI_MMIO_READ);fail_mmio=-1;
        uint32_t saved=mmio_words[i];mmio_words[i]=UINT32_MAX;check(QOTOM_EHCI_ABSENT);mmio_words[i]=saved;
    }
    for (unsigned length=0;length<256;++length) {
        mmio_words[0]=0x1000000|length;
        check(length>=16 && !(length&3) ? QOTOM_EHCI_OK : QOTOM_EHCI_FORMAT);
    }
    mmio_words[0]=0x1000020;
    mmio_words[1]=0;check(QOTOM_EHCI_FORMAT);mmio_words[1]=4;
    initial.words[4]^=0x1000;check(QOTOM_EHCI_HEADER);assert(!config_calls && !mmio_calls);initial.words[4]^=0x1000;
    for (uint32_t offset=0;offset<8192;++offset) {
        uint64_t address=123;
        int ok=qotom_ehci_capability_address(offset,&address);
        assert(ok==(offset==0 || offset==4 || offset==8));
        assert(address==(ok ? QOTOM_EHCI_BAR+offset : 123));
    }
    assert(!qotom_ehci_capability_address(UINT32_MAX,NULL));
    puts("PASS EHCI capability collector: staged publication, drift, read failures and offset bounds");
}
