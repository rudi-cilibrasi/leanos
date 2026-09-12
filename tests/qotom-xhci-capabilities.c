#include <assert.h>
#include <stdio.h>
#include <string.h>
#include "../boot/qotom-xhci-capabilities.h"
static struct pci_enumeration_header header;
static uint32_t config_words[6],samples[7];
static unsigned reads,failed,mmio_reads,drift_index;
static uint32_t drift_mask;
static int drift_final;
static int config(void *ctx,uint8_t b,uint8_t d,uint8_t f,uint8_t offset,uint32_t *out) {
    (void)ctx;assert(!b && d==20 && !f && !(offset&3) && offset<=20);
    if(++reads==failed)return 0;
    *out=config_words[offset/4];
    if(offset/4==drift_index && (!drift_final || mmio_reads==7))*out^=drift_mask;
    return 1;
}
static int mmio(void *ctx,uint64_t address,uint32_t *out) {
    (void)ctx;assert(mmio_reads<7 && address==QOTOM_XHCI_BAR+mmio_reads*4);
    if(++reads==failed)return 0;
    *out=samples[mmio_reads++];return 1;
}
static void reset(void) {
    header=(struct pci_enumeration_header){.device=20,.words={0x0f358086,0x2900006,0x0c03300e,0,0xd0900004,0}};
    memcpy(config_words,header.words,sizeof config_words);
    /* Datasheet defaults are synthetic test values, not a physical MMIO capture. */
    const uint32_t values[7]={0x1000080,0x07000820,0x84000054,0x40001,0x200071e1,0x3000,0x2000};
    memcpy(samples,values,sizeof samples);
    reads=failed=mmio_reads=drift_index=drift_mask=0;drift_final=0;
}
static void check(enum qotom_xhci_status expected) {
    struct qotom_xhci_capabilities out;memset(&out,0x55,sizeof out);
    assert(qotom_collect_xhci_capabilities(config,NULL,mmio,NULL,&header,&out)==expected);
    assert(reads<=19 && mmio_reads<=7);
    for(unsigned i=0;i<7;++i)assert(out.words[i]==(expected==QOTOM_XHCI_OK?samples[i]:0));
    if(expected==QOTOM_XHCI_OK)assert(reads==19 && mmio_reads==7);
}
int main(void) {
    assert(pci_enumerate_segment(NULL,NULL,NULL).status==PCI_ENUMERATION_INVALID_ARGUMENT);
    reset();check(QOTOM_XHCI_OK);
    for(unsigned i=1;i<=19;++i){reset();failed=i;check(i>=7 && i<=13?QOTOM_XHCI_MMIO_READ:QOTOM_XHCI_CONFIG_READ);}
    for(unsigned i=0;i<7;++i){reset();samples[i]=UINT32_MAX;check(QOTOM_XHCI_ABSENT);}
    for(unsigned bit=0;bit<32;++bit) {
        reset();samples[0]^=UINT32_C(1)<<bit;check(QOTOM_XHCI_FORMAT);
        reset();header.words[5]=UINT32_C(1)<<bit;check(QOTOM_XHCI_HEADER);assert(!reads);
    }
    const uint32_t masks[6]={UINT32_MAX,2,UINT32_MAX,0xff0000,UINT32_MAX,UINT32_MAX};
    for(unsigned i=0;i<6;++i)for(unsigned bit=0;bit<32;++bit)for(unsigned final=0;final<2;++final) {
        reset();drift_index=i;drift_mask=UINT32_C(1)<<bit;drift_final=final;
        check(drift_mask&masks[i]?QOTOM_XHCI_DRIFT:QOTOM_XHCI_OK);
    }
    for(unsigned offset=0;offset<4096;++offset) {
        uint64_t address=42;int valid=offset<=24 && !(offset&3);
        assert(qotom_xhci_capability_address(offset,&address)==valid);
        assert(address==(valid?QOTOM_XHCI_BAR+offset:42));
    }
    assert(!qotom_xhci_capability_address(UINT32_MAX,NULL));
    reset();header.words[4]=0xd0900000;check(QOTOM_XHCI_HEADER);
    reset();header.device=29;check(QOTOM_XHCI_HEADER);
    reset();struct qotom_xhci_capabilities out={{1}};
    assert(qotom_collect_xhci_capabilities(NULL,NULL,mmio,NULL,&header,&out)==QOTOM_XHCI_ARGUMENT);
    for(unsigned i=0;i<7;++i)assert(!out.words[i]);
    puts("PASS xHCI capability collector: paired BAR binding, all read failures, bracketed drift, exact addresses and private output");
}
