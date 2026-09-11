#include <assert.h>
#include <stdio.h>
#include <string.h>
#include "../boot/qotom-ahci-capabilities.h"
static struct pci_enumeration_header initial;
static uint32_t cfg[64], mmio_values[5];
static unsigned reads,fail_at,mutate_at,mutate_offset,mutate_mask;
static const uint8_t expected[15]={0,4,8,12,36,0,4,12,16,36,0,4,8,12,36};
static int config(void *ctx,uint8_t b,uint8_t d,uint8_t f,uint8_t off,uint32_t *out) {
    (void)ctx;assert(b==0 && d==19 && f==0 && reads<15);
    assert(reads<5 || reads>=10);assert(off==expected[reads]);++reads;
    if(reads==mutate_at) cfg[mutate_offset/4]^=mutate_mask;
    if(reads==fail_at)return 0;
    *out=cfg[off/4];return 1;
}
static int mmio(void *ctx,uint64_t addr,uint32_t *out) {
    (void)ctx;assert(reads>=5 && reads<10 && addr==QOTOM_AHCI_BAR+expected[reads]);
    unsigned index=reads-5;++reads;if(reads==fail_at)return 0;
    *out=mmio_values[index];return 1;
}
static void setup(void) {
    memset(&initial,0,sizeof initial);memset(cfg,0,sizeof cfg);
    initial.device=19;initial.words[0]=cfg[0]=0x0f238086;
    initial.words[1]=cfg[1]=0x02b00007;initial.words[2]=cfg[2]=0x0106010e;
    initial.words[9]=cfg[9]=QOTOM_AHCI_BAR;
    for(unsigned i=0;i<5;++i)mmio_values[i]=i;
    reads=fail_at=mutate_at=0;
}
static enum qotom_ahci_status collect(struct qotom_ahci_capabilities *out) {
    memset(out,0xff,sizeof *out);reads=0;
    return qotom_collect_ahci_capabilities(config,NULL,mmio,NULL,&initial,out);
}
static void zero(struct qotom_ahci_capabilities *out) {
    const struct qotom_ahci_capabilities empty={0};assert(!memcmp(out,&empty,sizeof empty));
}
int main(void) {
    assert(pci_enumerate_segment(NULL,NULL,NULL).status==PCI_ENUMERATION_INVALID_ARGUMENT);
    struct qotom_ahci_capabilities out;
    for(unsigned off=0;off<4096;++off) {
        uint64_t addr=7;int valid=off==0 || off==4 || off==12 || off==16 || off==36;
        assert(qotom_ahci_capability_address(off,&addr)==valid);
        assert(addr==(valid?QOTOM_AHCI_BAR+off:7));
    }
    uint64_t address=0;assert(!qotom_ahci_capability_address(UINT32_MAX,&address));
    assert(!qotom_ahci_capability_address(0,NULL));
    setup();assert(collect(&out)==QOTOM_AHCI_OK && reads==15);
    assert(out.capability==0 && out.control==1 && out.ports==2 && out.version==3 && out.extended==4);
    for(unsigned n=1;n<=15;++n) {
        setup();fail_at=n;assert(collect(&out)==((n>=6 && n<=10)?QOTOM_AHCI_MMIO_READ:QOTOM_AHCI_CONFIG_READ));zero(&out);
    }
    for(unsigned i=0;i<5;++i) {
        setup();mmio_values[i]=UINT32_MAX;assert(collect(&out)==QOTOM_AHCI_ABSENT);zero(&out);
        for(unsigned bit=0;bit<32;++bit) {
            setup();mmio_values[i]=1u<<bit;assert(collect(&out)==QOTOM_AHCI_OK);
            uint32_t actual[]={out.capability,out.control,out.ports,out.version,out.extended};assert(actual[i]==(1u<<bit));
        }
    }
    const unsigned offsets[]={0,4,8,12,36};
    const uint32_t masks[]={UINT32_MAX,2,UINT32_MAX,0x00ff0000,UINT32_MAX};
    for(unsigned i=0;i<5;++i)for(unsigned bit=0;bit<32;++bit) {
        setup();cfg[offsets[i]/4]^=1u<<bit;
        enum qotom_ahci_status status=collect(&out);
        if(masks[i]&(1u<<bit)) {assert(status==QOTOM_AHCI_DRIFT);zero(&out);}
        else assert(status==QOTOM_AHCI_OK);
        setup();mutate_at=11;mutate_offset=offsets[i];mutate_mask=1u<<bit;
        status=collect(&out);
        if(masks[i]&(1u<<bit)) {assert(status==QOTOM_AHCI_DRIFT);zero(&out);}
        else assert(status==QOTOM_AHCI_OK);
        setup();initial.words[offsets[i]/4]^=1u<<bit;
        status=collect(&out);
        if(masks[i]&(1u<<bit)) {assert(status==QOTOM_AHCI_HEADER && !reads);zero(&out);}
        else assert(status==QOTOM_AHCI_OK);
    }
    setup();initial.bus=1;assert(collect(&out)==QOTOM_AHCI_HEADER);zero(&out);
    setup();initial.device=20;assert(collect(&out)==QOTOM_AHCI_HEADER);zero(&out);
    setup();initial.function=1;assert(collect(&out)==QOTOM_AHCI_HEADER);zero(&out);
    setup();assert(qotom_collect_ahci_capabilities(NULL,NULL,mmio,NULL,&initial,&out)==QOTOM_AHCI_ARGUMENT);zero(&out);
    assert(qotom_collect_ahci_capabilities(config,NULL,NULL,NULL,&initial,&out)==QOTOM_AHCI_ARGUMENT);zero(&out);
    assert(qotom_collect_ahci_capabilities(config,NULL,mmio,NULL,NULL,&out)==QOTOM_AHCI_ARGUMENT);zero(&out);
    assert(qotom_collect_ahci_capabilities(config,NULL,mmio,NULL,&initial,NULL)==QOTOM_AHCI_ARGUMENT);
    puts("PASS AHCI capability observer: exact15reads, all failures, identity/resource drift, raw payloads");
}
