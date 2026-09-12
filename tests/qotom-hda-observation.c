#include <assert.h>
#include <stdio.h>
#include <string.h>
#include "../boot/qotom-hda-observation.h"
static struct pci_enumeration_header initial;
static uint32_t cfg[64], mmio_values[6];
static unsigned reads,fail_at,mutate_at,mutate_offset,mutate_mask;
static const uint8_t expected[18]={0,4,8,12,16,20,8,0,2,3,32,8,0,4,8,12,16,20};
static int config(void *ctx,uint8_t b,uint8_t d,uint8_t f,uint8_t off,uint32_t *out) {
    (void)ctx;assert(b==0 && d==27 && f==0 && reads<18);
    assert(reads<6 || reads>=12);assert(off==expected[reads]);++reads;
    if(reads==mutate_at) cfg[mutate_offset/4]^=mutate_mask;
    if(reads==fail_at)return 0;
    *out=cfg[off/4];return 1;
}
static int mmio(void *ctx,uint64_t addr,uint8_t width,uint32_t *out) {
    (void)ctx;assert(reads>=6 && reads<12 && addr==QOTOM_HDA_BAR+expected[reads]);
    const uint8_t widths[]={4,2,1,1,4,4};
    unsigned index=reads-6;assert(width==widths[index]);++reads;if(reads==fail_at)return 0;
    *out=mmio_values[index];return 1;
}
static void setup(void) {
    memset(&initial,0,sizeof initial);memset(cfg,0,sizeof cfg);
    initial.device=27;initial.words[0]=cfg[0]=0x0f048086;
    initial.words[1]=cfg[1]=0x00100006;initial.words[2]=cfg[2]=0x0403000e;
    initial.words[4]=cfg[4]=QOTOM_HDA_BAR|4;
    const uint32_t samples[]={1,0x4401,0,1,0,1};
    memcpy(mmio_values,samples,sizeof samples);
    reads=fail_at=mutate_at=0;
}
static enum qotom_hda_status collect(struct qotom_hda_observation *out) {
    memset(out,0xff,sizeof *out);reads=0;
    return qotom_collect_hda_observation(config,NULL,mmio,NULL,&initial,out);
}
static void zero(struct qotom_hda_observation *out) {
    const struct qotom_hda_observation empty={0};assert(!memcmp(out,&empty,sizeof empty));
}
int main(void) {
    assert(pci_enumerate_segment(NULL,NULL,NULL).status==PCI_ENUMERATION_INVALID_ARGUMENT);
    struct qotom_hda_observation out;
    for(unsigned off=0;off<16384;++off)for(unsigned width=0;width<=8;++width) {
        uint64_t addr=7;
        int valid=(off==0 && width==2) || ((off==2 || off==3) && width==1) ||
            ((off==8 || off==32) && width==4);
        assert(qotom_hda_observation_address(off,width,&addr)==valid);
        assert(addr==(valid?QOTOM_HDA_BAR+off:7));
    }
    uint64_t address=0;assert(!qotom_hda_observation_address(UINT32_MAX,4,&address));
    assert(!qotom_hda_observation_address(0,2,NULL));
    setup();assert(collect(&out)==QOTOM_HDA_OK && reads==18);
    assert(out.control_before==1 && out.capability==0x4401 && out.version_minor==0 &&
        out.version_major==1 && out.interrupt==0 && out.control_after==1);
    for(unsigned n=1;n<=18;++n) {
        setup();fail_at=n;
        assert(collect(&out)==((n>=7 && n<=12)?QOTOM_HDA_MMIO_READ:QOTOM_HDA_CONFIG_READ));
        assert(reads==n);zero(&out);
    }
    const unsigned bits[]={32,16,8,8,32,32};
    for(unsigned i=0;i<6;++i) {
        setup();mmio_values[i]=bits[i]==32?UINT32_MAX:(1u<<bits[i])-1;
        assert(collect(&out)==QOTOM_HDA_ABSENT && reads==7+i);zero(&out);
        for(unsigned bit=0;bit<32;++bit) {
            setup();mmio_values[i]=1u<<bit;
            if(i==0 || i==5)mmio_values[i]|=1;
            enum qotom_hda_status status=collect(&out);
            if(bit>=bits[i]) {assert(status==QOTOM_HDA_WIDTH && reads==7+i);zero(&out);}
            else {
                assert(status==QOTOM_HDA_OK && reads==18);
                const uint32_t actual[]={out.control_before,out.capability,out.version_minor,
                    out.version_major,out.interrupt,out.control_after};
                assert(actual[i]==mmio_values[i]);
            }
        }
    }
    /* CRST clear aborts before GCAP/other accesses or before final config;
     * every other GCTL bit is irrelevant to this read-access precondition. */
    for(unsigned i=0;i<6;i+=5)for(unsigned bit=0;bit<32;++bit) {
        setup();mmio_values[i]=(1u<<bit)&~1u;
        assert(collect(&out)==QOTOM_HDA_RESET && reads==7+i);zero(&out);
    }
    /* GCTL is a pair of observations, not an atomic/stable-state certificate. */
    setup();mmio_values[5]=0x101;assert(collect(&out)==QOTOM_HDA_OK);
    assert(out.control_before==1 && out.control_after==0x101);
    const unsigned offsets[]={0,4,8,12,16,20};
    const uint32_t masks[]={UINT32_MAX,2,UINT32_MAX,0x00ff0000,UINT32_MAX,UINT32_MAX};
    for(unsigned i=0;i<6;++i)for(unsigned bit=0;bit<32;++bit) {
        setup();cfg[offsets[i]/4]^=1u<<bit;
        enum qotom_hda_status status=collect(&out);
        if(masks[i]&(1u<<bit)) {assert(status==QOTOM_HDA_DRIFT);zero(&out);}
        else assert(status==QOTOM_HDA_OK);
        setup();mutate_at=13;mutate_offset=offsets[i];mutate_mask=1u<<bit;
        status=collect(&out);
        if(masks[i]&(1u<<bit)) {assert(status==QOTOM_HDA_DRIFT);zero(&out);}
        else assert(status==QOTOM_HDA_OK);
        setup();initial.words[offsets[i]/4]^=1u<<bit;
        status=collect(&out);
        if(masks[i]&(1u<<bit)) {assert(status==QOTOM_HDA_HEADER && !reads);zero(&out);}
        else assert(status==QOTOM_HDA_OK);
    }
    setup();initial.bus=1;assert(collect(&out)==QOTOM_HDA_HEADER);zero(&out);
    setup();initial.device=20;assert(collect(&out)==QOTOM_HDA_HEADER);zero(&out);
    setup();initial.function=1;assert(collect(&out)==QOTOM_HDA_HEADER);zero(&out);
    setup();assert(qotom_collect_hda_observation(NULL,NULL,mmio,NULL,&initial,&out)==QOTOM_HDA_ARGUMENT);zero(&out);
    assert(qotom_collect_hda_observation(config,NULL,NULL,NULL,&initial,&out)==QOTOM_HDA_ARGUMENT);zero(&out);
    assert(qotom_collect_hda_observation(config,NULL,mmio,NULL,NULL,&out)==QOTOM_HDA_ARGUMENT);zero(&out);
    assert(qotom_collect_hda_observation(config,NULL,mmio,NULL,&initial,NULL)==QOTOM_HDA_ARGUMENT);
    puts("PASS HDA global observer: exact18 width-specific reads, all failures, identity/resource drift, raw payloads");
}
