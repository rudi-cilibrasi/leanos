#include <assert.h>
#include <stdio.h>
#include <string.h>
#include "../boot/qotom-hda-state.h"
static struct pci_enumeration_header header;
static struct qotom_hda_observation prior;
static uint32_t cfg[6],globals[2][6],samples[11];
static unsigned reads,fail_at,mutate_at,mutate_word,mutate_mask;
static const uint8_t cfg_off[]={0,4,8,12,16,20};
static const uint8_t global_off[]={8,0,2,3,32,8},global_width[]={4,2,1,1,4,4};
static const uint16_t state_off[]={0x4c,0x5c,0x70,0x80,0xa0,0xc0,0xe0,0x100,0x120,0x140,0x160};
static int config(void *ctx,uint8_t b,uint8_t d,uint8_t f,uint8_t off,uint32_t *out) {
    assert(ctx==cfg && b==0 && d==27 && f==0 && reads<47);
    unsigned n=reads<18?reads:reads-29;
    assert(n<6 || (n>=12 && n<18));
    assert(off==cfg_off[n<6?n:n-12]);++reads;
    if(reads==mutate_at)cfg[mutate_word]^=mutate_mask;
    if(reads==fail_at)return 0;
    *out=cfg[off/4];return 1;
}
static int global(void *ctx,uint64_t address,uint8_t width,uint32_t *out) {
    assert(ctx==globals && reads<47);
    unsigned phase=reads<18?0:1,n=reads-(phase?29:0);
    assert(n>=6 && n<12);n-=6;
    assert(address==QOTOM_HDA_BAR+global_off[n] && width==global_width[n]);
    ++reads;if(reads==fail_at)return 0;
    *out=globals[phase][n];return 1;
}
static int state(void *ctx,uint64_t address,uint8_t width,uint32_t *out) {
    assert(ctx==samples && reads>=18 && reads<29);
    unsigned n=reads-18;assert(address==QOTOM_HDA_BAR+state_off[n] && width==(n<2?1:4));
    ++reads;if(reads==fail_at)return 0;
    *out=samples[n];return 1;
}
static void setup(void) {
    header=(struct pci_enumeration_header){.device=27,.words={0x0f048086,6,0x0403000e,0,0xd0910004,0}};
    memcpy(cfg,header.words,sizeof cfg);
    prior=(struct qotom_hda_observation){1,0x4401,0,1,0,1};
    const uint32_t g[]={1,0x4401,0,1,0,1};
    memcpy(globals[0],g,sizeof g);memcpy(globals[1],g,sizeof g);
    for(unsigned i=0;i<11;++i)samples[i]=i;
    reads=fail_at=mutate_at=mutate_word=mutate_mask=0;
}
static enum qotom_hda_state_status collect(enum qotom_hda_status status,struct qotom_hda_state *out) {
    memset(out,0xff,sizeof *out);reads=0;
    return qotom_collect_hda_state(config,cfg,global,globals,state,samples,&header,status,&prior,out);
}
static void zero(const struct qotom_hda_state *out) {
    const struct qotom_hda_state z={0};assert(!memcmp(out,&z,sizeof z));
}
int main(void) {
    assert(pci_enumerate_segment(NULL,NULL,NULL).status==PCI_ENUMERATION_INVALID_ARGUMENT);
    struct qotom_hda_state out;
    for(unsigned off=0;off<16384;++off)for(unsigned width=0;width<=8;++width) {
        int valid=((off==0x4c || off==0x5c) && width==1) || (off==0x70 && width==4) ||
            (off>=0x80 && off<=0x160 && !(off&31) && width==4);
        uint64_t address=7;assert(qotom_hda_state_address(off,width,&address)==valid);
        assert(address==(valid?QOTOM_HDA_BAR+off:7));
    }
    uint64_t a=7;assert(!qotom_hda_state_address(UINT32_MAX,4,&a) && a==7);
    assert(!qotom_hda_state_address(0x70,4,NULL));
    setup();assert(collect(QOTOM_HDA_OK,&out)==QOTOM_HDA_STATE_OK && reads==47);
    assert(out.corb==0 && out.rirb==1 && out.position==2);
    for(unsigned i=0;i<8;++i)assert(out.streams[i]==i+3);
    for(unsigned n=1;n<=47;++n) {
        setup();fail_at=n;
        assert(collect(QOTOM_HDA_OK,&out)==(n<=18?QOTOM_HDA_STATE_REFRESH:n<=29?QOTOM_HDA_STATE_READ:QOTOM_HDA_STATE_FINAL));
        assert(reads==n);zero(&out);
    }
    for(unsigned i=0;i<11;++i) {
        setup();samples[i]=i<2?255:UINT32_MAX;
        assert(collect(QOTOM_HDA_OK,&out)==QOTOM_HDA_STATE_ABSENT && reads==19+i);zero(&out);
        for(unsigned bit=0;bit<32;++bit) {
            setup();samples[i]=1u<<bit;
            enum qotom_hda_state_status s=collect(QOTOM_HDA_OK,&out);
            if(i<2 && bit>=8) {assert(s==QOTOM_HDA_STATE_WIDTH && reads==19+i);zero(&out);}
            else {
                assert(s==QOTOM_HDA_STATE_OK && reads==47);
                uint32_t value=i==0?out.corb:i==1?out.rirb:i==2?out.position:out.streams[i-3];
                assert(value==samples[i]);
            }
        }
    }
    for(unsigned i=0;i<6;++i)for(unsigned bit=0;bit<32;++bit) {
        setup();
        uint32_t *fields[]={&prior.control_before,&prior.capability,&prior.version_minor,
            &prior.version_major,&prior.interrupt,&prior.control_after};
        *fields[i]^=1u<<bit;
        assert(collect(QOTOM_HDA_OK,&out)==QOTOM_HDA_STATE_PRIOR && reads==0);zero(&out);
        for(unsigned phase=0;phase<2;++phase) {
            setup();globals[phase][i]^=1u<<bit;
            enum qotom_hda_state_status status=collect(QOTOM_HDA_OK,&out);
            if(phase)assert(status==QOTOM_HDA_STATE_FINAL);
            else assert(status==QOTOM_HDA_STATE_REFRESH || status==QOTOM_HDA_STATE_DRIFT);
            zero(&out);
        }
    }
    const uint32_t masks[]={UINT32_MAX,2,UINT32_MAX,0x00ff0000,UINT32_MAX,UINT32_MAX};
    for(unsigned i=0;i<6;++i)for(unsigned bit=0;bit<32;++bit)for(unsigned phase=0;phase<4;++phase) {
        setup();const unsigned starts[]={1,13,30,42};
        mutate_at=starts[phase];mutate_word=i;mutate_mask=1u<<bit;
        enum qotom_hda_state_status status=collect(QOTOM_HDA_OK,&out);
        if(masks[i]&(1u<<bit)) {
            assert(status==(phase<2?QOTOM_HDA_STATE_REFRESH:QOTOM_HDA_STATE_FINAL));zero(&out);
        } else assert(status==QOTOM_HDA_STATE_OK && reads==47);
    }
    for(unsigned s=1;s<=9;++s) {
        setup();assert(collect((enum qotom_hda_status)s,&out)==QOTOM_HDA_STATE_PRIOR && !reads);zero(&out);
    }
    setup();header.words[4]^=0x1000;
    assert(collect(QOTOM_HDA_OK,&out)==QOTOM_HDA_STATE_REFRESH && !reads);zero(&out);
    setup();
#define BAD(C,G,S,H,P,O) qotom_collect_hda_state(C,cfg,G,globals,S,samples,H,QOTOM_HDA_OK,P,O)
    assert(BAD(NULL,global,state,&header,&prior,&out)==QOTOM_HDA_STATE_ARGUMENT);zero(&out);
    assert(BAD(config,NULL,state,&header,&prior,&out)==QOTOM_HDA_STATE_ARGUMENT);zero(&out);
    assert(BAD(config,global,NULL,&header,&prior,&out)==QOTOM_HDA_STATE_ARGUMENT);zero(&out);
    assert(BAD(config,global,state,NULL,&prior,&out)==QOTOM_HDA_STATE_ARGUMENT);zero(&out);
    assert(BAD(config,global,state,&header,NULL,&out)==QOTOM_HDA_STATE_ARGUMENT);zero(&out);
    assert(BAD(config,global,state,&header,&prior,NULL)==QOTOM_HDA_STATE_ARGUMENT);
    assert(!reads);
    puts("PASS HDA state: exact47reads, all failures, prior/global/resource drift, widths, all stream bits");
}
