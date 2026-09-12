#include <assert.h>
#include <stdio.h>
#include <string.h>
#include "../boot/qotom-hda-bme.h"
static struct pci_enumeration_header header;
static struct qotom_hda_observation caps;
static struct qotom_hda_state prior;
static uint32_t cfg[6],globals[6],states[11];
static unsigned reads,writes,fail_at,mutate_at,mutate_index;
static uint32_t mutate_mask;
static int mutate_state,mutate_config,write_fails,write_ignored;
static unsigned local(unsigned n) {return n>=49?n-49:n;}
static unsigned offset_at(unsigned n) {
    static const unsigned c[]={0,4,8,12,16,20},g[]={8,0,2,3,32,8};
    static const unsigned p[]={0x4c,0x5c,0x70,0x80,0xa0,0xc0,0xe0,0x100,0x120,0x140,0x160};
    if(n==47 || n==48 || n==96)return 4;
    n=local(n);
    if(n>=18 && n<29)return p[n-18];
    if(n>=29)n-=29;
    return n<6?c[n]:n<12?g[n-6]:c[n-12];
}
static int step(void) {
    ++reads;assert(reads<=97);
    if(reads==mutate_at) {
        if(mutate_config)cfg[mutate_index]^=mutate_mask;
        else if(mutate_state)states[mutate_index]^=mutate_mask;
        else globals[mutate_index]^=mutate_mask;
    }
    return reads!=fail_at;
}
static int config(void *ctx,uint8_t b,uint8_t d,uint8_t f,uint8_t off,uint32_t *out) {
    assert(ctx==cfg && b==0 && d==27 && f==0 && off==offset_at(reads));
    if(reads!=47 && reads!=48 && reads!=96) {
        unsigned n=local(reads);if(n>=29)n-=29;
        assert(n<6 || (n>=12 && n<18));
    }
    if(!step())return 0;
    *out=cfg[off/4];return 1;
}
static int global(void *ctx,uint64_t address,uint8_t width,uint32_t *out) {
    assert(ctx==globals && address==QOTOM_HDA_BAR+offset_at(reads));
    unsigned n=local(reads);if(n>=29)n-=29;assert(n>=6 && n<12);unsigned i=n-6;
    const unsigned widths[]={4,2,1,1,4,4};assert(width==widths[i]);
    if(!step())return 0;
    *out=globals[i];return 1;
}
static int state(void *ctx,uint64_t address,uint8_t width,uint32_t *out) {
    unsigned n=local(reads);
    assert(ctx==states && n>=18 && n<29 && address==QOTOM_HDA_BAR+offset_at(reads));
    assert(width==(n<20?1:4));
    if(!step())return 0;
    *out=states[n-18];return 1;
}
static int write_command(void *ctx,uint8_t bus,uint8_t device,uint8_t function,uint8_t offset,uint16_t value) {
    assert(ctx==cfg && reads==48 && ++writes==1);
    assert(bus==0 && device==27 && function==0 && offset==4 && value==2);
    if(!write_ignored)cfg[1]=(cfg[1]&0xffff0000)|value;
    return !write_fails;
}
static void setup(void) {
    header=(struct pci_enumeration_header){.device=27,.words={0x0f048086,6,0x0403000e,0,0xd0910004,0}};
    memcpy(cfg,header.words,sizeof cfg);
    caps=(struct qotom_hda_observation){1,0x4401,0,1,0,1};
    prior=(struct qotom_hda_state){0};
    for(unsigned i=0;i<8;++i)prior.streams[i]=0x40000;
    const uint32_t g[]={1,0x4401,0,1,0,1};memcpy(globals,g,sizeof g);
    for(unsigned i=0;i<11;++i)states[i]=i<3?0:0x40000;
    reads=writes=fail_at=mutate_at=0;write_fails=write_ignored=mutate_state=mutate_config=0;
}
static enum qotom_hda_bme_status clear(struct qotom_hda_bme_result *out) {
    memset(out,0xff,sizeof *out);
    return qotom_clear_hda_bme(config,cfg,global,globals,state,states,write_command,cfg,
        &header,QOTOM_HDA_OK,&caps,QOTOM_HDA_STATE_OK,&prior,out);
}
static void zero(const struct qotom_hda_bme_result *out) {
    assert(!out->attempted && !out->before_command && !out->after_command);
}
int main(void) {
    assert(pci_enumerate_segment(NULL,NULL,NULL).status==PCI_ENUMERATION_INVALID_ARGUMENT);
    assert(!qotom_hda_stopped(NULL));
    struct qotom_hda_bme_result out;
    setup();assert(clear(&out)==QOTOM_HDA_BME_OK && reads==97 && writes==1);
    assert(out.attempted==1 && out.before_command==6 && out.after_command==2);
    for(unsigned n=1;n<=97;++n) {
        setup();fail_at=n;
        assert(clear(&out)==(n<=47?QOTOM_HDA_BME_REFRESH:n==48?QOTOM_HDA_BME_COMMAND:n==49?QOTOM_HDA_BME_READBACK:QOTOM_HDA_BME_FINAL));
        assert(reads==n && writes==(n>48));
        if(n<=48)zero(&out);
        else {assert(out.attempted==1 && out.before_command==6);assert(out.after_command==(n==49?0:2));}
    }
    for(unsigned i=0;i<11;++i)for(unsigned bit=0;bit<32;++bit) {
        setup();uint32_t *field=i==0?&prior.corb:i==1?&prior.rirb:i==2?&prior.position:&prior.streams[i-3];
        *field^=1u<<bit;
        assert(clear(&out)==QOTOM_HDA_BME_PRIOR && !reads && !writes);zero(&out);
        setup();states[i]^=1u<<bit;
        enum qotom_hda_bme_status s=clear(&out);
        if(i<2 && bit>=8)assert(s==QOTOM_HDA_BME_REFRESH);
        else assert(s==QOTOM_HDA_BME_STATE && reads==47);
        assert(!writes);zero(&out);
        setup();mutate_at=50;mutate_index=i;mutate_mask=1u<<bit;mutate_state=1;
        assert(clear(&out)==QOTOM_HDA_BME_FINAL && writes==1 && out.after_command==2);
    }
    for(unsigned i=0;i<6;++i)for(unsigned bit=0;bit<32;++bit) {
        setup();uint32_t *fields[]={&caps.control_before,&caps.capability,&caps.version_minor,
            &caps.version_major,&caps.interrupt,&caps.control_after};
        *fields[i]^=1u<<bit;
        assert(clear(&out)==QOTOM_HDA_BME_PRIOR && !reads && !writes);zero(&out);
        setup();globals[i]^=1u<<bit;
        assert(clear(&out)==QOTOM_HDA_BME_REFRESH && !writes);zero(&out);
        setup();mutate_at=50;mutate_index=i;mutate_mask=1u<<bit;
        assert(clear(&out)==QOTOM_HDA_BME_FINAL && writes==1);
    }
    for(unsigned bit=0;bit<32;++bit) {
        setup();header.words[1]^=1u<<bit;
        if(bit<16){assert(clear(&out)==QOTOM_HDA_BME_PRIOR && !reads && !writes);zero(&out);}
        else assert(clear(&out)==QOTOM_HDA_BME_OK);
        setup();mutate_at=48;mutate_index=1;mutate_mask=1u<<bit;mutate_config=1;
        if(bit<16){assert(clear(&out)==QOTOM_HDA_BME_COMMAND && !writes);zero(&out);}
        else {assert(clear(&out)==QOTOM_HDA_BME_OK);assert(cfg[1]==(2u|(1u<<bit)));}
        setup();mutate_at=49;mutate_index=1;mutate_mask=1u<<bit;mutate_config=1;
        if(bit<16){assert(clear(&out)==QOTOM_HDA_BME_READBACK && reads==49);assert(out.after_command==(2u^(1u<<bit)));}
        else assert(clear(&out)==QOTOM_HDA_BME_OK);
        setup();mutate_at=97;mutate_index=1;mutate_mask=1u<<bit;mutate_config=1;
        if(bit<16){assert(clear(&out)==QOTOM_HDA_BME_FINAL && reads==97);assert(out.after_command==(2u^(1u<<bit)));}
        else assert(clear(&out)==QOTOM_HDA_BME_OK);
    }
    setup();cfg[1]=0xa5a50006;assert(clear(&out)==QOTOM_HDA_BME_OK && cfg[1]==0xa5a50002);
    setup();mutate_at=50;mutate_index=1;mutate_mask=4;mutate_config=1;
    assert(clear(&out)==QOTOM_HDA_BME_FINAL && out.after_command==6 && reads==97);
    setup();mutate_at=50;mutate_index=4;mutate_mask=0x1000;mutate_config=1;
    assert(clear(&out)==QOTOM_HDA_BME_FINAL && writes==1 && out.after_command==2);
    setup();mutate_at=49;mutate_index=1;mutate_mask=UINT32_MAX^2;mutate_config=1;
    assert(clear(&out)==QOTOM_HDA_BME_READBACK && out.after_command==0xffff);
    setup();write_ignored=1;assert(clear(&out)==QOTOM_HDA_BME_READBACK && out.after_command==6 && reads==49);
    setup();write_fails=1;assert(clear(&out)==QOTOM_HDA_BME_WRITE && reads==48 && writes==1);
    assert(cfg[1]==2 && out.attempted==1 && out.before_command==6 && !out.after_command);
    setup();write_fails=write_ignored=1;assert(clear(&out)==QOTOM_HDA_BME_WRITE && cfg[1]==6);
    setup();cfg[4]^=0x1000;assert(clear(&out)==QOTOM_HDA_BME_REFRESH && !writes);zero(&out);
    setup();cfg[1]&=~2u;assert(clear(&out)==QOTOM_HDA_BME_REFRESH && !writes);zero(&out);
    for(unsigned status=1;status<=10;++status) {
        setup();assert(qotom_clear_hda_bme(config,cfg,global,globals,state,states,write_command,cfg,
            &header,status,&caps,QOTOM_HDA_STATE_OK,&prior,&out)==QOTOM_HDA_BME_PRIOR);zero(&out);
        assert(qotom_clear_hda_bme(config,cfg,global,globals,state,states,write_command,cfg,
            &header,QOTOM_HDA_OK,&caps,status,&prior,&out)==QOTOM_HDA_BME_PRIOR);zero(&out);assert(!reads && !writes);
    }
    setup();
#define BAD(C,G,S,W,H,P,Q,O) qotom_clear_hda_bme(C,cfg,G,globals,S,states,W,cfg,H,QOTOM_HDA_OK,P,QOTOM_HDA_STATE_OK,Q,O)
    assert(BAD(NULL,global,state,write_command,&header,&caps,&prior,&out)==QOTOM_HDA_BME_ARGUMENT);zero(&out);
    assert(BAD(config,NULL,state,write_command,&header,&caps,&prior,&out)==QOTOM_HDA_BME_ARGUMENT);zero(&out);
    assert(BAD(config,global,NULL,write_command,&header,&caps,&prior,&out)==QOTOM_HDA_BME_ARGUMENT);zero(&out);
    assert(BAD(config,global,state,NULL,&header,&caps,&prior,&out)==QOTOM_HDA_BME_ARGUMENT);zero(&out);
    assert(BAD(config,global,state,write_command,NULL,&caps,&prior,&out)==QOTOM_HDA_BME_ARGUMENT);zero(&out);
    assert(BAD(config,global,state,write_command,&header,NULL,&prior,&out)==QOTOM_HDA_BME_ARGUMENT);zero(&out);
    assert(BAD(config,global,state,write_command,&header,&caps,NULL,&out)==QOTOM_HDA_BME_ARGUMENT);zero(&out);
    assert(BAD(config,global,state,write_command,&header,&caps,&prior,NULL)==QOTOM_HDA_BME_ARGUMENT);
    assert(!reads && !writes);
    puts("PASS HDA BME: exact97reads, one word6to2, all failures, stopped/global/resource drift, status preservation");
}
