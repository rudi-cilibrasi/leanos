#include <assert.h>
#include <stdio.h>
#include <string.h>
#include "../boot/qotom-rootport-bme.h"
static const uint32_t captured[4][16]={
{0xf488086,0x100007,0x604000e,0x810010,0x0,0x0,0x10100,0x2000e0e0,0xd080d080,0x1fff1,0x0,0x0,0x0,0x40,0x0,0x100105},
{0xf4a8086,0x100007,0x604000e,0x810010,0x0,0x0,0x20200,0x200000f0,0xd070d070,0x1fff1,0x0,0x0,0x0,0x40,0x0,0x100205},
{0xf4c8086,0x100007,0x604000e,0x810010,0x0,0x0,0x30300,0x2000d0d0,0xd060d060,0x1fff1,0x0,0x0,0x0,0x40,0x0,0x100305},
{0xf4e8086,0x100007,0x604000e,0x810010,0x0,0x0,0x40400,0x200000f0,0xfff0,0x1fff1,0x0,0x0,0x0,0x40,0x0,0x100405}
};
static struct pci_enumeration_header header;
static struct pci_capability_snapshot caps;
static struct pci_express_observation prior;
static uint32_t cfg[64],change_mask;
static unsigned reads,writes,fail_at,change_at,change_word,write_mode;
static uint8_t expected[71];
static int config(void *ctx,uint8_t b,uint8_t d,uint8_t f,uint8_t off,uint32_t *out) {
    assert(ctx==cfg && b==0 && d==28 && f==header.function);
    assert(reads<71 && off==expected[reads]);++reads;
    if(reads==change_at)cfg[change_word]^=change_mask;
    if(reads==fail_at)return 0;
    *out=cfg[off/4];return 1;
}
static int store(void *ctx,uint8_t b,uint8_t d,uint8_t f,uint8_t off,uint16_t value) {
    assert(ctx==cfg && reads==35 && writes++==0);
    assert(b==0 && d==28 && f==header.function && off==4 && value==3);
    if(write_mode!=1 && write_mode!=3)cfg[1]=(cfg[1]&0xffff0000)|value;
    return write_mode<2;
}
static void setup(unsigned fn) {
    memset(&header,0,sizeof header);memset(cfg,0,sizeof cfg);memset(&caps,0,sizeof caps);
    header.device=28;header.function=fn;memcpy(header.words,captured[fn],sizeof header.words);
    memcpy(cfg,header.words,sizeof header.words);caps.count=4;
    const unsigned offsets[]={64,128,144,160};
    const uint32_t raws[]={21135376,36869,40973,3355639809u};
    for(unsigned i=0;i<4;++i){caps.headers[i]=(struct pci_capability_header){offsets[i],raws[i]};cfg[offsets[i]/4]=raws[i];}
    cfg[17]=0x8000;cfg[18]=0x100000;
    prior=(struct pci_express_observation){PCI_EXPRESS_OK,64,0x8000,0x100000};
    reads=writes=fail_at=change_at=change_word=change_mask=write_mode=0;
    unsigned n=0;const unsigned list[]={0,4,12,52,64,128,144,160};
    for(unsigned phase=0;phase<2;++phase){
        for(unsigned i=0;i<16;++i)expected[n++]=i*4;
        for(unsigned i=0;i<8;++i)expected[n++]=list[i];
        expected[n++]=68;expected[n++]=72;
        for(unsigned i=0;i<8;++i)expected[n++]=list[i];
        expected[n++]=4;if(!phase)expected[n++]=4;
    }
    assert(n==71);
}
static enum qotom_rootport_bme_status collect(struct qotom_rootport_bme_result *out) {
    memset(out,0xff,sizeof *out);
    return qotom_clear_rootport_bme(config,cfg,store,cfg,&header,&caps,&prior,out);
}
int main(void) {
    assert(pci_enumerate_segment(NULL,NULL,NULL).status==PCI_ENUMERATION_INVALID_ARGUMENT);
    struct qotom_rootport_bme_result out;
    for(unsigned fn=0;fn<4;++fn){setup(fn);assert(collect(&out)==QOTOM_ROOTPORT_OK);
        assert(reads==71 && writes==1 && out.attempted==1 && out.before_command==7 && out.after_command==3 && cfg[1]==0x100003);}
    for(unsigned n=1;n<=71;++n){setup(0);fail_at=n;
        unsigned status=n<=34?QOTOM_ROOTPORT_REFRESH:n==35?QOTOM_ROOTPORT_COMMAND:n==36?QOTOM_ROOTPORT_READBACK:QOTOM_ROOTPORT_FINAL;
        assert(collect(&out)==status && reads==n && writes==(n>35));
        assert(out.attempted==(n>35) && out.before_command==(n>35?7:0));}
    for(unsigned mode=1;mode<=3;++mode){setup(0);write_mode=mode;
        assert(collect(&out)==(mode==1?QOTOM_ROOTPORT_READBACK:QOTOM_ROOTPORT_WRITE));
        assert(out.attempted==1 && out.before_command==7 && writes==1);
        assert((cfg[1]&0xffff)==(mode==2?3:7));}
    for(unsigned word=0;word<16;++word)for(unsigned bit=0;bit<32;++bit)for(unsigned phase=0;phase<2;++phase){
        setup(0);change_at=phase?37:1;change_word=word;change_mask=UINT32_C(1)<<bit;
        uint32_t mask=word==1?0x0010ffff:word==7?0xffff:UINT32_MAX;
        unsigned status=collect(&out);
        assert(status==((mask&change_mask)?(phase?QOTOM_ROOTPORT_FINAL:QOTOM_ROOTPORT_REFRESH):QOTOM_ROOTPORT_OK));
        assert(writes==((mask&change_mask)?phase:1));
    }
    for(unsigned bit=0;bit<32;++bit)for(unsigned field=0;field<2;++field){
        setup(0);if(field)prior.device_control_status^=UINT32_C(1)<<bit;else prior.device_capabilities^=UINT32_C(1)<<bit;
        int allowed=field && ((UINT32_C(1)<<bit)&0x1f0000);
        assert(collect(&out)==(allowed?QOTOM_ROOTPORT_OK:QOTOM_ROOTPORT_PRIOR));
        assert(reads==(allowed?71:0));
    }
    for(unsigned word=0;word<4;++word)for(unsigned bit=0;bit<32;++bit){
        uint32_t mask=word==0 || word==2?UINT32_MAX:word==1?0xffff:0xff0000;
        if(!(mask&(UINT32_C(1)<<bit)))continue;
        setup(0);header.words[word]^=UINT32_C(1)<<bit;
        assert(collect(&out)==QOTOM_ROOTPORT_PRIOR && !reads && !writes);
    }
    for(unsigned phase=0;phase<2;++phase)for(unsigned word=17;word<=18;++word)for(unsigned bit=0;bit<32;++bit){
        setup(0);change_at=phase?37:1;change_word=word;change_mask=UINT32_C(1)<<bit;
        int allowed=word==18 && (change_mask&0x1f0000);
        assert(collect(&out)==(allowed?QOTOM_ROOTPORT_OK:phase?QOTOM_ROOTPORT_FINAL:QOTOM_ROOTPORT_REFRESH));
    }
    setup(0);header.bus=1;assert(collect(&out)==QOTOM_ROOTPORT_PRIOR && !reads);
    setup(0);header.device=27;assert(collect(&out)==QOTOM_ROOTPORT_PRIOR && !reads);
    setup(0);header.function=4;assert(collect(&out)==QOTOM_ROOTPORT_PRIOR && !reads);
    setup(0);prior.status=PCI_EXPRESS_NOT_PRESENT;assert(collect(&out)==QOTOM_ROOTPORT_PRIOR && !reads);
    setup(0);prior.offset=0x44;assert(collect(&out)==QOTOM_ROOTPORT_PRIOR && !reads);
    for(unsigned phase=0;phase<2;++phase){setup(0);change_at=phase?37:1;change_word=18;change_mask=0x200000;
        assert(collect(&out)==(phase?QOTOM_ROOTPORT_FINAL:QOTOM_ROOTPORT_REFRESH));}
    setup(0);change_at=71;change_word=1;change_mask=4;
    assert(collect(&out)==QOTOM_ROOTPORT_FINAL && out.after_command==7);
    setup(0);assert(qotom_clear_rootport_bme(NULL,cfg,store,cfg,&header,&caps,&prior,&out)==QOTOM_ROOTPORT_ARGUMENT);
    assert(!out.attempted && !reads && !writes);
    puts("Root-port BME: four native identities, exact71reads, all read failures, routing/status mutations, failed writes, TP and reassertion PASS");
}
