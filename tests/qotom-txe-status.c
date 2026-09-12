#include <assert.h>
#include <stdio.h>
#include <string.h>
#include "../boot/qotom-txe-status.h"
static struct pci_enumeration_header initial;
static uint32_t cfg[64];
static unsigned reads,fail_at,change_at,change_word;
static uint32_t change_mask;
static const uint8_t offsets[10]={0,4,8,12,0x40,0x48,0,4,8,12};
static int read_cfg(void *ctx,uint8_t b,uint8_t d,uint8_t f,uint8_t off,uint32_t *out) {
    assert(ctx==cfg && b==0 && d==26 && f==0 && reads<10);
    assert(off==offsets[reads]);++reads;
    if(reads==change_at)cfg[change_word]^=change_mask;
    if(reads==fail_at)return 0;
    *out=cfg[off/4];return 1;
}
static void setup(void) {
    memset(&initial,0,sizeof initial);memset(cfg,0,sizeof cfg);
    initial.device=26;initial.words[0]=cfg[0]=0x0f188086;
    initial.words[1]=cfg[1]=0x00100106;initial.words[2]=cfg[2]=0x1080000e;
    cfg[0x40/4]=0x12345678;cfg[0x48/4]=0x87654321;
    reads=fail_at=change_at=change_word=change_mask=0;
}
static enum qotom_txe_status collect(struct qotom_txe_status_observation *out) {
    memset(out,0xff,sizeof *out);
    return qotom_collect_txe_status(read_cfg,cfg,&initial,out);
}
static void zero(const struct qotom_txe_status_observation *out) {
    assert(out->firmware0==0 && out->firmware1==0);
}
int main(void) {
    assert(pci_enumerate_segment(NULL,NULL,NULL).status==PCI_ENUMERATION_INVALID_ARGUMENT);
    struct qotom_txe_status_observation out;
    setup();assert(collect(&out)==QOTOM_TXE_OK && reads==10);
    assert(out.firmware0==0x12345678 && out.firmware1==0x87654321);
    for(unsigned n=1;n<=10;++n) {
        setup();fail_at=n;
        assert(collect(&out)==((n==5 || n==6)?QOTOM_TXE_STATUS_READ:QOTOM_TXE_CONFIG_READ));
        assert(reads==n);zero(&out);
    }
    const uint32_t masks[]={UINT32_MAX,0xffff,UINT32_MAX,0xff0000};
    for(unsigned word=0;word<4;++word)for(unsigned bit=0;bit<32;++bit) {
        uint32_t mask=UINT32_C(1)<<bit;
        setup();initial.words[word]^=mask;
        assert(collect(&out)==((masks[word]&mask)?QOTOM_TXE_HEADER:QOTOM_TXE_OK));
        if(masks[word]&mask){assert(reads==0);zero(&out);}
        for(unsigned phase=0;phase<2;++phase) {
            setup();change_at=phase?7:1;change_word=word;change_mask=mask;
            assert(collect(&out)==((masks[word]&mask)?QOTOM_TXE_DRIFT:QOTOM_TXE_OK));
            if(masks[word]&mask){assert(reads==(phase?7:1)+word);zero(&out);}
        }
    }
    for(unsigned bit=0;bit<8;++bit)for(unsigned field=0;field<3;++field) {
        setup();if(field==0)initial.bus^=1u<<bit;
        if(field==1)initial.device^=1u<<bit;
        if(field==2)initial.function^=1u<<bit;
        assert(collect(&out)==QOTOM_TXE_HEADER && reads==0);zero(&out);
    }
    for(unsigned i=0;i<2;++i) {
        setup();cfg[(0x40+i*8)/4]=UINT32_MAX;
        assert(collect(&out)==QOTOM_TXE_ABSENT && reads==5+i);zero(&out);
        for(unsigned bit=0;bit<32;++bit) {
            setup();cfg[(0x40+i*8)/4]=UINT32_C(1)<<bit;
            assert(collect(&out)==QOTOM_TXE_OK && reads==10);
            assert((i?out.firmware1:out.firmware0)==(UINT32_C(1)<<bit));
        }
    }
    setup();cfg[16]=cfg[18]=0;assert(collect(&out)==QOTOM_TXE_OK);zero(&out);
    setup();assert(qotom_collect_txe_status(NULL,cfg,&initial,&out)==QOTOM_TXE_ARGUMENT);zero(&out);
    assert(qotom_collect_txe_status(read_cfg,cfg,NULL,&out)==QOTOM_TXE_ARGUMENT);zero(&out);
    assert(qotom_collect_txe_status(read_cfg,cfg,&initial,NULL)==QOTOM_TXE_ARGUMENT);
    assert(reads==0);puts("Qotom TXE status bounds PASS");
}
