#include <assert.h>
#include <stdio.h>
#include <string.h>
#include "../boot/qotom-txe-bme.h"

static struct pci_enumeration_header endpoint;
static struct qotom_txe_status_observation prior;
static uint32_t cfg[64];
static unsigned reads,writes,fail_at,mutate_at,mutate_value,write_mode;
static const uint8_t offsets[23]={0,4,8,12,64,72,0,4,8,12,4,4,
                                  0,4,8,12,64,72,0,4,8,12,4};
static int read_cfg(void *p,uint8_t b,uint8_t d,uint8_t f,uint8_t o,uint32_t *v) {
    assert(p==cfg && !b && d==26 && !f && reads<23 && offsets[reads]==o);
    ++reads;if(reads==fail_at)return 0;*v=cfg[o/4];
    if(reads==mutate_at)*v^=mutate_value;
    return 1;
}
static int write_cfg(void *p,uint8_t b,uint8_t d,uint8_t f,uint8_t o,uint16_t v) {
    assert(p==cfg && !b && d==26 && !f && o==4 && v==0x102 && reads==11);
    assert(++writes==1);
    if(write_mode!=1 && write_mode!=3)cfg[1]=(cfg[1]&0xffff0000u)|0x102;
    return write_mode<2;
}
static void setup(void) {
    endpoint=(struct pci_enumeration_header){.device=26,.words={
        0x0f188086,0x00100106,0x1080000e,0x10,0xd0500000,0xd0400000,
        0,0,0,0,0,0x0f188086,0,0x80,0,0x1ff}};
    memset(cfg,0,sizeof cfg);memcpy(cfg,endpoint.words,sizeof endpoint.words);
    cfg[0x40/4]=0x1f0000d5;cfg[0x48/4]=0x69000000;
    prior=(struct qotom_txe_status_observation){cfg[16],cfg[18]};
    reads=writes=fail_at=mutate_at=mutate_value=write_mode=0;
}
static enum qotom_txe_bme_status clear(struct qotom_txe_bme_result *out) {
    memset(out,0xff,sizeof *out);
    return qotom_clear_txe_bme(read_cfg,cfg,write_cfg,cfg,&endpoint,
        QOTOM_TXE_OK,&prior,out);
}
int main(void) {
    (void)pci_enumerate_segment;
    assert(!qotom_txe_same_status(NULL,NULL));
    setup();assert(qotom_txe_same_status(&prior,&prior));
    struct qotom_txe_bme_result out;
    assert(clear(&out)==QOTOM_TXE_BME_OK && reads==23 && writes==1);
    assert(out.attempted==1 && out.before_command==0x106 && out.after_command==0x102);
    for(unsigned n=1;n<=23;++n) {
        setup();fail_at=n;
        enum qotom_txe_bme_status s=n<=10?QOTOM_TXE_BME_REFRESH:
            n==11?QOTOM_TXE_BME_COMMAND:n==12?QOTOM_TXE_BME_READBACK:
            QOTOM_TXE_BME_FINAL;
        assert(clear(&out)==s && reads==n && writes==(n>11));
    }
    for(unsigned mode=1;mode<=3;++mode) {
        setup();write_mode=mode;
        enum qotom_txe_bme_status s=mode==1?QOTOM_TXE_BME_READBACK:QOTOM_TXE_BME_WRITE;
        assert(clear(&out)==s && writes==1);
    }
    setup();mutate_at=5;mutate_value=1;
    assert(clear(&out)==QOTOM_TXE_BME_STATE && !writes);
    setup();mutate_at=17;mutate_value=1;
    assert(clear(&out)==QOTOM_TXE_BME_FINAL && writes==1);
    setup();mutate_at=12;mutate_value=4;
    assert(clear(&out)==QOTOM_TXE_BME_READBACK && out.after_command==0x106);
    setup();mutate_at=23;mutate_value=4;
    assert(clear(&out)==QOTOM_TXE_BME_FINAL && out.after_command==0x106);
    setup();cfg[1]=(cfg[1]&0xffff0000u)|0x102;
    assert(clear(&out)==QOTOM_TXE_BME_REFRESH && reads==2 && !writes);
    for(unsigned s=1;s<=6;++s) {
        setup();assert(qotom_clear_txe_bme(read_cfg,cfg,write_cfg,cfg,&endpoint,
            (enum qotom_txe_status)s,&prior,&out)==QOTOM_TXE_BME_PRIOR);
        assert(!reads&&!writes);
    }
#define CALL(r,w,e,p,o) qotom_clear_txe_bme(r,cfg,w,cfg,e,QOTOM_TXE_OK,p,o)
    setup();assert(CALL(NULL,write_cfg,&endpoint,&prior,&out)==QOTOM_TXE_BME_ARGUMENT);
    assert(CALL(read_cfg,NULL,&endpoint,&prior,&out)==QOTOM_TXE_BME_ARGUMENT);
    assert(CALL(read_cfg,write_cfg,NULL,&prior,&out)==QOTOM_TXE_BME_ARGUMENT);
    assert(CALL(read_cfg,write_cfg,&endpoint,NULL,&out)==QOTOM_TXE_BME_ARGUMENT);
    assert(CALL(read_cfg,write_cfg,&endpoint,&prior,NULL)==QOTOM_TXE_BME_ARGUMENT);
    assert(!reads&&!writes);
#undef CALL
    puts("PASS TXE BME: stable firmware status, exact 23 reads, one word 0106-to-0102, all failures");
}
