#include <assert.h>
#include <stdio.h>
#include <string.h>
#include "../boot/qotom-xhci-bme.h"
static struct pci_enumeration_header header={.device=20,.words={0x0f358086,6,0x0c03300e,0,0xd0900004,0}};
static const struct qotom_xhci_capabilities caps={{0x1000080,0x7000820,0x84000054,0x200000a,0x200077c1,0x3000,0x2000}};
static struct qotom_xhci_legacy previous;
static struct qotom_xhci_smi_result smi;
static struct qotom_xhci_operational prior;
static enum qotom_xhci_operational_status prior_status;
static uint32_t ext[8192],samples[3],final_extra,final_vendor,final_other;
static unsigned reads,ops,failed,first_reads,writes;
static uint32_t command_word;
static int ignored,write_failed,command_bad,reassert_bme,stopped_drift;
static int reassert,config_drift;
static int config(void *ctx,uint8_t b,uint8_t d,uint8_t f,uint8_t off,uint32_t *out) {
    (void)ctx;assert(!b && d==20 && !f && !(off&3) && off<=20);
    if(++reads==failed)return 0;
    *out=off==4?command_word:header.words[off/4];
    if(writes && config_drift && !off)*out^=1;
    if(command_bad && reads==2*first_reads+4)*out^=1;
    if(reassert_bme && reads==2*(2*first_reads+3)+3)*out|=4;
    return 1;
}
static int mmio(void *ctx,uint64_t a,uint32_t *out) {
    (void)ctx;assert(a>=QOTOM_XHCI_BAR && a<=QOTOM_XHCI_BAR+24 && !(a&3));
    if(++reads==failed)return 0;
    *out=caps.words[(a-QOTOM_XHCI_BAR)/4];return 1;
}
static int extended(void *ctx,uint64_t a,uint32_t *out) {
    (void)ctx;assert(a>=QOTOM_XHCI_BAR+0x8000 && a<=QOTOM_XHCI_BAR+0xfffc && !(a&3));
    if(++reads==failed)return 0;
    *out=ext[(a-QOTOM_XHCI_BAR-0x8000)/4];return 1;
}
static int operational(void *ctx,uint64_t a,uint32_t *out) {
    (void)ctx;unsigned i=ops++%3;assert(a==QOTOM_XHCI_BAR+(i==1?0x80:0x84));
    if(++reads==failed)return 0;
    *out=samples[i];
    if(stopped_drift && (stopped_drift==1 || writes) && i==1)*out|=1;
    return 1;
}
static int write16(void *ctx,uint8_t b,uint8_t d,uint8_t f,uint8_t off,uint16_t value) {
    (void)ctx;assert(!b && d==20 && !f && off==4 && value==2 && !writes && reads==2*first_reads+4);
    ++writes;if(!ignored)command_word=(command_word&0xffff0000)|value;
    ext[0x464/4]|=final_extra;ext[16]^=final_vendor;ext[0]^=final_other;
    if(reassert)ext[0x460/4]|=0x10000;
    return !write_failed;
}
static void reset(void) {
    previous=(struct qotom_xhci_legacy){.count=6,.legacy_offset=0x8460,.control_status=0x2001,
        .headers={{0x8000,0x02000802},{0x8020,0x03000802},{0x8040,0x10cc1},
                  {0x8070,0xfcc0},{0x8460,0x10801},{0x8480,0x5000a}}};
    memset(ext,0,sizeof ext);
    for(unsigned i=0;i<previous.count;++i)ext[(previous.headers[i].offset-0x8000)/4]=previous.headers[i].raw;
    ext[0x460/4]=0x01000801;ext[0x464/4]=0;ext[16]=0xcc1;
    smi=(struct qotom_xhci_smi_result){1,0x2000,0};
    prior=(struct qotom_xhci_operational){1,0,1};
    prior_status=QOTOM_XHCI_OPERATIONAL_OK;
    reads=ops=writes=failed=final_extra=final_vendor=final_other=0;first_reads=45;
    ignored=write_failed=command_bad=reassert_bme=stopped_drift=0;
    header.words[1]=command_word=0x02900006;reassert=config_drift=0;samples[0]=samples[2]=1;samples[1]=0;
}
static void maximum(void) {
    reset();previous.count=48;
    for(unsigned i=0;i<46;++i)previous.headers[i]=(struct qotom_xhci_ext_header){0x8000+4*i,0x102};
    previous.headers[45].raw=0x02|(((0x8460-previous.headers[45].offset)/4)<<8);
    previous.headers[46]=(struct qotom_xhci_ext_header){0x8460,0x10801};
    previous.headers[47]=(struct qotom_xhci_ext_header){0x8480,0x5000a};
    for(unsigned i=0;i<48;++i)ext[(previous.headers[i].offset-0x8000)/4]=previous.headers[i].raw;
    ext[0x460/4]=0x01000801;first_reads=87;
}
static struct qotom_xhci_bme_result out;
static void check(enum qotom_xhci_bme_status status) {
    memset(&out,0x55,sizeof out);
    assert(qotom_clear_xhci_bme(config,NULL,mmio,NULL,extended,NULL,operational,NULL,write16,NULL,
        &header,&caps,&previous,QOTOM_XHCI_SMI_OBSERVED,&smi,prior_status,&prior,&out)==status);
    assert(reads<=357 && writes<=1 && out.attempted==writes);
    if(!writes)assert(!out.before_command && !out.after_command);
    else assert(out.before_command==6);
}
int main(void) {
    assert(pci_enumerate_segment(NULL,NULL,NULL).status==PCI_ENUMERATION_INVALID_ARGUMENT);
    reset();check(QOTOM_XHCI_BME_OK);assert(reads==189 && writes==1 && out.after_command==2 && command_word==0x02900002);
    maximum();check(QOTOM_XHCI_BME_OK);assert(reads==357);
    for(unsigned i=1;i<=357;++i) {
        maximum();failed=i;
        check(i<=177?QOTOM_XHCI_BME_REFRESH:i==178?QOTOM_XHCI_BME_COMMAND:
            i==179?QOTOM_XHCI_BME_READBACK:QOTOM_XHCI_BME_FINAL);
    }
    reset();ignored=1;check(QOTOM_XHCI_BME_READBACK);assert(out.after_command==6);
    reset();write_failed=1;check(QOTOM_XHCI_BME_WRITE);assert(command_word==0x02900002 && !out.after_command);
    reset();write_failed=ignored=1;check(QOTOM_XHCI_BME_WRITE);assert(command_word==0x02900006);
    reset();reassert_bme=1;check(QOTOM_XHCI_BME_FINAL);assert(out.after_command==6);
    reset();command_bad=1;check(QOTOM_XHCI_BME_COMMAND);
    reset();stopped_drift=1;check(QOTOM_XHCI_BME_STATE);
    reset();stopped_drift=2;check(QOTOM_XHCI_BME_FINAL);
    reset();config_drift=1;check(QOTOM_XHCI_BME_FINAL);
    reset();reassert=1;check(QOTOM_XHCI_BME_FINAL);
    reset();final_extra=1;check(QOTOM_XHCI_BME_FINAL);
    reset();final_other=0x10000;check(QOTOM_XHCI_BME_FINAL);
    reset();final_vendor=0x10000;check(QOTOM_XHCI_BME_OK);
    for(unsigned bit=0;bit<16;++bit) {
        reset();command_word=header.words[1]=6|(UINT32_C(1)<<(bit+16));
        check(QOTOM_XHCI_BME_OK);assert(command_word==(2|(UINT32_C(1)<<(bit+16))));
        reset();header.words[1]^=UINT32_C(1)<<bit;check(QOTOM_XHCI_BME_PRIOR);assert(!reads);
    }
    uint32_t *fields[]={&prior.status_before,&prior.command,&prior.status_after};
    for(unsigned f=0;f<3;++f)for(unsigned bit=0;bit<32;++bit) {
        reset();*fields[f]^=UINT32_C(1)<<bit;check(QOTOM_XHCI_BME_PRIOR);assert(!reads);
    }
    reset();prior_status=QOTOM_XHCI_OPERATIONAL_FINAL;check(QOTOM_XHCI_BME_PRIOR);
    reset();smi.after_control=1;check(QOTOM_XHCI_BME_REFRESH);
    reset();assert(qotom_clear_xhci_bme(NULL,NULL,mmio,NULL,extended,NULL,operational,NULL,write16,NULL,
        &header,&caps,&previous,QOTOM_XHCI_SMI_OBSERVED,&smi,prior_status,&prior,&out)==QOTOM_XHCI_BME_ARGUMENT);
    assert(!reads && !writes && !out.attempted && !out.before_command && !out.after_command);
    puts("PASS xHCI BME clear: all357 read failures, stopped-state refresh, word-only Command preservation and ambiguous writes");
}
