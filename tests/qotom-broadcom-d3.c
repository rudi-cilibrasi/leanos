#include <assert.h>
#include <stdio.h>
#include <string.h>
#include "../boot/qotom-broadcom-d3.h"

static uint32_t cfg[64];
static struct pci_enumeration_header endpoint,bridge;
static struct pci_capability_snapshot caps;
static struct pci_express_observation prior;
static struct qotom_rootport_bme_result root_bme;
static struct qotom_pcie_pending_result root_pending;
static unsigned reads,writes,delays,fail_read,fail_write,pending_polls;

static int read_config(void *context,uint8_t bus,uint8_t device,uint8_t function,
        uint8_t offset,uint32_t *value) {
    assert(context==cfg && bus==2 && !device && !function && !(offset&3));
    ++reads;if(reads==fail_read)return 0;
    *value=cfg[offset/4];
    if(offset==0xd8 && reads>104 && delays<pending_polls)*value|=QOTOM_PCIE_PENDING_BIT;
    return 1;
}
static int write_word(void *context,uint8_t bus,uint8_t device,uint8_t function,
        uint8_t offset,uint16_t value) {
    assert(context==cfg && bus==2 && !device && !function);
    ++writes;if(writes==fail_write)return 0;
    assert((writes==1 && offset==4 && value==0) ||
           (writes==2 && offset==0x44 && value==QOTOM_BROADCOM_PMCSR_D3HOT));
    cfg[offset/4]=(cfg[offset/4]&UINT32_C(0xffff0000))|value;return 1;
}
static int wait10(void *context,uint32_t milliseconds) {
    assert(context==(void *)0x1234 && milliseconds==10);++delays;return 1;
}
static void setup(void) {
    memset(cfg,0,sizeof cfg);memset(&endpoint,0,sizeof endpoint);
    const uint32_t words[16]={0x435314e4,0x00100006,0x02800001,0x10,
        0xd0700004,0,0,0,0,0,0,0x04d814e4,0,0x40,0,0x105};
    endpoint.bus=2;memcpy(endpoint.words,words,sizeof words);memcpy(cfg,words,sizeof words);
    cfg[0x40/4]=UINT32_C(0xce035801);cfg[0x44/4]=UINT32_C(0x00004008);
    cfg[0x58/4]=UINT32_C(0x00784809);cfg[0x48/4]=UINT32_C(0x0080d005);
    cfg[0xd0/4]=UINT32_C(0x00010010);cfg[0xd4/4]=UINT32_C(0x05908fa0);
    cfg[0xd8/4]=UINT32_C(0x00190000);
    reads=writes=delays=fail_read=fail_write=pending_polls=0;
    assert(pci_collect_capabilities(read_config,cfg,&endpoint,&caps).status==PCI_CAPABILITY_OK);
    prior=pci_observe_express(read_config,cfg,&endpoint,&caps);
    assert(qotom_broadcom_pcie_valid(&prior));
    memset(&bridge,0,sizeof bridge);bridge.device=28;bridge.function=1;
    bridge.words[0]=UINT32_C(0x0f4a8086);bridge.words[1]=UINT32_C(0x00100007);
    bridge.words[2]=UINT32_C(0x0604000e);bridge.words[3]=UINT32_C(0x00810010);
    bridge.words[6]=UINT32_C(0x00020200);bridge.words[8]=UINT32_C(0xd070d070);
    bridge.words[9]=UINT32_C(0x0001fff1);bridge.words[13]=0x40;
    root_bme=(struct qotom_rootport_bme_result){1,7,3};
    root_pending=(struct qotom_pcie_pending_result){2,17};
    reads=writes=delays=fail_read=fail_write=pending_polls=0;
}
static enum qotom_broadcom_d3_status run(struct qotom_broadcom_d3_result *out) {
    memset(out,0xff,sizeof *out);
    return qotom_broadcom_enter_d3hot(read_config,cfg,write_word,cfg,wait10,(void *)0x1234,
        &endpoint,&bridge,&caps,&prior,QOTOM_ROOTPORT_OK,&root_bme,
        QOTOM_PCIE_PENDING_OK,&root_pending,out);
}
int main(void) {
    (void)pci_enumerate_segment;
    struct qotom_broadcom_d3_result out;
    setup();assert(run(&out)==QOTOM_BROADCOM_D3_OK);
    assert(reads==206 && writes==2 && delays==1 && out.command_attempted==1 &&
        out.before_command==6 && out.after_command==0 && out.pending_polls==2 &&
        out.device_status==0x19 && out.before_pmcsr==0x4008 &&
        out.d3_attempted==1 && out.after_pmcsr==0x400b);
    setup();root_pending.device_status=16;
    assert(run(&out)==QOTOM_BROADCOM_D3_OK);
    for(unsigned n=1;n<=206;++n) {
        setup();fail_read=n;enum qotom_broadcom_d3_status s=run(&out);
        assert(s!=QOTOM_BROADCOM_D3_OK && reads==n && writes<=2);
    }
    for(unsigned n=1;n<=2;++n) {
        setup();fail_write=n;enum qotom_broadcom_d3_status s=run(&out);
        assert(s==(n==1?QOTOM_BROADCOM_D3_COMMAND_WRITE:QOTOM_BROADCOM_D3_PM_WRITE));
        assert(writes==n);
    }
    setup();pending_polls=100;assert(run(&out)==QOTOM_BROADCOM_D3_PENDING);
    assert(out.pending_polls==100 && !out.d3_attempted && writes==1 && delays==99);
    setup();cfg[0x44/4]^=1;assert(run(&out)==QOTOM_BROADCOM_D3_REFRESH && !writes);
    for(unsigned status=0;status<64;++status)if(status!=16 && status!=17) {
        setup();root_pending.device_status=status;
        assert(run(&out)==QOTOM_BROADCOM_D3_PRIOR && !reads && !writes);
    }
    setup();root_bme.after_command=7;
    assert(run(&out)==QOTOM_BROADCOM_D3_PRIOR && !reads && !writes);
    setup();memset(&out,0xff,sizeof out);
    assert(qotom_broadcom_enter_d3hot(NULL,cfg,write_word,cfg,wait10,(void *)0x1234,
        &endpoint,&bridge,&caps,&prior,QOTOM_ROOTPORT_OK,&root_bme,
        QOTOM_PCIE_PENDING_OK,&root_pending,&out)==QOTOM_BROADCOM_D3_ARGUMENT);
    assert(!out.command_attempted && !out.d3_attempted);
    puts("PASS Broadcom D3hot: exact two writes, full refreshes, delayed TP quiet and all read failures");
}
