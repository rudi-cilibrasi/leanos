#include <assert.h>
#include <stdio.h>
#include <string.h>
#include "../boot/qotom-pcie-pending.h"

static uint32_t cfg[64];
static struct pci_enumeration_header header;
static struct pci_capability_snapshot caps;
static struct pci_express_observation prior;
static unsigned reads,delays,fail_read,fail_delay,pending_polls,drift_poll;

static int config_read(void *context,uint8_t bus,uint8_t device,uint8_t function,
        uint8_t offset,uint32_t *value) {
    (void)context;
    assert(bus==header.bus && device==header.device && function==header.function && !(offset&3));
    ++reads;
    if(reads==fail_read)return 0;
    *value=cfg[offset/4];
    if(offset==0x78 && delays<pending_polls)*value|=QOTOM_PCIE_PENDING_BIT;
    if(offset==0x74 && delays==drift_poll)*value^=1;
    return 1;
}
static int wait10(void *context,uint32_t milliseconds) {
    assert(context==(void *)0x1234 && milliseconds==10);
    ++delays;return delays!=fail_delay;
}
static void setup_realtek(void) {
    memset(cfg,0,sizeof cfg);memset(&header,0,sizeof header);
    header.bus=1;header.words[0]=cfg[0]=UINT32_C(0x816810ec);
    header.words[1]=cfg[1]=UINT32_C(0x00100007);
    header.words[2]=cfg[2]=UINT32_C(0x02000007);
    header.words[3]=cfg[3]=0;header.words[6]=cfg[6]=UINT32_C(0xd0804004);
    header.words[8]=cfg[8]=UINT32_C(0xd080000c);
    header.words[13]=cfg[13]=0x70;
    cfg[0x70/4]=UINT32_C(0x00020010);
    cfg[0x74/4]=UINT32_C(0x05908cc0);
    cfg[0x78/4]=UINT32_C(0x00192000);
    reads=delays=fail_read=fail_delay=pending_polls=0;drift_poll=UINT32_MAX;
    assert(pci_collect_capabilities(config_read,NULL,&header,&caps).status==PCI_CAPABILITY_OK);
    prior=pci_observe_express(config_read,NULL,&header,&caps);
    assert(qotom_realtek_pending_sample_valid(&prior));
    cfg[1]=(cfg[1]&UINT32_C(0xffff0000))|3;
    reads=delays=fail_read=fail_delay=pending_polls=0;drift_poll=UINT32_MAX;
}
static void setup_rootport(void) {
    memset(cfg,0,sizeof cfg);memset(&header,0,sizeof header);
    header.device=28;header.function=1;
    header.words[0]=cfg[0]=UINT32_C(0x0f4a8086);
    header.words[1]=cfg[1]=UINT32_C(0x00100007);
    header.words[2]=cfg[2]=UINT32_C(0x0604000e);
    header.words[3]=cfg[3]=UINT32_C(0x00810000);
    header.words[13]=cfg[13]=0x40;
    cfg[0x40/4]=UINT32_C(0x01420010);
    cfg[0x44/4]=UINT32_C(0x00008000);
    cfg[0x48/4]=UINT32_C(0x00110000);
    reads=delays=fail_read=fail_delay=pending_polls=0;drift_poll=UINT32_MAX;
    assert(pci_collect_capabilities(config_read,NULL,&header,&caps).status==PCI_CAPABILITY_OK);
    prior=pci_observe_express(config_read,NULL,&header,&caps);
    assert(qotom_rootport_sample_valid(&prior));
    cfg[1]=(cfg[1]&UINT32_C(0xffff0000))|3;
    reads=delays=fail_read=fail_delay=pending_polls=0;drift_poll=UINT32_MAX;
}
static void clear_result(struct qotom_pcie_pending_result result) {
    assert(!result.polls && !result.device_status);
}
int main(void) {
    assert(pci_enumerate_segment(NULL,NULL,NULL).status==PCI_ENUMERATION_INVALID_ARGUMENT);
    struct qotom_pcie_pending_result result;
    struct qotom_realtek_state state={UINT32_C(0x2f900d00),0,0,UINT32_C(0x2ff0e),0,UINT32_C(0x2f900d00)};
    struct qotom_realtek_bme_result rbme={1,7,3};
    struct qotom_rootport_bme_result pbme={1,7,3};
    setup_realtek();
    assert(qotom_confirm_realtek_nonposted_quiet(config_read,NULL,wait10,(void *)0x1234,
        &header,&caps,&prior,QOTOM_REALTEK_OK,&state,QOTOM_REALTEK_BME_OK,&rbme,&result)==QOTOM_PCIE_PENDING_OK);
    assert(result.polls==2 && result.device_status==0x19 && delays==1);
    setup_realtek();pending_polls=3;
    assert(qotom_confirm_realtek_nonposted_quiet(config_read,NULL,wait10,(void *)0x1234,
        &header,&caps,&prior,QOTOM_REALTEK_OK,&state,QOTOM_REALTEK_BME_OK,&rbme,&result)==QOTOM_PCIE_PENDING_OK);
    assert(result.polls==5 && result.device_status==0x19 && delays==4);
    setup_realtek();pending_polls=100;
    assert(qotom_confirm_realtek_nonposted_quiet(config_read,NULL,wait10,(void *)0x1234,
        &header,&caps,&prior,QOTOM_REALTEK_OK,&state,QOTOM_REALTEK_BME_OK,&rbme,&result)==QOTOM_PCIE_PENDING_TIMEOUT);
    assert(result.polls==100 && (result.device_status&0x20) && delays==99);
    setup_realtek();fail_delay=1;
    assert(qotom_confirm_realtek_nonposted_quiet(config_read,NULL,wait10,(void *)0x1234,
        &header,&caps,&prior,QOTOM_REALTEK_OK,&state,QOTOM_REALTEK_BME_OK,&rbme,&result)==QOTOM_PCIE_PENDING_DELAY);
    assert(result.polls==1 && delays==1);
    setup_realtek();cfg[1]^=4;
    assert(qotom_confirm_realtek_nonposted_quiet(config_read,NULL,wait10,(void *)0x1234,
        &header,&caps,&prior,QOTOM_REALTEK_OK,&state,QOTOM_REALTEK_BME_OK,&rbme,&result)==QOTOM_PCIE_PENDING_COMMAND);
    clear_result(result);
    setup_realtek();drift_poll=0;
    assert(qotom_confirm_realtek_nonposted_quiet(config_read,NULL,wait10,(void *)0x1234,
        &header,&caps,&prior,QOTOM_REALTEK_OK,&state,QOTOM_REALTEK_BME_OK,&rbme,&result)==QOTOM_PCIE_PENDING_CHANGED);
    clear_result(result);
    setup_realtek();
    for(unsigned n=1;n<=14;++n) {
        reads=delays=0;fail_read=n;
        enum qotom_pcie_pending_status s=qotom_confirm_realtek_nonposted_quiet(config_read,NULL,
            wait10,(void *)0x1234,&header,&caps,&prior,QOTOM_REALTEK_OK,&state,
            QOTOM_REALTEK_BME_OK,&rbme,&result);
        assert(s==(n==1||n==14?QOTOM_PCIE_PENDING_COMMAND:QOTOM_PCIE_PENDING_OBSERVATION));
    }
    setup_rootport();
    assert(qotom_confirm_rootport_nonposted_quiet(config_read,NULL,wait10,(void *)0x1234,
        &header,&caps,&prior,QOTOM_ROOTPORT_OK,&pbme,&result)==QOTOM_PCIE_PENDING_OK);
    assert(result.polls==2 && result.device_status==0x11);
    setup_rootport();pbme.after_command=7;
    assert(qotom_confirm_rootport_nonposted_quiet(config_read,NULL,wait10,(void *)0x1234,
        &header,&caps,&prior,QOTOM_ROOTPORT_OK,&pbme,&result)==QOTOM_PCIE_PENDING_PRIOR);
    clear_result(result);
    setup_realtek();cfg[1]=(cfg[1]&UINT32_C(0xffff0000));
    assert(qotom_confirm_pcie_nonposted_quiet_command(config_read,NULL,wait10,(void *)0x1234,
        &header,&caps,&prior,0,&result)==QOTOM_PCIE_PENDING_OK);
    assert(result.polls==2 && result.device_status==0x19 && delays==1);
    setup_realtek();state.command_after=1;
    assert(qotom_confirm_realtek_nonposted_quiet(config_read,NULL,wait10,(void *)0x1234,
        &header,&caps,&prior,QOTOM_REALTEK_OK,&state,QOTOM_REALTEK_BME_OK,&rbme,&result)==QOTOM_PCIE_PENDING_PRIOR);
    clear_result(result);
    setup_realtek();
    assert(qotom_confirm_pcie_nonposted_quiet(NULL,NULL,wait10,(void *)0x1234,
        &header,&caps,&prior,&result)==QOTOM_PCIE_PENDING_ARGUMENT);
    puts("PASS Qotom PCIe non-posted quiet: two-clear window, pending timeout, failures, typed priors");
}
