#include <assert.h>
#include <stdio.h>
#include <string.h>
#include "../boot/pci-power-observation.h"

static uint32_t cfg[64];
static struct pci_enumeration_header header;
static struct pci_capability_snapshot prior;
static unsigned reads,fail_at,change_at;
static int read_config(void *context,uint8_t bus,uint8_t device,uint8_t function,
        uint8_t offset,uint32_t *value) {
    assert(context==cfg && bus==2 && !device && !function && !(offset&3));
    ++reads;if(reads==fail_at)return 0;
    *value=cfg[offset/4];if(reads==change_at)*value^=0x100;return 1;
}
static void setup(void) {
    memset(cfg,0,sizeof cfg);memset(&header,0,sizeof header);
    header.bus=2;header.words[0]=cfg[0]=UINT32_C(0x435314e4);
    header.words[1]=cfg[1]=UINT32_C(0x00100006);
    header.words[2]=cfg[2]=UINT32_C(0x02800001);
    header.words[13]=cfg[13]=0x40;
    cfg[0x40/4]=UINT32_C(0xce035801);
    cfg[0x58/4]=UINT32_C(0x00000009);
    cfg[0x44/4]=UINT32_C(0x00004008);
    reads=fail_at=change_at=0;
    assert(pci_collect_capabilities(read_config,cfg,&header,&prior).status==PCI_CAPABILITY_OK);
    reads=0;
}
int main(void) {
    (void)pci_enumerate_segment;
    setup();struct pci_power_observation p=pci_observe_power(read_config,cfg,&header,&prior);
    assert(p.status==PCI_POWER_OK && p.offset==0x40 && p.pm_capabilities==0xce03 &&
        p.control_status==0x4008 && reads==13);
    for(unsigned n=1;n<=13;++n) {
        setup();fail_at=n;p=pci_observe_power(read_config,cfg,&header,&prior);
        assert(p.status!=PCI_POWER_OK && !p.offset && !p.pm_capabilities && !p.control_status);
    }
    setup();cfg[0x40/4]=UINT32_C(0x00005801);
    p=pci_observe_power(read_config,cfg,&header,&prior);assert(p.status==PCI_POWER_LIST_CHANGED);
    setup();prior.headers[0].raw=cfg[0x40/4]=UINT32_C(0xce004401);
    prior.headers[1]=(struct pci_capability_header){0x44,9};prior.count=2;
    cfg[0x44/4]=9;p=pci_observe_power(read_config,cfg,&header,&prior);
    assert(p.status==PCI_POWER_SHAPE);
    for(unsigned version=0;version<=7;++version)if(version<1||version>3) {
        setup();cfg[0x40/4]=(cfg[0x40/4]&UINT32_C(0xfff8ffff))|(version<<16);
        prior.headers[0].raw=cfg[0x40/4];
        p=pci_observe_power(read_config,cfg,&header,&prior);assert(p.status==PCI_POWER_SHAPE);
    }
    setup();cfg[0x44/4]=UINT32_MAX;
    p=pci_observe_power(read_config,cfg,&header,&prior);assert(p.status==PCI_POWER_ABSENT);
    setup();change_at=13;
    p=pci_observe_power(read_config,cfg,&header,&prior);assert(p.status==PCI_POWER_FINAL_FAILED);
    assert(pci_observe_power(NULL,cfg,&header,&prior).status==PCI_POWER_ARGUMENT);
    puts("PASS PCI power observation: bracketed PMCSR, list drift, shapes and all read failures");
}
