#include <assert.h>
#include <stdio.h>
#include <string.h>
#include "../boot/pci-express-observation.h"
static uint32_t cfg[64];
static unsigned reads, fail_at, mutate_at, mutate_offset, mutate_mask;
static struct pci_enumeration_header initial;
static struct pci_capability_snapshot previous;
static int read_config(void *ctx,uint8_t b,uint8_t d,uint8_t f,uint8_t off,uint32_t *v) {
    (void)ctx; assert(b==initial.bus && d==initial.device && f==initial.function && !(off&3));
    ++reads; assert(reads<=106);
    if (reads==mutate_at) cfg[mutate_offset/4]^=mutate_mask;
    if (reads==fail_at) return 0;
    *v=cfg[off/4]; return 1;
}
static void setup(unsigned off,unsigned flags,unsigned layout) {
    memset(cfg,0,sizeof cfg); memset(&initial,0,sizeof initial);
    initial.bus=2; initial.device=0; initial.function=0;
    initial.words[0]=cfg[0]=0x435314e4;
    initial.words[1]=cfg[1]=0x00100006;
    initial.words[3]=cfg[3]=layout<<16;
    initial.words[13]=cfg[13]=off;
    cfg[off/4]=(flags<<16)|0x10;
    if(off<=244) {cfg[off/4+1]=0x10008000;cfg[off/4+2]=0x00202810;}
    reads=fail_at=mutate_at=0;
    assert(pci_collect_capabilities(read_config,NULL,&initial,&previous).status==PCI_CAPABILITY_OK);
    reads=0;
}
static struct pci_express_observation observe(void) {
    reads=0; return pci_observe_express(read_config,NULL,&initial,&previous);
}
static void reject(struct pci_express_observation o,enum pci_express_status s) {
    assert(o.status==s && !o.offset && !o.device_capabilities && !o.device_control_status);
}
int main(void) {
    assert(pci_enumerate_segment(NULL,NULL,NULL).status==PCI_ENUMERATION_INVALID_ARGUMENT);
    reject(pci_observe_express(NULL,NULL,&initial,&previous),PCI_EXPRESS_ARGUMENT);
    reject(pci_observe_express(read_config,NULL,NULL,&previous),PCI_EXPRESS_ARGUMENT);
    reject(pci_observe_express(read_config,NULL,&initial,NULL),PCI_EXPRESS_ARGUMENT);
    for(unsigned off=64;off<=252;off+=4) {
        setup(off,1,0);
        if(off>244) {reject(observe(),PCI_EXPRESS_SHAPE);continue;}
        for(unsigned flr=0;flr<2;++flr) for(unsigned pending=0;pending<2;++pending) {
            cfg[off/4+1]=flr<<28;cfg[off/4+2]=pending<<21;
            struct pci_express_observation o=observe();
            assert(o.status==PCI_EXPRESS_OK && o.offset==off && o.device_capabilities==flr<<28 &&
                o.device_control_status==pending<<21 && reads==12);
        }
    }
    /* Exhaust every header flag combination in each supported PCI layout. */
    for(unsigned layout=0;layout<2;++layout) for(unsigned flags=0;flags<65536;++flags) {
        setup(0x70,flags,layout);
        unsigned ver=flags&15,type=(flags>>4)&15;
        int valid=(ver==1 || ver==2) && !(flags&0xc000) &&
            ((layout==0 && (type==0 || type==1) && !(flags&0x100)) || (layout==1 && type==4));
        struct pci_express_observation o=observe();
        if(valid) assert(o.status==PCI_EXPRESS_OK); else reject(o,PCI_EXPRESS_SHAPE);
    }
    /* Largest nonoverlapping list: PCIe occupies 0x40,0x44,0x48. */
    setup(0x40,0x142,1);
    cfg[16]=0x01424c10;
    for(unsigned off=0x4c;off<=0xfc;off+=4) cfg[off/4]=1|((off==0xfc?0:off+4)<<8);
    assert(pci_collect_capabilities(read_config,NULL,&initial,&previous).status==PCI_CAPABILITY_OK);
    assert(previous.count==46);
    struct pci_express_observation o=observe();assert(o.status==PCI_EXPRESS_OK && reads==102);
    for(unsigned n=1;n<=102;++n) {
        fail_at=n;
        enum pci_express_status s=n<=50?PCI_EXPRESS_COLLECTION_FAILED:n<=52?PCI_EXPRESS_READ_FAILED:PCI_EXPRESS_FINAL_FAILED;
        reject(observe(),s);
    }
    fail_at=0;
    /* Detect each retained header's pre-read drift and final-list drift. */
    for(unsigned i=0;i<previous.count;++i) {
        unsigned off=previous.headers[i].offset;
        cfg[off/4]^=0x10000; reject(observe(),PCI_EXPRESS_LIST_CHANGED);cfg[off/4]^=0x10000;
        mutate_at=53;mutate_offset=off;mutate_mask=0x10000;
        reject(observe(),PCI_EXPRESS_FINAL_FAILED);cfg[off/4]^=0x10000;mutate_at=0;
    }
    for(unsigned k=0;k<4;++k) {
        unsigned offsets[]={0,4,12,52},masks[]={1,0x00100000,0x10000,4};
        mutate_at=53;mutate_offset=offsets[k];mutate_mask=masks[k];
        reject(observe(),PCI_EXPRESS_FINAL_FAILED);cfg[offsets[k]/4]^=masks[k];mutate_at=0;
    }
    for(unsigned off=0x74;off<=0x78;off+=4) {
        setup(0x70,2,0);cfg[off/4]=UINT32_MAX;reject(observe(),PCI_EXPRESS_ABSENT);
        setup(0x70,2,0);cfg[0x70/4]|=off<<8;cfg[off/4]=1;
        assert(pci_collect_capabilities(read_config,NULL,&initial,&previous).status==PCI_CAPABILITY_OK);
        reject(observe(),PCI_EXPRESS_SHAPE);
    }
    setup(0x70,2,0);cfg[28]|=0x8000;cfg[32]=0x00010010;
    assert(pci_collect_capabilities(read_config,NULL,&initial,&previous).status==PCI_CAPABILITY_OK);
    reject(observe(),PCI_EXPRESS_SHAPE);
    setup(0x70,2,0);cfg[28]=1;previous.headers[0].raw=1;reject(observe(),PCI_EXPRESS_NOT_PRESENT);
    setup(0x70,2,0);previous.count=49;reject(observe(),PCI_EXPRESS_ARGUMENT);assert(!reads);
    setup(0x70,2,0);previous.count=0;reject(observe(),PCI_EXPRESS_LIST_CHANGED);
    /* Payload bits are raw observations: neither pending nor FLR is admission. */
    for(unsigned bit=0;bit<32;++bit) {
        setup(0x70,2,0);cfg[29]=1u<<bit;cfg[30]=~(1u<<bit);
        o=observe();assert(o.status==PCI_EXPRESS_OK && o.device_capabilities==(1u<<bit) && o.device_control_status==~(1u<<bit));
    }
    puts("PASS PCIe device observer: bounds, all flags, 102 failures, drift, raw payloads");
}
