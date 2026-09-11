#include <assert.h>
#include <string.h>
#include "../boot/pci-capabilities.h"
struct source {uint32_t words[64],reads; int fail;};
static int read_config(void *p,uint8_t bus,uint8_t device,uint8_t function,uint8_t offset,uint32_t *value) {
    struct source *s=p;assert(bus==3 && device==2 && function==1 && !(offset&3));
    ++s->reads;if(offset==s->fail)return 0;*value=s->words[offset/4];return 1;
}
int main(void) {
    struct source s={.fail=-1};
    s.words[0]=0x12348086;s.words[1]=0x00100007;s.words[13]=64;
    for(unsigned i=16;i<64;++i)s.words[i]=0xabc00005 | (i==63?0:(i+1)*4)<<8;
    struct pci_enumeration_header h={.bus=3,.device=2,.function=1};
    memcpy(h.words,s.words,sizeof(h.words));
    struct pci_capability_snapshot snap;
    struct pci_capability_result r=pci_collect_capabilities(read_config,&s,&h,&snap);
    assert(r.status==PCI_CAPABILITY_OK && snap.count==48 && s.reads==52);
    for(unsigned i=0;i<48;++i)assert(snap.headers[i].offset==64+4*i && snap.headers[i].raw==s.words[16+i]);
    for(unsigned i=16;i<64;++i){
        uint32_t saved=s.words[i];s.words[i]=(saved&0xffff00ff)|64<<8;s.reads=0;
        r=pci_collect_capabilities(read_config,&s,&h,&snap);
        assert(r.status==PCI_CAPABILITY_CYCLE && r.offset==64 && !snap.count && s.reads==i-16+5);
        s.words[i]=saved;
        s.fail=i*4;s.reads=0;r=pci_collect_capabilities(read_config,&s,&h,&snap);
        assert(r.status==PCI_CAPABILITY_READ_FAILED && r.offset==i*4 && !snap.count && s.reads==i-16+5);
        s.fail=-1;
    }
    for(unsigned offset=1;offset<256;++offset){
        if(offset>=64 && !(offset&3))continue;
        h.words[13]=s.words[13]=offset;s.reads=0;r=pci_collect_capabilities(read_config,&s,&h,&snap);
        assert(r.status==PCI_CAPABILITY_POINTER && r.offset==offset && !snap.count && s.reads==4);
    }
    h.words[13]=s.words[13]=64;
    const unsigned initial_offsets[]={0,4,12,52};
    const uint32_t changes[]={1,0x00100000,0x00800000,4};
    for(unsigned i=0;i<4;++i){
        s.words[initial_offsets[i]/4]^=changes[i];s.reads=0;
        r=pci_collect_capabilities(read_config,&s,&h,&snap);
        assert(r.status==PCI_CAPABILITY_HEADER_CHANGED && !snap.count && s.reads==i+1);
        s.words[initial_offsets[i]/4]^=changes[i];
    }
    s.words[16]=UINT32_MAX;r=pci_collect_capabilities(read_config,&s,&h,&snap);
    assert(r.status==PCI_CAPABILITY_ABSENT && r.offset==64 && !snap.count);
    /* Acyclic backward links are valid: the FreeBSD Broadcom report lists
       PM at40, vendor at58, MSI at48, then PCIe atd0. Payloads here are synthetic. */
    s.words[0x40/4]=0x5801;s.words[0x58/4]=0x4809;
    s.words[0x48/4]=0xd005;s.words[0xd0/4]=0x10;s.reads=0;
    r=pci_collect_capabilities(read_config,&s,&h,&snap);
    assert(r.status==PCI_CAPABILITY_OK && snap.count==4 && s.reads==8);
    assert(snap.headers[0].offset==0x40 && snap.headers[1].offset==0x58 &&
        snap.headers[2].offset==0x48 && snap.headers[3].offset==0xd0);
    h.words[1]=s.words[1]=7;s.reads=0;
    r=pci_collect_capabilities(read_config,&s,&h,&snap);
    assert(r.status==PCI_CAPABILITY_OK && !snap.count && s.reads==4);
    snap.count=99;r=pci_collect_capabilities(0,&s,&h,&snap);
    assert(r.status==PCI_CAPABILITY_ARGUMENT && !snap.count);
    /* Keep the complete-segment collector compiled in this translation unit. */
    struct pci_enumeration_snapshot enumeration;
    assert(pci_enumerate_segment(0,0,&enumeration).status==PCI_ENUMERATION_INVALID_ARGUMENT);
    return 0;
}
