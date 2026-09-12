#include <assert.h>
#include <stdio.h>
#include <string.h>
#include "../boot/qotom-ahci-port.h"
static struct pci_enumeration_header header;
static struct qotom_ahci_capabilities prior;
static uint32_t cfg[64], globals[5], ports[7];
static unsigned reads,fail_at,mutate_at,mutate_index;
static uint32_t mutate_mask;
static unsigned offset_at(unsigned n) {
    static const unsigned c[]={0,4,8,12,36},g[]={0,4,12,16,36};
    static const unsigned p[]={0x198,0x194,0x1a0,0x1a8,0x1b4,0x1b8,0x198};
    if(n>=15 && n<22)return p[n-15];
    if(n>=22)n-=22;
    return n<5?c[n]:n<10?g[n-5]:c[n-10];
}
static int step(void) {
    ++reads;assert(reads<=37);
    if(reads==mutate_at)globals[mutate_index]^=mutate_mask;
    return reads!=fail_at;
}
static int config(void *ctx,uint8_t b,uint8_t d,uint8_t f,uint8_t off,uint32_t *out) {
    (void)ctx;assert(b==0 && d==19 && f==0 && off==offset_at(reads));
    unsigned n=reads>=22?reads-22:reads;assert(n<5 || (n>=10 && n<15));
    if(!step())return 0;
    *out=cfg[off/4];return 1;
}
static int global(void *ctx,uint64_t address,uint32_t *out) {
    (void)ctx;assert(address==QOTOM_AHCI_BAR+offset_at(reads));
    unsigned n=reads>=22?reads-22:reads;assert(n>=5 && n<10);
    if(!step())return 0;
    *out=globals[n-5];return 1;
}
static int port(void *ctx,uint64_t address,uint32_t *out) {
    (void)ctx;assert(reads>=15 && reads<22 && address==QOTOM_AHCI_BAR+offset_at(reads));
    unsigned n=reads-15;if(!step())return 0;
    *out=ports[n];return 1;
}
static void setup(void) {
    memset(&header,0,sizeof header);memset(cfg,0,sizeof cfg);
    header.device=19;header.words[0]=cfg[0]=0x0f238086;
    header.words[1]=cfg[1]=7;header.words[2]=cfg[2]=0x0106010e;header.words[9]=cfg[9]=QOTOM_AHCI_BAR;
    prior=(struct qotom_ahci_capabilities){0xc720ff01,0x80000002,2,0x10300,0x38};
    globals[0]=prior.capability;globals[1]=prior.control;globals[2]=prior.ports;
    globals[3]=prior.version;globals[4]=prior.extended;
    for(unsigned i=0;i<7;++i)ports[i]=i;
    reads=fail_at=mutate_at=0;
}
static enum qotom_ahci_port_status collect(struct qotom_ahci_port *out) {
    memset(out,0xff,sizeof *out);reads=0;
    return qotom_collect_ahci_port(config,NULL,global,NULL,port,NULL,&header,QOTOM_AHCI_OK,&prior,out);
}
static void zero(const struct qotom_ahci_port *out) {
    const struct qotom_ahci_port empty={0};assert(!memcmp(out,&empty,sizeof empty));
}
int main(void) {
    assert(pci_enumerate_segment(NULL,NULL,NULL).status==PCI_ENUMERATION_INVALID_ARGUMENT);
    struct qotom_ahci_port out;
    setup();assert(collect(&out)==QOTOM_AHCI_PORT_OK && reads==37);
    assert(out.command_before==0 && out.interrupt_enable==1 && out.task_file==2 && out.sata_status==3 && out.active==4 && out.issued==5 && out.command_after==6);
    for(unsigned n=1;n<=37;++n) {
        setup();fail_at=n;
        assert(collect(&out)==(n<=15?QOTOM_AHCI_PORT_REFRESH:n<=22?QOTOM_AHCI_PORT_READ:QOTOM_AHCI_PORT_FINAL));zero(&out);
    }
    for(unsigned i=0;i<7;++i) {
        setup();ports[i]=UINT32_MAX;assert(collect(&out)==QOTOM_AHCI_PORT_ABSENT);zero(&out);
        for(unsigned bit=0;bit<32;++bit) {
            setup();ports[i]=1u<<bit;assert(collect(&out)==QOTOM_AHCI_PORT_OK);
            uint32_t v[]={out.command_before,out.interrupt_enable,out.task_file,out.sata_status,out.active,out.issued,out.command_after};assert(v[i]==(1u<<bit));
        }
    }
    for(unsigned i=0;i<5;++i)for(unsigned bit=0;bit<32;++bit) {
        setup();globals[i]^=1u<<bit;assert(collect(&out)==QOTOM_AHCI_PORT_DRIFT && reads==15);zero(&out);
        setup();mutate_at=23;mutate_index=i;mutate_mask=1u<<bit;
        assert(collect(&out)==QOTOM_AHCI_PORT_FINAL);zero(&out);
    }
    setup();prior.ports=1;assert(collect(&out)==QOTOM_AHCI_PORT_PRIOR && !reads);zero(&out);
    setup();prior.control=globals[1]=0x80000000;assert(collect(&out)==QOTOM_AHCI_PORT_OK);
    setup();prior.control=0x80000003;assert(collect(&out)==QOTOM_AHCI_PORT_PRIOR && !reads);zero(&out);
    setup();assert(qotom_collect_ahci_port(config,NULL,global,NULL,port,NULL,&header,QOTOM_AHCI_DRIFT,&prior,&out)==QOTOM_AHCI_PORT_PRIOR);zero(&out);
    assert(qotom_collect_ahci_port(NULL,NULL,global,NULL,port,NULL,&header,QOTOM_AHCI_OK,&prior,&out)==QOTOM_AHCI_PORT_ARGUMENT);zero(&out);
    for(unsigned off=0;off<4096;++off) {
        uint64_t address=42;int valid=off==0x194 || off==0x198 || off==0x1a0 || off==0x1a8 || off==0x1b4 || off==0x1b8;
        assert(qotom_ahci_port_address(off,&address)==valid);assert(address==(valid?QOTOM_AHCI_BAR+off:42));
    }
    puts("PASS AHCI port: exact37reads, all failures, global drift, raw command/queue samples");
}
