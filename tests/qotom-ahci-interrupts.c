#include <assert.h>
#include <stdio.h>
#include <string.h>
#include "../boot/qotom-ahci-interrupts.h"
static struct pci_enumeration_header header;
static struct qotom_ahci_capabilities caps;
static struct qotom_ahci_port prior;
static uint32_t cfg[64],globals[5],ports[7];
static unsigned reads,writes,fail_at,mutate_at,mutate_index;
static uint32_t mutate_mask;
static int mutate_port,write_fails,write_ignored;
static unsigned local(unsigned n) {return n>=38?n-38:n;}
static unsigned offset_at(unsigned n) {
    static const unsigned c[]={0,4,8,12,36},g[]={0,4,12,16,36};
    static const unsigned p[]={0x198,0x194,0x1a0,0x1a8,0x1b4,0x1b8,0x198};
    if(n==37)return 4;
    n=local(n);
    if(n>=15 && n<22)return p[n-15];
    if(n>=22)n-=22;
    return n<5?c[n]:n<10?g[n-5]:c[n-10];
}
static int step(void) {
    ++reads;assert(reads<=75);
    if(reads==mutate_at) {
        if(mutate_port)ports[mutate_index]^=mutate_mask;
        else globals[mutate_index]^=mutate_mask;
    }
    return reads!=fail_at;
}
static int config(void *ctx,uint8_t b,uint8_t d,uint8_t f,uint8_t off,uint32_t *out) {
    (void)ctx;assert(b==0 && d==19 && f==0 && off==offset_at(reads));
    unsigned n=local(reads);if(n>=22)n-=22;
    assert(n<5 || (n>=10 && n<15));
    if(!step())return 0;
    *out=cfg[off/4];return 1;
}
static int global(void *ctx,uint64_t address,uint32_t *out) {
    (void)ctx;assert(address==QOTOM_AHCI_BAR+offset_at(reads));
    unsigned n=local(reads),i;
    if(n==37)i=1;
    else {if(n>=22)n-=22;assert(n>=5 && n<10);i=n-5;}
    if(!step())return 0;
    *out=globals[i];return 1;
}
static int port(void *ctx,uint64_t address,uint32_t *out) {
    (void)ctx;unsigned n=local(reads);
    assert(n>=15 && n<22 && address==QOTOM_AHCI_BAR+offset_at(reads));
    if(!step())return 0;
    *out=ports[n-15];return 1;
}
static int write_control(void *ctx,uint64_t address,uint32_t value) {
    (void)ctx;assert(reads==37 && ++writes==1);
    assert(address==QOTOM_AHCI_BAR+4 && value==UINT32_C(0x80000000));
    if(!write_ignored)globals[1]=value;
    return !write_fails;
}
static void setup(void) {
    memset(&header,0,sizeof header);memset(cfg,0,sizeof cfg);
    header.device=19;header.words[0]=cfg[0]=0x0f238086;
    header.words[1]=cfg[1]=7;header.words[2]=cfg[2]=0x0106010e;header.words[9]=cfg[9]=QOTOM_AHCI_BAR;
    caps=(struct qotom_ahci_capabilities){0xc720ff01,0x80000002,2,0x10300,0x38};
    prior=(struct qotom_ahci_port){6,0,0x50,0x123,0,0,6};
    const uint32_t g[]={caps.capability,caps.control,caps.ports,caps.version,caps.extended};
    const uint32_t p[]={6,0,0x50,0x123,0,0,6};
    memcpy(globals,g,sizeof g);memcpy(ports,p,sizeof p);
    reads=writes=fail_at=mutate_at=0;write_fails=write_ignored=mutate_port=0;
}
static enum qotom_ahci_interrupt_status disable(struct qotom_ahci_interrupt_result *out) {
    memset(out,0xff,sizeof *out);
    return qotom_disable_ahci_interrupts(config,NULL,global,NULL,port,NULL,write_control,NULL,
        &header,QOTOM_AHCI_OK,&caps,QOTOM_AHCI_PORT_OK,&prior,out);
}
static void zero(const struct qotom_ahci_interrupt_result *out) {
    assert(!out->write_attempted && !out->before_control && !out->after_control);
}
int main(void) {
    assert(pci_enumerate_segment(NULL,NULL,NULL).status==PCI_ENUMERATION_INVALID_ARGUMENT);
    struct qotom_ahci_interrupt_result out;
    setup();assert(disable(&out)==QOTOM_AHCI_INTERRUPTS_OK && reads==75 && writes==1);
    assert(out.write_attempted==1 && out.before_control==0x80000002 && out.after_control==0x80000000);
    for(unsigned n=1;n<=75;++n) {
        setup();fail_at=n;
        assert(disable(&out)==(n<=37?QOTOM_AHCI_INTERRUPTS_REFRESH:n==38?QOTOM_AHCI_INTERRUPTS_READ:QOTOM_AHCI_INTERRUPTS_FINAL));
        assert(reads==n && writes==(n>37));
        if(n<=37)zero(&out);
        else {assert(out.write_attempted==1 && out.before_control==0x80000002);assert(out.after_control==(n==38?0:0x80000000));}
    }
    for(unsigned i=0;i<7;++i)for(unsigned bit=0;bit<32;++bit) {
        setup();uint32_t p[]={6,0,0x50,0x123,0,0,6};p[i]^=1u<<bit;
        prior=(struct qotom_ahci_port){p[0],p[1],p[2],p[3],p[4],p[5],p[6]};
        assert(disable(&out)==QOTOM_AHCI_INTERRUPTS_PRIOR && !reads && !writes);zero(&out);
        setup();ports[i]^=1u<<bit;
        assert(disable(&out)==QOTOM_AHCI_INTERRUPTS_STATE && reads==37 && !writes);zero(&out);
        setup();mutate_at=39;mutate_index=i;mutate_mask=1u<<bit;mutate_port=1;
        assert(disable(&out)==QOTOM_AHCI_INTERRUPTS_FINAL && writes==1 && reads==75);
    }
    for(unsigned i=0;i<5;++i)for(unsigned bit=0;bit<32;++bit) {
        setup();uint32_t g[]={caps.capability,caps.control,caps.ports,caps.version,caps.extended};g[i]^=1u<<bit;
        caps=(struct qotom_ahci_capabilities){g[0],g[1],g[2],g[3],g[4]};
        assert(disable(&out)==QOTOM_AHCI_INTERRUPTS_PRIOR && !reads && !writes);zero(&out);
        setup();globals[i]^=1u<<bit;
        assert(disable(&out)==QOTOM_AHCI_INTERRUPTS_REFRESH && !writes);zero(&out);
        setup();mutate_at=39;mutate_index=i;mutate_mask=1u<<bit;
        assert(disable(&out)==QOTOM_AHCI_INTERRUPTS_FINAL && writes==1);
    }
    for(unsigned bit=0;bit<32;++bit) {
        setup();mutate_at=38;mutate_index=1;mutate_mask=1u<<bit;
        assert(disable(&out)==QOTOM_AHCI_INTERRUPTS_READBACK && reads==38 && writes==1);
        assert(out.after_control==(UINT32_C(0x80000000)^(1u<<bit)));
    }
    setup();write_ignored=1;assert(disable(&out)==QOTOM_AHCI_INTERRUPTS_READBACK);
    assert(out.write_attempted==1 && out.after_control==0x80000002);
    setup();write_fails=1;assert(disable(&out)==QOTOM_AHCI_INTERRUPTS_WRITE && reads==37 && writes==1);
    assert(globals[1]==0x80000000 && out.write_attempted==1 && !out.after_control);
    setup();write_fails=write_ignored=1;assert(disable(&out)==QOTOM_AHCI_INTERRUPTS_WRITE);
    assert(globals[1]==0x80000002 && out.write_attempted==1 && !out.after_control);
    setup();cfg[9]^=0x1000;assert(disable(&out)==QOTOM_AHCI_INTERRUPTS_REFRESH && !writes);zero(&out);
    setup();cfg[1]&=~2u;assert(disable(&out)==QOTOM_AHCI_INTERRUPTS_REFRESH && !writes);zero(&out);
    for(unsigned status=1;status<=8;++status) {
        setup();assert(qotom_disable_ahci_interrupts(config,NULL,global,NULL,port,NULL,write_control,NULL,
            &header,(enum qotom_ahci_status)status,&caps,QOTOM_AHCI_PORT_OK,&prior,&out)==QOTOM_AHCI_INTERRUPTS_PRIOR);zero(&out);
        assert(qotom_disable_ahci_interrupts(config,NULL,global,NULL,port,NULL,write_control,NULL,
            &header,QOTOM_AHCI_OK,&caps,(enum qotom_ahci_port_status)status,&prior,&out)==QOTOM_AHCI_INTERRUPTS_PRIOR);zero(&out);assert(!reads && !writes);
    }
    setup();assert(qotom_disable_ahci_interrupts(config,NULL,global,NULL,port,NULL,NULL,NULL,
        &header,QOTOM_AHCI_OK,&caps,QOTOM_AHCI_PORT_OK,&prior,&out)==QOTOM_AHCI_INTERRUPTS_ARGUMENT);zero(&out);
    puts("PASS AHCI interrupt clear: 75 reads, one exact write, every read failure, prior/live/final drift, ambiguous writes");
}
