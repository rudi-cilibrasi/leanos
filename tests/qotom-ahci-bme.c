#include <assert.h>
#include <stdio.h>
#include <string.h>
#include "../boot/qotom-ahci-bme.h"
static struct pci_enumeration_header header;
static struct qotom_ahci_capabilities caps;
static struct qotom_ahci_port prior;
static struct qotom_ahci_interrupt_result interrupt;
static uint32_t cfg[64],globals[5],ports[7];
static unsigned reads,writes,fail_at,mutate_at,mutate_index;
static uint32_t mutate_mask;
static int mutate_port,mutate_config,write_fails,write_ignored;
static unsigned local(unsigned n) {return n>=39?n-39:n;}
static unsigned offset_at(unsigned n) {
    static const unsigned c[]={0,4,8,12,36},g[]={0,4,12,16,36};
    static const unsigned p[]={0x198,0x194,0x1a0,0x1a8,0x1b4,0x1b8,0x198};
    if(n==37 || n==38 || n==76)return 4;
    n=local(n);
    if(n>=15 && n<22)return p[n-15];
    if(n>=22)n-=22;
    return n<5?c[n]:n<10?g[n-5]:c[n-10];
}
static int step(void) {
    ++reads;assert(reads<=77);
    if(reads==mutate_at) {
        if(mutate_config)cfg[mutate_index]^=mutate_mask;
        else if(mutate_port)ports[mutate_index]^=mutate_mask;
        else globals[mutate_index]^=mutate_mask;
    }
    return reads!=fail_at;
}
static int config(void *ctx,uint8_t b,uint8_t d,uint8_t f,uint8_t off,uint32_t *out) {
    (void)ctx;assert(b==0 && d==19 && f==0 && off==offset_at(reads));
    if(reads!=37 && reads!=38 && reads!=76) {
        unsigned n=local(reads);if(n>=22)n-=22;
        assert(n<5 || (n>=10 && n<15));
    }
    if(!step())return 0;
    *out=cfg[off/4];return 1;
}
static int global(void *ctx,uint64_t address,uint32_t *out) {
    (void)ctx;assert(address==QOTOM_AHCI_BAR+offset_at(reads));
    unsigned n=local(reads);if(n>=22)n-=22;assert(n>=5 && n<10);unsigned i=n-5;
    if(!step())return 0;
    *out=globals[i];return 1;
}
static int port(void *ctx,uint64_t address,uint32_t *out) {
    (void)ctx;unsigned n=local(reads);
    assert(n>=15 && n<22 && address==QOTOM_AHCI_BAR+offset_at(reads));
    if(!step())return 0;
    *out=ports[n-15];return 1;
}
static int write_command(void *ctx,uint8_t bus,uint8_t device,uint8_t function,uint8_t offset,uint16_t value) {
    (void)ctx;assert(reads==38 && ++writes==1);
    assert(bus==0 && device==19 && function==0 && offset==4 && value==3);
    if(!write_ignored)cfg[1]=(cfg[1]&0xffff0000)|value;
    return !write_fails;
}
static void setup(void) {
    memset(&header,0,sizeof header);memset(cfg,0,sizeof cfg);
    header.device=19;header.words[0]=cfg[0]=0x0f238086;
    header.words[1]=cfg[1]=7;header.words[2]=cfg[2]=0x0106010e;header.words[9]=cfg[9]=QOTOM_AHCI_BAR;
    caps=(struct qotom_ahci_capabilities){0xc720ff01,0x80000002,2,0x10300,0x38};
    prior=(struct qotom_ahci_port){6,0,0x50,0x123,0,0,6};
    const uint32_t g[]={caps.capability,0x80000000,caps.ports,caps.version,caps.extended};
    const uint32_t p[]={6,0,0x50,0x123,0,0,6};
    memcpy(globals,g,sizeof g);memcpy(ports,p,sizeof p);
    interrupt=(struct qotom_ahci_interrupt_result){1,0x80000002,0x80000000};
    reads=writes=fail_at=mutate_at=0;write_fails=write_ignored=mutate_port=mutate_config=0;
}
static enum qotom_ahci_bme_status clear(struct qotom_ahci_bme_result *out) {
    memset(out,0xff,sizeof *out);
    return qotom_clear_ahci_bme(config,NULL,global,NULL,port,NULL,write_command,NULL,
        &header,QOTOM_AHCI_OK,&caps,QOTOM_AHCI_PORT_OK,&prior,QOTOM_AHCI_INTERRUPTS_OK,&interrupt,out);
}
static void zero(const struct qotom_ahci_bme_result *out) {
    assert(!out->attempted && !out->before_command && !out->after_command);
}
int main(void) {
    assert(pci_enumerate_segment(NULL,NULL,NULL).status==PCI_ENUMERATION_INVALID_ARGUMENT);
    struct qotom_ahci_bme_result out;
    setup();assert(clear(&out)==QOTOM_AHCI_BME_OK && reads==77 && writes==1);
    assert(out.attempted==1 && out.before_command==7 && out.after_command==3);
    for(unsigned n=1;n<=77;++n) {
        setup();fail_at=n;
        assert(clear(&out)==(n<=37?QOTOM_AHCI_BME_REFRESH:n==38?QOTOM_AHCI_BME_COMMAND:n==39?QOTOM_AHCI_BME_READBACK:QOTOM_AHCI_BME_FINAL));
        assert(reads==n && writes==(n>38));
        if(n<=38)zero(&out);
        else {assert(out.attempted==1 && out.before_command==7);assert(out.after_command==(n==39?0:3));}
    }
    for(unsigned i=0;i<7;++i)for(unsigned bit=0;bit<32;++bit) {
        setup();uint32_t p[]={6,0,0x50,0x123,0,0,6};p[i]^=1u<<bit;
        prior=(struct qotom_ahci_port){p[0],p[1],p[2],p[3],p[4],p[5],p[6]};
        assert(clear(&out)==QOTOM_AHCI_BME_PRIOR && !reads && !writes);zero(&out);
        setup();ports[i]^=1u<<bit;
        assert(clear(&out)==QOTOM_AHCI_BME_STATE && reads==37 && !writes);zero(&out);
        setup();mutate_at=40;mutate_index=i;mutate_mask=1u<<bit;mutate_port=1;
        assert(clear(&out)==QOTOM_AHCI_BME_FINAL && writes==1 && reads==76);
    }
    for(unsigned i=0;i<5;++i)for(unsigned bit=0;bit<32;++bit) {
        setup();uint32_t g[]={caps.capability,caps.control,caps.ports,caps.version,caps.extended};g[i]^=1u<<bit;
        caps=(struct qotom_ahci_capabilities){g[0],g[1],g[2],g[3],g[4]};
        assert(clear(&out)==QOTOM_AHCI_BME_PRIOR && !reads && !writes);zero(&out);
        setup();globals[i]^=1u<<bit;
        assert(clear(&out)==QOTOM_AHCI_BME_REFRESH && !writes);zero(&out);
        setup();mutate_at=40;mutate_index=i;mutate_mask=1u<<bit;
        assert(clear(&out)==QOTOM_AHCI_BME_FINAL && writes==1);
    }
    for(unsigned i=0;i<3;++i)for(unsigned bit=0;bit<32;++bit) {
        setup();uint32_t *field=i==0?&interrupt.write_attempted:i==1?&interrupt.before_control:&interrupt.after_control;
        *field^=1u<<bit;assert(clear(&out)==QOTOM_AHCI_BME_PRIOR && !reads && !writes);zero(&out);
    }
    for(unsigned bit=0;bit<32;++bit) {
        setup();header.words[1]^=1u<<bit;
        if(bit<16){assert(clear(&out)==QOTOM_AHCI_BME_PRIOR && !reads && !writes);zero(&out);}
        else assert(clear(&out)==QOTOM_AHCI_BME_OK);
        setup();mutate_at=38;mutate_index=1;mutate_mask=1u<<bit;mutate_config=1;
        if(bit<16){assert(clear(&out)==QOTOM_AHCI_BME_COMMAND && !writes);zero(&out);}
        else {assert(clear(&out)==QOTOM_AHCI_BME_OK);assert(cfg[1]==(3u|(1u<<bit)));}
        setup();mutate_at=39;mutate_index=1;mutate_mask=1u<<bit;mutate_config=1;
        if(bit<16){assert(clear(&out)==QOTOM_AHCI_BME_READBACK && reads==39);assert(out.after_command==(3u^(1u<<bit)));}
        else assert(clear(&out)==QOTOM_AHCI_BME_OK);
        setup();mutate_at=77;mutate_index=1;mutate_mask=1u<<bit;mutate_config=1;
        if(bit<16){assert(clear(&out)==QOTOM_AHCI_BME_FINAL && reads==77);assert(out.after_command==(3u^(1u<<bit)));}
        else assert(clear(&out)==QOTOM_AHCI_BME_OK);
    }
    setup();cfg[1]=0xa5a50007;assert(clear(&out)==QOTOM_AHCI_BME_OK && cfg[1]==0xa5a50003);
    setup();mutate_at=40;mutate_index=1;mutate_mask=4;mutate_config=1;
    assert(clear(&out)==QOTOM_AHCI_BME_FINAL && out.after_command==7 && reads==77);
    setup();mutate_at=40;mutate_index=9;mutate_mask=0x1000;mutate_config=1;
    assert(clear(&out)==QOTOM_AHCI_BME_FINAL && writes==1 && out.after_command==3);
    setup();mutate_at=39;mutate_index=1;mutate_mask=UINT32_MAX^3;mutate_config=1;
    assert(clear(&out)==QOTOM_AHCI_BME_READBACK && out.after_command==0xffff);
    setup();write_ignored=1;assert(clear(&out)==QOTOM_AHCI_BME_READBACK && out.after_command==7 && reads==39);
    setup();write_fails=1;assert(clear(&out)==QOTOM_AHCI_BME_WRITE && reads==38 && writes==1);
    assert(cfg[1]==3 && out.attempted==1 && out.before_command==7 && !out.after_command);
    setup();write_fails=write_ignored=1;assert(clear(&out)==QOTOM_AHCI_BME_WRITE && cfg[1]==7);
    setup();cfg[9]^=0x1000;assert(clear(&out)==QOTOM_AHCI_BME_REFRESH && !writes);zero(&out);
    setup();cfg[1]&=~2u;assert(clear(&out)==QOTOM_AHCI_BME_REFRESH && !writes);zero(&out);
    for(unsigned status=1;status<=11;++status) {
        setup();assert(qotom_clear_ahci_bme(config,NULL,global,NULL,port,NULL,write_command,NULL,
            &header,status,&caps,QOTOM_AHCI_PORT_OK,&prior,QOTOM_AHCI_INTERRUPTS_OK,&interrupt,&out)==QOTOM_AHCI_BME_PRIOR);zero(&out);
        assert(qotom_clear_ahci_bme(config,NULL,global,NULL,port,NULL,write_command,NULL,
            &header,QOTOM_AHCI_OK,&caps,status,&prior,QOTOM_AHCI_INTERRUPTS_OK,&interrupt,&out)==QOTOM_AHCI_BME_PRIOR);zero(&out);
        assert(qotom_clear_ahci_bme(config,NULL,global,NULL,port,NULL,write_command,NULL,
            &header,QOTOM_AHCI_OK,&caps,QOTOM_AHCI_PORT_OK,&prior,status,&interrupt,&out)==QOTOM_AHCI_BME_PRIOR);zero(&out);assert(!reads && !writes);
    }
    setup();assert(qotom_clear_ahci_bme(config,NULL,global,NULL,port,NULL,NULL,NULL,
        &header,QOTOM_AHCI_OK,&caps,QOTOM_AHCI_PORT_OK,&prior,QOTOM_AHCI_INTERRUPTS_OK,&interrupt,&out)==QOTOM_AHCI_BME_ARGUMENT);zero(&out);
    puts("PASS AHCI BME: exact77reads, one word7to3, all failures, stopped/interrupt/resource drift, status preservation");
}
