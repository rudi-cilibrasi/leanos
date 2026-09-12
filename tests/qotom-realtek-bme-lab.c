#include <assert.h>
#include <setjmp.h>
#include <stdio.h>
#include <string.h>
#include "qotom-realtek-state-arm.h"
#include "qotom-realtek-route.h"
#define LEANOS_QOTOM_REALTEK_BME 1
static uint64_t root[512],pdpt[512],pd[512],pt[4096];
static struct lab_ecam_root_view view={root,pdpt,pd,pt,0x100000,0x101000,0x102000,0x103000};
static const struct lab_ecam_firmware_table *lab_ecam_tables=lab_ecam_expected_tables;
static const uint32_t lab_ecam_table_count=LAB_ECAM_FIRMWARE_TABLE_COUNT;
#define lab_ecam_aperture ((void *)0x200000)
static struct { unsigned armed; } lab_ecam_window;
static int lab_ecam_reader;
static struct pci_capability_snapshot lab_retained_pci_caps[16];
static struct qotom_rootport_bme_result lab_retained_rootport_bme[4];
static struct pci_enumeration_snapshot snapshot;
static uint32_t cfg[2][64],endpoint_cfg[2][64],reads[2],mmio_reads[2],writes[2];
static uint32_t failed_port,failed_read,failed_write;
static char output[4096];static size_t used;static jmp_buf terminal;
static int lab_ecam_native_controls(void *p,struct lab_ecam_controls *out) {
    (void)p;*out=(struct lab_ecam_controls){0x0007040600070406,0x80010001,0x100000,0x20,0xd00,2};return 1;
}
static void lab_ecam_native_invalidate(void *p,uint64_t address){(void)p;assert(address==0x200000);}
static int lab_bme_store16(void *p,uint64_t address,uint16_t value) {
    (void)p;assert(address==0x200004 && value==3);
    uint64_t mapped=pt[512]&~UINT64_C(0x60);
    assert(mapped==UINT64_C(0x80000000e010001b) ||
        mapped==UINT64_C(0x80000000e030001b));
    unsigned port=mapped==UINT64_C(0x80000000e010001b)?0:1;
    assert(reads[port]==181 && writes[port]++==0);
    if(failed_write==port)return 0;
    endpoint_cfg[port][1]=(endpoint_cfg[port][1]&UINT32_C(0xffff0000))|3;
    return 1;
}
static int lab_hda_load(void *p,uint64_t address,uint8_t width,uint32_t *value) {
    (void)p;
    uint64_t mapped=pt[512]&~UINT64_C(0x20);
    assert(mapped==UINT64_C(0x80000000d0804019) || mapped==UINT64_C(0x80000000d0604019));
    unsigned port=mapped==UINT64_C(0x80000000d0804019)?0:1;
    ++reads[port];++mmio_reads[port];
    if(failed_port==port && failed_read==reads[port])return 0;
    assert(address>=0x200000 && address<0x201000);unsigned offset=address-0x200000;
    assert((offset==0x37 && width==1)||(offset==0x3c && width==2)||((offset==0x40 || offset==0x44)&&width==4));
    *value=offset==0x40?0x2c800800:0;pt[512]|=0x20;return 1;
}
static int qotom_ecam_read(void *p,uint8_t bus,uint8_t device,uint8_t fn,uint8_t offset,uint32_t *out) {
    assert(p==&lab_ecam_reader && lab_ecam_window.armed && !(offset&3));
    assert(pt[512]==UINT64_C(0x8000000000200003));
    unsigned port;
    if(!bus){assert(device==28 && (fn==0 || fn==2));port=fn/2;}
    else {assert((bus==1 || bus==3) && !device && !fn);port=(bus-1)/2;}
    ++reads[port];assert(reads[port]<=273);
    if(failed_port==port && failed_read==reads[port])return 0;
    *out=bus?endpoint_cfg[port][offset/4]:cfg[port][offset/4];return 1;
}
static void serial_puts(const char *s);
static void serial_u64(uint64_t n){char b[32];snprintf(b,sizeof b,"%llu",(unsigned long long)n);serial_puts(b);}
static void serial_putc(char c){char b[2]={c,0};serial_puts(b);}
static __attribute__((noreturn)) void pre_admission_fail(const char *s) {
    assert((!strcmp(s,"qotom-realtek-state") || !strcmp(s,"qotom-realtek-bme")) &&
        !lab_ecam_window.armed);longjmp(terminal,1);
}
#include "../hardware/lab/qotom-realtek-state.c.inc"
static void serial_puts(const char *s) {
    assert(!lab_ecam_window.armed && !lab_realtek_state_window.armed &&
        !lab_realtek_bme_writer.armed);
    assert(pt[512]==UINT64_C(0x8000000000200003));
    size_t n=strlen(s);assert(used+n<sizeof output);memcpy(output+used,s,n+1);used+=n;
}
static void setup(void) {
    memset(&snapshot,0,sizeof snapshot);snapshot.count=16;memset(cfg,0,sizeof cfg);
    memset(endpoint_cfg,0,sizeof endpoint_cfg);memset(reads,0,sizeof reads);
    memset(mmio_reads,0,sizeof mmio_reads);memset(writes,0,sizeof writes);
    used=0;output[0]=0;failed_port=failed_write=2;failed_read=0;lab_ecam_window.armed=0;
    root[0]=view.pdpt_address|7;pdpt[0]=view.pd_address|7;
    for(unsigned i=0;i<8;++i)pd[i]=(view.pt_address+i*4096)|7;
    for(unsigned i=0;i<4096;++i)pt[i]=((uint64_t)i*4096)|UINT64_C(0x8000000000000003);
    for(unsigned port=0;port<2;++port) {
        unsigned bus=1+port*2;uint32_t bar=(uint32_t)qotom_realtek_bar(bus);
        struct pci_enumeration_header *h=&snapshot.headers[13+port*2];h->bus=bus;
        uint32_t endpoint[16]={0x816810ec,0x100007,0x02000007,16,bus==1?0xe001:0xd001,0,bar|4,0,(bar-0x4000)|12,0,0,0x012310ec,0,64,0,261};
        memcpy(h->words,endpoint,sizeof endpoint);
        memcpy(endpoint_cfg[port],endpoint,sizeof endpoint);
        uint32_t bridge[16]={bus==1?0x0f488086:0x0f4c8086,0x100007,0x0604000e,0x810010,
            0,0,(bus<<16)|(bus<<8),bus==1?0x2000e0e0:0x2000d0d0,
            bus==1?0xd080d080:0xd060d060,0x1fff1,0,0,0,0x40,0,bus==1?0x100105:0x100305};
        h=&snapshot.headers[6+port*2];h->device=28;h->function=port*2;
        memcpy(h->words,bridge,sizeof bridge);memcpy(cfg[port],bridge,sizeof bridge);cfg[port][1]=0x100003;
        struct pci_capability_snapshot *caps=&lab_retained_pci_caps[6+port*2];caps->count=4;
        const unsigned offsets[]={64,128,144,160};const uint32_t raws[]={21135376,36869,40973,3355639809u};
        for(unsigned i=0;i<4;++i){caps->headers[i]=(struct pci_capability_header){offsets[i],raws[i]};cfg[port][offsets[i]/4]=raws[i];}
        cfg[port][17]=0x8000;cfg[port][18]=0x100000;
        lab_retained_rootport_bme[port*2]=(struct qotom_rootport_bme_result){1,7,3};
    }
}
static size_t append_state(char *expected,size_t n,unsigned port) {
    return n+(size_t)snprintf(expected+n,4096-n,
        "LEANOS-LAB/1 REALTEK-STATE profile=qotom-realtek-state-v1 index=%u status=0 transmit-before=%u command-before=0 interrupt-mask=0 receive=0 command-after=0 transmit-after=%u\n",
        13+port*2,0x2c800800,0x2c800800);
}
static size_t append_bme(char *expected,size_t n,unsigned port,unsigned status,
        unsigned attempted,unsigned before,unsigned after) {
    return n+(size_t)snprintf(expected+n,4096-n,
        "LEANOS-LAB/1 REALTEK-BME profile=qotom-realtek-bme-v1 index=%u status=%u attempted=%u before=%u after=%u\n",
        13+port*2,status,attempted,before,after);
}
static void assert_disarmed(void) {
    assert(!lab_ecam_window.armed && !lab_realtek_state_window.armed &&
        !lab_realtek_bme_writer.armed);
    assert(pt[512]==UINT64_C(0x8000000000200003));
}
static void expect_full(unsigned last,unsigned status,unsigned attempted,
        unsigned before,unsigned after) {
    char expected[4096];size_t n=0;
    for(unsigned port=0;port<2;++port)n=append_state(expected,n,port);
    for(unsigned port=0;port<=last;++port)
        n=append_bme(expected,n,port,port==last?status:0,
            port==last?attempted:1,port==last?before:7,port==last?after:3);
    assert(n<sizeof expected && !strcmp(output,expected));assert_disarmed();
}
static void expect_direct(unsigned status) {
    char expected[4096];size_t n=append_bme(expected,0,0,status,0,0,0);
    assert(n<sizeof expected && !strcmp(output,expected));assert_disarmed();
}
static void prime_prior(void) {
    for(unsigned port=0;port<2;++port)
        lab_retained_realtek_state[port]=(struct qotom_realtek_state){
            0x2c800800,0,0,0,0,0x2c800800};
}
int main(void) {
    (void)pci_enumerate_segment;
    setup();lab_capture_realtek_state(&view,&snapshot);expect_full(1,0,1,7,3);
    for(unsigned port=0;port<2;++port) {
        assert(reads[port]==273 && mmio_reads[port]==18 && writes[port]==1);
        assert((endpoint_cfg[port][1]&0xffff)==3);
        assert(qotom_realtek_stopped(&lab_retained_realtek_state[port]));
    }
    for(volatile unsigned port=0;port<2;++port)for(volatile unsigned n=1;n<=183;++n) {
        setup();failed_port=port;failed_read=90+n;
        if(!setjmp(terminal)){lab_capture_realtek_state(&view,&snapshot);assert(0);}
        unsigned status=n<=90?QOTOM_REALTEK_BME_REFRESH:
            n==91?QOTOM_REALTEK_BME_COMMAND:n==92?QOTOM_REALTEK_BME_READBACK:
            QOTOM_REALTEK_BME_FINAL;
        expect_full(port,status,n>91,n>91?7:0,n>92?3:0);
        assert(reads[port]==90+n && writes[port]==(n>91));
        for(unsigned before_port=0;before_port<port;++before_port)
            assert(reads[before_port]==273 && writes[before_port]==1);
        for(unsigned after_port=port+1;after_port<2;++after_port)
            assert(reads[after_port]==90 && !writes[after_port]);
    }
    for(volatile unsigned port=0;port<2;++port) {
        setup();failed_write=port;
        if(!setjmp(terminal)){lab_capture_realtek_state(&view,&snapshot);assert(0);}
        expect_full(port,QOTOM_REALTEK_BME_WRITE,1,7,0);
        assert(reads[port]==181 && writes[port]==1 &&
            (endpoint_cfg[port][1]&0xffff)==7);
        for(unsigned after_port=port+1;after_port<2;++after_port)
            assert(reads[after_port]==90 && !writes[after_port]);
    }
    setup();prime_prior();snapshot.count=15;
    if(!setjmp(terminal)){lab_capture_realtek_bme(&view,&snapshot);assert(0);}
    expect_direct(9);assert(!reads[0] && !writes[0]);
    setup();prime_prior();snapshot.headers[13]=snapshot.headers[15];
    if(!setjmp(terminal)){lab_capture_realtek_bme(&view,&snapshot);assert(0);}
    expect_direct(9);assert(!reads[0] && !writes[0]);
    setup();prime_prior();lab_retained_realtek_state[0].transmit_after^=1;
    if(!setjmp(terminal)){lab_capture_realtek_bme(&view,&snapshot);assert(0);}
    expect_direct(10);assert(!reads[0] && !writes[0]);
    puts("PASS native Realtek BME: both ports, actual state/helper/windows, all 366 BME read failures, writes, arm rejection, exact output and disarm");
}
