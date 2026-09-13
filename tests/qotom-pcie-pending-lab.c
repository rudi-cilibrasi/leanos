#include <assert.h>
#include <setjmp.h>
#include <stdio.h>
#include <string.h>
#include "qotom-ecam-arm.h"
#include "qotom-pcie-pending.h"

static uint64_t root[512],pdpt[512],pd[512],pt[4096];
static struct lab_ecam_root_view view={root,pdpt,pd,pt,0x100000,0x101000,0x102000,0x103000};
static const struct lab_ecam_firmware_table *lab_ecam_tables=lab_ecam_expected_tables;
static const uint32_t lab_ecam_table_count=LAB_ECAM_FIRMWARE_TABLE_COUNT;
#define lab_ecam_aperture ((void *)0x200000)
static struct pci_enumeration_snapshot snapshot;
static struct pci_capability_snapshot lab_retained_pci_caps[16];
static struct pci_express_observation lab_retained_pcie_device[16];
static struct qotom_rootport_bme_result lab_retained_rootport_bme[4];
static struct qotom_realtek_state lab_retained_realtek_state[2];
static struct qotom_realtek_bme_result lab_retained_realtek_bme[2];
static uint32_t config[16][64],reads,fail_read,pm_value,pm_reads,pending_index=UINT32_MAX;
static char output[4096];static size_t used;static jmp_buf terminal;static const char *reason;
static int lab_ecam_native_controls(void *p,struct lab_ecam_controls *out) {
    (void)p;*out=(struct lab_ecam_controls){0x0007040600070406,0x80010001,0x100000,0x20,0xd00,2};return 1;
}
static void lab_ecam_native_invalidate(void *p,uint64_t address){(void)p;assert(address==0x200000);}
static int lab_ecam_native_load32(void *p,uint64_t address,uint32_t *value){
    (void)p;(void)address;*value=0;return 1;
}
static __attribute__((noreturn)) void lab_ecam_native_fault(void *p){(void)p;assert(0);}
static struct lab_ecam_window lab_ecam_window={.controls=lab_ecam_native_controls,
    .invalidate=lab_ecam_native_invalidate,.load32=lab_ecam_native_load32,.fault=lab_ecam_native_fault};
static int lab_ecam_reader;
static unsigned index_for(uint8_t bus,uint8_t device,uint8_t function) {
    if(!bus && device==28 && function<4)return 6+function;
    if(!bus && device==31 && !function)return 11;
    if((bus==1 || bus==3) && !device && !function)return bus==1?13:15;
    assert(0);return 0;
}
static int qotom_ecam_read(void *p,uint8_t bus,uint8_t device,uint8_t function,
        uint8_t offset,uint32_t *value) {
    assert(p==&lab_ecam_reader && lab_ecam_window.armed && !(offset&3));
    unsigned index=index_for(bus,device,function);++reads;
    if(reads==fail_read)return 0;
    *value=config[index][offset/4];
    if(index==pending_index && offset==lab_retained_pcie_device[index].offset+8)
        *value|=QOTOM_PCIE_PENDING_BIT;
    return 1;
}
static uint32_t in32(uint16_t port) {
    assert(port==0x408);++pm_reads;uint32_t result=pm_value;pm_value=(pm_value+40000)&0xffffff;return result;
}
static void serial_puts(const char *s);
static void serial_u64(uint64_t n){char b[32];snprintf(b,sizeof b,"%llu",(unsigned long long)n);serial_puts(b);}
static void serial_putc(char c){char b[2]={c,0};serial_puts(b);}
static __attribute__((noreturn)) void pre_admission_fail(const char *s) {
    assert(!lab_ecam_window.armed);reason=s;longjmp(terminal,1);
}
#include "../hardware/lab/qotom-pcie-pending.c.inc"
static void serial_puts(const char *s) {
    assert(!lab_ecam_window.armed && !lab_pcie_pending_timer.armed);
    size_t n=strlen(s);assert(used+n<sizeof output);memcpy(output+used,s,n+1);used+=n;
}

static void retain_caps(unsigned index,const unsigned *offsets,const uint32_t *raws,unsigned count) {
    lab_retained_pci_caps[index].count=count;
    for(unsigned i=0;i<count;++i) {
        lab_retained_pci_caps[index].headers[i]=(struct pci_capability_header){offsets[i],raws[i]};
        config[index][offsets[i]/4]=raws[i];
    }
}
static void setup(void) {
    memset(&snapshot,0,sizeof snapshot);snapshot.count=16;memset(config,0,sizeof config);
    memset(lab_retained_pci_caps,0,sizeof lab_retained_pci_caps);
    used=reads=fail_read=pm_value=pm_reads=0;output[0]=0;pending_index=UINT32_MAX;reason=NULL;
    root[0]=view.pdpt_address|7;pdpt[0]=view.pd_address|7;
    for(unsigned i=0;i<8;++i)pd[i]=(view.pt_address+i*4096)|7;
    for(unsigned i=0;i<4096;++i)pt[i]=((uint64_t)i*4096)|UINT64_C(0x8000000000000003);
    config[11][0]=UINT32_C(0x0f1c8086);config[11][1]=7;config[11][0x40/4]=UINT32_C(0x403);
    const unsigned poff[]={64,128,144,160};
    const uint32_t praw[]={21135376,36869,40973,3355639809u};
    for(unsigned fn=0;fn<4;++fn) {
        unsigned index=6+fn;struct pci_enumeration_header *h=&snapshot.headers[index];
        h->device=28;h->function=fn;h->words[0]=UINT32_C(0x0f488086)+fn*UINT32_C(0x20000);
        h->words[1]=UINT32_C(0x00100007);h->words[2]=UINT32_C(0x0604000e);
        h->words[3]=UINT32_C(0x00810000);h->words[13]=0x40;
        memcpy(config[index],h->words,sizeof h->words);config[index][1]=UINT32_C(0x00100003);
        retain_caps(index,poff,praw,4);config[index][0x44/4]=UINT32_C(0x8000);
        config[index][0x48/4]=(fn==3?UINT32_C(0x10):UINT32_C(0x11))<<16;
        lab_retained_pcie_device[index]=(struct pci_express_observation){PCI_EXPRESS_OK,0x40,
            UINT32_C(0x8000),config[index][0x48/4]};
        lab_retained_rootport_bme[fn]=(struct qotom_rootport_bme_result){1,7,3};
    }
    const unsigned eoff[]={64,80,112,176,208};
    const uint32_t eraw[]={4290990081u,8417285,33730576,249873,3};
    for(unsigned port=0;port<2;++port) {
        unsigned index=13+2*port,bus=1+2*port;uint32_t bar=(uint32_t)qotom_realtek_bar(bus);
        struct pci_enumeration_header *h=&snapshot.headers[index];h->bus=bus;
        uint32_t words[16]={UINT32_C(0x816810ec),UINT32_C(0x00100007),UINT32_C(0x02000007),16,
            bus==1?0xe001u:0xd001u,0,bar|4,0,(bar-0x4000)|12,0,0,UINT32_C(0x012310ec),0,64,0,261};
        memcpy(h->words,words,sizeof words);memcpy(config[index],words,sizeof words);
        config[index][1]=UINT32_C(0x00100003);retain_caps(index,eoff,eraw,5);
        config[index][0x74/4]=UINT32_C(0x05908cc0);config[index][0x78/4]=UINT32_C(0x00192000);
        lab_retained_pcie_device[index]=(struct pci_express_observation){PCI_EXPRESS_OK,0x70,
            UINT32_C(0x05908cc0),UINT32_C(0x00192000)};
        lab_retained_realtek_state[port]=(struct qotom_realtek_state){
            UINT32_C(0x2f900d00),0,0,UINT32_C(0x2ff0e),0,UINT32_C(0x2f900d00)};
        lab_retained_realtek_bme[port]=(struct qotom_realtek_bme_result){1,7,3};
    }
}
static void expect_success(void) {
    char expected[4096];size_t n=0;
    for(unsigned fn=0;fn<4;++fn)n+=(size_t)snprintf(expected+n,sizeof expected-n,
        "LEANOS-LAB/1 PCIE-PENDING profile=qotom-pcie-pending-v1 index=%u status=0 polls=2 device-status=%u\n",
        6+fn,fn==3?16:17);
    for(unsigned port=0;port<2;++port)n+=(size_t)snprintf(expected+n,sizeof expected-n,
        "LEANOS-LAB/1 PCIE-PENDING profile=qotom-pcie-pending-v1 index=%u status=0 polls=2 device-status=25\n",
        13+2*port);
    assert(n<sizeof expected && !strcmp(output,expected));
    assert(!lab_ecam_window.armed && !lab_pcie_pending_timer.armed);
}
int main(void) {
    (void)pci_enumerate_segment;
    setup();lab_capture_pcie_pending(&view,&snapshot);expect_success();
    assert(pm_reads==12);
    setup();snapshot.count=15;
    if(!setjmp(terminal)){lab_capture_pcie_pending(&view,&snapshot);assert(0);}
    assert(!strcmp(reason,"qotom-pcie-pending") && !used);
    setup();root[0]=0;
    if(!setjmp(terminal)){lab_capture_pcie_pending(&view,&snapshot);assert(0);}
    assert(strstr(output,"index=6 status=8 polls=0 device-status=0\n"));
    setup();config[11][0x40/4]^=1;
    if(!setjmp(terminal)){lab_capture_pcie_pending(&view,&snapshot);assert(0);}
    assert(strstr(output,"index=6 status=9 polls=0 device-status=0\n"));
    setup();pending_index=6;
    if(!setjmp(terminal)){lab_capture_pcie_pending(&view,&snapshot);assert(0);}
    assert(strstr(output,"index=6 status=7 polls=100 device-status=49\n"));
    setup();fail_read=4;
    if(!setjmp(terminal)){lab_capture_pcie_pending(&view,&snapshot);assert(0);}
    assert(strstr(output,"index=6 status=3 polls=0 device-status=0\n"));
    setup();lab_retained_realtek_state[0].command_after=1;
    if(!setjmp(terminal)){lab_capture_pcie_pending(&view,&snapshot);assert(0);}
    assert(strstr(output,"index=13 status=8 polls=0 device-status=0\n"));
    puts("PASS native PCIe pending: six exact functions, two-clear delay, local arms, timeout and disarm");
}
