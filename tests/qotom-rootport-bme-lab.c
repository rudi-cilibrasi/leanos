#include <assert.h>
#include <setjmp.h>
#include <stdio.h>
#include <string.h>
#include "qotom-rootport-bme-arm.h"
static uint64_t root[512],pdpt[512],pd[512],pt[4096];
static struct lab_ecam_root_view view={root,pdpt,pd,pt,0x100000,0x101000,0x102000,0x103000};
static const struct lab_ecam_firmware_table *lab_ecam_tables=lab_ecam_expected_tables;
static const uint32_t lab_ecam_table_count=LAB_ECAM_FIRMWARE_TABLE_COUNT;
#define lab_ecam_aperture ((void *)0x200000)
static struct { unsigned armed; } lab_ecam_window;
static int lab_ecam_reader;
static struct pci_capability_snapshot lab_retained_pci_caps[16];
static struct pci_express_observation lab_retained_pcie_device[16];
static struct pci_enumeration_snapshot snapshot;
static uint32_t cfg[4][64];
static unsigned reads[4],writes[4],failed_fn,failed_read,failed_write;
static char output[2048];static size_t used;static jmp_buf terminal;
static int lab_ecam_native_controls(void *p,struct lab_ecam_controls *out){
    (void)p;*out=(struct lab_ecam_controls){0x0007040600070406,0x80010001,0x100000,0x20,0xd00,2};return 1;
}
static void lab_ecam_native_invalidate(void *p,uint64_t a){(void)p;assert(a==0x200000);}
static int lab_bme_store16(void *p,uint64_t a,uint16_t value){
    (void)p;assert(a==0x200004 && value==3);
    uint64_t mapped=pt[512]&~UINT64_C(0x60);
    unsigned fn=(unsigned)((mapped-UINT64_C(0x80000000e00e001b))/4096);
    assert(fn<4 && mapped==UINT64_C(0x80000000e00e001b)+fn*4096);
    assert(reads[fn]==35 && writes[fn]++==0);
    if(failed_write && fn==failed_fn)return 0;
    cfg[fn][1]=(cfg[fn][1]&0xffff0000)|3;return 1;
}
static int qotom_ecam_read(void *p,uint8_t b,uint8_t d,uint8_t fn,uint8_t off,uint32_t *out){
    assert(p==&lab_ecam_reader && lab_ecam_window.armed && b==0 && d==28 && fn<4 && !(off&3));
    assert(pt[512]==UINT64_C(0x8000000000200003));++reads[fn];
    if(fn==failed_fn && reads[fn]==failed_read)return 0;
    *out=cfg[fn][off/4];return 1;
}
static void serial_puts(const char *s);
static void serial_u64(uint64_t n){char b[32];snprintf(b,sizeof b,"%llu",(unsigned long long)n);serial_puts(b);}
static void serial_putc(char c){char b[2]={c,0};serial_puts(b);}
static __attribute__((noreturn)) void pre_admission_fail(const char *s){
    assert(!strcmp(s,"qotom-rootport-bme") && !lab_ecam_window.armed);longjmp(terminal,1);
}
#include "../hardware/lab/qotom-rootport-bme.c.inc"
static void serial_puts(const char *s){
    assert(!lab_ecam_window.armed && !lab_rootport_bme_writer.armed);
    size_t n=strlen(s);assert(used+n<sizeof output);memcpy(output+used,s,n+1);used+=n;
}
static const uint32_t captured[4][16]={
{0xf488086,0x100007,0x604000e,0x810010,0x0,0x0,0x10100,0x2000e0e0,0xd080d080,0x1fff1,0x0,0x0,0x0,0x40,0x0,0x100105},
{0xf4a8086,0x100007,0x604000e,0x810010,0x0,0x0,0x20200,0x200000f0,0xd070d070,0x1fff1,0x0,0x0,0x0,0x40,0x0,0x100205},
{0xf4c8086,0x100007,0x604000e,0x810010,0x0,0x0,0x30300,0x2000d0d0,0xd060d060,0x1fff1,0x0,0x0,0x0,0x40,0x0,0x100305},
{0xf4e8086,0x100007,0x604000e,0x810010,0x0,0x0,0x40400,0x200000f0,0xfff0,0x1fff1,0x0,0x0,0x0,0x40,0x0,0x100405}
};
static void setup(void){
    memset(&snapshot,0,sizeof snapshot);snapshot.count=16;memset(cfg,0,sizeof cfg);
    memset(reads,0,sizeof reads);memset(writes,0,sizeof writes);used=0;output[0]=0;
    failed_fn=4;failed_read=failed_write=0;lab_ecam_window.armed=0;
    root[0]=view.pdpt_address|7;pdpt[0]=view.pd_address|7;
    for(unsigned i=0;i<8;++i)pd[i]=(view.pt_address+i*4096)|7;
    for(unsigned i=0;i<4096;++i)pt[i]=((uint64_t)i*4096)|UINT64_C(0x8000000000000003);
    for(unsigned fn=0;fn<4;++fn){
        snapshot.headers[6+fn].device=28;snapshot.headers[6+fn].function=fn;
        memcpy(snapshot.headers[6+fn].words,captured[fn],sizeof captured[fn]);
        memcpy(cfg[fn],captured[fn],sizeof captured[fn]);
        struct pci_capability_snapshot *caps=&lab_retained_pci_caps[6+fn];caps->count=4;
        const unsigned offsets[]={64,128,144,160};const uint32_t raws[]={21135376,36869,40973,3355639809u};
        for(unsigned i=0;i<4;++i){caps->headers[i]=(struct pci_capability_header){offsets[i],raws[i]};cfg[fn][offsets[i]/4]=raws[i];}
        cfg[fn][17]=0x8000;cfg[fn][18]=0x100000;
        lab_retained_pcie_device[6+fn]=(struct pci_express_observation){PCI_EXPRESS_OK,64,0x8000,0x100000};
    }
}
static void expect(unsigned last,unsigned status,unsigned attempted,unsigned before,unsigned after){
    char expected[2048];size_t n=0;
    for(unsigned fn=0;fn<=last;++fn)n+=(size_t)snprintf(expected+n,sizeof expected-n,
        "LEANOS-LAB/1 ROOTPORT-BME profile=qotom-rootport-bme-v1 index=%u status=%u attempted=%u before=%u after=%u\n",
        6+fn,fn==last?status:0,fn==last?attempted:1,fn==last?before:7,fn==last?after:3);
    assert(!strcmp(output,expected));
    assert(!lab_ecam_window.armed && !lab_rootport_bme_writer.armed);
    for(unsigned fn=last+1;fn<4;++fn)assert(!reads[fn] && !writes[fn]);
}
int main(void){
    assert(pci_enumerate_segment(NULL,NULL,NULL).status==PCI_ENUMERATION_INVALID_ARGUMENT);
    setup();lab_capture_rootport_bme(&view,&snapshot);expect(3,0,1,7,3);
    for(volatile unsigned fn=0;fn<4;++fn)assert(reads[fn]==71 && writes[fn]==1);
    for(volatile unsigned fn=0;fn<4;++fn)for(volatile unsigned n=1;n<=71;++n){
        setup();failed_fn=fn;failed_read=n;
        if(!setjmp(terminal)){lab_capture_rootport_bme(&view,&snapshot);assert(0);}
        unsigned status=n<=34?3:n==35?4:n==36?6:7;
        expect(fn,status,n>35,n>35?7:0,n>36?3:0);assert(reads[fn]==n);
    }
    for(volatile unsigned fn=0;fn<4;++fn){
        setup();failed_fn=fn;failed_write=1;
        if(!setjmp(terminal)){lab_capture_rootport_bme(&view,&snapshot);assert(0);}
        expect(fn,5,1,7,0);
        setup();lab_retained_pcie_device[6+fn].device_control_status|=0x200000;
        if(!setjmp(terminal)){lab_capture_rootport_bme(&view,&snapshot);assert(0);}
        expect(fn,8,0,0,0);assert(!reads[fn] && !writes[fn]);
    }
    for(volatile unsigned fn=0;fn<4;++fn){
        setup();unsigned other=(fn+1)%4;
        snapshot.headers[6+fn]=snapshot.headers[6+other];
        if(!setjmp(terminal)){lab_capture_rootport_bme(&view,&snapshot);assert(0);}
        expect(fn,8,0,0,0);assert(!reads[fn] && !writes[fn]);
    }
    setup();snapshot.count=15;
    if(!setjmp(terminal)){lab_capture_rootport_bme(&view,&snapshot);assert(0);}
    expect(0,8,0,0,0);assert(!reads[0]);
    puts("Root-port native: actual arm/helper/window, four ordered results, every read failure, first-failure stop and disarm PASS");
}
