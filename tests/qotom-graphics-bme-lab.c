#include <assert.h>
#include <setjmp.h>
#include <stdio.h>
#include <string.h>
#include "qotom-graphics-state-arm.h"
#define LEANOS_QOTOM_GRAPHICS_BME 1
static uint64_t root[512],pdpt[512],pd[512],pt[4096];
static struct lab_ecam_root_view view={root,pdpt,pd,pt,0x100000,0x101000,0x102000,0x103000};
static const struct lab_ecam_firmware_table *lab_ecam_tables=lab_ecam_expected_tables;
static const uint32_t lab_ecam_table_count=LAB_ECAM_FIRMWARE_TABLE_COUNT;
#define lab_ecam_aperture ((void *)0x200000)
static struct { unsigned armed; } lab_ecam_window;
static int lab_ecam_reader;
static struct pci_enumeration_snapshot snapshot;
static uint32_t cfg[16],reads,mmio_reads,writes,failed_read,failed_write;
static char output[4096];static size_t used;static jmp_buf terminal;
static int lab_ecam_native_controls(void *p,struct lab_ecam_controls *out) {
    (void)p;*out=(struct lab_ecam_controls){0x0007040600070406,0x80010001,0x100000,0x20,0xd00,2};return 1;
}
static void lab_ecam_native_invalidate(void *p,uint64_t address){(void)p;assert(address==0x200000);}
static int lab_bme_store16(void *p,uint64_t address,uint16_t value) {
    (void)p;assert(address==0x200004 && value==3);
    assert((pt[512]&~UINT64_C(0x60))==UINT64_C(0x80000000e001001b));
    assert(reads==125 && writes++==0);
    if(failed_write)return 0;
    cfg[1]=(cfg[1]&UINT32_C(0xffff0000))|3;return 1;
}
static int lab_ecam_native_load32(void *p,uint64_t address,uint32_t *value) {
    (void)p;uint64_t mapped=pt[512]&UINT64_C(0x000ffffffffff000);
    assert(mapped==0xd0002000 || mapped==0xd0012000 || mapped==0xd0022000);
    assert(address>=0x200000 && address<0x201000);unsigned offset=address-0x200000;
    assert(offset==0x30 || offset==0x34 || offset==0x38 || offset==0x3c || offset==0x9c);
    ++reads;++mmio_reads;if(reads==failed_read)return 0;
    *value=offset==0x9c?0x200:0;pt[512]|=0x20;return 1;
}
static int qotom_ecam_read(void *p,uint8_t bus,uint8_t device,uint8_t fn,uint8_t offset,uint32_t *out) {
    assert(p==&lab_ecam_reader && lab_ecam_window.armed && !(offset&3));
    assert(pt[512]==UINT64_C(0x8000000000200003));
    assert(!bus && device==2 && !fn);++reads;if(reads==failed_read)return 0;
    *out=cfg[offset/4];return 1;
}
static void serial_puts(const char *s);
static void serial_u64(uint64_t n){char b[32];snprintf(b,sizeof b,"%llu",(unsigned long long)n);serial_puts(b);}
static void serial_putc(char c){char b[2]={c,0};serial_puts(b);}
static __attribute__((noreturn)) void pre_admission_fail(const char *s) {
    assert((!strcmp(s,"qotom-graphics-state") || !strcmp(s,"qotom-graphics-bme") ||
        !strcmp(s,"qotom-platform-pending")) && !lab_ecam_window.armed);
    longjmp(terminal,1);
}
#include "../hardware/lab/qotom-graphics-state.c.inc"
static void serial_puts(const char *s) {
    assert(!lab_ecam_window.armed && !lab_graphics_state_reader.armed &&
        !lab_graphics_bme_writer.armed);
    assert(pt[512]==UINT64_C(0x8000000000200003));
    size_t n=strlen(s);assert(used+n<sizeof output);memcpy(output+used,s,n+1);used+=n;
}
static void setup(void) {
    memset(&snapshot,0,sizeof snapshot);snapshot.count=16;reads=mmio_reads=writes=0;
    failed_read=failed_write=used=0;output[0]=0;lab_ecam_window.armed=0;
    root[0]=view.pdpt_address|7;pdpt[0]=view.pd_address|7;
    for(unsigned i=0;i<8;++i)pd[i]=(view.pt_address+i*4096)|7;
    for(unsigned i=0;i<4096;++i)pt[i]=((uint64_t)i*4096)|UINT64_C(0x8000000000000003);
    struct pci_enumeration_header *h=&snapshot.headers[1];h->device=2;
    const uint32_t words[16]={0x0f318086,0x00100007,0x0300000e,0,
        0xd0000000,0,0xc0000008,0,0x0000f081,0,0,0x0f318086,0,0xd0,0,0x110};
    memcpy(h->words,words,sizeof words);memcpy(cfg,words,sizeof words);
}
static void expected(char *out,unsigned status,unsigned attempted,unsigned before,unsigned after) {
    size_t n=(size_t)snprintf(out,4096,
        "LEANOS-LAB/1 GRAPHICS-STATE profile=qotom-valleyview-rings-v1 index=1 status=0 width=30 words=");
    for(unsigned i=0;i<30;++i)n+=(size_t)snprintf(out+n,4096-n,"%s%u",i?",":"",i%5==4?512:0);
    (void)snprintf(out+n,4096-n,
        "\nLEANOS-LAB/1 GRAPHICS-BME profile=qotom-valleyview-bme-v1 index=1 status=%u attempted=%u before=%u after=%u\n",
        status,attempted,before,after);
}
static void assert_disarmed(void) {
    assert(!lab_ecam_window.armed && !lab_graphics_state_reader.armed &&
        !lab_graphics_bme_writer.armed && pt[512]==UINT64_C(0x8000000000200003));
}
int main(void) {
    (void)pci_enumerate_segment;char wanted[4096];
    setup();if(!setjmp(terminal)){lab_capture_graphics_state(&view,&snapshot);assert(0);}
    expected(wanted,0,1,7,3);assert(!strcmp(output,wanted));assert_disarmed();
    assert(reads==189 && mmio_reads==90 && writes==1 && (cfg[1]&0xffff)==3);
    for(volatile unsigned n=1;n<=127;++n) {
        setup();failed_read=62+n;
        if(!setjmp(terminal)){lab_capture_graphics_state(&view,&snapshot);assert(0);}
        unsigned status=n<=62?QOTOM_GRAPHICS_BME_REFRESH:n==63?QOTOM_GRAPHICS_BME_COMMAND:
            n==64?QOTOM_GRAPHICS_BME_READBACK:QOTOM_GRAPHICS_BME_FINAL;
        expected(wanted,status,n>63,n>63?7:0,n>64?3:0);
        assert(!strcmp(output,wanted));assert_disarmed();
        assert(reads==62+n && writes==(n>63));
    }
    setup();failed_write=1;
    if(!setjmp(terminal)){lab_capture_graphics_state(&view,&snapshot);assert(0);}
    expected(wanted,QOTOM_GRAPHICS_BME_WRITE,1,7,0);
    assert(!strcmp(output,wanted) && reads==125 && writes==1);assert_disarmed();
    setup();lab_retained_graphics_state=(struct qotom_graphics_state){0};snapshot.count=15;
    if(!setjmp(terminal)){lab_capture_graphics_bme(&view,&snapshot);assert(0);}
    snprintf(wanted,sizeof wanted,
        "LEANOS-LAB/1 GRAPHICS-BME profile=qotom-valleyview-bme-v1 index=1 status=9 attempted=0 before=0 after=0\n");
    assert(!strcmp(output,wanted) && !reads && !writes);assert_disarmed();
    puts("PASS native graphics BME: actual observer/helper/windows, all 127 read failures, write, arm rejection and disarm");
}
