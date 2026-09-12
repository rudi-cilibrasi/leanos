#include <assert.h>
#include <setjmp.h>
#include <stdio.h>
#include <string.h>
#include "../boot/pci-enumeration.h"
#define LEANOS_QOTOM_PCI_DIAGNOSTIC 1
static struct { int armed; } lab_ecam_window;
static int lab_ecam_reader;
static uint32_t cfg[64];
static unsigned reads,fail_at,used;
static char output[512];
static jmp_buf terminal;
static int qotom_ecam_read(void *ctx,uint8_t b,uint8_t d,uint8_t f,uint8_t off,uint32_t *out) {
    const uint8_t offsets[]={0,4,8,12,0x40,0x48,0,4,8,12};
    assert(ctx==&lab_ecam_reader && lab_ecam_window.armed);
    assert(b==0 && d==26 && f==0 && reads<10 && off==offsets[reads]);
    ++reads;if(reads==fail_at)return 0;*out=cfg[off/4];return 1;
}
static void serial_puts(const char *s) {
    assert(!lab_ecam_window.armed);size_t n=strlen(s);
    assert(used+n<sizeof output);memcpy(output+used,s,n+1);used+=n;
}
static void serial_u64(uint64_t n) { char b[32];snprintf(b,sizeof b,"%llu",(unsigned long long)n);serial_puts(b); }
static void serial_putc(char c) { char b[2]={c,0};serial_puts(b); }
static __attribute__((noreturn)) void pre_admission_fail(const char *s) {
    assert(!lab_ecam_window.armed && !strcmp(s,"qotom-txe-status"));longjmp(terminal,1);
}
#include "../hardware/lab/qotom-txe-status.c.inc"
static struct pci_enumeration_snapshot snapshot;
static void setup(void) {
    memset(&snapshot,0,sizeof snapshot);memset(cfg,0,sizeof cfg);
    snapshot.count=16;cfg[0]=0x0f188086;cfg[1]=0x100106;cfg[2]=0x1080000e;
    snapshot.headers[4].device=26;
    memcpy(snapshot.headers[4].words,cfg,sizeof snapshot.headers[4].words);
    cfg[16]=17;cfg[18]=29;reads=fail_at=used=0;output[0]=0;lab_ecam_window.armed=1;
}
int main(void) {
    assert(pci_enumerate_segment(NULL,NULL,NULL).status==PCI_ENUMERATION_INVALID_ARGUMENT);
    setup();lab_capture_txe_status(&snapshot);
    assert(reads==10 && !lab_ecam_window.armed);
    assert(!strcmp(output,"LEANOS-LAB/1 TXE-STATUS profile=qotom-txe-status-v1 index=4 status=0 firmware0=17 firmware1=29\n"));
    for(unsigned n=1;n<=10;++n) {
        setup();fail_at=n;
        if(!setjmp(terminal)){lab_capture_txe_status(&snapshot);assert(0);}
        char expected[200];snprintf(expected,sizeof expected,"LEANOS-LAB/1 TXE-STATUS profile=qotom-txe-status-v1 index=4 status=%u firmware0=0 firmware1=0\n",(n==5 || n==6)?5:3);
        assert(reads==n && !strcmp(output,expected));
    }
    setup();snapshot.count=15;
    if(!setjmp(terminal)){lab_capture_txe_status(&snapshot);assert(0);}
    assert(reads==0 && strstr(output,"status=7 firmware0=0 firmware1=0\n"));
    setup();snapshot.headers[4].device=27;
    if(!setjmp(terminal)){lab_capture_txe_status(&snapshot);assert(0);}
    assert(reads==0 && strstr(output,"status=2 firmware0=0 firmware1=0\n"));
    puts("TXE native emission and disarm PASS");
}
