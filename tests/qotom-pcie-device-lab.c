#include <assert.h>
#include <setjmp.h>
#include <stdio.h>
#include <string.h>
#include "../boot/pci-capabilities.h"
#define LEANOS_QOTOM_PCI_DIAGNOSTIC 1
#define LEANOS_QOTOM_PCIE_DEVICE_OBSERVATION 1
static struct { int armed; } lab_ecam_window;
static int lab_ecam_reader;
static uint32_t config[16][64];
static unsigned fail_read;
static unsigned reads;
static int failed_offset = -1;
static char output[8192];
static size_t used;
static jmp_buf terminal;
static const char *reason;
static int qotom_ecam_read(void *ctx, uint8_t bus, uint8_t device,
        uint8_t function, uint8_t offset, uint32_t *out) {
    assert(ctx == &lab_ecam_reader && lab_ecam_window.armed);
    assert(bus == 0 && device < 16 && function == 0 && !(offset & 3));
    ++reads;
    if (offset == failed_offset || reads == fail_read) return 0;
    *out = config[device][offset / 4]; return 1;
}
static void serial_puts(const char *s) {
    assert(!lab_ecam_window.armed);
    size_t n = strlen(s); assert(used + n < sizeof output);
    memcpy(output + used, s, n + 1); used += n;
}
static void serial_u64(uint64_t n) {
    char s[32]; snprintf(s, sizeof s, "%llu", (unsigned long long)n); serial_puts(s);
}
static void serial_putc(char c) { char s[2] = {c, 0}; serial_puts(s); }
static void pre_admission_fail(const char *s) {
    assert(!lab_ecam_window.armed); reason = s; longjmp(terminal, 1);
}
#include "../hardware/lab/qotom-pci-capabilities.c.inc"
#include "../hardware/lab/qotom-pcie-device.c.inc"
static struct pci_enumeration_snapshot snapshot;
static void setup(unsigned count) {
    memset(config,0,sizeof config); memset(&snapshot,0,sizeof snapshot);
    snapshot.count=count; used=reads=fail_read=0; failed_offset=-1;output[0]=0;
    for(unsigned i=0;i<count;++i) {
        snapshot.headers[i].device=i;
        config[i][0]=0x12348086;config[i][1]=0x100000;config[i][13]=0x70;
        config[i][28]=(i&1)?1:0x00020010;
        config[i][29]=0x10000000;config[i][30]=0x00200000;
        memcpy(snapshot.headers[i].words,config[i],sizeof snapshot.headers[i].words);
    }
    lab_capture_pci_capabilities(&snapshot);
    used=reads=0;output[0]=0;
}
int main(void) {
    assert(pci_enumerate_segment(NULL,NULL,NULL).status==PCI_ENUMERATION_INVALID_ARGUMENT);
    setup(16);lab_capture_pcie_device(&snapshot);
    assert(!lab_ecam_window.armed && reads==8*12+8*5);
    const char *cursor=output;
    for(unsigned i=0;i<16;++i) {
        char line[200];
        snprintf(line,sizeof line,"LEANOS-LAB/1 PCIE-DEVICE profile=qotom-pcie-device-v1 index=%u status=%u offset=%u capability=%u control-status=%u\n",
            i,i&1,(i&1)?0:112,(i&1)?0:0x10000000,(i&1)?0:0x00200000);
        size_t n=strlen(line);assert(!strncmp(cursor,line,n));cursor+=n;
    }
    assert(!*cursor);
    for(unsigned n=1;n<=12;++n) {
        setup(1);fail_read=n;
        if(!setjmp(terminal)) {lab_capture_pcie_device(&snapshot);assert(0);}
        assert(!strcmp(reason,"qotom-pcie-device") && !lab_ecam_window.armed && reads==n);
        unsigned status=n<=5?3:n<=7?6:8;
        char line[200];snprintf(line,sizeof line,"index=0 status=%u offset=0 capability=0 control-status=0\n",status);
        assert(strstr(output,line));
    }
    setup(1);config[0][28]^=0x10000;
    if(!setjmp(terminal)) {lab_capture_pcie_device(&snapshot);assert(0);}
    assert(strstr(output,"status=4 offset=0 capability=0 control-status=0\n"));
    puts("PASS PCIe native emission: mixed 16 functions, complete records, all failures disarmed");
}
