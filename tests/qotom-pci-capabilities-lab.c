#include <assert.h>
#include <setjmp.h>
#include <stdio.h>
#include <string.h>
#include "../boot/pci-capabilities.h"
#define LEANOS_QOTOM_PCI_DIAGNOSTIC 1
static struct { int armed; } lab_ecam_window;
static int lab_ecam_reader;
static uint32_t config[64];
static unsigned reads;
static int failed_offset = -1;
static char output[8192];
static size_t used;
static jmp_buf terminal;
static const char *reason;
static int qotom_ecam_read(void *ctx, uint8_t bus, uint8_t device,
        uint8_t function, uint8_t offset, uint32_t *out) {
    assert(ctx == &lab_ecam_reader && lab_ecam_window.armed);
    assert(bus == 0 && device == 0 && function == 0 && !(offset & 3));
    ++reads;
    if (offset == failed_offset) return 0;
    *out = config[offset / 4]; return 1;
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
int main(void) {
    assert(pci_enumerate_segment(NULL, NULL, NULL).status == PCI_ENUMERATION_INVALID_ARGUMENT);
    struct pci_enumeration_snapshot snapshot = {.count=1};
#ifdef LEANOS_QOTOM_AF_OBSERVATION
    config[0] = 0x12348086; config[1] = 0x100000; config[13] = 88;
    config[22] = 0x03060013; config[23] = 256;
    memcpy(snapshot.headers[0].words, config, sizeof snapshot.headers[0].words);
    lab_capture_pci_capabilities(&snapshot);
    assert(reads == 11 && !lab_ecam_window.armed);
    assert(strstr(output, "PCI-AF profile=af-observation-v1 index=0 status=0 offset=88 raw=256\n"));
    used = reads = 0; output[0] = 0; failed_offset = 92;
    if (!setjmp(terminal)) { lab_capture_pci_capabilities(&snapshot); assert(0); }
    assert(reads == 11 && !strcmp(reason, "qotom-pci-af"));
    assert(strstr(output, "PCI-AF profile=af-observation-v1 index=0 status=5 offset=0 raw=0\n"));
    puts("PASS AF lab emission and window disarm");
#else
    config[0] = 0x12348086; config[1] = 0x100000; config[13] = 0x58;
    config[0x58/4] = 0x4809; config[0x48/4] = 5;
    memcpy(snapshot.headers[0].words, config, sizeof snapshot.headers[0].words);
    lab_capture_pci_capabilities(&snapshot);
    assert(reads == 6 && !lab_ecam_window.armed);
    assert(!strcmp(output,
        "LEANOS-LAB/1 PCI-CAPS profile=conventional-v1 index=0 status=0 offset=0 count=2\n"
        "LEANOS-LAB/1 PCI-CAP index=0 slot=0 offset=88 raw=18441\n"
        "LEANOS-LAB/1 PCI-CAP index=0 slot=1 offset=72 raw=5\n"));
    used = reads = 0; output[0] = 0; failed_offset = 0x48;
    if (!setjmp(terminal)) { lab_capture_pci_capabilities(&snapshot); assert(0); }
    assert(reads == 6 && !strcmp(reason, "qotom-pci-capabilities"));
    assert(!strcmp(output,
        "LEANOS-LAB/1 PCI-CAPS profile=conventional-v1 index=0 status=2 offset=72 count=0\n"));
    puts("PASS native capability emission: bounded read window and failure disarm");
#endif
}
