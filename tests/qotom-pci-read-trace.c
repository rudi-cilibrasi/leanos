#include <assert.h>
#include <inttypes.h>
#include <stdio.h>
#include <string.h>
#include "pci-enumeration.h"
#include "pci-config-read.h"

static uint32_t last_address, mismatch_address;
static unsigned data_reads, selector_reads;
static char serial_output[1024];
static size_t serial_length;

uint32_t leanos_pci_config_read_dword(uint32_t address) {
    last_address = address;
    ++data_reads;
    unsigned bus = (address >> 16) & 255u;
    unsigned device = (address >> 11) & 31u;
    unsigned offset = address & 255u;
    /* Sixteen legitimate functions, followed by a suspect seventeenth
       identity only when selector interference is injected there. */
    if (bus == 0 && device < 2)
        return offset ? offset : UINT32_C(0x12348086);
    if (address == mismatch_address) return UINT32_C(0xdead8086);
    return UINT32_MAX;
}

static uint32_t in32(uint16_t port) {
    assert(port == 0xcf8);
    ++selector_reads;
    return last_address == mismatch_address ? UINT32_C(0x8000e86c) : last_address;
}

static void serial_puts(const char *text) {
    size_t size = strlen(text);
    assert(serial_length + size < sizeof(serial_output));
    memcpy(serial_output + serial_length, text, size + 1);
    serial_length += size;
}
static void serial_u64(uint64_t value) {
    char text[32];
    snprintf(text, sizeof(text), "%" PRIu64, value);
    serial_puts(text);
}
static void serial_putc(char value) {
    char text[2] = {value, 0};
    serial_puts(text);
}

#define LEANOS_QOTOM_PCI_DIAGNOSTIC 1
#include "../hardware/lab/qotom-pci-read-trace.c.inc"

static void reset(uint32_t mismatch) {
    mismatch_address = mismatch;
    data_reads = selector_reads = 0;
    memset(&lab_pci_trace, 0, sizeof(lab_pci_trace));
    serial_length = 0;
    serial_output[0] = 0;
}

int main(void) {
    struct pci_enumeration_snapshot snapshot;
    reset(0);
    struct pci_enumeration_result result = pci_enumerate_segment(lab_pci_read, 0, &snapshot);
    assert(result.status == PCI_ENUMERATION_OK && snapshot.count == 16);
    assert(data_reads == 65536 + 16*15 && selector_reads == data_reads);
    assert(lab_pci_trace.mismatches == 0);

    /* Mismatch on the apparent seventeenth identity must be a read failure,
       not capacity overflow or a partially published inventory. */
    reset(UINT32_C(0x80001000));
    snapshot.count = 99;
    result = pci_enumerate_segment(lab_pci_read, 0, &snapshot);
    assert(result.status == PCI_ENUMERATION_READ_FAILED && snapshot.count == 0);
    assert(result.bus == 0 && result.device == 2 && result.function == 0 && result.offset == 0);
    assert(data_reads == 16*16 + 1 && selector_reads == data_reads);
    assert(lab_pci_trace.reads == data_reads && lab_pci_trace.mismatches == 1);
    assert(lab_pci_trace.first_requested == mismatch_address);
    assert(lab_pci_trace.first_observed == UINT32_C(0x8000e86c));
    assert(lab_pci_trace.first_value == UINT32_C(0xdead8086));
    assert(lab_pci_trace.requested == lab_pci_trace.first_requested);
    assert(lab_pci_trace.observed == lab_pci_trace.first_observed);
    assert(lab_pci_trace.value == lab_pci_trace.first_value);
    lab_report_pci_read();
    assert(strstr(serial_output, "mismatches=1") != 0);
    assert(strstr(serial_output, "first_requested=2147487744") != 0);
    assert(strstr(serial_output, "first_observed=2147543148") != 0);
    assert(strstr(serial_output, "first_value=3735912582") != 0);

    /* A mismatch while reading a present function's header stops immediately. */
    reset(UINT32_C(0x80000008));
    result = pci_enumerate_segment(lab_pci_read, 0, &snapshot);
    assert(result.status == PCI_ENUMERATION_READ_FAILED && snapshot.count == 0);
    assert(result.bus == 0 && result.device == 0 && result.function == 0 && result.offset == 8);
    assert(data_reads == 3 && selector_reads == 3 && lab_pci_trace.first_value == 8);

    /* Adapter-level rejection performs no hardware or trace read. */
    reset(0);
    uint32_t value = 42;
    assert(!lab_pci_read(0, 0, 32, 0, 0, &value));
    assert(value == 42 && data_reads == 0 && selector_reads == 0 && lab_pci_trace.reads == 0);
    puts("Qotom PCI trace: detected selector mismatch rejects without retry or publication PASS");
    return 0;
}
