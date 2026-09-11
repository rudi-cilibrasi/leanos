#include <assert.h>
#include <stdio.h>
#include "pci-enumeration.h"
#include "pci-config-read.h"

static uint32_t expected_address, response;
static unsigned calls, scan;

uint32_t leanos_pci_config_read_dword(uint32_t address) {
    ++calls;
    if (!scan) {
        assert(address == expected_address);
        return response;
    }
    /* A function at the last possible BDF, despite absent function zero. */
    unsigned bus = (address >> 16) & 255u;
    unsigned device = (address >> 11) & 31u;
    unsigned function = (address >> 8) & 7u;
    unsigned offset = address & 255u;
    assert((address & UINT32_C(0xff000003)) == UINT32_C(0x80000000));
    if (bus != 255 || device != 31 || function != 7) {
        assert(offset == 0);
        return UINT32_MAX;
    }
    return offset ? offset : UINT32_C(0x12348086);
}

int main(void) {
    uint32_t value;
    /* Exhaust all 4,194,304 legal address tuples. Independent arithmetic
     * oracle detects a missing, shifted or overlapping bus/BDF field. */
    for (unsigned bus = 0; bus < 256; ++bus)
        for (unsigned device = 0; device < 32; ++device)
            for (unsigned function = 0; function < 8; ++function)
                for (unsigned offset = 0; offset < 256; offset += 4) {
                    expected_address = UINT32_C(0x80000000) + bus * 65536u +
                        device * 2048u + function * 256u + offset;
                    response = ~expected_address;
                    assert(pci_config_read(0, bus, device, function, offset, &value));
                    assert(value == response);
                }
    assert(calls == 4194304u);
    unsigned before = calls;
    value = 42;
    for (unsigned device = 32; device < 256; ++device)
        assert(!pci_config_read(0, 0, device, 0, 0, &value));
    for (unsigned function = 8; function < 256; ++function)
        assert(!pci_config_read(0, 0, 0, function, 0, &value));
    for (unsigned offset = 0; offset < 256; ++offset)
        if (offset & 3u) assert(!pci_config_read(0, 0, 0, 0, offset, &value));
    assert(!pci_config_read(0, 0, 0, 0, 0, 0));
    assert(value == 42 && calls == before);
    scan = 1;
    calls = 0;
    struct pci_enumeration_snapshot snapshot;
    struct pci_enumeration_result result = pci_enumerate_segment(pci_config_read, 0, &snapshot);
    assert(result.status == PCI_ENUMERATION_OK && snapshot.count == 1);
    assert(calls == 65536u + 15u);
    assert(snapshot.headers[0].bus == 255 && snapshot.headers[0].device == 31 &&
           snapshot.headers[0].function == 7);
    assert(snapshot.headers[0].words[0] == UINT32_C(0x12348086));
    for (unsigned i = 1; i < 16; ++i) assert(snapshot.headers[0].words[i] == i * 4);
    puts("PCI configuration adapter: exhaustive addresses, rejection and downstream collection PASS");
}
