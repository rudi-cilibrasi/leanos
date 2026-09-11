#include <assert.h>
#include <stdio.h>
#include "pci-enumeration.h"
#include "qotom-ecam-read.h"
#include "qotom-ecam-allocation.h"

static unsigned calls;
static uint64_t fail_address;
static int access_dword(void *context, uint64_t address, uint32_t *value) {
    assert(context == &calls);
    ++calls;
    assert(address >= UINT64_C(0xe0000000) && address <= UINT64_C(0xeffff0fc));
    assert((address & 3u) == 0 && (address & 4095u) <= 252);
    if (address == fail_address) {
        *value = 123; /* A failed transport must not publish even written data. */
        return 0;
    }
    /* Only the last possible BDF is present; function zero is absent. */
    if (address < UINT64_C(0xeffff000)) *value = UINT32_MAX;
    else *value = (address & 4095u) ? (uint32_t)(address & 4095u) : UINT32_C(0x12348086);
    return 1;
}

int main(void) {
    const struct qotom_ecam_allocation baseline = QOTOM_CAPTURED_ECAM_ALLOCATION;
    uint64_t address = 99;
    unsigned checked = 0;
    for (unsigned bus = 0; bus < 256; ++bus)
        for (unsigned device = 0; device < 32; ++device)
            for (unsigned function = 0; function < 8; ++function)
                for (unsigned offset = 0; offset < 256; offset += 4) {
                    assert(qotom_ecam_dword_address(&baseline, bus, device, function, offset, &address));
                    /* Independent arithmetic oracle, including every BDF. */
                    assert(address == UINT64_C(0xe0000000) + bus*UINT64_C(1048576) +
                           device*UINT64_C(32768) + function*UINT64_C(4096) + offset);
                    assert((address & 4095u) == offset);
                    ++checked;
                }
    assert(checked == 4194304 && address == UINT64_C(0xeffff0fc));
    const struct qotom_ecam_allocation rejected[] = {
        {0,0,0,255}, {UINT64_C(0xe0000001),0,0,255},
        {UINT64_C(0xf0000000),0,0,255}, {UINT64_MAX,0,0,255},
        {UINT64_C(0xe0000000),1,0,255}, {UINT64_C(0xe0000000),0,1,255},
        {UINT64_C(0xe0000000),0,0,254}, {UINT64_C(0xe0000000),0,255,0}
    };
    address = 99;
    for (unsigned i = 0; i < sizeof(rejected)/sizeof(rejected[0]); ++i)
        assert(!qotom_ecam_dword_address(&rejected[i],0,0,0,0,&address));
    const uint32_t malformed[][4] = {
        {256,0,0,0}, {UINT32_MAX,0,0,0}, {0,32,0,0}, {0,UINT32_MAX,0,0},
        {0,0,8,0}, {0,0,UINT32_MAX,0}, {0,0,0,1}, {0,0,0,2}, {0,0,0,3},
        {0,0,0,253}, {0,0,0,256}, {0,0,0,4092}, {0,0,0,UINT32_MAX}
    };
    for (unsigned i = 0; i < sizeof(malformed)/sizeof(malformed[0]); ++i)
        assert(!qotom_ecam_dword_address(&baseline,malformed[i][0],malformed[i][1],
                                       malformed[i][2],malformed[i][3],&address));
    assert(!qotom_ecam_dword_address(0,0,0,0,0,&address));
    assert(!qotom_ecam_dword_address(&baseline,0,0,0,0,0));
    assert(address == 99);

    struct qotom_ecam_reader reader = {baseline, access_dword, &calls};
    uint32_t value = 42;
    assert(!qotom_ecam_read(0,0,0,0,0,&value));
    assert(!qotom_ecam_read(&reader,0,32,0,0,&value));
    assert(!qotom_ecam_read(&reader,0,0,8,0,&value));
    assert(!qotom_ecam_read(&reader,0,0,0,1,&value));
    assert(!qotom_ecam_read(&reader,0,0,0,0,0));
    reader.access = 0;
    assert(!qotom_ecam_read(&reader,0,0,0,0,&value));
    reader.access = access_dword;
    reader.allocation = rejected[4];
    assert(!qotom_ecam_read(&reader,0,0,0,0,&value));
    reader.allocation = baseline;
    assert(calls == 0 && value == 42);
    fail_address = UINT64_C(0xe0000000);
    assert(!qotom_ecam_read(&reader,0,0,0,0,&value));
    assert(calls == 1 && value == 42);

    struct pci_enumeration_snapshot snapshot;
    fail_address = 0;
    calls = 0;
    struct pci_enumeration_result result = pci_enumerate_segment(qotom_ecam_read,&reader,&snapshot);
    assert(result.status == PCI_ENUMERATION_OK && snapshot.count == 1);
    assert(calls == 65536 + 15);
    assert(snapshot.headers[0].bus == 255 && snapshot.headers[0].device == 31 && snapshot.headers[0].function == 7);
    for (unsigned i = 1; i < 16; ++i) assert(snapshot.headers[0].words[i] == i*4);
    fail_address = UINT64_C(0xeffff008);
    calls = 0;
    result = pci_enumerate_segment(qotom_ecam_read,&reader,&snapshot);
    assert(result.status == PCI_ENUMERATION_READ_FAILED && snapshot.count == 0);
    assert(result.bus == 255 && result.device == 31 && result.function == 7 && result.offset == 8);
    assert(calls == 65536 + 2);
    puts("Qotom ECAM candidate: exhaustive address domain, rejection, transport and collection PASS");
    return 0;
}
