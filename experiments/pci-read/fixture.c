#include "pci-enumeration.h"
#include "pci-config-read.h"

extern uint32_t fixture_read_flags(uint32_t, uint64_t, uint64_t *);
static struct pci_enumeration_snapshot snapshot;

static void put(char c) {
    __asm__ volatile ("outb %0, $0xe9" : : "a"(c));
}

static void hex(uint32_t value) {
    const char *digits = "0123456789abcdef";
    for (unsigned shift = 32; shift; shift -= 4)
        put(digits[(value >> (shift - 4)) & 15]);
}

static void field(uint32_t value) {
    put(' ');
    hex(value);
}

void fixture_main(void) {
    uint64_t flags;
    for (unsigned enabled = 0; enabled < 2; ++enabled) {
        uint64_t seed = 0x47u | (enabled << 9);
        uint32_t identity = fixture_read_flags(0x80000000u, seed, &flags);
        put('F');
        field((uint32_t)seed);
        field((uint32_t)flags);
        field(identity);
        put('\n');
    }
    struct pci_enumeration_result result =
        pci_enumerate_segment(pci_config_read, 0, &snapshot);
    put('S');
    field(result.status);
    field(snapshot.count);
    field(result.bus);
    field(result.device);
    field(result.function);
    field(result.offset);
    put('\n');
    if (result.status == PCI_ENUMERATION_OK) {
        for (unsigned i = 0; i < snapshot.count; ++i) {
            const struct pci_enumeration_header *h = &snapshot.headers[i];
            put('H');
            field(h->bus);
            field(h->device);
            field(h->function);
            for (unsigned j = 0; j < PCI_ENUMERATION_WORDS; ++j)
                field(h->words[j]);
            put('\n');
        }
    }
    put('D');
    put('\n');
}
