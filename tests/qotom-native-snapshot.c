#include "../boot/qotom-native-inventory.h"
extern uint8_t lp_leanos_LeanOS_QotomNativePCIFields_checkHeader(
    uint64_t, uint64_t, uint64_t, uint64_t,
    uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t,
    uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t);

uint64_t qotom_native_snapshot_replay(uint32_t status,
    const struct pci_enumeration_snapshot *snapshot) {
    struct qotom_native_inventory_result r = qotom_check_native_inventory(
        (enum pci_enumeration_status)status, snapshot,
        lp_leanos_LeanOS_QotomNativePCIFields_checkHeader);
    return ((uint64_t)r.status << 32) | r.index;
}

struct source_context {
    const struct pci_enumeration_snapshot *source;
    int fail_last;
};
static int read_source(void *opaque, uint8_t bus, uint8_t device,
    uint8_t function, uint8_t offset, uint32_t *out) {
    struct source_context *context = opaque;
    if (context->fail_last && bus == 255 && device == 31 && function == 7)
        return 0;
    for (unsigned i = 0; i < context->source->count; ++i) {
        const struct pci_enumeration_header *h = &context->source->headers[i];
        if (h->bus == bus && h->device == device && h->function == function) {
            *out = h->words[offset / 4];
            return 1;
        }
    }
    *out = UINT32_MAX;
    return 1;
}
uint64_t qotom_native_collect_replay(const struct pci_enumeration_snapshot *source,
    int fail_last) {
    struct source_context context = {source, fail_last};
    struct pci_enumeration_snapshot snapshot;
    if (!source || source->count > PCI_ENUMERATION_CAPACITY) return UINT64_MAX;
    struct pci_enumeration_result result = pci_enumerate_segment(
        read_source, &context, &snapshot);
    return qotom_native_snapshot_replay(result.status, &snapshot);
}
