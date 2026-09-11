#include <assert.h>
#include <stdio.h>
#include "../boot/pci-af-observation.h"
static uint32_t config[64];
static unsigned reads;
static int failure = -1;
static int read_config(void *ctx, uint8_t bus, uint8_t device, uint8_t function,
        uint8_t offset, uint32_t *out) {
    (void)ctx;
    assert(bus == 0 && device == 29 && function == 0 && !(offset & 3));
    ++reads;
    if (offset == failure) return 0;
    *out = config[offset/4]; return 1;
}
static void rejected(struct pci_af_observation o, enum pci_af_status status) {
    assert(o.status == status && !o.offset && !o.raw_control_status);
}
int main(void) {
    assert(pci_enumerate_segment(NULL, NULL, NULL).status == PCI_ENUMERATION_INVALID_ARGUMENT);
    struct pci_enumeration_header initial = {.device=29};
    initial.words[0] = config[0] = 0x0f348086;
    initial.words[1] = config[1] = 0x00100406;
    for (unsigned offset = 64; offset <= 248; offset += 4) {
        for (unsigned i = 16; i < 64; ++i) config[i] = 0;
        initial.words[13] = config[13] = offset;
        config[offset/4] = 0x03060013;
        struct pci_capability_snapshot previous = {.count=1, .headers={{offset,0x03060013}}};
        /* Both pending values are observations, not success/failure policy. */
        for (unsigned pending = 0; pending < 2; ++pending) {
            config[offset/4+1] = pending << 8;
            reads = 0;
            struct pci_af_observation o = pci_observe_af(read_config, NULL, &initial, &previous);
            assert(o.status == PCI_AF_OK && o.offset == offset &&
                   o.raw_control_status == pending << 8 && reads == 6);
        }
        failure = offset + 4;
        rejected(pci_observe_af(read_config,NULL,&initial,&previous), PCI_AF_READ_FAILED);
        failure = offset;
        rejected(pci_observe_af(read_config,NULL,&initial,&previous), PCI_AF_COLLECTION_FAILED);
        failure = -1;
        config[offset/4+1] = UINT32_MAX;
        rejected(pci_observe_af(read_config,NULL,&initial,&previous), PCI_AF_ABSENT);
        previous.headers[0].raw ^= 0x10000;
        rejected(pci_observe_af(read_config,NULL,&initial,&previous), PCI_AF_LIST_CHANGED);
    }
    initial.words[13] = config[13] = 252;
    config[63] = 0x03060013;
    struct pci_capability_snapshot previous = {.count=1,.headers={{252,0x03060013}}};
    reads = 0;
    rejected(pci_observe_af(read_config,NULL,&initial,&previous), PCI_AF_SHAPE);
    assert(reads == 5);
    initial.words[13] = config[13] = 64;
    for (uint32_t upper = 0; upper < 65536; ++upper) {
        config[16] = previous.headers[0].raw = (upper << 16) | 0x13;
        previous.headers[0].offset = 64;
        config[17] = 0;
        struct pci_af_observation o = pci_observe_af(read_config,NULL,&initial,&previous);
        if (upper == 0x306) assert(o.status == PCI_AF_OK);
        else rejected(o, PCI_AF_SHAPE);
    }
    config[16] = 0x03064413; config[17] = 1;
    previous.count = 2;
    previous.headers[0] = (struct pci_capability_header){64,config[16]};
    previous.headers[1] = (struct pci_capability_header){68,1};
    rejected(pci_observe_af(read_config,NULL,&initial,&previous), PCI_AF_SHAPE);
    config[16] = 0x03064813; config[18] = 0x03060013;
    previous.headers[0].raw = config[16];
    previous.headers[1] = (struct pci_capability_header){72,config[18]};
    rejected(pci_observe_af(read_config,NULL,&initial,&previous), PCI_AF_SHAPE);
    previous.count = 1;
    config[16] = previous.headers[0].raw = 0x03060013;
    config[17] = 0;
    const unsigned indices[] = {0,1,3,13};
    const uint32_t masks[] = {1,0x100000,0x10000,4};
    for (unsigned i = 0; i < 4; ++i) {
        config[indices[i]] ^= masks[i];
        rejected(pci_observe_af(read_config,NULL,&initial,&previous), PCI_AF_COLLECTION_FAILED);
        config[indices[i]] ^= masks[i];
    }
    previous.count = 0;
    rejected(pci_observe_af(read_config,NULL,&initial,&previous), PCI_AF_LIST_CHANGED);
    rejected(pci_observe_af(read_config,NULL,NULL,&previous), PCI_AF_ARGUMENT);
    rejected(pci_observe_af(read_config,NULL,&initial,NULL), PCI_AF_ARGUMENT);
    previous.count = 49;
    reads = 0;
    rejected(pci_observe_af(read_config,NULL,&initial,&previous), PCI_AF_ARGUMENT);
    assert(!reads);
    rejected(pci_observe_af(NULL,NULL,&initial,&previous), PCI_AF_ARGUMENT);
    initial.words[1] = config[1] = 0;
    previous.count = 0;
    rejected(pci_observe_af(read_config,NULL,&initial,&previous), PCI_AF_NOT_PRESENT);
    puts("PASS AF observation: all payload shapes, boundary offsets, drift, failures, overlap and duplicates");
}
