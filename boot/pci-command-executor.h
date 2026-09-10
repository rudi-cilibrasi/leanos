#ifndef LEANOS_PCI_COMMAND_EXECUTOR_H
#define LEANOS_PCI_COMMAND_EXECUTOR_H

#include "pci-enumeration.h"

/* A successful inventory check is necessary but does not authorize hardware
 * use: the caller must also establish the board's device policy, serialization
 * and quiescence assumptions. Callbacks and the initial snapshot are trusted,
 * terminate, and remain immutable throughout execution. No rollback is safe
 * after a partial sequence; every failure requires the caller to stop boot.
 */
typedef uint64_t (*pci_command_admit)(const struct pci_enumeration_snapshot *);
typedef int (*pci_command_write16)(void *, uint8_t, uint8_t, uint8_t,
                                   uint8_t, uint16_t);

struct pci_command_trace {
    uint32_t count;
    uint64_t words[15u * 25u];
};

enum pci_command_status {
    PCI_COMMAND_OK,
    PCI_COMMAND_INVALID_ARGUMENT,
    PCI_COMMAND_INVENTORY_REJECTED,
    PCI_COMMAND_WRITE_FAILED,
    PCI_COMMAND_READ_FAILED,
    PCI_COMMAND_READBACK_NONZERO,
    PCI_COMMAND_REGISTER_CHANGED
};

struct pci_command_result {
    enum pci_command_status status;
    uint32_t step, writes_completed, reads_completed;
    uint8_t bus, device, function, offset;
    uint64_t admission;
};

/* The Qotom observation contract orders downstream endpoints, bus-zero
 * endpoints, then bridges, preserving snapshot order within each group.
 * The admission callback must check the complete canonical Qotom inventory
 * and return exactly 1 for acceptance. No identity table is duplicated here.
 * Trace slots use the existing 25-word observation ABI. Only a fully completed
 * trace publishes count=15; failed operations retain their exact location.
 */
static struct pci_command_result pci_execute_command_clear(
        pci_enumeration_read read, pci_command_write16 write,
        pci_command_admit admit, void *context,
        const struct pci_enumeration_snapshot *initial,
        struct pci_command_trace *trace) {
    struct pci_command_result r = {0};
    if (trace) trace->count = 0;
    if (!read || !write || !admit || !initial || !trace) {
        r.status = PCI_COMMAND_INVALID_ARGUMENT;
        return r;
    }
    if (initial->count != 15) {
        r.status = PCI_COMMAND_INVENTORY_REJECTED;
        return r;
    }
    r.admission = admit(initial);
    if (r.admission != 1) {
        r.status = PCI_COMMAND_INVENTORY_REJECTED;
        return r;
    }
    for (unsigned group = 0; group < 3; ++group) {
        for (unsigned i = 0; i < initial->count; ++i) {
            const struct pci_enumeration_header *h = &initial->headers[i];
            unsigned bridge = ((h->words[3] >> 16) & 0x7fu) == 1;
            unsigned category = bridge ? 2u : h->bus ? 0u : 1u;
            if (category != group) continue;
            r.bus = h->bus; r.device = h->device; r.function = h->function;
            r.offset = 4;
            uint64_t *slot = &trace->words[r.step * 25u];
            slot[0] = h->bus; slot[1] = h->device; slot[2] = h->function;
            slot[3] = 4; slot[4] = 2; slot[5] = 0;
            slot[6] = h->bus; slot[7] = h->device; slot[8] = h->function;
            if (!write(context, h->bus, h->device, h->function, 4, 0)) {
                r.status = PCI_COMMAND_WRITE_FAILED;
                return r;
            }
            ++r.writes_completed;
            for (unsigned word = 0; word < PCI_ENUMERATION_WORDS; ++word) {
                uint32_t value;
                r.offset = (uint8_t)(word * 4);
                if (!read(context, h->bus, h->device, h->function,
                          r.offset, &value)) {
                    r.status = PCI_COMMAND_READ_FAILED;
                    return r;
                }
                ++r.reads_completed;
                slot[9 + word] = value;
                if (word == 1 ? (value & 0xffffu) != 0 : value != h->words[word]) {
                    r.status = word == 1 ? PCI_COMMAND_READBACK_NONZERO
                                         : PCI_COMMAND_REGISTER_CHANGED;
                    return r;
                }
            }
            ++r.step;
        }
    }
    trace->count = r.step;
    r.bus = r.device = r.function = r.offset = 0;
    return r;
}

#endif
