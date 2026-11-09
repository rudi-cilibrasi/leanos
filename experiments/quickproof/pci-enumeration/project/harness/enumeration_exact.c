/* Law enumeration_exact.  For a device whose every configuration read may fail or answer any value, also a different
   one each time (a device that changes its configuration space between reads, or lies), any prior snapshot count and
   result record, and each of the read callback, the snapshot and the result record either present or NULL,
   pci_enumerate_segment (enum_scan):
     - reads exactly in this order and nothing else: for each function of the segment in bus, device, function order
       (bus 0..255, device 0..31, function 0..7), its identity dword at offset 0; and right after an identity read that
       succeeded with a vendor (low 16 bits) other than 0xffff, when fewer than 16 functions were found before it,
       that function's dwords at offsets 4, 8, ..., 60.  It reads nothing after a read that failed, nor after the
       identity of a 17th function found.  So it makes at most 65536 + 16 * 15 reads, all of conventional space;
     - returns one of the four statuses, and when there is a result record writes it and the location it names;
     - returns INVALID_ARGUMENT, location 0, without a read, exactly when the callback or the snapshot is NULL;
     - returns READ_FAILED exactly when a read failed, naming that read's bus, device, function and offset;
     - returns CAPACITY_EXCEEDED exactly when a 17th function was found, naming it, offset 0;
     - otherwise returns OK, location 0, after the identity reads of all 65536 functions;
     - publishes count 0 on every status but OK (when there is a snapshot);
     - on OK publishes the functions found, in the order found: count headers, each with the function's bus, device
       and function and the 16 dwords the device answered for it.
   So no device can make the scan read outside conventional space, read without bound, write past its 16-entry
   snapshot, skip a function, or publish a header it did not read.  The device below is the reference: it checks
   every read against the order above and keeps its own copy of the functions found.  Not claimed: termination
   (partial correctness; every loop is bounded). */
#include "quickproof.h"
#include "enum_api.h"

#define FUNCTIONS 65536u

struct device {
    uint32_t next;      /* the index bus * 256 + device * 8 + function of the next identity read */
    uint32_t word;      /* 0: the next read is an identity read; 1..15: the next read is that dword of function next-1 */
    uint32_t found;     /* functions found so far: identity reads that succeeded with a vendor other than 0xffff */
    uint32_t stopped;   /* no read may follow: after a failed read or the 17th function found */
    uint32_t failed;    /* a read failed */
    uint32_t reads;
    uint8_t last_bus, last_device, last_function, last_offset;   /* the last read */
    struct pci_enumeration_header seen[PCI_ENUMERATION_CAPACITY];   /* the functions found, as the device answered */
};

static int device_read(void *context, uint8_t bus, uint8_t device, uint8_t function, uint8_t offset,
                       uint32_t *value) {
    struct device *d = context;
    qp_assert(!d->stopped);
    uint32_t index = d->word == 0 ? d->next : d->next - 1;
    qp_assert(index < FUNCTIONS);
    qp_assert(bus == (index >> 8) && device == ((index >> 3) & 31u) && function == (index & 7u));
    qp_assert(offset == 4 * d->word);
    d->reads = d->reads + 1;
    d->last_bus = bus;
    d->last_device = device;
    d->last_function = function;
    d->last_offset = offset;
    if (nondet_u8() == 0) {
        d->stopped = 1;
        d->failed = 1;
        return 0;
    }
    uint32_t v = nondet_u32();
    *value = v;
    if (d->word == 0) {
        d->next = index + 1;
        if ((v & 0xffffu) != 0xffffu) {
            if (d->found == PCI_ENUMERATION_CAPACITY) {
                d->found = PCI_ENUMERATION_CAPACITY + 1;
                d->stopped = 1;
            } else {
                struct pci_enumeration_header *h = &d->seen[d->found];
                h->bus = bus;
                h->device = device;
                h->function = function;
                h->words[0] = v;
                d->found = d->found + 1;
                d->word = 1;
            }
        }
    } else {
        d->seen[d->found - 1].words[d->word] = v;
        d->word = d->word == PCI_ENUMERATION_WORDS - 1 ? 0 : d->word + 1;
    }
    return 1;
}

int main(void) {
    struct device d;
    d.next = 0;
    d.word = 0;
    d.found = 0;
    d.stopped = 0;
    d.failed = 0;
    d.reads = 0;
    struct pci_enumeration_snapshot snapshot;
    snapshot.count = nondet_u32();
    uint32_t prior_count = snapshot.count;
    struct pci_enumeration_result result;
    result.status = PCI_ENUMERATION_OK;
    result.bus = nondet_u8();
    result.device = nondet_u8();
    result.function = nondet_u8();
    result.offset = nondet_u8();
    uint8_t prior_bus = result.bus, prior_device = result.device, prior_function = result.function,
            prior_offset = result.offset;
    pci_enumeration_read read_arg = nondet_u8() == 0 ? NULL : device_read;
    struct pci_enumeration_snapshot *snapshot_arg = nondet_u8() == 0 ? NULL : &snapshot;
    struct pci_enumeration_result *result_arg = nondet_u8() == 0 ? NULL : &result;

    enum pci_enumeration_status status = enum_scan(read_arg, &d, snapshot_arg, result_arg);

    qp_assert(status >= PCI_ENUMERATION_OK && status <= PCI_ENUMERATION_INVALID_ARGUMENT);
    if (result_arg != NULL) {
        qp_assert(result.status == status);
    } else {
        qp_assert(result.status == PCI_ENUMERATION_OK && result.bus == prior_bus && result.device == prior_device &&
                  result.function == prior_function && result.offset == prior_offset);
    }
    int located = result_arg != NULL;
    qp_assert((status == PCI_ENUMERATION_INVALID_ARGUMENT) == (read_arg == NULL || snapshot_arg == NULL));
    qp_assert(snapshot.count == (snapshot_arg == NULL ? prior_count : (status == PCI_ENUMERATION_OK ? d.found : 0)));
    if (status == PCI_ENUMERATION_INVALID_ARGUMENT) {
        qp_assert(d.reads == 0);
        qp_assert(!located || (result.bus == 0 && result.device == 0 && result.function == 0 && result.offset == 0));
        return 0;
    }
    qp_assert((status == PCI_ENUMERATION_READ_FAILED) == (d.failed == 1));
    qp_assert((status == PCI_ENUMERATION_CAPACITY_EXCEEDED) == (d.found == PCI_ENUMERATION_CAPACITY + 1));
    if (status != PCI_ENUMERATION_OK) {
        qp_assert(d.stopped == 1 && d.reads >= 1);
        qp_assert(!located || (result.bus == d.last_bus && result.device == d.last_device &&
                               result.function == d.last_function && result.offset == d.last_offset));
        return 0;
    }
    qp_assert(d.stopped == 0 && d.next == FUNCTIONS && d.word == 0 && d.found <= PCI_ENUMERATION_CAPACITY);
    qp_assert(!located || (result.bus == 0 && result.device == 0 && result.function == 0 && result.offset == 0));
    for (uint32_t i = 0; i < snapshot.count; ++i) {
        const struct pci_enumeration_header *h = &snapshot.headers[i];
        qp_assert(h->bus == d.seen[i].bus && h->device == d.seen[i].device && h->function == d.seen[i].function);
        for (uint32_t w = 0; w < PCI_ENUMERATION_WORDS; ++w)
            qp_assert(h->words[w] == d.seen[i].words[w]);
    }
    return 0;
}
