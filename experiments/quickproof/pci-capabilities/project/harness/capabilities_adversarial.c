/* Law capabilities_adversarial.  For every initial header (any bus, device, function and sixteen header words), any
   prior snapshot count, and a device whose every configuration read may fail or return any value, also a different
   one each time (a device that changes its configuration space between reads, or lies), and each of the read
   callback, the initial header, the snapshot and the result record either present or NULL,
   pci_collect_capabilities (caps_collect):
     - asks the device only for the initial header's bus, device and function, only for dword-aligned offsets of
       conventional configuration space (at most 0xfc), and at most 4 + 48 times;
     - returns one of the seven statuses, and writes it and an offset into the result record when there is one;
     - returns PCI_CAPABILITY_ARGUMENT, with offset 0 and without a read, exactly when the callback, the header or
       the snapshot is NULL, the device is above 31, the function above 7, the header type above 1 or the vendor
       0xffff;
     - on every other status but OK, every read before the last succeeded, and the offset names the failure:
       READ_FAILED the last read, which failed; HEADER_CHANGED the last read, one of the four header words, whose
       value differs from the initial header under its mask; ABSENT the last read, a capability header with id
       0xff; POINTER and CYCLE the pointer the last read named (the list head after the four header reads), which is
       below 0x40, misaligned or the 49th (POINTER) or one already read (CYCLE);
     - on every status but OK, publishes count 0 (when there is a snapshot);
     - on OK, the result's offset is 0, and the device answered exactly 4 + count reads, every one successfully:
       first the header words at offsets 0, 4, 12 and 52, each matching the initial header under its mask
       (identity, the capability-list status bit, the header type, the list head); then, for i < count, a read at
       headers[i].offset that returned headers[i].raw.  headers[0].offset is the list head (word 13's low byte
       when the status word's capability bit is set, else there are no headers), each further offset is the
       previous raw word's next pointer (bits 8..15), and the last raw word's next pointer is 0.  Every offset is
       at least 0x40, dword aligned and distinct from the others, no header has id 0xff, and count <= 48.
   So no device can make the walker read outside the function's conventional space, read without bound, write past
   its 48-entry snapshot, or publish a list it did not read.  Not claimed: termination (partial correctness; every
   loop is bounded). */
#include "quickproof.h"
#include "caps_api.h"

#define MAX_READS 52u

struct device {
    uint8_t bus, device, function;
    uint32_t reads;
    uint8_t offsets[MAX_READS];
    uint8_t ok[MAX_READS];
    uint32_t values[MAX_READS];
};

static int device_read(void *context, uint8_t bus, uint8_t device, uint8_t function, uint8_t offset,
                       uint32_t *value) {
    struct device *d = context;
    qp_assert(bus == d->bus && device == d->device && function == d->function);
    qp_assert((offset & 3u) == 0 && offset <= 0xfcu);
    qp_assert(d->reads < MAX_READS);
    uint32_t i = d->reads;
    d->reads = i + 1;
    d->offsets[i] = offset;
    if (nondet_u8() == 0) {
        d->ok[i] = 0;
        return 0;
    }
    uint32_t v = nondet_u32();
    d->ok[i] = 1;
    d->values[i] = v;
    *value = v;
    return 1;
}

/* The pointer the last read names: the list head after the header reads, else the last header's next field. */
static uint32_t named_pointer(const struct device *d, const struct pci_enumeration_header *initial) {
    if (d->reads == 4)
        return (initial->words[1] & UINT32_C(0x00100000)) != 0 ? (initial->words[13] & 255u) : 0;
    return (d->values[d->reads - 1] >> 8) & 255u;
}

int main(void) {
    struct pci_enumeration_header initial;
    initial.bus = nondet_u8();
    initial.device = nondet_u8();
    initial.function = nondet_u8();
    for (uint32_t i = 0; i < PCI_ENUMERATION_WORDS; ++i)
        initial.words[i] = nondet_u32();
    struct device d;
    d.bus = initial.bus;
    d.device = initial.device;
    d.function = initial.function;
    d.reads = 0;
    struct pci_capability_snapshot snapshot;
    snapshot.count = nondet_u32();
    struct pci_capability_result result;
    result.status = PCI_CAPABILITY_OK;
    result.offset = nondet_u8();
    uint8_t result_offset = result.offset;
    pci_enumeration_read read_arg = nondet_u8() == 0 ? NULL : device_read;
    const struct pci_enumeration_header *initial_arg = nondet_u8() == 0 ? NULL : &initial;
    struct pci_capability_snapshot *snapshot_arg = nondet_u8() == 0 ? NULL : &snapshot;
    struct pci_capability_result *result_arg = nondet_u8() == 0 ? NULL : &result;
    uint32_t prior_count = snapshot.count;
    int invalid = read_arg == NULL || initial_arg == NULL || snapshot_arg == NULL || initial.device > 31 ||
        initial.function > 7 || ((initial.words[3] >> 16) & 0x7fu) > 1 || (initial.words[0] & 0xffffu) == 0xffffu;

    enum pci_capability_status status = caps_collect(read_arg, &d, initial_arg, snapshot_arg, result_arg);

    qp_assert(status >= PCI_CAPABILITY_OK && status <= PCI_CAPABILITY_ABSENT);
    uint32_t offset = result_offset;
    if (result_arg != NULL) {
        qp_assert(result.status == status);
        offset = result.offset;
    } else {
        qp_assert(result.status == PCI_CAPABILITY_OK && result.offset == result_offset);
    }
    qp_assert((status == PCI_CAPABILITY_ARGUMENT) == invalid);
    qp_assert(snapshot.count == (snapshot_arg == NULL ? prior_count : (status == PCI_CAPABILITY_OK ? snapshot.count : 0)));
    if (status == PCI_CAPABILITY_ARGUMENT) {
        qp_assert(d.reads == 0 && (result_arg == NULL || offset == 0));
        return 0;
    }
    const uint8_t header_offsets[4] = {0, 4, 12, 52};
    const uint32_t masks[4] = {UINT32_MAX, UINT32_C(0x00100000), UINT32_C(0x00ff0000), 255};
    qp_assert(d.reads >= 1);
    uint32_t last = d.reads - 1;
    for (uint32_t k = 0; k < d.reads && k < 4; ++k)
        qp_assert(d.offsets[k] == header_offsets[k]);
    for (uint32_t k = 0; k < last; ++k) {
        qp_assert(d.ok[k] == 1);
        if (k < 4)
            qp_assert((d.values[k] & masks[k]) == (initial.words[header_offsets[k] / 4] & masks[k]));
    }
    if (status == PCI_CAPABILITY_READ_FAILED) {
        qp_assert(d.ok[last] == 0 && (result_arg == NULL || offset == d.offsets[last]));
        return 0;
    }
    qp_assert(d.ok[last] == 1);
    if (status == PCI_CAPABILITY_HEADER_CHANGED) {
        qp_assert(last < 4 && (d.values[last] & masks[last]) != (initial.words[header_offsets[last] / 4] & masks[last]));
        qp_assert(result_arg == NULL || offset == d.offsets[last]);
        return 0;
    }
    qp_assert(d.reads >= 4);
    if (last >= 4)
        qp_assert((d.values[last] & masks[3]) != 255u || status == PCI_CAPABILITY_ABSENT);
    else
        qp_assert((d.values[last] & masks[last]) == (initial.words[header_offsets[last] / 4] & masks[last]));
    if (status == PCI_CAPABILITY_ABSENT) {
        qp_assert(last >= 4 && (d.values[last] & 255u) == 255u && (result_arg == NULL || offset == d.offsets[last]));
        return 0;
    }
    if (status == PCI_CAPABILITY_POINTER || status == PCI_CAPABILITY_CYCLE) {
        uint32_t p = named_pointer(&d, &initial);
        qp_assert(p != 0 && (result_arg == NULL || offset == p));
        int repeated = 0;
        for (uint32_t k = 4; k < d.reads; ++k)
            if (d.offsets[k] == p)
                repeated = 1;
        if (status == PCI_CAPABILITY_POINTER)
            qp_assert(p < 64 || (p & 3u) != 0 || (!repeated && d.reads == 4 + PCI_CAPABILITY_CAPACITY));
        else
            qp_assert(p >= 64 && (p & 3u) == 0 && repeated);
        return 0;
    }
    qp_assert(result_arg == NULL || offset == 0);
    uint32_t count = snapshot.count;
    qp_assert(count <= PCI_CAPABILITY_CAPACITY && d.reads == 4 + count);
    for (uint32_t k = 0; k < 4; ++k) {
        qp_assert(d.offsets[k] == header_offsets[k] && d.ok[k] == 1);
        qp_assert((d.values[k] & masks[k]) == (initial.words[header_offsets[k] / 4] & masks[k]));
    }
    uint32_t next = (initial.words[1] & UINT32_C(0x00100000)) != 0 ? (initial.words[13] & 255u) : 0;
    for (uint32_t i = 0; i < count; ++i) {
        uint32_t at = snapshot.headers[i].offset;
        uint32_t raw = snapshot.headers[i].raw;
        qp_assert(at == next && at >= 64 && (at & 3u) == 0);
        for (uint32_t j = 0; j < i; ++j)
            qp_assert(snapshot.headers[j].offset != at);
        qp_assert(d.offsets[4 + i] == at && d.ok[4 + i] == 1 && d.values[4 + i] == raw);
        qp_assert((raw & 255u) != 255u);
        next = (raw >> 8) & 255u;
    }
    qp_assert(next == 0);
    return 0;
}
