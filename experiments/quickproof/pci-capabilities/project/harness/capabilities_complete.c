/* Law capabilities_complete.  For a device whose conventional configuration space is fixed (every read succeeds
   and returns the same 64 dwords) and holds a capability list of any n <= 48 headers, at distinct dword-aligned
   offsets of at least 0x40, with any ids but 0xff and any upper halves, linked in that order and terminated by 0,
   the capability-list status bit set and word 13's low byte naming the first header (for n = 0: the status bit
   clear, or set with a zero head), and an initial header that is the space's first sixteen words with device
   <= 31, function <= 7, header type 0 or 1 and a vendor other than 0xffff, pci_collect_capabilities
   (caps_collect) returns OK and publishes exactly those n headers in order: offset and raw word of each.  Not
   claimed: termination (partial correctness). */
#include "quickproof.h"
#include "caps_api.h"

struct space {
    uint8_t bus, device, function;
    uint32_t words[64];
};

static int space_read(void *context, uint8_t bus, uint8_t device, uint8_t function, uint8_t offset,
                      uint32_t *value) {
    struct space *s = context;
    qp_assert(bus == s->bus && device == s->device && function == s->function);
    qp_assert((offset & 3u) == 0 && offset <= 0xfcu);
    *value = s->words[offset / 4];
    return 1;
}

int main(void) {
    struct space s;
    for (uint32_t i = 0; i < 64; ++i)
        s.words[i] = nondet_u32();
    uint32_t n = nondet_u32();
    qp_assume(n <= PCI_CAPABILITY_CAPACITY);
    uint32_t at[PCI_CAPABILITY_CAPACITY];
    for (uint32_t i = 0; i < n; ++i) {
        at[i] = nondet_u32();
        qp_assume(at[i] >= 64 && at[i] <= 0xfcu && (at[i] & 3u) == 0);
        for (uint32_t j = 0; j < i; ++j)
            qp_assume(at[j] != at[i]);
    }
    for (uint32_t i = 0; i < n; ++i) {
        uint32_t id = nondet_u32() & 255u;
        qp_assume(id != 255u);
        uint32_t next = i + 1 < n ? at[i + 1] : 0;
        s.words[at[i] / 4] = (s.words[at[i] / 4] & UINT32_C(0xffff0000)) | (next << 8) | id;
    }
    if (n > 0) {
        s.words[1] |= UINT32_C(0x00100000);
        s.words[13] = (s.words[13] & ~UINT32_C(255)) | at[0];
    } else if (nondet_u8() & 1u) {
        s.words[1] &= ~UINT32_C(0x00100000);
    } else {
        s.words[1] |= UINT32_C(0x00100000);
        s.words[13] &= ~UINT32_C(255);
    }
    qp_assume(((s.words[3] >> 16) & 0x7fu) <= 1 && (s.words[0] & 0xffffu) != 0xffffu);
    s.bus = nondet_u8();
    s.device = nondet_u8();
    s.function = nondet_u8();
    qp_assume(s.device <= 31 && s.function <= 7);

    struct pci_enumeration_header initial;
    initial.bus = s.bus;
    initial.device = s.device;
    initial.function = s.function;
    for (uint32_t i = 0; i < PCI_ENUMERATION_WORDS; ++i)
        initial.words[i] = s.words[i];
    struct pci_capability_snapshot snapshot;

    enum pci_capability_status status = caps_collect(space_read, &s, &initial, &snapshot, 0);

    qp_assert(status == PCI_CAPABILITY_OK && snapshot.count == n);
    for (uint32_t i = 0; i < n; ++i)
        qp_assert(snapshot.headers[i].offset == at[i] && snapshot.headers[i].raw == s.words[at[i] / 4]);
    return 0;
}
