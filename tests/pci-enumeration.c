#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "pci-enumeration.h"
#include "pci-enumeration-capture.h"

struct function {
    uint32_t words[16];
    uint16_t reads;
};
static struct function *functions;
static unsigned calls, fail_slot, fail_word, previous_slot, next_word;
static int fail_enabled, started;

static unsigned slot(unsigned bus, unsigned device, unsigned function) {
    return bus * 256 + device * 8 + function;
}

static int read_word(void *context, uint8_t bus, uint8_t device,
                     uint8_t function, uint8_t offset, uint32_t *value) {
    assert(context == functions && device < 32 && function < 8);
    assert(offset < 64 && offset % 4 == 0);
    unsigned index = slot(bus, device, function), word = offset / 4;
    if (word == 0) {
        assert(!started || index == previous_slot + 1);
        assert(!started || next_word == 16 || next_word == 1);
        previous_slot = index;
        next_word = 0;
        started = 1;
    } else assert(index == previous_slot);
    assert(word == next_word++);
    assert(!(functions[index].reads & (1u << word)));
    functions[index].reads |= (uint16_t)(1u << word);
    ++calls;
    if (fail_enabled && index == fail_slot && word == fail_word) return 0;
    *value = functions[index].words[word];
    return 1;
}

static void reset(void) {
    memset(functions, 0, 65536 * sizeof(*functions));
    for (unsigned i = 0; i < 65536; ++i) functions[i].words[0] = UINT32_MAX;
    for (unsigned i = 0; i < CAPTURE_COUNT; ++i) {
        const struct pci_enumeration_header *h = &capture[i];
        memcpy(functions[slot(h->bus, h->device, h->function)].words,
               h->words, sizeof(h->words));
    }
    calls = previous_slot = next_word = 0;
    fail_enabled = started = 0;
}

static struct pci_enumeration_snapshot snapshot;

static struct pci_enumeration_result run(void) {
    snapshot.count = 99; /* Failure must invalidate even a prior count. */
    return pci_enumerate_segment(read_word, functions, &snapshot);
}

int main(void) {
    functions = calloc(65536, sizeof(*functions));
    assert(functions);
    reset();
    assert(run().status == PCI_ENUMERATION_OK && snapshot.count == CAPTURE_COUNT);
    assert(calls == 65536 + CAPTURE_COUNT * 15);
    for (unsigned i = 0; i < CAPTURE_COUNT; ++i) {
        const struct pci_enumeration_header *a = &snapshot.headers[i], *b = &capture[i];
        assert(a->bus == b->bus && a->device == b->device && a->function == b->function);
        assert(memcmp(a->words, b->words, sizeof(a->words)) == 0);
    }
    for (unsigned i = 0; i < 65536; ++i)
        assert(functions[i].reads == ((uint16_t)functions[i].words[0] == UINT16_MAX ? 1 : UINT16_MAX));

    /* Missing devices remain missing; collection never fills them from the
     * capture. An empty segment is a valid observation, not admitted hardware.
     */
    for (unsigned i = 0; i < CAPTURE_COUNT; ++i) {
        reset();
        const struct pci_enumeration_header *h = &capture[i];
        functions[slot(h->bus, h->device, h->function)].words[0] = UINT32_MAX;
        assert(run().status == PCI_ENUMERATION_OK && snapshot.count == CAPTURE_COUNT - 1);
        for (unsigned j = 0; j < snapshot.count; ++j)
            assert(snapshot.headers[j].bus != h->bus || snapshot.headers[j].device != h->device ||
                   snapshot.headers[j].function != h->function);
    }
    reset();
    for (unsigned i = 0; i < 65536; ++i) functions[i].words[0] = UINT32_MAX;
    assert(run().status == PCI_ENUMERATION_OK && snapshot.count == 0 && calls == 65536);

    /* No function-zero or multifunction shortcut: the last possible address
     * is collected even though its function zero and every other slot are absent.
     */
    reset();
    for (unsigned i = 0; i < 65536; ++i) functions[i].words[0] = UINT32_MAX;
    functions[65535].words[0] = 0x12348086;
    assert(run().status == PCI_ENUMERATION_OK && snapshot.count == 1);
    assert(snapshot.headers[0].bus == 255 && snapshot.headers[0].device == 31 &&
           snapshot.headers[0].function == 7 && calls == 65551);

    /* Rogue functions are retained, never silently filtered against an allowlist.
     * The inventory checker, not enumeration, rejects a changed topology.
     */
    reset();
    functions[65535].words[0] = 0x12348086;
    assert(run().status == PCI_ENUMERATION_OK && snapshot.count == 16);
    reset();
    functions[65534].words[0] = functions[65535].words[0] = 0x12348086;
    struct pci_enumeration_result r = run();
    assert(r.status == PCI_ENUMERATION_CAPACITY_EXCEEDED && snapshot.count == 0);
    assert(r.bus == 255 && r.device == 31 && r.function == 7 && r.offset == 0);
    assert(functions[65535].reads == 1);

    /* Every raw header position can fail, with exact location and no continued IO. */
    for (unsigned i = 0; i < CAPTURE_COUNT; ++i) {
        for (unsigned word = 0; word < 16; ++word) {
            reset();
            const struct pci_enumeration_header *h = &capture[i];
            fail_enabled = 1;
            fail_slot = slot(h->bus, h->device, h->function);
            fail_word = word;
            r = run();
            assert(r.status == PCI_ENUMERATION_READ_FAILED && snapshot.count == 0);
            assert(r.bus == h->bus && r.device == h->device && r.function == h->function);
            assert(r.offset == word * 4 && previous_slot == fail_slot && next_word == word + 1);
        }
    }
    reset();
    fail_enabled = 1; fail_slot = 65535; fail_word = 0;
    r = run();
    assert(r.status == PCI_ENUMERATION_READ_FAILED && snapshot.count == 0 && calls == 65761);
    reset();
    assert(pci_enumerate_segment(NULL, functions, &snapshot).status == PCI_ENUMERATION_INVALID_ARGUMENT);
    assert(snapshot.count == 0 && calls == 0);
    assert(pci_enumerate_segment(read_word, functions, NULL).status == PCI_ENUMERATION_INVALID_ARGUMENT);
    assert(calls == 0);
    free(functions);
    puts("PCI enumeration: full segment, exact capture, overflow and 241 read failures passed");
    return 0;
}
