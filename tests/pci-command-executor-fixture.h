#include <stdlib.h>
#include "../boot/pci-command-executor.h"

#define EXEC_REQUIRE(x) do { if (!(x)) { \
    fprintf(stderr, "executor assertion at line %d: %s\n", __LINE__, #x); \
    exit(1); } } while (0)

struct executor_fixture {
    struct pci_enumeration_snapshot initial;
    uint32_t raw[15][16];
    unsigned writes, reads, active;
    int fail_write, fail_read, drift_read, nonzero_step;
    int volatile_status;
    int readonly_lpc;
};

static uint64_t executor_admit(const struct pci_enumeration_snapshot *s) {
    lean_object *a = lean_mk_empty_array_with_capacity(lean_box(s->count * 19));
    for (unsigned i = 0; i < s->count; ++i) {
        const struct pci_enumeration_header *h = &s->headers[i];
        a = lean_array_push(a, lean_box_uint64(h->bus));
        a = lean_array_push(a, lean_box_uint64(h->device));
        a = lean_array_push(a, lean_box_uint64(h->function));
        for (unsigned j = 0; j < 16; ++j)
            a = lean_array_push(a, lean_box_uint64(h->words[j]));
    }
    return leanos_qotom_pci_inventory_check(s->count, a);
}

static void executor_reset(struct executor_fixture *f) {
    *f = (struct executor_fixture){.fail_write = -1, .fail_read = -1,
        .drift_read = -1, .nonzero_step = -1};
    f->initial.count = 15;
    for (unsigned i = 0; i < 15; ++i) {
        struct pci_enumeration_header *h = &f->initial.headers[i];
        const uint64_t *w = &inventory_cases[0].words[i * 19];
        h->bus = w[0]; h->device = w[1]; h->function = w[2];
        for (unsigned j = 0; j < 16; ++j)
            f->raw[i][j] = h->words[j] = (uint32_t)w[3 + j];
    }
}

static int executor_write(void *ctx, uint8_t bus, uint8_t dev, uint8_t fn,
                          uint8_t offset, uint16_t value) {
    struct executor_fixture *f = ctx;
    unsigned step = f->writes++;
    EXEC_REQUIRE(step < 15 && f->reads == step * 16);
    const uint64_t *expected = &inventory_cases[0].words[285 + step * 25];
    EXEC_REQUIRE(bus == expected[0] && dev == expected[1] && fn == expected[2]);
    EXEC_REQUIRE(offset == 4 && value == 0);
    if ((int)step == f->fail_write) return 0;
    f->active = 15;
    for (unsigned i = 0; i < 15; ++i) {
        const struct pci_enumeration_header *h = &f->initial.headers[i];
        if (h->bus == bus && h->device == dev && h->function == fn) f->active = i;
    }
    EXEC_REQUIRE(f->active < 15);
    f->raw[f->active][1] &= 0xffff0000u;
    /* Intel 329670-002 section 24.6.2: LPC Command[2:0] are RO ones.
     * This is a device-behavior fixture, not a physical write capture. */
    if (f->readonly_lpc && bus == 0 && dev == 31 && fn == 0)
        f->raw[f->active][1] |= 7u;
    if ((int)step == f->nonzero_step) f->raw[f->active][1] |= 4;
    if (f->volatile_status) f->raw[f->active][1] ^= 0x10000u;
    return 1;
}

static int executor_read(void *ctx, uint8_t bus, uint8_t dev, uint8_t fn,
                         uint8_t offset, uint32_t *value) {
    struct executor_fixture *f = ctx;
    unsigned n = f->reads++;
    EXEC_REQUIRE(f->writes == n / 16 + 1 && offset == (n % 16) * 4);
    const struct pci_enumeration_header *h = &f->initial.headers[f->active];
    EXEC_REQUIRE(bus == h->bus && dev == h->device && fn == h->function);
    if ((int)n == f->fail_read) return 0;
    *value = f->raw[f->active][offset / 4];
    if ((int)n == f->drift_read) *value ^= 1;
    return 1;
}

static uint64_t executor_transition(const struct pci_enumeration_snapshot *s,
                                    const struct pci_command_trace *t) {
    lean_object *a = lean_mk_empty_array_with_capacity(lean_box(660));
    for (unsigned i = 0; i < s->count; ++i) {
        const struct pci_enumeration_header *h = &s->headers[i];
        a = lean_array_push(a, lean_box_uint64(h->bus));
        a = lean_array_push(a, lean_box_uint64(h->device));
        a = lean_array_push(a, lean_box_uint64(h->function));
        for (unsigned j = 0; j < 16; ++j)
            a = lean_array_push(a, lean_box_uint64(h->words[j]));
    }
    for (unsigned i = 0; i < t->count * 25; ++i)
        a = lean_array_push(a, lean_box_uint64(t->words[i]));
    return leanos_qotom_pci_quarantine_transition(t->count, a);
}

static int executor_initial_read(void *ctx, uint8_t bus, uint8_t dev,
                                 uint8_t fn, uint8_t offset, uint32_t *value) {
    const struct executor_fixture *f = ctx;
    *value = UINT32_MAX;
    for (unsigned i = 0; i < 15; ++i) {
        const struct pci_enumeration_header *h = &f->initial.headers[i];
        if (h->bus == bus && h->device == dev && h->function == fn)
            *value = h->words[offset / 4];
    }
    return 1;
}

static void test_command_executor(void) {
    struct executor_fixture f;
    struct pci_command_trace t;
    struct pci_command_result r;
    unsigned negatives = 0;
    executor_reset(&f);
    struct pci_enumeration_snapshot collected;
    struct pci_enumeration_result collection = pci_enumerate_segment(
        executor_initial_read, &f, &collected);
    EXEC_REQUIRE(collection.status == PCI_ENUMERATION_OK && collected.count == 15);
    r = pci_execute_command_clear(executor_read, executor_write, executor_admit,
                                  &f, &collected, &t);
    EXEC_REQUIRE(r.status == PCI_COMMAND_OK && executor_transition(&collected, &t) == 1);
    for (unsigned volatile_status = 0; volatile_status < 2; ++volatile_status) {
        executor_reset(&f);
        f.volatile_status = volatile_status;
        r = pci_execute_command_clear(executor_read, executor_write, executor_admit,
                                      &f, &f.initial, &t);
        EXEC_REQUIRE(r.status == PCI_COMMAND_OK && r.step == 15 && t.count == 15);
        EXEC_REQUIRE(r.writes_completed == 15 && r.reads_completed == 240);
        EXEC_REQUIRE(executor_transition(&f.initial, &t) == 1);
        if (!volatile_status)
            for (unsigned j = 0; j < 375; ++j)
                EXEC_REQUIRE(t.words[j] == inventory_cases[0].words[285 + j]);
    }
    executor_reset(&f);
    f.readonly_lpc = 1;
    r = pci_execute_command_clear(executor_read, executor_write, executor_admit,
                                  &f, &f.initial, &t);
    EXEC_REQUIRE(r.status == PCI_COMMAND_READBACK_NONZERO && !t.count);
    EXEC_REQUIRE(r.step == 9 && r.bus == 0 && r.device == 31 && r.function == 0);
    EXEC_REQUIRE(r.offset == 4 && f.writes == 10 && f.reads == 146);
    EXEC_REQUIRE(r.writes_completed == 10 && r.reads_completed == 146);
    EXEC_REQUIRE(t.words[9 * 25 + 10] % 65536 == 7);
    ++negatives;
    for (unsigned i = 0; i < 15; ++i) {
        executor_reset(&f);
        f.initial.headers[i].words[0] ^= 1;
        r = pci_execute_command_clear(executor_read, executor_write, executor_admit,
                                      &f, &f.initial, &t);
        EXEC_REQUIRE(r.status == PCI_COMMAND_INVENTORY_REJECTED && r.admission != 1);
        EXEC_REQUIRE(!f.writes && !f.reads && !t.count);
        ++negatives;
    }
    /* Every write, every read, every stable dword, and every Command readback
     * can independently fail. Exact counters prove no later access occurred. */
    for (unsigned mode = 0; mode < 4; ++mode) {
        unsigned bound = (mode == 0 || mode == 3) ? 15 : 240;
        for (unsigned n = 0; n < bound; ++n) {
            if (mode == 2 && n % 16 == 1) continue;
            executor_reset(&f);
            if (mode == 0) f.fail_write = n;
            if (mode == 1) f.fail_read = n;
            if (mode == 2) f.drift_read = n;
            if (mode == 3) f.nonzero_step = n;
            t.count = 15;
            r = pci_execute_command_clear(executor_read, executor_write, executor_admit,
                                          &f, &f.initial, &t);
            unsigned step = (mode == 0 || mode == 3) ? n : n / 16;
            unsigned reads = mode == 0 ? step * 16 : mode == 3 ? step * 16 + 2 : n + 1;
            enum pci_command_status expected = mode == 0 ? PCI_COMMAND_WRITE_FAILED :
                mode == 1 ? PCI_COMMAND_READ_FAILED : mode == 2 ? PCI_COMMAND_REGISTER_CHANGED :
                PCI_COMMAND_READBACK_NONZERO;
            EXEC_REQUIRE(r.status == expected && r.step == step && !t.count);
            EXEC_REQUIRE(f.writes == step + 1 && f.reads == reads);
            EXEC_REQUIRE(r.writes_completed == step + (mode != 0));
            EXEC_REQUIRE(r.reads_completed == reads - (mode == 1));
            const uint64_t *target = &inventory_cases[0].words[285 + step * 25];
            EXEC_REQUIRE(r.bus == target[0] && r.device == target[1] && r.function == target[2]);
            EXEC_REQUIRE(r.offset == ((mode == 0 || mode == 3) ? 4 : (n % 16) * 4));
            ++negatives;
        }
    }
    for (unsigned n = 0; n <= 16; ++n) {
        if (n == 15) continue;
        executor_reset(&f);
        f.initial.count = n;
        r = pci_execute_command_clear(executor_read, executor_write, executor_admit,
                                      &f, &f.initial, &t);
        EXEC_REQUIRE(r.status == PCI_COMMAND_INVENTORY_REJECTED && !t.count);
        EXEC_REQUIRE(!f.writes && !f.reads);
        ++negatives;
    }
    for (unsigned n = 0; n < 5; ++n) {
        executor_reset(&f);
        r = pci_execute_command_clear(n == 0 ? NULL : executor_read,
            n == 1 ? NULL : executor_write, n == 2 ? NULL : executor_admit,
            &f, n == 3 ? NULL : &f.initial, n == 4 ? NULL : &t);
        EXEC_REQUIRE(r.status == PCI_COMMAND_INVALID_ARGUMENT && !f.writes && !f.reads);
        ++negatives;
    }
    printf("PCI command executor passed: 3 generated-C transitions, %u rejection cases\n", negatives);
}
