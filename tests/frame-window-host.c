/* Hosted test of the frame copy window's generated operand (issue #569).

   leanos_frame_window_operand (LeanOS.FrameCopyWindow.frameWindowOperand)
   is the export the frame-window kernel calls on every frame copy: for a
   request the frame port witness accepts, with the request's window owner as
   the caller, over a window of the reviewed geometry, it returns the alias
   address of the buffer, slot * 4096 + (addr - base); otherwise 0.

   1. Fixed requests whose answers are written out here from the documented
      semantics: every refusal reason of the port witness, every geometry
      rule, one- and two-page windows, the first and last byte of a window.
   2. Differential: 200000 pseudo-random requests near the boundaries
      against a C restatement of the documented semantics, and against the
      port witness leanos_frame_port_check itself. */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include "boundary-abi.h"

extern void leanos_register_boundary_target(const char *, void *);

static unsigned long failures, cases;

static uint64_t request(uint64_t op, uint64_t pending, uint64_t route, uint64_t owner) {
    return op | pending << 8 | (route & 0xffu) << 16 | (owner & 0xffu) << 24;
}

static void expect(const char *name, uint64_t got, uint64_t want) {
    ++cases;
    if (got != want) {
        ++failures;
        fprintf(stderr, "FAIL %s: got %#llx want %#llx\n", name,
                (unsigned long long)got, (unsigned long long)want);
    }
}

/* The documented port decision (DhcpSubject.framePortDecide). */
static uint64_t port_decide(uint64_t subject, uint64_t req, uint64_t addr, uint64_t len,
                            uint64_t base, uint64_t limit) {
    uint64_t op = req & 0xff, pending = (req >> 8) & 0xff, route = (req >> 16) & 0xff;
    uint64_t owner = (req >> 24) & 0xff;
    int range = base <= addr && addr <= limit && len <= limit - addr;
    if (subject != 2 && subject != 3) return 1;
    if (owner != subject) return 2;
    if (route != subject) return 3;
    if (op == 1) {
        if (pending != 1) return 4;
        if (len > 1514) return 5;
        return range ? 0 : 6;
    }
    if (op == 2) {
        if (pending != 0) return 4;
        if (len < 14 || len > 1514) return 5;
        return range ? 0 : 6;
    }
    return 7;
}

/* The documented geometry (FrameCopyWindow.geometryOk). */
static int geometry_ok(uint64_t base, uint64_t limit, uint64_t slot) {
    return base % 4096 == 0 && base < limit && limit <= 0x1000000u &&
        (limit - base == 4096 || limit - base == 8192) && slot != 0 && slot <= 4096 &&
        slot + (limit - base) / 4096 <= 4096;
}

static uint64_t operand_spec(uint64_t slot, uint64_t req, uint64_t addr, uint64_t len,
                             uint64_t base, uint64_t limit) {
    uint64_t owner = (req >> 24) & 0xff;
    if (port_decide(owner, req, addr, len, base, limit) != 0 || !geometry_ok(base, limit, slot))
        return 0;
    return slot * 4096 + (addr - base);
}

static uint64_t rng_state = 0x5eed569u;
static uint64_t next(void) {
    rng_state = rng_state * 6364136223846793005ull + 1442695040888963407ull;
    return rng_state >> 11;
}

static uint64_t pick(const uint64_t *values, unsigned count) {
    return values[next() % count];
}

int main(void) {
    leanos_register_boundary_target("leanos_frame_window_operand",
                                    (void *)leanos_frame_window_operand);
    const uint64_t base = 0x200000, limit = 0x201000, slot = 0x150;
    const uint64_t fetch2 = request(1, 1, 2, 2), send2 = request(2, 0, 2, 2);
    const uint64_t fetch3 = request(1, 1, 3, 3);

    /* Accepted: the alias of the buffer. */
    expect("fetch-first-byte", leanos_frame_window_operand(slot, fetch2, base, 6, base, limit),
           slot * 4096);
    expect("fetch-offset", leanos_frame_window_operand(slot, fetch2, base + 100, 342, base, limit),
           slot * 4096 + 100);
    expect("fetch-last-bytes",
           leanos_frame_window_operand(slot, fetch2, limit - 1514, 1514, base, limit),
           slot * 4096 + 4096 - 1514);
    expect("send-frame", leanos_frame_window_operand(slot, send2, base + 8, 342, base, limit),
           slot * 4096 + 8);
    expect("echo-fetch", leanos_frame_window_operand(slot, fetch3, base, 60, base, limit),
           slot * 4096);
    expect("two-page-window",
           leanos_frame_window_operand(slot, fetch2, base + 4000, 1514, base, base + 8192),
           slot * 4096 + 4000);
    expect("empty-fetch", leanos_frame_window_operand(slot, fetch2, limit, 0, base, limit),
           slot * 4096 + 4096);

    /* Refused by the port witness. */
    expect("driver", leanos_frame_window_operand(slot, request(1, 1, 2, 1), base, 6, base, limit), 0);
    expect("unrouted", leanos_frame_window_operand(slot, request(1, 1, 3, 2), base, 6, base, limit), 0);
    expect("fetch-not-pending", leanos_frame_window_operand(slot, request(1, 0, 2, 2), base, 6, base, limit), 0);
    expect("send-pending", leanos_frame_window_operand(slot, request(2, 1, 2, 2), base, 60, base, limit), 0);
    expect("send-short", leanos_frame_window_operand(slot, send2, base, 13, base, limit), 0);
    expect("fetch-long", leanos_frame_window_operand(slot, fetch2, base, 1515, base, limit), 0);
    expect("outside-below", leanos_frame_window_operand(slot, fetch2, base - 1, 6, base, limit), 0);
    expect("outside-above", leanos_frame_window_operand(slot, fetch2, limit - 5, 6, base, limit), 0);
    expect("unknown-op", leanos_frame_window_operand(slot, request(3, 1, 2, 2), base, 6, base, limit), 0);

    /* Refused by the geometry. */
    expect("unaligned", leanos_frame_window_operand(slot, fetch2, base + 8, 6, base + 8, limit + 8), 0);
    expect("three-pages", leanos_frame_window_operand(slot, fetch2, base, 6, base, base + 12288), 0);
    expect("half-page", leanos_frame_window_operand(slot, fetch2, base, 6, base, base + 2048), 0);
    expect("slot-zero", leanos_frame_window_operand(0, fetch2, base, 6, base, limit), 0);
    expect("slot-past-arena", leanos_frame_window_operand(4096, fetch2, base, 6, base, limit), 0);
    expect("slot-last", leanos_frame_window_operand(4095, fetch2, base, 6, base, limit), 4095u * 4096);
    expect("two-page-slot-last",
           leanos_frame_window_operand(4095, fetch2, base, 6, base, base + 8192), 0);
    expect("above-arena", leanos_frame_window_operand(slot, fetch2, 0x1000000, 6, 0x1000000, 0x1001000), 0);
    expect("huge-slot", leanos_frame_window_operand(UINT64_C(1) << 40, fetch2, base, 6, base, limit), 0);

    /* Differential, near every boundary. */
    const uint64_t bases[] = { 0, 0x1000, 0x200000, 0x200008, 0xfff000, 0xffe000, 0x1000000,
                               UINT64_C(0xfffffffffffff000) };
    const uint64_t spans[] = { 0, 2048, 4096, 8192, 12288, 4095 };
    const uint64_t slots[] = { 0, 1, 0x150, 4094, 4095, 4096, 4097, UINT64_C(1) << 32 };
    const uint64_t lens[] = { 0, 1, 6, 13, 14, 342, 1514, 1515, 4096, UINT64_MAX };
    for (unsigned i = 0; i < 200000; ++i) {
        uint64_t b = pick(bases, 8), l = b + pick(spans, 6), s = pick(slots, 8);
        uint64_t op = 1 + next() % 3, pending = next() % 2, route = 1 + next() % 3;
        uint64_t owner = 1 + next() % 3;
        uint64_t req = request(op, pending, route, owner);
        uint64_t len = pick(lens, 10);
        uint64_t addr = b + (next() % 3 == 0 ? (uint64_t)-1 : next() % 8200);
        uint64_t got = leanos_frame_window_operand(s, req, addr, len, b, l);
        uint64_t want = operand_spec(s, req, addr, len, b, l);
        ++cases;
        if (got != want) {
            ++failures;
            if (failures < 10)
                fprintf(stderr, "FAIL random %u: slot=%#llx req=%#llx addr=%#llx len=%llu "
                        "base=%#llx limit=%#llx got=%#llx want=%#llx\n", i,
                        (unsigned long long)s, (unsigned long long)req,
                        (unsigned long long)addr, (unsigned long long)len,
                        (unsigned long long)b, (unsigned long long)l,
                        (unsigned long long)got, (unsigned long long)want);
        }
        uint64_t port = leanos_frame_port_check(owner, req, addr, len, b, l);
        ++cases;
        if ((got != 0) != (port == 0 && geometry_ok(b, l, s))) ++failures;
    }
    if (failures != 0) {
        fprintf(stderr, "frame window operand: %lu of %lu cases failed\n", failures, cases);
        return 1;
    }
    printf("Frame window operand: %lu cases PASS\n", cases);
    return 0;
}
