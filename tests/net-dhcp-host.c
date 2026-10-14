/* Hosted test of the DHCP subject's generated boundary (issue #556).

   1. leanos_frame_port_check (LeanOS.DhcpSubject.framePortCheck), the
      witness the dhcp-subject kernel calls on every frame copy, on fixed
      requests whose answers are written out here from the documented
      semantics.
   2. Differential: leanos_dhcp_step, the C the Lean compiler generates for
      LeanOS.Net.DhcpClient.step at the C hooks (LeanOS/Net/DhcpClientC.lean),
      over the same hooks subjects/dhcp/main.c defines, against the model
      reading DhcpClient.stepRecord on the vectors of tests/NetDhcpVectors.lean
      in $LEANOS_NET_DHCP_VECTORS.

   Each vector line is "<registers> <record hex> <sent hex | -> <registers
   after>", registers as ten comma-separated hex words. The record is placed
   in a 1536-byte buffer whose remaining bytes are a fixed pattern; the
   generated client must return the sent frame's length (0 for "-"), leave
   that frame at the start of the buffer, leave every byte past both the
   record and the frame unchanged, never touch the buffer or the registers
   out of range, and end with the expected registers. */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "boundary-abi.h"

extern void leanos_register_boundary_target(const char *, void *);

#define DHCP_FRAME_BUFFER 1536u
#define DHCP_REGISTERS 10u

static uint8_t dhcp_frame[DHCP_FRAME_BUFFER];
static uint64_t dhcp_regs[DHCP_REGISTERS];
static unsigned long dhcp_out_of_range;

uint64_t dhcp_gen_value(uint64_t t, uint64_t x);
uint64_t dhcp_gen_rd8(uint64_t t, uint32_t off);
uint64_t dhcp_gen_wr8(uint64_t t, uint32_t off, uint32_t v);
uint64_t dhcp_gen_ld(uint64_t t, uint32_t k);
uint64_t dhcp_gen_st(uint64_t t, uint32_t k, uint64_t v);

uint64_t dhcp_gen_value(uint64_t t, uint64_t x) { (void)t; return x; }

uint64_t dhcp_gen_rd8(uint64_t t, uint32_t off) {
    (void)t;
    if (off >= DHCP_FRAME_BUFFER) { ++dhcp_out_of_range; return 0; }
    return dhcp_frame[off];
}

uint64_t dhcp_gen_wr8(uint64_t t, uint32_t off, uint32_t v) {
    (void)t;
    if (off >= DHCP_FRAME_BUFFER) { ++dhcp_out_of_range; return 0; }
    dhcp_frame[off] = (uint8_t)v;
    return 0;
}

uint64_t dhcp_gen_ld(uint64_t t, uint32_t k) {
    (void)t;
    if (k >= DHCP_REGISTERS) { ++dhcp_out_of_range; return 0; }
    return dhcp_regs[k];
}

uint64_t dhcp_gen_st(uint64_t t, uint32_t k, uint64_t v) {
    (void)t;
    if (k >= DHCP_REGISTERS) { ++dhcp_out_of_range; return 0; }
    dhcp_regs[k] = v;
    return 0;
}

static int unhex(const char *s, uint8_t *out, size_t cap, size_t *len) {
    size_t n = strlen(s);
    if (n % 2 || n / 2 > cap) return -1;
    for (size_t i = 0; i < n / 2; ++i) {
        unsigned v;
        if (sscanf(s + 2 * i, "%2x", &v) != 1) return -1;
        out[i] = (uint8_t)v;
    }
    *len = n / 2;
    return 0;
}

static int unregs(const char *s, uint64_t *out) {
    for (unsigned k = 0; k < DHCP_REGISTERS; ++k) {
        char *end = NULL;
        out[k] = strtoull(s, &end, 16);
        if (end == s) return -1;
        if (k + 1 < DHCP_REGISTERS) {
            if (*end != ',') return -1;
            s = end + 1;
        } else if (*end != 0) {
            return -1;
        }
    }
    return 0;
}

/* The port witness: subject, request (op | pending << 8 | route << 16 |
   owner << 24), address, length, window [base, limit), expected answer. */
struct port_case {
    uint64_t subject, request, addr, len, base, limit, expected;
    const char *name;
};

#define REQ(op, pending, route, owner) \
    ((uint64_t)(op) | (uint64_t)(pending) << 8 | (uint64_t)(route) << 16 | (uint64_t)(owner) << 24)

static int check_port_witness(void) {
    static const struct port_case cases[] = {
        { 2, REQ(1, 1, 2, 2), 0x40800, 6, 0x40000, 0x41000, 0, "DHCP fetch of the link record" },
        { 2, REQ(1, 1, 2, 2), 0x40a16, 1514, 0x40000, 0x41000, 0, "DHCP fetch ending at its window's end" },
        { 3, REQ(1, 1, 3, 3), 0x42800, 60, 0x42000, 0x43000, 0, "echo fetch after the hand-off" },
        { 1, REQ(1, 1, 2, 1), 0x40800, 60, 0x40000, 0x41000, 1, "fetch by the driver subject" },
        { 4, REQ(1, 1, 2, 2), 0x40800, 60, 0x40000, 0x41000, 1, "fetch by another subject" },
        { 2, REQ(1, 1, 2, 3), 0x42800, 60, 0x42000, 0x43000, 2, "DHCP fetch into the echo window" },
        { 3, REQ(1, 1, 3, 2), 0x40800, 60, 0x40000, 0x41000, 2, "echo fetch into the DHCP window" },
        { 3, REQ(1, 1, 2, 3), 0x42800, 60, 0x42000, 0x43000, 3, "echo fetch before the hand-off" },
        { 2, REQ(1, 1, 3, 2), 0x40800, 60, 0x40000, 0x41000, 3, "DHCP fetch after the hand-off" },
        { 2, REQ(1, 0, 2, 2), 0x40800, 60, 0x40000, 0x41000, 4, "fetch with no record pending" },
        { 2, REQ(1, 1, 2, 2), 0x40000, 1515, 0x40000, 0x41000, 5, "fetch longer than a frame" },
        { 2, REQ(1, 1, 2, 2), 0x3ffff, 60, 0x40000, 0x41000, 6, "fetch below the window" },
        { 2, REQ(1, 1, 2, 2), 0x40fd0, 60, 0x40000, 0x41000, 6, "fetch across the window's end" },
        { 2, REQ(1, 1, 2, 2), UINT64_C(0xfffffffffffffff0), 60, 0x40000, 0x41000, 6, "fetch wrapping" },
        { 2, REQ(2, 0, 2, 2), 0x40800, 342, 0x40000, 0x41000, 0, "DHCP send of a DISCOVER" },
        { 3, REQ(2, 0, 3, 3), 0x42800, 42, 0x42000, 0x43000, 0, "echo send of an ARP reply" },
        { 2, REQ(2, 1, 2, 2), 0x40800, 342, 0x40000, 0x41000, 4, "send with a frame pending" },
        { 2, REQ(2, 0, 2, 2), 0x40800, 13, 0x40000, 0x41000, 5, "send shorter than a frame" },
        { 2, REQ(2, 0, 2, 2), 0x40800, 1515, 0x40000, 0x41000, 5, "send longer than a frame" },
        { 2, REQ(2, 0, 2, 2), 0x40ff0, 42, 0x40000, 0x41000, 6, "send across the window's end" },
        { 3, REQ(2, 0, 2, 3), 0x42800, 42, 0x42000, 0x43000, 3, "echo send before the hand-off" },
        { 1, REQ(2, 0, 2, 1), 0x40800, 42, 0x40000, 0x41000, 1, "send by the driver subject" },
        { 2, REQ(3, 0, 2, 2), 0x40800, 42, 0x40000, 0x41000, 7, "unknown operation" },
    };
    for (size_t i = 0; i < sizeof cases / sizeof cases[0]; ++i) {
        const struct port_case *c = &cases[i];
        uint64_t got = leanos_frame_port_check(c->subject, c->request, c->addr,
            c->len, c->base, c->limit);
        if (got != c->expected) {
            fprintf(stderr, "error: frame port witness, %s: %llu, expected %llu\n",
                    c->name, (unsigned long long)got, (unsigned long long)c->expected);
            return 1;
        }
    }
    printf("frame port witness: %zu requests answered as documented\n",
           sizeof cases / sizeof cases[0]);
    return 0;
}

int main(void) {
    leanos_register_boundary_target("leanos_frame_port_check",
        (void *)(uintptr_t)&leanos_frame_port_check);
    leanos_register_boundary_target("leanos_dhcp_step",
        (void *)(uintptr_t)&leanos_dhcp_step);
    if (check_port_witness()) return 1;
    const char *path = getenv("LEANOS_NET_DHCP_VECTORS");
    if (!path) {
        fprintf(stderr, "error: LEANOS_NET_DHCP_VECTORS is unset\n");
        return 2;
    }
    FILE *vectors = fopen(path, "r");
    if (!vectors) { perror(path); return 2; }
    static char line[8192], before_s[512], record_hex[4096], sent_hex[4096], after_s[512];
    static uint8_t record[DHCP_FRAME_BUFFER], sent[DHCP_FRAME_BUFFER];
    static uint8_t pattern[DHCP_FRAME_BUFFER];
    uint64_t after[DHCP_REGISTERS];
    unsigned long count = 0, sends = 0;
    while (fgets(line, sizeof line, vectors)) {
        size_t record_len = 0, sent_len = 0;
        if (sscanf(line, "%511s %4095s %4095s %511s", before_s, record_hex, sent_hex,
                   after_s) != 4 ||
            unregs(before_s, dhcp_regs) || unregs(after_s, after) ||
            unhex(record_hex, record, sizeof record, &record_len) ||
            (strcmp(sent_hex, "-") != 0 &&
             unhex(sent_hex, sent, sizeof sent, &sent_len))) {
            fprintf(stderr, "error: malformed vector %lu\n", count + 1);
            return 1;
        }
        for (size_t i = 0; i < DHCP_FRAME_BUFFER; ++i)
            pattern[i] = dhcp_frame[i] = (uint8_t)(0xa5u ^ i);
        memcpy(dhcp_frame, record, record_len);
        memcpy(pattern, record, record_len);
        uint64_t got = leanos_dhcp_step(0, record_len);
        size_t touched = sent_len > record_len ? sent_len : record_len;
        int bad = got != sent_len || dhcp_out_of_range != 0 ||
            memcmp(dhcp_regs, after, sizeof after) != 0;
        if (!bad && sent_len)
            bad = memcmp(dhcp_frame, sent, sent_len) != 0 ||
                memcmp(dhcp_frame + touched, pattern + touched,
                       DHCP_FRAME_BUFFER - touched) != 0;
        if (!bad && !sent_len)
            bad = memcmp(dhcp_frame, pattern, DHCP_FRAME_BUFFER) != 0;
        if (bad) {
            fprintf(stderr, "error: vector %lu: generated client sent %llu bytes, model %zu\n",
                    count + 1, (unsigned long long)got, sent_len);
            return 1;
        }
        ++count;
        if (sent_len) ++sends;
    }
    fclose(vectors);
    if (count == 0) {
        fprintf(stderr, "error: no vectors\n");
        return 1;
    }
    printf("generated client: %lu vectors, %lu frames sent, all equal to the model\n",
           count, sends);
    return 0;
}
