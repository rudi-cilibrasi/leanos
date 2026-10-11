/* Hosted test of the network subject's generated boundary (issue #450).

   1. leanos_frame_copy_check (LeanOS.NetworkSubject.frameCopyCheck), the
      witness the kernel calls on every frame copy, on fixed requests whose
      answers are written out here from the documented semantics.
   2. Differential: leanos_net_reply, the C the Lean compiler generates for
      LeanOS.Net.Echo.reply at the C hooks (LeanOS/Net/EchoC.lean), over the
      same hooks subjects/net/main.c defines, against the reference
      LeanOS.Net.Echo.replyFrame on the vectors of tests/NetEchoVectors.lean
      in $LEANOS_NET_ECHO_VECTORS.

   Each vector line is "<frame hex> <reply hex | ->". The frame is placed in a
   1536-byte buffer whose remaining bytes are a fixed pattern; the generated
   responder must return the reference reply's length (0 for "-"), leave the
   reference reply in the buffer, and leave every byte past the frame
   unchanged (for no reply: the whole buffer). */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "boundary-abi.h"

extern void leanos_register_boundary_target(const char *, void *);

#define NET_FRAME_BUFFER 1536u
#define NET_HOST_MAC UINT64_C(0x02004c45414e)
#define NET_HOST_IP UINT64_C(0x0a00020f)

static uint8_t net_frame[NET_FRAME_BUFFER];
static unsigned long net_out_of_range;

uint64_t net_gen_value(uint64_t t, uint64_t x);
uint64_t net_gen_rd8(uint64_t t, uint32_t off);
uint64_t net_gen_wr8(uint64_t t, uint32_t off, uint32_t v);

uint64_t net_gen_value(uint64_t t, uint64_t x) { (void)t; return x; }

uint64_t net_gen_rd8(uint64_t t, uint32_t off) {
    (void)t;
    if (off >= NET_FRAME_BUFFER) { ++net_out_of_range; return 0; }
    return net_frame[off];
}

uint64_t net_gen_wr8(uint64_t t, uint32_t off, uint32_t v) {
    (void)t;
    if (off >= NET_FRAME_BUFFER) { ++net_out_of_range; return 0; }
    net_frame[off] = (uint8_t)v;
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

/* The frame copy witness: subject, request (op | pending << 8), address,
   length, window [base, limit), and the expected answer. */
struct copy_case {
    uint64_t subject, request, addr, len, base, limit, expected;
    const char *name;
};

static int check_copy_witness(void) {
    static const struct copy_case cases[] = {
        { 3, 0x101, 0x40800, 60, 0x40000, 0x41000, 0, "fetch accepted" },
        { 3, 0x101, 0x40a16, 1514, 0x40000, 0x41000, 0, "fetch ending at the window end" },
        { 1, 0x101, 0x40800, 60, 0x40000, 0x41000, 1, "fetch by the driver subject" },
        { 2, 0x101, 0x40800, 60, 0x40000, 0x41000, 1, "fetch by a bystander" },
        { 3, 0x001, 0x40800, 60, 0x40000, 0x41000, 2, "fetch with no frame pending" },
        { 3, 0x101, 0x40000, 1515, 0x40000, 0x41000, 3, "fetch longer than a frame" },
        { 3, 0x101, 0x3ffff, 60, 0x40000, 0x41000, 4, "fetch below the window" },
        { 3, 0x101, 0x40fd0, 60, 0x40000, 0x41000, 4, "fetch across the window's end" },
        { 3, 0x101, UINT64_C(0xfffffffffffffff0), 60, 0x40000, 0x41000, 4, "fetch wrapping" },
        { 3, 0x002, 0x40800, 42, 0x40000, 0x41000, 0, "send accepted" },
        { 3, 0x102, 0x40800, 42, 0x40000, 0x41000, 2, "send with a reply pending" },
        { 3, 0x002, 0x40800, 13, 0x40000, 0x41000, 3, "send shorter than a frame" },
        { 3, 0x002, 0x40800, 1515, 0x40000, 0x41000, 3, "send longer than a frame" },
        { 3, 0x002, 0x40ff0, 42, 0x40000, 0x41000, 4, "send across the window's end" },
        { 1, 0x002, 0x40800, 42, 0x40000, 0x41000, 1, "send by the driver subject" },
        { 3, 0x003, 0x40800, 42, 0x40000, 0x41000, 5, "unknown operation" },
    };
    for (size_t i = 0; i < sizeof cases / sizeof cases[0]; ++i) {
        const struct copy_case *c = &cases[i];
        uint64_t got = leanos_frame_copy_check(c->subject, c->request, c->addr,
            c->len, c->base, c->limit);
        if (got != c->expected) {
            fprintf(stderr, "error: frame copy witness, %s: %llu, expected %llu\n",
                    c->name, (unsigned long long)got, (unsigned long long)c->expected);
            return 1;
        }
    }
    printf("frame copy witness: %zu requests answered as documented\n",
           sizeof cases / sizeof cases[0]);
    return 0;
}

int main(void) {
    leanos_register_boundary_target("leanos_frame_copy_check",
        (void *)(uintptr_t)&leanos_frame_copy_check);
    leanos_register_boundary_target("leanos_net_reply",
        (void *)(uintptr_t)&leanos_net_reply);
    if (check_copy_witness()) return 1;
    const char *path = getenv("LEANOS_NET_ECHO_VECTORS");
    if (!path) {
        fprintf(stderr, "error: LEANOS_NET_ECHO_VECTORS is unset\n");
        return 2;
    }
    FILE *vectors = fopen(path, "r");
    if (!vectors) { perror(path); return 2; }
    static char line[8192], frame_hex[4096], reply_hex[4096];
    static uint8_t frame[NET_FRAME_BUFFER], reply[NET_FRAME_BUFFER];
    static uint8_t pattern[NET_FRAME_BUFFER];
    unsigned long count = 0, replied = 0;
    while (fgets(line, sizeof line, vectors)) {
        size_t frame_len = 0, reply_len = 0;
        if (sscanf(line, "%4095s %4095s", frame_hex, reply_hex) != 2 ||
            unhex(frame_hex, frame, sizeof frame, &frame_len) ||
            (strcmp(reply_hex, "-") != 0 &&
             unhex(reply_hex, reply, sizeof reply, &reply_len))) {
            fprintf(stderr, "error: malformed vector %lu\n", count + 1);
            return 1;
        }
        for (size_t i = 0; i < NET_FRAME_BUFFER; ++i)
            pattern[i] = net_frame[i] = (uint8_t)(0xa5u ^ i);
        memcpy(net_frame, frame, frame_len);
        memcpy(pattern, frame, frame_len);
        uint64_t got = leanos_net_reply(0, frame_len, NET_HOST_MAC, NET_HOST_IP);
        int bad = got != reply_len || net_out_of_range != 0;
        if (!bad && reply_len)
            bad = memcmp(net_frame, reply, reply_len) != 0 ||
                memcmp(net_frame + frame_len, pattern + frame_len,
                       NET_FRAME_BUFFER - frame_len) != 0;
        if (!bad && !reply_len)
            bad = memcmp(net_frame, pattern, NET_FRAME_BUFFER) != 0;
        if (bad) {
            fprintf(stderr, "error: vector %lu: generated reply length %llu, reference %zu\n",
                    count + 1, (unsigned long long)got, reply_len);
            return 1;
        }
        ++count;
        if (reply_len) ++replied;
    }
    fclose(vectors);
    if (count == 0) {
        fprintf(stderr, "error: no vectors\n");
        return 1;
    }
    printf("generated responder: %lu vectors, %lu replies, all equal to the reference\n",
           count, replied);
    return 0;
}
