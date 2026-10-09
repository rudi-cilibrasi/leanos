/* The deterministic device model of the differential fuzzer (tests/WifiFuzz.lean
   `model`) and the per-image summary line both executors must print.
   Shared by fuzz-runner.c (handwritten executor) and
   tests/device-program-exec-host.c (generated executor). Include after
   wifi-exec.h. */
#ifndef LEANOS_WIFI_FUZZ_MODEL_H
#define LEANOS_WIFI_FUZZ_MODEL_H

#include <stdio.h>

#define FUZZ_MAX_STEPS 4000u

struct model { uint32_t acc, n, prints; };

static uint32_t mix(uint32_t a, uint32_t b) { return (a ^ b) * 0x01000193u + 0x9e3779b9u; }

static uint32_t r32(void *c, uint32_t o) {
    struct model *m = c; m->n++;
    uint32_t v = mix(m->n, o ^ 0xa5a5a5a5u); m->acc = mix(m->acc, v ^ 1u); return v;
}
static uint16_t r16(void *c, uint32_t o) {
    struct model *m = c; m->n++;
    uint32_t v = mix(m->n, o ^ 0x3c3c3c3cu); m->acc = mix(m->acc, v ^ 2u); return (uint16_t)v;
}
static uint8_t r8(void *c, uint32_t o) {
    struct model *m = c; m->n++;
    uint32_t v = mix(m->n, o ^ 0x69696969u); m->acc = mix(m->acc, v ^ 7u); return (uint8_t)v;
}
static void w8(void *c, uint32_t o, uint8_t v) { struct model *m = c; m->acc = mix(mix(m->acc, o ^ 8u), v); }
static void w32(void *c, uint32_t o, uint32_t v) { struct model *m = c; m->acc = mix(mix(m->acc, o ^ 3u), v); }
static void w16(void *c, uint32_t o, uint16_t v) { struct model *m = c; m->acc = mix(mix(m->acc, o ^ 4u), v); }
static uint32_t cr(void *c, uint32_t o) {
    struct model *m = c; m->n++;
    uint32_t v = mix(m->n, o ^ 0x5a5a5a5au); m->acc = mix(m->acc, v ^ 5u); return v;
}
static void cw(void *c, uint32_t o, uint32_t v) { struct model *m = c; m->acc = mix(mix(m->acc, o ^ 6u), v); }
static void dl(void *c, uint32_t u) { (void)c; (void)u; }
static void pr(void *c, uint32_t t, uint32_t v) { struct model *m = c; m->prints = mix(mix(m->prints, t), v); }
static uint32_t ph(void *c, uint32_t o) { (void)c; return 0x01000000u + o; }

typedef int (*fuzz_resume_fn)(struct wifi_vm *, const struct wifi_hooks *, uint64_t, uint32_t *);

/* Run one image with `resume` (resuming after every yield; the step budget
   is shared) and write its summary line, without the newline, to `out`. */
static void fuzz_summary(const uint8_t *image, uint32_t len, fuzz_resume_fn resume,
                         char *out, size_t size) {
    struct model m = { 0, 0, 0 };
    struct wifi_hooks h = { r32, r16, w32, w16, cr, cw, dl, pr, &m, ph, r8, w8 };
    static struct wifi_vm vm;
    uint32_t code = 0, yields = 0;
    int s = wifi_start(&vm, image, len);
    if (s) { snprintf(out, size, "%d", s); return; }
    while ((s = resume(&vm, &h, FUZZ_MAX_STEPS, &code)) == WIFI_YIELD)
        yields = mix(yields, code);
    uint32_t scratch = 0x811c9dc5u;
    for (uint32_t i = 0; i < WIFI_SCRATCH_BYTES; ++i)
        scratch = (scratch ^ wifi_scratch[i]) * 0x01000193u;
    int at = snprintf(out, size, "%d %u", s, code);
    for (int i = 0; i < 16 && at > 0 && (size_t)at < size; ++i)
        at += snprintf(out + at, size - (size_t)at, " %u", vm.r[i]);
    if (at > 0 && (size_t)at < size)
        snprintf(out + at, size - (size_t)at, " %u %u %u %u %u", m.prints, m.acc, m.n, scratch, yields);
}

#endif
