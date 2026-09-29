/* Differential-fuzz runner: executes device-program images with the
   deterministic device model of tests/WifiFuzz.lean and prints one summary
   line per image, which must equal the simulator's line for the same image.
   usage: fuzz-runner image.bin... */
#include <stdio.h>
#include <stdlib.h>
#include "wifi-exec.h"

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

int main(int argc, char **argv) {
    static uint8_t image[1 << 20];
    for (int k = 1; k < argc; ++k) {
        FILE *f = fopen(argv[k], "rb");
        if (!f) { perror(argv[k]); return 2; }
        size_t len = fread(image, 1, sizeof image, f);
        fclose(f);
        struct model m = { 0, 0, 0 };
        struct wifi_hooks h = { r32, r16, w32, w16, cr, cw, dl, pr, &m, ph };
        static struct wifi_vm vm;
        uint32_t code = 0, yields = 0;
        int s = wifi_start(&vm, image, (uint32_t)len);
        if (s) { printf("%d\n", s); continue; }
        /* Resume after every yield; the step budget is shared. */
        while ((s = wifi_resume(&vm, &h, FUZZ_MAX_STEPS, &code)) == WIFI_YIELD)
            yields = mix(yields, code);
        uint32_t scratch = 0x811c9dc5u;
        for (uint32_t i = 0; i < WIFI_SCRATCH_BYTES; ++i)
            scratch = (scratch ^ wifi_scratch[i]) * 0x01000193u;
        printf("%d %u", s, code);
        for (int i = 0; i < 16; ++i) printf(" %u", vm.r[i]);
        printf(" %u %u %u %u %u\n", m.prints, m.acc, m.n, scratch, yields);
    }
    return 0;
}
