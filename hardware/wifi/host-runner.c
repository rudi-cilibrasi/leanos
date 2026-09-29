/* Hosted runner for computation-only WiFi programs (no device): used to
   cross-check the C executor against LeanOS/Wifi/Sim.lean.
   usage: host-runner program.bin */
#include <stdio.h>
#include <stdlib.h>
#include "wifi-exec.h"

static uint32_t r32(void *c, uint32_t o) { (void)c; (void)o; return 0; }
static uint16_t r16(void *c, uint32_t o) { (void)c; (void)o; return 0; }
static void w32(void *c, uint32_t o, uint32_t v) { (void)c; (void)o; (void)v; }
static void w16(void *c, uint32_t o, uint16_t v) { (void)c; (void)o; (void)v; }
static uint32_t cr(void *c, uint32_t o) { (void)c; (void)o; return 0; }
static void cw(void *c, uint32_t o, uint32_t v) { (void)c; (void)o; (void)v; }
static void dl(void *c, uint32_t u) { (void)c; (void)u; }
static uint8_t r8(void *c, uint32_t o) { (void)c; (void)o; return 0; }
static void w8(void *c, uint32_t o, uint8_t v) { (void)c; (void)o; (void)v; }
static void pr(void *c, uint32_t t, uint32_t v) { (void)c; printf("WIFI %04x 0x%08x\n", t, v); }

int main(int argc, char **argv) {
    if (argc != 2) return 2;
    FILE *f = fopen(argv[1], "rb");
    if (!f) { perror(argv[1]); return 2; }
    static uint8_t image[4 << 20];
    size_t n = fread(image, 1, sizeof image, f);
    fclose(f);
    struct wifi_hooks h = { r32, r16, w32, w16, cr, cw, dl, pr, 0, 0, r8, w8 };
    uint32_t code = 0;
    int s = wifi_exec(image, (uint32_t)n, &h, 1000000000ull, &code);
    printf("WIFI-END status=%d code=0x%x\n", s, code);
    return s;
}
