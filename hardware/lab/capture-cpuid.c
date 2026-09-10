/* Read-only x86 CPUID inventory. Pin the process externally when collecting. */
#include <stdint.h>
#include <stdio.h>

static uint32_t capture(uint32_t leaf, uint32_t subleaf) {
    uint32_t a, b, c, d;
    __asm__ volatile ("cpuid" : "=a"(a), "=b"(b), "=c"(c), "=d"(d)
                      : "a"(leaf), "c"(subleaf));
    printf("%08x\t%08x\t%08x\t%08x\t%08x\t%08x\n",
           leaf, subleaf, a, b, c, d);
    return a;
}

int main(void) {
    puts("leaf\tsubleaf\teax\tebx\tecx\tedx");
    uint32_t basic = capture(0, 0);
    if (basic >= 1) capture(1, 0);
    if (basic >= 7) capture(7, 0);
    if (basic >= 13) capture(13, 0);
    uint32_t extended = capture(0x80000000u, 0);
    if (extended >= 0x80000001u) capture(0x80000001u, 0);
    return ferror(stdout) ? 1 : 0;
}
