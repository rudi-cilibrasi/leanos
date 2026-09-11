#include "qotom-ecam-native.h"
extern uint64_t root[], directory[];
static uint64_t leaves[512] __attribute__((aligned(4096)));
static uint32_t first[1024] __attribute__((aligned(4096)));
static uint32_t second[1024] __attribute__((aligned(4096)));
static void put(const char *s) {
    while (*s) { __asm__ volatile ("outb %0, $0xe9" : : "a"(*s)); ++s; }
}
static __attribute__((noreturn)) void done(unsigned code) {
    __asm__ volatile ("outl %0, $0xf4" : : "a"(code));
    for (;;) __asm__ volatile ("cli; hlt");
}
#define CHECK(x) do { if (!(x)) { put("FAIL\n"); done(1); } } while (0)
static uint64_t msr(uint32_t index) {
    uint32_t lo, hi;
    __asm__ volatile ("rdmsr" : "=a"(lo), "=d"(hi) : "c"(index));
    return ((uint64_t)hi << 32) | lo;
}
void fixture_main(void) {
    struct lab_ecam_controls c = {11, 22, 33, 44, 55, 66};
    uint32_t a=1, b, e=0, d;
    __asm__ volatile ("cpuid" : "+a"(a), "=b"(b), "+c"(e), "=d"(d));
    int available = (d & 0x10020) == 0x10020;
    CHECK(lab_ecam_native_controls(0, &c) == available);
    if (!available) {
        CHECK(c.pat==11 && c.cr0==22 && c.cr3==33 && c.cr4==44 && c.efer==55 && c.rflags==66);
        put("UNAVAILABLE output=unchanged\n"); done(0);
    }
    uint64_t cr0, cr3, cr4;
    __asm__ volatile ("mov %%cr0,%0" : "=r"(cr0));
    __asm__ volatile ("mov %%cr3,%0" : "=r"(cr3));
    __asm__ volatile ("mov %%cr4,%0" : "=r"(cr4));
    CHECK(c.pat == msr(0x277) && c.efer == msr(0xc0000080));
    CHECK(c.cr0==cr0 && c.cr3==cr3 && c.cr4==cr4 && cr3==(uintptr_t)root);
    CHECK((c.rflags & 0x20202) == 2);
    /* Replace only the first huge RAM mapping with equivalent 4 KiB leaves. */
    for (unsigned i=0; i<512; ++i) leaves[i]=(uint64_t)i*4096 | 3;
    directory[0]=(uintptr_t)leaves | 3;
    __asm__ volatile ("mov %0,%%cr3" : : "r"(cr3) : "memory");
    const uint64_t aperture=0x180000;
    CHECK((uintptr_t)first < aperture && (uintptr_t)second < aperture);
    first[0]=0x12345678; second[0]=0xfedcba98;
    uint32_t value=0;
    volatile uint64_t *leaf=&leaves[aperture/4096];
    *leaf=(uintptr_t)first | 3;
    lab_ecam_native_invalidate(0, aperture);
    CHECK(lab_ecam_native_load32(0, aperture, &value) && value==first[0]);
    *leaf=(uintptr_t)second | 3;
    lab_ecam_native_invalidate(0, aperture);
    CHECK(lab_ecam_native_load32(0, aperture, &value) && value==second[0]);
    *leaf=aperture | 3;
    lab_ecam_native_invalidate(0, aperture);
    put("PASS controls=matched remap=observed restore=invalidated\n"); done(0);
}
