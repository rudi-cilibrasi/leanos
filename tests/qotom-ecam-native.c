#define _GNU_SOURCE
#include <assert.h>
#include <stdio.h>
#include <sys/mman.h>
#include <unistd.h>
#include "qotom-ecam-native.h"

int main(void) {
    long page = sysconf(_SC_PAGESIZE);
    assert(page >= 4096);
    uint8_t *mapping = mmap(0, (size_t)page * 2, PROT_NONE,
                            MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    assert(mapping != MAP_FAILED);
    uint32_t *source = (uint32_t *)(mapping + page - 4);
    const uint32_t words[] = {0, 1, UINT32_MAX, 0x80000000, 0xfedcba98};
    for (unsigned i = 0; i < sizeof(words)/sizeof(words[0]); ++i) {
        assert(mprotect(mapping, (size_t)page, PROT_READ | PROT_WRITE) == 0);
        *source = words[i];
        assert(mprotect(mapping, (size_t)page, PROT_READ) == 0);
        struct { uint32_t before, value, after; } output = {0x11223344, 42, 0x55667788};
        assert(lab_ecam_native_load32(0, (uintptr_t)source, &output.value) == 1);
        assert(output.before == 0x11223344 && output.after == 0x55667788);
        assert(output.value == words[i] && *source == words[i]);
    }
    assert(munmap(mapping, (size_t)page * 2) == 0);
    puts("ECAM native load: read-only source, guard-page boundary and exact private dword output PASS");
}
