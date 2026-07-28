#include <stdint.h>
#include <stdlib.h>
#include <string.h>

static int address_fixture(int selector) {
    volatile unsigned char *bytes = malloc(8);
    if (bytes == NULL)
        return 2;
    bytes[selector] = 1;
    free((void *)bytes);
    return 0;
}

static int undefined_fixture(int selector) {
    volatile uint64_t one = 1;
    volatile unsigned shift = (unsigned)selector;
    return (int)(one << shift);
}

int main(int argc, char **argv) {
    if (argc != 2)
        return 2;
    if (strcmp(argv[1], "address") == 0)
        return address_fixture(argc + 14);
    if (strcmp(argv[1], "undefined") == 0)
        return undefined_fixture((argc - 2) + 64);
    return 2;
}
