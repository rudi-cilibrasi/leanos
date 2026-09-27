/* FreeBSD userland development runner for Lean-authored WiFi programs.

   Lab-only: maps the Broadcom BAR0 through /dev/mem and reaches its PCI
   configuration space through /dev/pci, then executes a program image
   produced by `lake exe leanos-wifi-gen`. Requires root. It performs no DMA.

   usage: fbsd-runner [-t] [-s bus:dev:fn] program.bin */
#include <sys/types.h>
#include <sys/ioctl.h>
#include <sys/mman.h>
#include <sys/pciio.h>
#include <sys/stat.h>
#include <errno.h>
#include <fcntl.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <unistd.h>

#include "wifi-exec.h"

struct run {
    int pci_fd;
    struct pcisel sel;
    volatile uint8_t *bar;
    int trace;
    unsigned long accesses;
};

static uint32_t cfg_read32(void *ctx, uint32_t off) {
    struct run *r = ctx;
    struct pci_io io = { .pi_sel = r->sel, .pi_reg = (int)off, .pi_width = 4 };
    if (ioctl(r->pci_fd, PCIOCREAD, &io) < 0) { perror("PCIOCREAD"); exit(3); }
    if (r->trace) printf("  cfg  R32 %03x -> %08x\n", off, io.pi_data);
    return io.pi_data;
}

static void cfg_write32(void *ctx, uint32_t off, uint32_t value) {
    struct run *r = ctx;
    struct pci_io io = { .pi_sel = r->sel, .pi_reg = (int)off, .pi_width = 4, .pi_data = value };
    if (r->trace) printf("  cfg  W32 %03x <- %08x\n", off, value);
    if (ioctl(r->pci_fd, PCIOCWRITE, &io) < 0) { perror("PCIOCWRITE"); exit(3); }
}

static uint32_t mmio_read32(void *ctx, uint32_t off) {
    struct run *r = ctx;
    uint32_t v = *(volatile uint32_t *)(r->bar + off);
    r->accesses++;
    if (r->trace) printf("  mmio R32 %04x -> %08x\n", off, v);
    return v;
}

static uint16_t mmio_read16(void *ctx, uint32_t off) {
    struct run *r = ctx;
    uint16_t v = *(volatile uint16_t *)(r->bar + off);
    r->accesses++;
    if (r->trace) printf("  mmio R16 %04x -> %04x\n", off, v);
    return v;
}

static void mmio_write32(void *ctx, uint32_t off, uint32_t value) {
    struct run *r = ctx;
    r->accesses++;
    if (r->trace) printf("  mmio W32 %04x <- %08x\n", off, value);
    *(volatile uint32_t *)(r->bar + off) = value;
}

static void mmio_write16(void *ctx, uint32_t off, uint16_t value) {
    struct run *r = ctx;
    r->accesses++;
    if (r->trace) printf("  mmio W16 %04x <- %04x\n", off, value);
    *(volatile uint16_t *)(r->bar + off) = value;
}

static void delay_us(void *ctx, uint32_t us) {
    (void)ctx;
    struct timespec start, now;
    clock_gettime(CLOCK_MONOTONIC, &start);
    if (us >= 2000) { usleep(us); return; }
    do clock_gettime(CLOCK_MONOTONIC, &now);
    while ((now.tv_sec - start.tv_sec) * 1000000L +
           (now.tv_nsec - start.tv_nsec) / 1000L < (long)us);
}

static void print(void *ctx, uint32_t tag, uint32_t value) {
    (void)ctx;
    printf("WIFI %04x 0x%08x\n", tag, value);
    fflush(stdout);
}

int main(int argc, char **argv) {
    struct run r = {0};
    unsigned bus = 2, dev = 0, fn = 0;
    int opt;
    while ((opt = getopt(argc, argv, "ts:")) != -1) {
        if (opt == 't') r.trace = 1;
        else if (opt == 's' && sscanf(optarg, "%u:%u:%u", &bus, &dev, &fn) == 3) ;
        else { fprintf(stderr, "usage: %s [-t] [-s b:d:f] program.bin\n", argv[0]); return 2; }
    }
    if (optind != argc - 1) { fprintf(stderr, "missing program\n"); return 2; }
    int pfd = open(argv[optind], O_RDONLY);
    struct stat st;
    if (pfd < 0 || fstat(pfd, &st) < 0) { perror(argv[optind]); return 2; }
    uint8_t *image = malloc((size_t)st.st_size);
    if (read(pfd, image, (size_t)st.st_size) != st.st_size) { perror("read"); return 2; }
    r.sel = (struct pcisel){ .pc_domain = 0, .pc_bus = (uint8_t)bus, .pc_dev = (uint8_t)dev, .pc_func = (uint8_t)fn };
    r.pci_fd = open("/dev/pci", O_RDWR);
    if (r.pci_fd < 0) { perror("/dev/pci"); return 2; }
    uint32_t id = cfg_read32(&r, 0), bar0 = cfg_read32(&r, 0x10);
    if (id != 0x435314e4u) { fprintf(stderr, "unexpected device %08x\n", id); return 2; }
    int mfd = open("/dev/mem", O_RDWR);
    if (mfd < 0) { perror("/dev/mem"); return 2; }
    r.bar = mmap(0, WIFI_WINDOW_BYTES, PROT_READ | PROT_WRITE, MAP_SHARED, mfd, bar0 & ~0xfu);
    if (r.bar == MAP_FAILED) { perror("mmap"); return 2; }
    struct wifi_hooks h = { mmio_read32, mmio_read16, mmio_write32, mmio_write16,
                            cfg_read32, cfg_write32, delay_us, print, &r };
    uint32_t code = 0;
    int status = wifi_exec(image, (uint32_t)st.st_size, &h, 400000000ull, &code);
    printf("WIFI-END status=%d code=0x%x accesses=%lu\n", status, code, r.accesses);
    return status == WIFI_HALT ? 0 : 1;
}
