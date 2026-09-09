/* FreeBSD/amd64 read-only probe for the observed Qotom Bay Trail watchdog.
 * No register writes, timer arming, driver attachment, or reboot.
 * Register definitions: FreeBSD releng/15.0 sys/dev/ichwd/ichwd.{c,h}.
 */
#include <sys/types.h>
#include <sys/ioctl.h>
#include <sys/mman.h>
#include <sys/pciio.h>
#include <machine/cpufunc.h>
#include <err.h>
#include <fcntl.h>
#include <stdint.h>
#include <stdio.h>
#include <unistd.h>

static uint32_t
pci_read(int fd, unsigned dev, int reg)
{
    struct pci_io request = {
        .pi_sel = {.pc_domain = 0, .pc_bus = 0, .pc_dev = dev, .pc_func = 0},
        .pi_reg = reg, .pi_width = 4
    };
    if (ioctl(fd, PCIOCREAD, &request) < 0)
        err(1, "PCI read");
    return request.pi_data;
}

int
main(void)
{
    /* FreeBSD requires write-open permission even for PCIOCREAD. */
    int pci = open("/dev/pci", O_RDWR);
    if (pci < 0)
        err(1, "/dev/pci");
    uint32_t host = pci_read(pci, 0, 0);
    uint32_t lpc = pci_read(pci, 31, 0);
    if (host != 0x0f008086 || lpc != 0x0f1c8086)
        errx(1, "unrecognized host/LPC identity; no I/O or memory reads");
    uint32_t acpi = pci_read(pci, 31, 0x40);
    uint32_t pbase = pci_read(pci, 31, 0x44);
    close(pci);
    /* Deliberately closed to the captured board's enabled decode values. */
    if (acpi != 0x403 || pbase != 0xfed03002)
        errx(1, "unexpected ACPI/PBASE register; no I/O or memory reads");
    int mem = open("/dev/mem", O_RDONLY);
    if (mem < 0)
        err(1, "/dev/mem");
    void *page = mmap(NULL, 4096, PROT_READ, MAP_SHARED, mem, 0xfed03000);
    if (page == MAP_FAILED)
        err(1, "map PMC read-only");
    uint32_t pmc = *(volatile const uint32_t *)((const char *)page + 8);
    munmap(page, 4096);
    close(mem);
    /* FreeBSD grants port instructions through /dev/io's open permission.
     * O_RDWR is required for that grant; only inl/inw are executed below. */
    int io = open("/dev/io", O_RDWR);
    if (io < 0)
        err(1, "/dev/io");
    uint32_t smi = inl(0x430);
    uint16_t count = inw(0x468);
    uint16_t timer = inw(0x472);
    uint16_t reload = inw(0x460);
    uint16_t status1 = inw(0x464);
    uint16_t status2 = inw(0x466);
    close(io);
    printf("host=%08x lpc=%08x acpi=%08x pbase=%08x\n", host, lpc, acpi, pbase);
    printf("pmc=%08x no_reboot=%u smi_en=%08x tco_smi=%u\n",
        pmc, !!(pmc & 0x10), smi, !!(smi & 0x2000));
    printf("tco1_cnt=%04x halted=%u locked=%u timer=%04x reload=%04x "
        "status1=%04x status2=%04x\n", count, !!(count & 0x800),
        !!(count & 0x1000), timer, reload, status1, status2);
    return 0;
}
