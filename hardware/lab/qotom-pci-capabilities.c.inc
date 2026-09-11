#ifdef LEANOS_QOTOM_PCI_DIAGNOSTIC
#include "pci-capabilities.h"

/* Called only after exact native inventory acceptance. The prior scan has
 * disarmed the read window; enable it for each bounded collection and disable
 * it before emitting records or taking a terminal path. No config writes. */
static void lab_capture_pci_capabilities(
        const struct pci_enumeration_snapshot *snapshot) {
    for (uint32_t i = 0; i < snapshot->count; ++i) {
        struct pci_capability_snapshot caps;
        lab_ecam_window.armed = 1;
        struct pci_capability_result result = pci_collect_capabilities(
            qotom_ecam_read, &lab_ecam_reader, &snapshot->headers[i], &caps);
        lab_ecam_window.armed = 0;
        serial_puts("LEANOS-LAB/1 PCI-CAPS profile=conventional-v1 index=");
        serial_u64(i);
        serial_puts(" status="); serial_u64(result.status);
        serial_puts(" offset="); serial_u64(result.offset);
        serial_puts(" count="); serial_u64(caps.count); serial_putc('\n');
        for (uint32_t j = 0; j < caps.count; ++j) {
            serial_puts("LEANOS-LAB/1 PCI-CAP index="); serial_u64(i);
            serial_puts(" slot="); serial_u64(j);
            serial_puts(" offset="); serial_u64(caps.headers[j].offset);
            serial_puts(" raw="); serial_u64(caps.headers[j].raw);
            serial_putc('\n');
        }
        if (result.status != PCI_CAPABILITY_OK)
            pre_admission_fail("qotom-pci-capabilities");
    }
}
#endif
