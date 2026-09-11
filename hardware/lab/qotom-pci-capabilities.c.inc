#ifdef LEANOS_QOTOM_PCI_DIAGNOSTIC
#include "pci-capabilities.h"
#ifdef LEANOS_QOTOM_AF_OBSERVATION
#include "pci-af-observation.h"
#endif

/* Called only after exact native inventory acceptance. The prior scan has
 * disarmed the read window; enable it for each bounded collection and disable
 * it before emitting records or taking a terminal path. No config writes. */
static void lab_capture_pci_capabilities(
        const struct pci_enumeration_snapshot *snapshot) {
#ifdef LEANOS_QOTOM_AF_OBSERVATION
    static struct pci_capability_snapshot retained[PCI_ENUMERATION_CAPACITY];
#endif
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
#ifdef LEANOS_QOTOM_AF_OBSERVATION
        retained[i] = caps;
#endif
    }
#ifdef LEANOS_QOTOM_AF_OBSERVATION
    for (uint32_t i = 0; i < snapshot->count; ++i) {
        lab_ecam_window.armed = 1;
        struct pci_af_observation af = pci_observe_af(qotom_ecam_read,
            &lab_ecam_reader, &snapshot->headers[i], &retained[i]);
        lab_ecam_window.armed = 0;
        serial_puts("LEANOS-LAB/1 PCI-AF profile=af-observation-v1 index=");
        serial_u64(i);
        serial_puts(" status="); serial_u64(af.status);
        serial_puts(" offset="); serial_u64(af.offset);
        serial_puts(" raw="); serial_u64(af.raw_control_status); serial_putc('\n');
        if (af.status != PCI_AF_OK && af.status != PCI_AF_NOT_PRESENT)
            pre_admission_fail("qotom-pci-af");
    }
#endif
}
#endif
