#ifdef LEANOS_QOTOM_PCI_DIAGNOSTIC
#include "pci-express-observation.h"

#ifdef LEANOS_QOTOM_ROOTPORT_BME
static struct pci_express_observation lab_retained_pcie_device[16];
#endif

/* Exact native inventory and the complete earlier capability capture precede
 * this stage. All previous device contexts are disarmed on successful return.
 * Reuse the bounded ECAM reader only while observing each function. */
static __attribute__((noinline)) void lab_capture_pcie_device(
        const struct pci_enumeration_snapshot *snapshot) {
#ifdef LEANOS_QOTOM_ROOTPORT_BME
    if(snapshot->count!=16)pre_admission_fail("qotom-pcie-device");
#endif
    for (uint32_t i=0; i<snapshot->count; ++i) {
        lab_ecam_window.armed=1;
        struct pci_express_observation result=pci_observe_express(qotom_ecam_read,
            &lab_ecam_reader,&snapshot->headers[i],&lab_retained_pci_caps[i]);
        lab_ecam_window.armed=0;
#ifdef LEANOS_QOTOM_ROOTPORT_BME
        lab_retained_pcie_device[i]=result;
#endif
        serial_puts("LEANOS-LAB/1 PCIE-DEVICE profile=qotom-pcie-device-v1 index=");serial_u64(i);
        serial_puts(" status=");serial_u64(result.status);
        serial_puts(" offset=");serial_u64(result.offset);
        serial_puts(" capability=");serial_u64(result.device_capabilities);
        serial_puts(" control-status=");serial_u64(result.device_control_status);serial_putc('\n');
        if(result.status!=PCI_EXPRESS_OK && result.status!=PCI_EXPRESS_NOT_PRESENT)
            pre_admission_fail("qotom-pcie-device");
    }
}
#endif
