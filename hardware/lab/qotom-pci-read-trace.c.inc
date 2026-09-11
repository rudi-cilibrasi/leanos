#ifdef LEANOS_QOTOM_PCI_DIAGNOSTIC
/* Lab observation only. Read back CF8 after the existing mechanism-1 reader.
 * This adds timing and an I/O read; it cannot prove exclusion of SMM or APs.
 * Never retry, repair, or replace the returned configuration value.
 */
static struct {
    uint32_t reads, mismatches, requested, observed, value;
    uint32_t first_requested, first_observed, first_value;
} lab_pci_trace;

static int lab_pci_read(void *context, uint8_t bus, uint8_t device,
        uint8_t function, uint8_t offset, uint32_t *value) {
    int ok = pci_config_read(context, bus, device, function, offset, value);
    if (!ok) return 0;
    uint32_t requested = UINT32_C(0x80000000) | (uint32_t)bus << 16 |
        (uint32_t)device << 11 | (uint32_t)function << 8 | offset;
    uint32_t observed = in32(0xcf8);
    ++lab_pci_trace.reads;
    lab_pci_trace.requested = requested;
    lab_pci_trace.observed = observed;
    lab_pci_trace.value = *value;
    if (observed != requested) {
        if (!lab_pci_trace.mismatches) {
            lab_pci_trace.first_requested = requested;
            lab_pci_trace.first_observed = observed;
            lab_pci_trace.first_value = *value;
        }
        ++lab_pci_trace.mismatches;
    }
    return ok;
}

static void lab_report_pci_read(void) {
    serial_puts("LEANOS-LAB/1 PCI-READ reads="); serial_u64(lab_pci_trace.reads);
    serial_puts(" mismatches="); serial_u64(lab_pci_trace.mismatches);
    serial_puts(" requested="); serial_u64(lab_pci_trace.requested);
    serial_puts(" observed="); serial_u64(lab_pci_trace.observed);
    serial_puts(" value="); serial_u64(lab_pci_trace.value);
    serial_puts(" first_requested="); serial_u64(lab_pci_trace.first_requested);
    serial_puts(" first_observed="); serial_u64(lab_pci_trace.first_observed);
    serial_puts(" first_value="); serial_u64(lab_pci_trace.first_value);
    serial_putc('\n');
}
#endif
