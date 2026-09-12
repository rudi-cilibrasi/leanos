#ifdef LEANOS_QOTOM_PCI_DIAGNOSTIC
#include "qotom-ahci-arm.h"
static __attribute__((noreturn)) void lab_ahci_fault(void *opaque) {
    (void)opaque;
    pre_admission_fail("qotom-ahci-capabilities");
}
static struct lab_ahci_window lab_ahci_window = {
    .controls=lab_ecam_native_controls, .invalidate=lab_ecam_native_invalidate,
    .load32=lab_ecam_native_load32, .fault=lab_ahci_fault
};
#ifdef LEANOS_QOTOM_AHCI_PORT
#include "qotom-ahci-port.c.inc"
#endif
#ifdef LEANOS_QOTOM_HDA
#include "qotom-hda.c.inc"
#endif
#ifdef LEANOS_QOTOM_TXE_STATUS
#include "qotom-txe-status.c.inc"
#endif
/* Prior device stages have returned with their contexts disarmed. The private
 * ECAM and AHCI reads serialize through the same restored identity aperture. */
static __attribute__((noinline)) void lab_capture_ahci(
        const struct pci_enumeration_snapshot *snapshot) {
    const struct lab_ecam_root_view view = {
        page_map_level_4_a,page_directory_pointer_a,page_directory_a,page_table_a,
        (uintptr_t)page_map_level_4_a,(uintptr_t)page_directory_pointer_a,
        (uintptr_t)page_directory_a,(uintptr_t)page_table_a
    };
    struct qotom_ahci_capabilities result={0};
    uint32_t status=7; /* Local arm rejection, outside helper status range. */
    if(snapshot->count==16 && lab_ahci_arm(&lab_ahci_window,&view,
            lab_ecam_tables,lab_ecam_table_count,(uintptr_t)lab_ecam_aperture,
            &snapshot->headers[2])) {
        lab_ecam_window.armed=1;
        status=qotom_collect_ahci_capabilities(qotom_ecam_read,&lab_ecam_reader,
            lab_ahci_window_read,&lab_ahci_window,&snapshot->headers[2],&result);
    }
    lab_ecam_window.armed=0;
    lab_ahci_window.armed=0;
    serial_puts("LEANOS-LAB/1 AHCI-CAPS profile=qotom-ahci-v1 index=2 status=");serial_u64(status);
    serial_puts(" capability=");serial_u64(result.capability);
    serial_puts(" control=");serial_u64(result.control);
    serial_puts(" ports=");serial_u64(result.ports);
    serial_puts(" version=");serial_u64(result.version);
    serial_puts(" extended=");serial_u64(result.extended);serial_putc('\n');
    if(status!=QOTOM_AHCI_OK)pre_admission_fail("qotom-ahci-capabilities");
#ifdef LEANOS_QOTOM_AHCI_PORT
    lab_capture_ahci_port(&view,&snapshot->headers[2],&result);
#endif
#ifdef LEANOS_QOTOM_HDA
    lab_capture_hda(&view,&snapshot->headers[5]);
#endif
#ifdef LEANOS_QOTOM_TXE_STATUS
    lab_capture_txe_status(snapshot);
#endif
}
#endif
