#ifdef LEANOS_QOTOM_PCI_DIAGNOSTIC
#include "qotom-native-inventory.h"

/* Caller has completed the ECAM scan and owns the private snapshot. This
 * boundary establishes inventory only; subsequent platform admission stays
 * closed until device policy and the remaining platform contracts are met. */
static void lab_check_native_inventory(enum pci_enumeration_status status,
        const struct pci_enumeration_snapshot *snapshot) {
    struct qotom_native_inventory_result result = qotom_check_native_inventory(
        status, snapshot, leanos_qotom_native_pci_header_check);
    serial_puts("LEANOS-LAB/1 NATIVE-PCI profile=qotom-native-ecam-v1 status=");
    serial_u64(result.status);
    serial_puts(" index="); serial_u64(result.index);
    serial_puts(" count="); serial_u64(snapshot->count); serial_putc('\n');
    if (result.status != QOTOM_NATIVE_INVENTORY_MATCH)
        pre_admission_fail("qotom-native-inventory");
}
#endif
