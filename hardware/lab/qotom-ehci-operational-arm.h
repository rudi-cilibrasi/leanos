#ifndef LEANOS_LAB_QOTOM_EHCI_OPERATIONAL_ARM_H
#define LEANOS_LAB_QOTOM_EHCI_OPERATIONAL_ARM_H
#include "qotom-ehci-arm.h"
#include "qotom-ehci-operational-window.h"
#include "qotom-ehci-operational.h"

/* Reuse the capability window's firmware/root/alias validation through private
 * staging, without exporting its address authority. The resulting distinct
 * type admits only the four operational addresses. Arming accesses no device;
 * the collector must still refresh ownership and resources before reading.
 * Immutable, nonaliasing input views and trusted bounded callbacks are required.
 * Failure revokes all previous authority, including failure of a rearm. */
static inline int lab_ehci_operational_arm(struct lab_ehci_operational_window *window,
        const struct lab_ecam_root_view *view,
        const struct lab_ecam_firmware_table *tables,uint32_t count,
        uint64_t address,const struct pci_enumeration_header *header,
        const struct qotom_ehci_capabilities *caps,
        enum qotom_ehci_smi_status status,const struct qotom_ehci_smi_result *prior) {
    if(!window)return 0;
    window->armed=0;window->leaf=0;window->root=0;window->window=0;
    if(!caps || !prior || status!=QOTOM_EHCI_SMI_OBSERVED || prior->write_attempted!=1 ||
       (prior->before_control&~(QOTOM_EHCI_SMI_ENABLE|QOTOM_EHCI_SMI_STATUS)) ||
       (prior->after_control&~QOTOM_EHCI_SMI_STATUS) ||
       caps->capbase!=UINT32_C(0x01000020) || caps->structural!=UINT32_C(0x00200008) ||
       caps->capability!=UINT32_C(0x00036881))return 0;
    struct lab_ehci_window staging={.opaque=window->opaque,
        .controls=window->controls,.invalidate=window->invalidate,
        .load32=window->load32,.fault=window->fault};
    if(!lab_ehci_arm(&staging,view,tables,count,address,header))return 0;
    window->leaf=staging.leaf;window->root=staging.root;
    window->window=staging.window;window->armed=1;
    return 1;
}
#endif
