#ifndef LEANOS_LAB_QOTOM_AHCI_PORT_ARM_H
#define LEANOS_LAB_QOTOM_AHCI_PORT_ARM_H
#include "qotom-ahci-arm.h"
#include "qotom-ahci-port.h"
#include "qotom-ahci-port-window.h"

/* Private staging reuses the existing firmware/root/resource/alias checks.
 * The collector must refresh the bound globals before port reads. Arming
 * performs no device access, and every failure revokes previous authority. */
static inline int lab_ahci_port_arm(struct lab_ahci_port_window *window,
        const struct lab_ecam_root_view *view,
        const struct lab_ecam_firmware_table *tables,uint32_t count,
        uint64_t address,const struct pci_enumeration_header *header,
        enum qotom_ahci_status status,const struct qotom_ahci_capabilities *prior) {
    if(!window)return 0;
    window->armed=0;window->leaf=0;window->root=0;window->window=0;
    if(status!=QOTOM_AHCI_OK || !qotom_ahci_port1_profile(prior))return 0;
    struct lab_ahci_window staging={.opaque=window->opaque,
        .controls=window->controls,.invalidate=window->invalidate,
        .load32=window->load32,.fault=window->fault};
    if(!lab_ahci_arm(&staging,view,tables,count,address,header))return 0;
    window->leaf=staging.leaf;window->root=staging.root;
    window->window=staging.window;window->armed=1;
    return 1;
}
#endif
