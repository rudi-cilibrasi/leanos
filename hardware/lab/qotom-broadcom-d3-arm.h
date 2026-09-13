#ifndef LEANOS_LAB_QOTOM_BROADCOM_D3_ARM_H
#define LEANOS_LAB_QOTOM_BROADCOM_D3_ARM_H
#include "qotom-broadcom-d3-window.h"
#include "qotom-ecam-firmware.h"
#include "qotom-ecam-root.h"

/* Bind the exact endpoint, bus-2 bridge BME/quiet priors, copied firmware and
 * active root before granting the two-store sequence. Arming itself performs
 * no hardware read or write. Every rejected rearm revokes an earlier grant. */
static inline int lab_broadcom_d3_arm(struct lab_broadcom_d3_window *window,
        const struct lab_ecam_root_view *view,
        const struct lab_ecam_firmware_table *tables,uint32_t count,uint64_t address,
        const struct pci_enumeration_header *endpoint,
        const struct pci_enumeration_header *bridge,
        const struct pci_capability_snapshot *caps,
        const struct pci_express_observation *pcie,
        enum qotom_rootport_bme_status root_bme_status,
        const struct qotom_rootport_bme_result *root_bme,
        enum qotom_pcie_pending_status root_pending_status,
        const struct qotom_pcie_pending_result *root_pending) {
    if(!window)return 0;
    window->armed=0;window->stage=0;window->leaf=0;window->root=0;window->window=0;
    if(!qotom_broadcom_header_valid_command(endpoint,QOTOM_BROADCOM_COMMAND_INITIAL) ||
       !qotom_broadcom_pcie_valid(pcie) || !qotom_broadcom_caps_valid(caps) ||
       !qotom_broadcom_root_prior_valid(bridge,root_bme_status,root_bme,
            root_pending_status,root_pending))return 0;
    if(!view || !window->controls || !window->invalidate || !window->store16 ||
       !window->fault || !lab_ecam_firmware_matches(tables,count))return 0;
    struct lab_ecam_controls before,after;
    if(!window->controls(window->opaque,&before) ||
       !lab_ecam_controls_match(&before,view->root_address) ||
       !lab_ecam_root_matches(view,before.cr3,address) ||
       !window->controls(window->opaque,&after) ||
       !lab_ecam_controls_match(&after,view->root_address))return 0;
    window->leaf=&view->pt[address/4096u];window->root=view->root_address;
    window->window=address;window->armed=1;return 1;
}
#endif
