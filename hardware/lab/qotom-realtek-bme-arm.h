#ifndef LEANOS_LAB_QOTOM_REALTEK_BME_ARM_H
#define LEANOS_LAB_QOTOM_REALTEK_BME_ARM_H
#include "qotom-ecam-firmware.h"
#include "qotom-ecam-root.h"
#include "qotom-realtek-bme-window.h"
#include "qotom-realtek-bme.h"

/* Arming binds exact endpoint/routing/prior stopped state, copied firmware and
 * active root/control state. root_matches excludes every present ECAM alias.
 * This config-only authority needs no endpoint resource mapping. Arming performs
 * no hardware access; each rejection first revokes prior bus/authority. */
static inline int lab_realtek_bme_arm(struct lab_realtek_bme_window *window,
        const struct lab_ecam_root_view *view,
        const struct lab_ecam_firmware_table *tables,uint32_t count,uint64_t address,
        const struct pci_enumeration_header *endpoint,
        const struct pci_enumeration_header *bridge,
        enum qotom_rootport_bme_status route_status,const struct qotom_rootport_bme_result *route,
        enum qotom_realtek_status prior_status,const struct qotom_realtek_state *prior) {
    if(!window)return 0;
    window->armed=0;window->leaf=0;window->root=0;window->window=0;window->bus=0;
    if(prior_status!=QOTOM_REALTEK_OK || !qotom_realtek_stopped(prior) ||
       !qotom_realtek_route_valid(endpoint,bridge,route_status,route))return 0;
    if(!view || !window->controls || !window->invalidate || !window->store16 ||
       !window->fault || !lab_ecam_firmware_matches(tables,count))return 0;
    struct lab_ecam_controls before,after;
    if(!window->controls(window->opaque,&before) ||
       !lab_ecam_controls_match(&before,view->root_address) ||
       !lab_ecam_root_matches(view,before.cr3,address) ||
       !window->controls(window->opaque,&after) ||
       !lab_ecam_controls_match(&after,view->root_address))return 0;
    window->leaf=&view->pt[address/4096u];window->root=view->root_address;
    window->window=address;window->bus=endpoint->bus;window->armed=1;return 1;
}
#endif
