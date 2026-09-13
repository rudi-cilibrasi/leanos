#ifndef LEANOS_LAB_QOTOM_GRAPHICS_BME_ARM_H
#define LEANOS_LAB_QOTOM_GRAPHICS_BME_ARM_H
#include "qotom-ecam-firmware.h"
#include "qotom-ecam-root.h"
#include "qotom-graphics-bme-window.h"
#include "qotom-graphics-bme.h"

/* Bind the exact boot graphics header, successful quiet observation, copied
 * firmware tables and active ECAM root. Arming performs no device access.
 * Every rejection revokes any previously armed authority. */
static inline int lab_graphics_bme_arm(struct lab_graphics_bme_window *window,
        const struct lab_ecam_root_view *view,
        const struct lab_ecam_firmware_table *tables,uint32_t count,
        uint64_t address,const struct pci_enumeration_header *header,
        enum qotom_graphics_status prior_status,const struct qotom_graphics_state *prior) {
    if(!window)return 0;
    window->armed=0;window->leaf=0;window->root=0;window->window=0;
    if(!qotom_graphics_header_valid(header) || prior_status!=QOTOM_GRAPHICS_OK ||
       !qotom_graphics_quiet(prior))return 0;
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
