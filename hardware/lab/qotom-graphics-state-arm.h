#ifndef LEANOS_LAB_QOTOM_GRAPHICS_STATE_ARM_H
#define LEANOS_LAB_QOTOM_GRAPHICS_STATE_ARM_H
#include "qotom-ecam-firmware.h"
#include "qotom-ecam-root.h"
#include "qotom-graphics-state-window.h"

/* Bind the exact integrated graphics function, copied firmware and active
 * root before granting read-only register access. All BAR0 and BAR2 pages are
 * excluded from the existing boot mapping so the temporary aperture is the
 * sole kernel alias. Rejected rearm revokes an earlier grant. */
static inline int lab_graphics_state_arm(struct lab_graphics_state_window *window,
        const struct lab_ecam_root_view *view,
        const struct lab_ecam_firmware_table *tables,uint32_t count,
        uint64_t address,const struct pci_enumeration_header *header) {
    if(!window)return 0;
    window->armed=0;window->leaf=0;window->root=0;window->window=0;
    if(!qotom_graphics_header_valid(header) || !view || !window->controls ||
       !window->invalidate || !window->load32 || !window->fault ||
       !lab_ecam_firmware_matches(tables,count))return 0;
    struct lab_ecam_controls before,after;
    if(!window->controls(window->opaque,&before) ||
       !lab_ecam_controls_match(&before,view->root_address) ||
       !lab_ecam_root_matches(view,before.cr3,address) ||
       !window->controls(window->opaque,&after) ||
       !lab_ecam_controls_match(&after,view->root_address))return 0;
    for(unsigned i=0;i<4096;++i)if(view->pt[i]&1) {
        uint64_t physical=view->pt[i]&UINT64_C(0x000ffffffffff000);
        if((physical>=QOTOM_GRAPHICS_BAR0 &&
            physical<QOTOM_GRAPHICS_BAR0+QOTOM_GRAPHICS_BAR0_SIZE) ||
           (physical>=QOTOM_GRAPHICS_BAR2 &&
            physical<QOTOM_GRAPHICS_BAR2+QOTOM_GRAPHICS_BAR2_SIZE))return 0;
    }
    window->leaf=&view->pt[address/4096u];window->root=view->root_address;
    window->window=address;window->armed=1;return 1;
}
#endif
