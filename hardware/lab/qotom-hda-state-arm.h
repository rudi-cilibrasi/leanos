#ifndef LEANOS_LAB_QOTOM_HDA_STATE_ARM_H
#define LEANOS_LAB_QOTOM_HDA_STATE_ARM_H
#include "qotom-hda-arm.h"
#include "qotom-hda-state.h"
#include "qotom-hda-state-window.h"

/* Private staging reuses the existing firmware/root/resource/alias checks.
 * The collector must refresh the bound globals before state reads. Arming
 * performs no device access, and every failure revokes previous authority. */
static inline int lab_hda_state_arm(struct lab_hda_state_window *window,
        const struct lab_ecam_root_view *view,
        const struct lab_ecam_firmware_table *tables,uint32_t count,
        uint64_t address,const struct pci_enumeration_header *header,
        enum qotom_hda_status status,const struct qotom_hda_observation *prior) {
    if(!window)return 0;
    window->armed=0;window->leaf=0;window->root=0;window->window=0;
    if(status!=QOTOM_HDA_OK || !qotom_hda_state_profile(prior))return 0;
    struct lab_hda_window staging={.opaque=window->opaque,
        .controls=window->controls,.invalidate=window->invalidate,
        .load=window->load,.fault=window->fault};
    if(!lab_hda_arm(&staging,view,tables,count,address,header))return 0;
    window->leaf=staging.leaf;window->root=staging.root;
    window->window=staging.window;window->armed=1;
    return 1;
}
#endif
