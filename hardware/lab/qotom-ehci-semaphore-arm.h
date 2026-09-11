#ifndef LEANOS_LAB_QOTOM_EHCI_SEMAPHORE_ARM_H
#define LEANOS_LAB_QOTOM_EHCI_SEMAPHORE_ARM_H
#include "qotom-ecam-firmware.h"
#include "qotom-ecam-root.h"
#include "qotom-ehci-semaphore.h"
#include "qotom-ehci-legacy.h"

/* Closed lab binding for the captured OS-byte request. This consumes immutable
 * successful collector samples, not arbitrary hardware claims. The caller
 * refreshes the binding through qotom_request_ehci_handoff before the write.
 * Root/firmware views and callbacks are trusted and stable for the transaction.
 * Rejection revokes prior authority; arming performs no device access. */
static inline int lab_ehci_semaphore_arm(struct lab_ehci_semaphore *w,
        const struct lab_ecam_root_view *view,
        const struct lab_ecam_firmware_table *tables,uint32_t count,
        uint64_t address,const struct pci_enumeration_header *header,
        const struct qotom_ehci_capabilities *caps,
        const struct qotom_ehci_legacy_snapshot *legacy) {
    if(!w)return 0;
    w->armed=0;w->leaf=0;w->root=0;w->window=0;
    if(!header || header->bus || header->device!=29 || header->function ||
       header->words[0]!=UINT32_C(0x0f348086) || header->words[2]!=UINT32_C(0x0c03200e) ||
       (header->words[3]&UINT32_C(0x00ff0000)) || !(header->words[1]&2) ||
       header->words[4]!=QOTOM_EHCI_BAR || !caps ||
       caps->capbase!=UINT32_C(0x01000020) || caps->structural!=UINT32_C(0x00200008) ||
       caps->capability!=UINT32_C(0x00036881) || !legacy || legacy->count!=1 ||
       legacy->legacy_offset!=0x68 || legacy->headers[0].offset!=0x68 ||
       legacy->headers[0].raw!=UINT32_C(0x00010001) ||
       legacy->control_status!=UINT32_C(0x00082005))return 0;
    if(!view || !w->controls || !w->invalidate || !w->store8 || !w->fault ||
       !lab_ecam_firmware_matches(tables,count))return 0;
    struct lab_ecam_controls before,after;
    if(!w->controls(w->opaque,&before) || !lab_ecam_controls_match(&before,view->root_address) ||
       !lab_ecam_root_matches(view,before.cr3,address))return 0;
    /* root_matches excludes all ECAM aliases. Also keep the EHCI MMIO page
     * unaliased while its capability refresh shares this private aperture. */
    for(unsigned i=0;i<4096;++i)
        if((view->pt[i]&1) && (view->pt[i]&UINT64_C(0x000ffffffffff000))==QOTOM_EHCI_BAR)return 0;
    if(!w->controls(w->opaque,&after) || !lab_ecam_controls_match(&after,view->root_address))return 0;
    w->leaf=&view->pt[address/4096u];w->root=view->root_address;w->window=address;w->armed=1;
    return 1;
}
#endif
