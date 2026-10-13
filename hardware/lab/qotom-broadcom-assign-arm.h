#ifndef LEANOS_LAB_QOTOM_BROADCOM_ASSIGN_ARM_H
#define LEANOS_LAB_QOTOM_BROADCOM_ASSIGN_ARM_H
#include "qotom-broadcom-assign-window.h"

/* Grant the single PMCSR store only after binding the accepted initial trust
 * contract, the exact successful D3hot record of this boot, the retained
 * inventory header, capability list and PCIe observation of 02:00.0, and an
 * assignable program policy: exactly 02:00.0 14e4:4353, no DMA, no
 * configuration write outside the profile's backplane windows 80 and ac,
 * and no Command bit other than Memory Space. Arming performs no hardware
 * access. Every rejected rearm revokes an earlier grant. */
static inline int lab_broadcom_assign_arm(struct lab_broadcom_assign_window *window,
        uint64_t contract,enum qotom_broadcom_d3_status d3_status,
        const struct qotom_broadcom_d3_result *d3,
        const struct pci_enumeration_header *endpoint,
        const struct pci_capability_snapshot *caps,
        const struct pci_express_observation *pcie,
        const struct qotom_broadcom_assign_policy *policy) {
    if(!window)return 0;
    window->armed=0;
    if(contract!=1 || !qotom_broadcom_assign_d3_valid(d3_status,d3) ||
       !qotom_broadcom_header_valid_command(endpoint,QOTOM_BROADCOM_COMMAND_INITIAL) ||
       endpoint->words[4]!=QOTOM_BROADCOM_BAR0 || endpoint->words[5] ||
       !qotom_broadcom_caps_valid(caps) || !qotom_broadcom_pcie_valid(pcie) ||
       !policy || policy->bus!=2 || policy->device || policy->function ||
       policy->identity!=UINT32_C(0x435314e4) || policy->dma ||
       (policy->cfg_write&~UINT64_C(0x80100000000)) || (policy->cmd_set&~UINT64_C(2)) ||
       !window->store16)return 0;
    window->armed=1;return 1;
}
#endif
