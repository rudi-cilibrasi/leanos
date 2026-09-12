#ifndef LEANOS_QOTOM_REALTEK_ROUTE_H
#define LEANOS_QOTOM_REALTEK_ROUTE_H
#include "qotom-realtek-state.h"
#include "qotom-rootport-bme.h"
/* Bind this endpoint's captured upstream bridge and the successful preceding
 * BME transition. Initial headers remain immutable, with Command7 historical. */
static inline int qotom_realtek_route_valid(const struct pci_enumeration_header *endpoint,
        const struct pci_enumeration_header *bridge,
        enum qotom_rootport_bme_status status,const struct qotom_rootport_bme_result *prior) {
    if (!qotom_realtek_header_valid(endpoint) || !qotom_rootport_header_valid(bridge) ||
        status!=QOTOM_ROOTPORT_OK || !prior || prior->attempted!=1 ||
        prior->before_command!=7 || prior->after_command!=3) return 0;
    uint32_t bus=endpoint->bus;
    return bridge->function==bus-1 && bridge->words[6]==((bus<<16)|(bus<<8)) &&
        bridge->words[8]==(bus==1?UINT32_C(0xd080d080):UINT32_C(0xd060d060)) &&
        bridge->words[9]==UINT32_C(0x0001fff1) && !bridge->words[10] && !bridge->words[11];
}
/* New statuses 10 binding, 11 initial bridge refresh, 12 final bridge refresh.
 * The refresh checks all bridge header/routing DWORDs and the complete PCIe
 * list/payload with current Command3. It brackets the 22-read endpoint helper:
 * 90 reads for the native four-capability bridge; conservative bound 266.
 * The first failed operation stops. No publication on final refresh failure,
 * writes, polls, transaction-drain inference or atomic/continuing-state claim.
 * Callback/context and immutable nonaliasing inputs are caller obligations. */
static inline uint32_t qotom_collect_realtek_routed_state(
        pci_enumeration_read config,void *config_context,
        qotom_realtek_mmio_read mmio,void *mmio_context,
        const struct pci_enumeration_header *endpoint,
        const struct pci_enumeration_header *bridge,const struct pci_capability_snapshot *caps,
        enum qotom_rootport_bme_status status,const struct qotom_rootport_bme_result *prior,
        struct qotom_realtek_state *out) {
    if (out) *out=(struct qotom_realtek_state){0};
    if (!config || !mmio || !out) return QOTOM_REALTEK_ARGUMENT;
    if (!caps || !qotom_realtek_route_valid(endpoint,bridge,status,prior)) return 10;
    struct pci_enumeration_header current=*bridge;
    current.words[1]=(current.words[1]&UINT32_C(0xffff0000))|3;
    if (!qotom_rootport_refresh(config,config_context,&current,caps)) return 11;
    struct qotom_realtek_state sampled;
    uint32_t result=qotom_collect_realtek_state(config,config_context,mmio,mmio_context,endpoint,&sampled);
    if(result!=QOTOM_REALTEK_OK)return result;
    if (!qotom_rootport_refresh(config,config_context,&current,caps)) return 12;
    *out=sampled;return QOTOM_REALTEK_OK;
}
#endif
