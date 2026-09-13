#ifndef LEANOS_PCI_POWER_OBSERVATION_H
#define LEANOS_PCI_POWER_OBSERVATION_H
#include "pci-express-observation.h"

enum pci_power_status {
    PCI_POWER_OK,PCI_POWER_NOT_PRESENT,PCI_POWER_ARGUMENT,
    PCI_POWER_COLLECTION_FAILED,PCI_POWER_LIST_CHANGED,PCI_POWER_SHAPE,
    PCI_POWER_READ_FAILED,PCI_POWER_ABSENT,PCI_POWER_FINAL_FAILED
};
struct pci_power_observation {
    enum pci_power_status status;
    uint8_t offset;
    uint32_t pm_capabilities;
    uint32_t control_status;
};

/* Conventional PCI PM v1-v3 only. Two complete identity/list collections
 * bracket one PMCSR/Data read. The returned DWORD preserves all device bits.
 * No power-state interpretation, write, delay, or restore authority is granted.
 * Serialized access and immutable/nonaliasing inputs are caller obligations. */
static inline struct pci_power_observation pci_observe_power(
        pci_enumeration_read read,void *context,
        const struct pci_enumeration_header *initial,
        const struct pci_capability_snapshot *previous) {
    struct pci_power_observation out={PCI_POWER_ARGUMENT,0,0,0};
    if(!read || !initial || !previous || previous->count>PCI_CAPABILITY_CAPACITY)
        return out;
    struct pci_capability_snapshot fresh,final;
    if(pci_collect_capabilities(read,context,initial,&fresh).status!=PCI_CAPABILITY_OK) {
        out.status=PCI_POWER_COLLECTION_FAILED;return out;
    }
    if(!pci_express_same_list(&fresh,previous)) {
        out.status=PCI_POWER_LIST_CHANGED;return out;
    }
    uint32_t selected=PCI_CAPABILITY_CAPACITY;
    for(uint32_t i=0;i<fresh.count;++i) {
        if((fresh.headers[i].raw&255)!=1)continue;
        if(selected!=PCI_CAPABILITY_CAPACITY) {out.status=PCI_POWER_SHAPE;return out;}
        selected=i;
    }
    if(selected==PCI_CAPABILITY_CAPACITY) {out.status=PCI_POWER_NOT_PRESENT;return out;}
    const struct pci_capability_header *cap=&fresh.headers[selected];
    uint32_t pmc=cap->raw>>16;
    if((pmc&7)<1 || (pmc&7)>3 || cap->offset>0xf8) {
        out.status=PCI_POWER_SHAPE;return out;
    }
    for(uint32_t i=0;i<fresh.count;++i)
        if(fresh.headers[i].offset==cap->offset+4) {
            out.status=PCI_POWER_SHAPE;return out;
        }
    uint32_t value;
    if(!read(context,initial->bus,initial->device,initial->function,
            (uint8_t)(cap->offset+4),&value)) {
        out.status=PCI_POWER_READ_FAILED;return out;
    }
    if(value==UINT32_MAX) {out.status=PCI_POWER_ABSENT;return out;}
    if(pci_collect_capabilities(read,context,initial,&final).status!=PCI_CAPABILITY_OK ||
       !pci_express_same_list(&fresh,&final)) {
        out.status=PCI_POWER_FINAL_FAILED;return out;
    }
    out.status=PCI_POWER_OK;out.offset=cap->offset;
    out.pm_capabilities=pmc;out.control_status=value;return out;
}
#endif
