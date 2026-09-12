#ifndef LEANOS_QOTOM_TXE_STATUS_H
#define LEANOS_QOTOM_TXE_STATUS_H
#include "pci-enumeration.h"

struct qotom_txe_status_observation { uint32_t firmware0,firmware1; };
enum qotom_txe_status {
    QOTOM_TXE_OK,QOTOM_TXE_ARGUMENT,QOTOM_TXE_HEADER,
    QOTOM_TXE_CONFIG_READ,QOTOM_TXE_DRIFT,QOTOM_TXE_STATUS_READ,QOTOM_TXE_ABSENT
};
/* Ten configuration reads: four identity/Command/layout reads before and
 * after FW_STS0/1 at 40h/48h. Linux v6.12 Intel MEI TXE driver documents
 * these DWORD reads for Bay Trail 8086:0f18. No MMIO, write or polling.
 * Raw firmware status is not a DMA-stop, drain or firmware-exclusion witness.
 * Caller supplies serialized bounded reads and immutable nonaliasing inputs,
 * plus native firmware/root/ECAM binding. All rejected outputs remain zero. */
static inline enum qotom_txe_status qotom_collect_txe_status(
        pci_enumeration_read read,void *context,
        const struct pci_enumeration_header *initial,
        struct qotom_txe_status_observation *out) {
    if(out)*out=(struct qotom_txe_status_observation){0};
    if(!read || !initial || !out)return QOTOM_TXE_ARGUMENT;
    if(initial->bus || initial->device!=26 || initial->function ||
       initial->words[0]!=UINT32_C(0x0f188086) ||
       initial->words[2]!=UINT32_C(0x1080000e) ||
       (initial->words[3]&UINT32_C(0x00ff0000)) ||
       (initial->words[1]&UINT32_C(0xffff))!=UINT32_C(0x0106))
        return QOTOM_TXE_HEADER;
    const uint32_t masks[4]={UINT32_MAX,UINT32_C(0xffff),UINT32_MAX,UINT32_C(0x00ff0000)};
    uint32_t values[2]={0};
    for(unsigned phase=0;phase<2;++phase) {
        for(unsigned i=0;i<4;++i) {
            uint32_t raw;
            if(!read(context,0,26,0,(uint8_t)(i*4),&raw))return QOTOM_TXE_CONFIG_READ;
            if((raw&masks[i])!=(initial->words[i]&masks[i]))return QOTOM_TXE_DRIFT;
        }
        if(!phase)for(unsigned i=0;i<2;++i) {
            if(!read(context,0,26,0,(uint8_t)(0x40+i*8),&values[i]))return QOTOM_TXE_STATUS_READ;
            if(values[i]==UINT32_MAX)return QOTOM_TXE_ABSENT;
        }
    }
    *out=(struct qotom_txe_status_observation){values[0],values[1]};
    return QOTOM_TXE_OK;
}
#endif
