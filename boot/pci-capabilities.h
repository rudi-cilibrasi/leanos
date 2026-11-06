#ifndef LEANOS_PCI_CAPABILITIES_H
#define LEANOS_PCI_CAPABILITIES_H
#include <stdint.h>
#include "pci-enumeration.h"

/* Conventional configuration space only: 48 aligned slots in [0x40,0xfc].
 * This observes capability headers, not capability payloads or DMA safety. */
#define PCI_CAPABILITY_CAPACITY 48u
struct pci_capability_header { uint8_t offset; uint32_t raw; };
struct pci_capability_snapshot {
    uint32_t count;
    struct pci_capability_header headers[PCI_CAPABILITY_CAPACITY];
};
enum pci_capability_status {
    PCI_CAPABILITY_OK, PCI_CAPABILITY_ARGUMENT, PCI_CAPABILITY_READ_FAILED,
    PCI_CAPABILITY_HEADER_CHANGED, PCI_CAPABILITY_POINTER,
    PCI_CAPABILITY_CYCLE, PCI_CAPABILITY_ABSENT
};
struct pci_capability_result { enum pci_capability_status status; uint8_t offset; };

/* Publish an outcome: the status, and the configuration offset it names (the
 * failing read, pointer or header word; 0 on success) into *result when the
 * caller asks for them. */
static inline enum pci_capability_status pci_capability_finish(
        struct pci_capability_result *result, enum pci_capability_status status,
        uint8_t offset) {
    if (result) {
        result->status = status;
        result->offset = offset;
    }
    return status;
}

/* The caller owns an immutable initial header and serialized read callback.
 * Rechecking identity, layout and list head detects drift at the beginning;
 * it cannot make the following hardware reads an atomic snapshot.
 * Failed traversals publish count zero. Only successful, terminated lists
 * expose their full count; staging bytes on failure are not authority.
 * Returns the status; `result` may be NULL (#604: no struct is returned by
 * value, so QuickProof's clightgen and VST can take this function). */
static inline enum pci_capability_status pci_collect_capabilities(
        pci_enumeration_read read, void *context,
        const struct pci_enumeration_header *initial,
        struct pci_capability_snapshot *snapshot,
        struct pci_capability_result *result) {
    if (snapshot) snapshot->count=0;
    if (!read || !initial || !snapshot || initial->device>31 || initial->function>7 ||
        ((initial->words[3]>>16)&0x7f)>1 || (initial->words[0]&0xffff)==0xffff)
        return pci_capability_finish(result,PCI_CAPABILITY_ARGUMENT,0);
    const uint8_t offsets[4]={0,4,12,52};
    const uint32_t masks[4]={UINT32_MAX,UINT32_C(0x00100000),UINT32_C(0x00ff0000),255};
    for (uint32_t i=0;i<4;++i) {
        uint32_t value;
        if (!read(context,initial->bus,initial->device,initial->function,offsets[i],&value))
            return pci_capability_finish(result,PCI_CAPABILITY_READ_FAILED,offsets[i]);
        if ((value&masks[i])!=(initial->words[offsets[i]/4]&masks[i]))
            return pci_capability_finish(result,PCI_CAPABILITY_HEADER_CHANGED,offsets[i]);
    }
    uint32_t count=0;
    uint64_t seen=0;
    uint8_t offset=(initial->words[1]&UINT32_C(0x00100000)) ?
        (uint8_t)initial->words[13] : 0;
    while (offset) {
        if (offset<64 || (offset&3))
            return pci_capability_finish(result,PCI_CAPABILITY_POINTER,offset);
        const uint64_t bit=UINT64_C(1)<<((offset-64)/4);
        if (seen&bit) return pci_capability_finish(result,PCI_CAPABILITY_CYCLE,offset);
        /* Unique valid pointers imply <=48 reads. Keep the explicit array
           guard even if a future change weakens pointer/cycle validation. */
        if (count==PCI_CAPABILITY_CAPACITY)
            return pci_capability_finish(result,PCI_CAPABILITY_POINTER,offset);
        seen|=bit;
        uint32_t raw;
        if (!read(context,initial->bus,initial->device,initial->function,offset,&raw))
            return pci_capability_finish(result,PCI_CAPABILITY_READ_FAILED,offset);
        if ((raw&255)==255) return pci_capability_finish(result,PCI_CAPABILITY_ABSENT,offset);
        snapshot->headers[count].offset=offset;
        snapshot->headers[count].raw=raw;
        ++count;
        offset=(uint8_t)(raw>>8);
    }
    snapshot->count=count;
    return pci_capability_finish(result,PCI_CAPABILITY_OK,0);
}
#endif
