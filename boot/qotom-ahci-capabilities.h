#ifndef LEANOS_QOTOM_AHCI_CAPABILITIES_H
#define LEANOS_QOTOM_AHCI_CAPABILITIES_H
#include "pci-enumeration.h"

#define QOTOM_AHCI_BAR UINT64_C(0xd0916000)
typedef int (*qotom_ahci_mmio_read)(void *,uint64_t,uint32_t *);
struct qotom_ahci_capabilities {
    uint32_t capability, control, ports, version, extended;
};
enum qotom_ahci_status {
    QOTOM_AHCI_OK, QOTOM_AHCI_ARGUMENT, QOTOM_AHCI_HEADER,
    QOTOM_AHCI_CONFIG_READ, QOTOM_AHCI_DRIFT,
    QOTOM_AHCI_MMIO_READ, QOTOM_AHCI_ABSENT
};
/* Address selection is not authority to map MMIO. The caller establishes the
 * UC/root/alias/resource contract and owns serialized, immutable, nonaliasing
 * inputs and its private mapping window. No BOHC or port access is admitted. */
static inline int qotom_ahci_capability_address(uint32_t offset,uint64_t *out) {
    if (!out || (offset!=0 && offset!=4 && offset!=12 && offset!=16 && offset!=36)) return 0;
    *out=QOTOM_AHCI_BAR+offset; return 1;
}
/* Exactly 15 reads on success: five config checks, five MMIO observations,
 * then the same config checks. All failures publish zero. No write or policy
 * inference: these samples do not prove halt, drain or firmware exclusion. */
static inline enum qotom_ahci_status qotom_collect_ahci_capabilities(
        pci_enumeration_read config,void *config_context,
        qotom_ahci_mmio_read mmio,void *mmio_context,
        const struct pci_enumeration_header *initial,
        struct qotom_ahci_capabilities *out) {
    if (out) *out=(struct qotom_ahci_capabilities){0};
    if (!config || !mmio || !initial || !out) return QOTOM_AHCI_ARGUMENT;
    if (initial->bus!=0 || initial->device!=19 || initial->function!=0 ||
        initial->words[0]!=UINT32_C(0x0f238086) || initial->words[2]!=UINT32_C(0x0106010e) ||
        (initial->words[3]&UINT32_C(0x00ff0000)) || !(initial->words[1]&2) ||
        initial->words[9]!=QOTOM_AHCI_BAR) return QOTOM_AHCI_HEADER;
    const uint8_t offsets[5]={0,4,8,12,36};
    const uint32_t masks[5]={UINT32_MAX,2,UINT32_MAX,UINT32_C(0x00ff0000),UINT32_MAX};
    const uint8_t registers[5]={0,4,12,16,36};
    uint32_t values[5];
    for (uint32_t phase=0;phase<2;++phase) {
        for (uint32_t i=0;i<5;++i) {
            uint32_t raw;
            if (!config(config_context,0,19,0,offsets[i],&raw)) return QOTOM_AHCI_CONFIG_READ;
            if ((raw&masks[i])!=(initial->words[offsets[i]/4]&masks[i])) return QOTOM_AHCI_DRIFT;
        }
        if (!phase) for (uint32_t i=0;i<5;++i) {
            uint64_t address;
            if (!qotom_ahci_capability_address(registers[i],&address)) return QOTOM_AHCI_ARGUMENT;
            if (!mmio(mmio_context,address,&values[i])) return QOTOM_AHCI_MMIO_READ;
            if (values[i]==UINT32_MAX) return QOTOM_AHCI_ABSENT;
        }
    }
    *out=(struct qotom_ahci_capabilities){values[0],values[1],values[2],values[3],values[4]};
    return QOTOM_AHCI_OK;
}
#endif
