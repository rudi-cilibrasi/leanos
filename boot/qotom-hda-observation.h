#ifndef LEANOS_QOTOM_HDA_OBSERVATION_H
#define LEANOS_QOTOM_HDA_OBSERVATION_H
#include "pci-enumeration.h"

#define QOTOM_HDA_BAR UINT64_C(0xd0910000)
/* Width is bytes, and successful narrow reads must be zero-extended. */
typedef int (*qotom_hda_mmio_read)(void *,uint64_t,uint8_t,uint32_t *);
struct qotom_hda_observation {
    uint32_t control_before,capability,version_minor,version_major,interrupt,control_after;
};
enum qotom_hda_status {
    QOTOM_HDA_OK,QOTOM_HDA_ARGUMENT,QOTOM_HDA_HEADER,
    QOTOM_HDA_CONFIG_READ,QOTOM_HDA_DRIFT,QOTOM_HDA_MMIO_READ,
    QOTOM_HDA_ABSENT,QOTOM_HDA_WIDTH,QOTOM_HDA_RESET
};
/* This is address selection, not MMIO mapping authority. The caller binds the
 * UC/root/alias/resource contract and serialized immutable nonaliasing inputs. */
static inline int qotom_hda_observation_address(uint32_t offset,uint8_t width,uint64_t *out) {
    if (!out || !((offset==0 && width==2) || ((offset==2 || offset==3) && width==1) ||
        ((offset==8 || offset==32) && width==4))) return 0;
    *out=QOTOM_HDA_BAR+offset;return 1;
}
/* Six config reads bracket six width-specific MMIO reads: 18 on success.
 * Read GCTL.CRST before accessing other controller registers, and check it
 * again last. Rejected/failed observations publish zero. No writes, polling,
 * stream access, drain inference or continuing firmware-exclusion claim. */
static inline enum qotom_hda_status qotom_collect_hda_observation(
        pci_enumeration_read config,void *config_context,
        qotom_hda_mmio_read mmio,void *mmio_context,
        const struct pci_enumeration_header *initial,
        struct qotom_hda_observation *out) {
    if (out) *out=(struct qotom_hda_observation){0};
    if (!config || !mmio || !initial || !out) return QOTOM_HDA_ARGUMENT;
    if (initial->bus || initial->device!=27 || initial->function ||
        initial->words[0]!=UINT32_C(0x0f048086) || initial->words[2]!=UINT32_C(0x0403000e) ||
        (initial->words[3]&UINT32_C(0x00ff0000)) || !(initial->words[1]&2) ||
        initial->words[4]!=(QOTOM_HDA_BAR|4) || initial->words[5]) return QOTOM_HDA_HEADER;
    const uint8_t offsets[6]={0,4,8,12,16,20};
    const uint32_t masks[6]={UINT32_MAX,2,UINT32_MAX,UINT32_C(0x00ff0000),UINT32_MAX,UINT32_MAX};
    const uint8_t registers[6]={8,0,2,3,32,8},widths[6]={4,2,1,1,4,4};
    uint32_t values[6];
    for (uint32_t phase=0;phase<2;++phase) {
        for (uint32_t i=0;i<6;++i) {
            uint32_t raw;
            if (!config(config_context,0,27,0,offsets[i],&raw)) return QOTOM_HDA_CONFIG_READ;
            if ((raw&masks[i])!=(initial->words[offsets[i]/4]&masks[i])) return QOTOM_HDA_DRIFT;
        }
        if (!phase) for (uint32_t i=0;i<6;++i) {
            uint64_t address;
            if (!qotom_hda_observation_address(registers[i],widths[i],&address)) return QOTOM_HDA_ARGUMENT;
            if (!mmio(mmio_context,address,widths[i],&values[i])) return QOTOM_HDA_MMIO_READ;
            uint32_t maximum=widths[i]==4?UINT32_MAX:(widths[i]==2?UINT32_C(65535):UINT32_C(255));
            if (values[i]>maximum) return QOTOM_HDA_WIDTH;
            if (values[i]==maximum) return QOTOM_HDA_ABSENT;
            if ((i==0 || i==5) && !(values[i]&1)) return QOTOM_HDA_RESET;
        }
    }
    *out=(struct qotom_hda_observation){values[0],values[1],values[2],values[3],values[4],values[5]};
    return QOTOM_HDA_OK;
}
#endif
