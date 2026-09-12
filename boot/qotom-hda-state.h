#ifndef LEANOS_QOTOM_HDA_STATE_H
#define LEANOS_QOTOM_HDA_STATE_H
#include "qotom-hda-observation.h"

struct qotom_hda_state {
    uint32_t corb,rirb,position,streams[8];
};
enum qotom_hda_state_status {
    QOTOM_HDA_STATE_OK,QOTOM_HDA_STATE_ARGUMENT,QOTOM_HDA_STATE_PRIOR,
    QOTOM_HDA_STATE_REFRESH,QOTOM_HDA_STATE_DRIFT,QOTOM_HDA_STATE_READ,
    QOTOM_HDA_STATE_ABSENT,QOTOM_HDA_STATE_WIDTH,QOTOM_HDA_STATE_FINAL
};
static inline int qotom_hda_state_profile(const struct qotom_hda_observation *p) {
    return p && p->control_before==1 && p->capability==UINT32_C(0x4401) &&
        p->version_minor==0 && p->version_major==1 && p->interrupt==0 && p->control_after==1;
}
/* Address selection only: the caller binds roots/aliases/resource and private
 * serialized immutable, nonaliasing inputs. Four input plus four output stream
 * controls require the exact observed GCAP profile, not a guessed count. */
static inline int qotom_hda_state_address(uint32_t offset,uint8_t width,uint64_t *out) {
    if(!out || !(((offset==0x4c || offset==0x5c) && width==1) ||
        (offset==0x70 && width==4) ||
        (offset>=0x80 && offset<=0x160 && !(offset&0x1f) && width==4))) return 0;
    *out=QOTOM_HDA_BAR+offset;return 1;
}
/* Two complete 18-read global/resource collections bracket 11 state samples:
 * exactly 47 reads on success. Every rejection zeroes the published output.
 * Reads only, no pointer following, polling, reset or stop request. Sequential
 * raw samples do not establish engine halt, drain or firmware/AP exclusion. */
static inline enum qotom_hda_state_status qotom_collect_hda_state(
        pci_enumeration_read config,void *config_context,
        qotom_hda_mmio_read global,void *global_context,
        qotom_hda_mmio_read state,void *state_context,
        const struct pci_enumeration_header *header,
        enum qotom_hda_status prior_status,const struct qotom_hda_observation *prior,
        struct qotom_hda_state *out) {
    if(out)*out=(struct qotom_hda_state){0};
    if(!config || !global || !state || !header || !prior || !out) return QOTOM_HDA_STATE_ARGUMENT;
    if(prior_status!=QOTOM_HDA_OK || !qotom_hda_state_profile(prior)) return QOTOM_HDA_STATE_PRIOR;
    struct qotom_hda_observation fresh;
    if(qotom_collect_hda_observation(config,config_context,global,global_context,header,&fresh)!=QOTOM_HDA_OK)
        return QOTOM_HDA_STATE_REFRESH;
    if(!qotom_hda_state_profile(&fresh)) return QOTOM_HDA_STATE_DRIFT;
    const uint16_t offsets[11]={0x4c,0x5c,0x70,0x80,0xa0,0xc0,0xe0,0x100,0x120,0x140,0x160};
    uint32_t values[11];
    for(unsigned i=0;i<11;++i) {
        const uint8_t width=i<2?1:4;
        uint64_t address;
        if(!qotom_hda_state_address(offsets[i],width,&address)) return QOTOM_HDA_STATE_ARGUMENT;
        if(!state(state_context,address,width,&values[i])) return QOTOM_HDA_STATE_READ;
        const uint32_t maximum=i<2?UINT32_C(255):UINT32_MAX;
        if(values[i]>maximum) return QOTOM_HDA_STATE_WIDTH;
        if(values[i]==maximum) return QOTOM_HDA_STATE_ABSENT;
    }
    if(qotom_collect_hda_observation(config,config_context,global,global_context,header,&fresh)!=QOTOM_HDA_OK ||
        !qotom_hda_state_profile(&fresh)) return QOTOM_HDA_STATE_FINAL;
    *out=(struct qotom_hda_state){values[0],values[1],values[2],{0}};
    for(unsigned i=0;i<8;++i)out->streams[i]=values[i+3];
    return QOTOM_HDA_STATE_OK;
}
#endif
