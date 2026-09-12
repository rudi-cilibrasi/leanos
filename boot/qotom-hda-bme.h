#ifndef LEANOS_QOTOM_HDA_BME_H
#define LEANOS_QOTOM_HDA_BME_H
#include "qotom-hda-state.h"
typedef int (*qotom_hda_write_word)(void *,uint8_t,uint8_t,uint8_t,uint8_t,uint16_t);
struct qotom_hda_bme_result { uint32_t attempted,before_command,after_command; };
enum qotom_hda_bme_status {
    QOTOM_HDA_BME_OK,QOTOM_HDA_BME_ARGUMENT,QOTOM_HDA_BME_PRIOR,
    QOTOM_HDA_BME_REFRESH,QOTOM_HDA_BME_STATE,QOTOM_HDA_BME_COMMAND,
    QOTOM_HDA_BME_WRITE,QOTOM_HDA_BME_READBACK,QOTOM_HDA_BME_FINAL
};
static inline int qotom_hda_stopped(const struct qotom_hda_state *p) {
    if(!p || p->corb || p->rirb || p->position)return 0;
    for(unsigned i=0;i<8;++i)if(p->streams[i]!=UINT32_C(0x40000))return 0;
    return 1;
}
/* <=97 reads: two complete 47-read state collections and three Command reads.
 * One 16-bit write clears only BME: Command 0006 -> 0002 at 00:1b.0 +4.
 * Retain MMIO decoding and adjacent PCI Status. No ring/stream/position write,
 * reset, polling or rollback. Failed writes may have effects; preserve evidence.
 * Immutable nonaliasing observations, serialized bounded callbacks, native
 * firmware/root/resource binding and exclusion are caller obligations.
 * This bounded experiment does not establish transaction drain or admission. */
static inline enum qotom_hda_bme_status qotom_clear_hda_bme(
        pci_enumeration_read config,void *config_context,
        qotom_hda_mmio_read global,void *global_context,
        qotom_hda_mmio_read state,void *state_context,
        qotom_hda_write_word write,void *write_context,
        const struct pci_enumeration_header *header,
        enum qotom_hda_status global_status,const struct qotom_hda_observation *caps,
        enum qotom_hda_state_status state_status,const struct qotom_hda_state *prior,
        struct qotom_hda_bme_result *out) {
    if(out)*out=(struct qotom_hda_bme_result){0};
    if(!config || !global || !state || !write || !header || !caps || !prior || !out)
        return QOTOM_HDA_BME_ARGUMENT;
    if(global_status!=QOTOM_HDA_OK || state_status!=QOTOM_HDA_STATE_OK ||
       !qotom_hda_state_profile(caps) || !qotom_hda_stopped(prior) ||
       (header->words[1]&0xffff)!=6)return QOTOM_HDA_BME_PRIOR;
    struct qotom_hda_state fresh={0};
    if(qotom_collect_hda_state(config,config_context,global,global_context,state,state_context,
            header,QOTOM_HDA_OK,caps,&fresh)!=QOTOM_HDA_STATE_OK)
        return QOTOM_HDA_BME_REFRESH;
    if(!qotom_hda_stopped(&fresh))return QOTOM_HDA_BME_STATE;
    uint32_t command;
    if(!config(config_context,0,27,0,4,&command) || (command&0xffff)!=6)
        return QOTOM_HDA_BME_COMMAND;
    out->before_command=command&0xffff;out->attempted=1;
    if(!write(write_context,0,27,0,4,2))return QOTOM_HDA_BME_WRITE;
    if(!config(config_context,0,27,0,4,&command))return QOTOM_HDA_BME_READBACK;
    out->after_command=command&0xffff;
    if(out->after_command!=2)return QOTOM_HDA_BME_READBACK;
    if(qotom_collect_hda_state(config,config_context,global,global_context,state,state_context,
            header,QOTOM_HDA_OK,caps,&fresh)!=QOTOM_HDA_STATE_OK ||
       !qotom_hda_stopped(&fresh))return QOTOM_HDA_BME_FINAL;
    if(!config(config_context,0,27,0,4,&command))return QOTOM_HDA_BME_FINAL;
    out->after_command=command&0xffff;
    if(out->after_command!=2)return QOTOM_HDA_BME_FINAL;
    return QOTOM_HDA_BME_OK;
}
#endif
