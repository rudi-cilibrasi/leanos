#ifndef LEANOS_QOTOM_GRAPHICS_BME_H
#define LEANOS_QOTOM_GRAPHICS_BME_H
#include "qotom-graphics-state.h"

typedef int (*qotom_graphics_write_word)(void *,uint8_t,uint8_t,uint8_t,uint8_t,uint16_t);
struct qotom_graphics_bme_result { uint32_t attempted,before_command,after_command; };
enum qotom_graphics_bme_status {
    QOTOM_GRAPHICS_BME_OK,QOTOM_GRAPHICS_BME_ARGUMENT,QOTOM_GRAPHICS_BME_PRIOR,
    QOTOM_GRAPHICS_BME_REFRESH,QOTOM_GRAPHICS_BME_STATE,QOTOM_GRAPHICS_BME_COMMAND,
    QOTOM_GRAPHICS_BME_WRITE,QOTOM_GRAPHICS_BME_READBACK,QOTOM_GRAPHICS_BME_FINAL
};
static inline int qotom_graphics_quiet(const struct qotom_graphics_state *state) {
    if(!state)return 0;
    for(unsigned sample=0;sample<2;++sample)
        for(unsigned engine=0;engine<QOTOM_GRAPHICS_ENGINE_COUNT;++engine) {
            unsigned i=sample*15+engine*5;
            if(state->words[i]!=state->words[i+1] || state->words[i+3]&1 ||
               !(state->words[i+4]&UINT32_C(0x200)))return 0;
            if(sample)for(unsigned field=0;field<5;++field)
                if(state->words[i-15+field]!=state->words[i+field])return 0;
        }
    return 1;
}
static inline int qotom_graphics_same_state(const struct qotom_graphics_state *a,
        const struct qotom_graphics_state *b) {
    if(!a || !b)return 0;
    for(unsigned i=0;i<QOTOM_GRAPHICS_SAMPLE_WORDS;++i)
        if(a->words[i]!=b->words[i])return 0;
    return 1;
}

/* Refresh an already quiet observation, clear only PCI Command.BME (7 to 3),
 * then re-observe the same three rings with decode preserved. The operation is
 * 127 reads and one exact 16-bit configuration write. A failed write may have
 * effects and is reported; there is no rollback. Sequential empty-ring and
 * readback evidence does not establish posted-write drain, continuing
 * firmware/AP exclusion, display ownership or whole-platform quarantine. */
static inline enum qotom_graphics_bme_status qotom_clear_graphics_bme(
        pci_enumeration_read config,void *config_context,
        qotom_graphics_mmio_read mmio,void *mmio_context,
        qotom_graphics_write_word write,void *write_context,
        const struct pci_enumeration_header *endpoint,
        enum qotom_graphics_status prior_status,const struct qotom_graphics_state *prior,
        struct qotom_graphics_bme_result *out) {
    if(out)*out=(struct qotom_graphics_bme_result){0};
    if(!config || !mmio || !write || !endpoint || !prior || !out)
        return QOTOM_GRAPHICS_BME_ARGUMENT;
    if(prior_status!=QOTOM_GRAPHICS_OK || !qotom_graphics_quiet(prior))
        return QOTOM_GRAPHICS_BME_PRIOR;
    struct qotom_graphics_state fresh={0};
    if(qotom_collect_graphics_state(config,config_context,mmio,mmio_context,
            endpoint,&fresh)!=QOTOM_GRAPHICS_OK)return QOTOM_GRAPHICS_BME_REFRESH;
    if(!qotom_graphics_quiet(&fresh) || !qotom_graphics_same_state(prior,&fresh))
        return QOTOM_GRAPHICS_BME_STATE;
    uint32_t command;
    if(!config(config_context,0,2,0,4,&command) || (command&0xffff)!=7)
        return QOTOM_GRAPHICS_BME_COMMAND;
    out->before_command=7;out->attempted=1;
    if(!write(write_context,0,2,0,4,3))return QOTOM_GRAPHICS_BME_WRITE;
    if(!config(config_context,0,2,0,4,&command))return QOTOM_GRAPHICS_BME_READBACK;
    out->after_command=command&0xffff;
    if(out->after_command!=3)return QOTOM_GRAPHICS_BME_READBACK;
    struct pci_enumeration_header final=*endpoint;
    final.words[1]=(final.words[1]&UINT32_C(0xffff0000))|3;
    if(qotom_collect_graphics_state_command(config,config_context,mmio,mmio_context,
            &final,3,&fresh)!=QOTOM_GRAPHICS_OK || !qotom_graphics_quiet(&fresh) ||
       !qotom_graphics_same_state(prior,&fresh))return QOTOM_GRAPHICS_BME_FINAL;
    if(!config(config_context,0,2,0,4,&command))return QOTOM_GRAPHICS_BME_FINAL;
    out->after_command=command&0xffff;
    if(out->after_command!=3)return QOTOM_GRAPHICS_BME_FINAL;
    return QOTOM_GRAPHICS_BME_OK;
}
#endif
