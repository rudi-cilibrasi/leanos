#ifndef LEANOS_LAB_QOTOM_GRAPHICS_STATE_WINDOW_H
#define LEANOS_LAB_QOTOM_GRAPHICS_STATE_WINDOW_H
#include "qotom-ecam-memory.h"
#include "qotom-graphics-state.h"

static inline int lab_graphics_state_read_leaf(uint64_t address,uint64_t *leaf) {
    for(unsigned engine=0;engine<QOTOM_GRAPHICS_ENGINE_COUNT;++engine)
        for(unsigned reg=0;reg<QOTOM_GRAPHICS_REGISTER_COUNT;++reg) {
            uint64_t checked;
            if(qotom_graphics_state_address(engine,reg,&checked) && checked==address) {
                if(!leaf)return 0;
                *leaf=(address&~UINT64_C(4095))|UINT64_C(0x8000000000000019);
                return 1;
            }
        }
    return 0;
}

struct lab_graphics_state_window {
    volatile uint64_t *leaf;
    uint64_t root,window;
    unsigned armed;
    void *opaque;
    int (*controls)(void *,struct lab_ecam_controls *);
    void (*invalidate)(void *,uint64_t);
    int (*load32)(void *,uint64_t,uint32_t *);
    void (*fault)(void *);
};
static __attribute__((noreturn)) inline void lab_graphics_state_window_fault(
        struct lab_graphics_state_window *window) {
    window->fault(window->opaque);__builtin_trap();
}
/* Temporarily map exactly one approved graphics-register page into the private
 * low aperture as supervisor read-only, NX and PAT-slot-3 UC. Restoration or
 * active-root interference is terminal. A native load fault is terminal under
 * the kernel fault policy; the fallible callback supports hosted negatives. */
static inline int lab_graphics_state_window_read(void *context,uint64_t address,
        uint32_t *value) {
    struct lab_graphics_state_window *window=context;uint64_t mapped;
    struct lab_ecam_controls before,after;
    if(!window || !value || window->armed!=1 || !window->leaf ||
       !window->controls || !window->invalidate || !window->load32 || !window->fault ||
       !window->window || window->window>=UINT64_C(0x1000000) ||
       (window->window&4095) || !lab_graphics_state_read_leaf(address,&mapped))return 0;
    if(!window->controls(window->opaque,&before) ||
       !lab_ecam_controls_match(&before,window->root))return 0;
    const uint64_t saved=*window->leaf,ad=UINT64_C(0x60);
    const uint64_t expected=window->window|UINT64_C(0x8000000000000003);
    if((saved&~ad)!=expected)return 0;
    *window->leaf=mapped;window->invalidate(window->opaque,window->window);
    uint32_t sampled=0;
    int loaded=window->load32(window->opaque,window->window+(address&4095),&sampled);
    uint64_t observed=*window->leaf;
    *window->leaf=saved;window->invalidate(window->opaque,window->window);
    if(*window->leaf!=saved || (observed&~UINT64_C(0x20))!=mapped ||
       !window->controls(window->opaque,&after) ||
       !lab_ecam_controls_match(&after,window->root))
        lab_graphics_state_window_fault(window);
    if(!loaded)return 0;
    *value=sampled;return 1;
}
#endif
