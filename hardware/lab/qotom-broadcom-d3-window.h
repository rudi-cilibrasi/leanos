#ifndef LEANOS_LAB_QOTOM_BROADCOM_D3_WINDOW_H
#define LEANOS_LAB_QOTOM_BROADCOM_D3_WINDOW_H
#include "qotom-ecam-memory.h"
#include "qotom-broadcom-d3.h"

struct lab_broadcom_d3_window {
    volatile uint64_t *leaf;
    uint64_t root,window;
    unsigned armed,stage;
    void *opaque;
    int (*controls)(void *,struct lab_ecam_controls *);
    void (*invalidate)(void *,uint64_t);
    int (*store16)(void *,uint64_t,uint16_t);
    void (*fault)(void *);
};
static __attribute__((noreturn)) inline void lab_broadcom_d3_window_fault(
        struct lab_broadcom_d3_window *window) {
    window->fault(window->opaque);__builtin_trap();
}
/* Exactly two ordered bus-2 configuration word stores are authorized: Command
 * 0000, then PMCSR 400b. Each request consumes the current grant; only a
 * successful first store, restored mapping and unchanged controls grants the
 * second. Rejection or reported store failure leaves the window disarmed.
 * Store failure may still have effects. Mapping interference is terminal. */
static inline int lab_broadcom_d3_window_write(void *context,uint8_t bus,
        uint8_t device,uint8_t function,uint8_t offset,uint16_t value) {
    struct lab_broadcom_d3_window *window=context;
    if(!window)return 0;
    unsigned armed=window->armed,stage=window->stage;window->armed=0;
    uint8_t expected_offset=stage?0x44:4;
    uint16_t expected_value=stage?QOTOM_BROADCOM_PMCSR_D3HOT:0;
    const uint64_t mapped=UINT64_C(0x80000000e020001b);
    struct lab_ecam_controls before,after;
    if(armed!=1 || stage>1 || bus!=2 || device || function ||
       offset!=expected_offset || value!=expected_value || !window->leaf ||
       !window->controls || !window->invalidate || !window->store16 || !window->fault ||
       !window->window || window->window>=UINT64_C(0x1000000) ||
       (window->window&4095))return 0;
    if(!window->controls(window->opaque,&before) ||
       !lab_ecam_controls_match(&before,window->root))return 0;
    uint64_t saved=*window->leaf,ad=UINT64_C(0x60);
    uint64_t expected=window->window|UINT64_C(0x8000000000000003);
    if((saved&~ad)!=expected)return 0;
    *window->leaf=mapped;window->invalidate(window->opaque,window->window);
    int stored=window->store16(window->opaque,window->window+expected_offset,expected_value);
    uint64_t observed=*window->leaf;
    *window->leaf=saved;window->invalidate(window->opaque,window->window);
    if(*window->leaf!=saved || (observed&~ad)!=mapped ||
       !window->controls(window->opaque,&after) ||
       !lab_ecam_controls_match(&after,window->root))
        lab_broadcom_d3_window_fault(window);
    if(stored && !stage) {window->stage=1;window->armed=1;}
    return stored!=0;
}
#endif
