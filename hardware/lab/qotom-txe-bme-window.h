#ifndef LEANOS_LAB_QOTOM_TXE_BME_WINDOW_H
#define LEANOS_LAB_QOTOM_TXE_BME_WINDOW_H
#include "qotom-ecam-memory.h"

struct lab_txe_bme_window {
    volatile uint64_t *leaf;
    uint64_t root,window;
    unsigned armed;
    void *opaque;
    int (*controls)(void *,struct lab_ecam_controls *);
    void (*invalidate)(void *,uint64_t);
    int (*store16)(void *,uint64_t,uint16_t);
    void (*fault)(void *);
};
static __attribute__((noreturn)) inline void lab_txe_bme_window_fault(
        struct lab_txe_bme_window *window) {
    window->fault(window->opaque);__builtin_trap();
}
/* One request to PCI 00:1a.0 Command +4 with value 0102 consumes authority.
 * The temporary mapping is RW, supervisor, NX and UC. Restore and invalidate
 * the mapping and recheck the active root before returning any store result. */
static inline int lab_txe_bme_window_write(void *context,uint8_t bus,
        uint8_t device,uint8_t function,uint8_t offset,uint16_t value) {
    struct lab_txe_bme_window *window=context;
    if(!window)return 0;
    unsigned armed=window->armed;window->armed=0;
    const uint64_t mapped=UINT64_C(0x80000000e00d001b);
    struct lab_ecam_controls before,after;
    if(armed!=1 || bus || device!=26 || function || offset!=4 || value!=0x102 ||
       !window->leaf || !window->controls || !window->invalidate ||
       !window->store16 || !window->fault || !window->window ||
       window->window>=UINT64_C(0x1000000) || (window->window&4095))return 0;
    if(!window->controls(window->opaque,&before) ||
       !lab_ecam_controls_match(&before,window->root))return 0;
    uint64_t saved=*window->leaf,ad=UINT64_C(0x60);
    uint64_t expected=window->window|UINT64_C(0x8000000000000003);
    if((saved&~ad)!=expected)return 0;
    *window->leaf=mapped;window->invalidate(window->opaque,window->window);
    int stored=window->store16(window->opaque,window->window+4,UINT16_C(0x0102));
    uint64_t observed=*window->leaf;
    *window->leaf=saved;window->invalidate(window->opaque,window->window);
    if(*window->leaf!=saved || (observed&~ad)!=mapped ||
       !window->controls(window->opaque,&after) ||
       !lab_ecam_controls_match(&after,window->root))
        lab_txe_bme_window_fault(window);
    return stored!=0;
}
#endif
