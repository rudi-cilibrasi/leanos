#ifndef LEANOS_LAB_QOTOM_REALTEK_BME_WINDOW_H
#define LEANOS_LAB_QOTOM_REALTEK_BME_WINDOW_H
#include "qotom-ecam-memory.h"

struct lab_realtek_bme_window {
    volatile uint64_t *leaf;
    uint64_t root,window;
    unsigned armed;
    uint8_t bus;
    void *opaque;
    int (*controls)(void *,struct lab_ecam_controls *);
    void (*invalidate)(void *,uint64_t);
    int (*store16)(void *,uint64_t,uint16_t);
    void (*fault)(void *);
};
static __attribute__((noreturn)) inline void lab_realtek_bme_window_fault(
        struct lab_realtek_bme_window *window) {
    window->fault(window->opaque);__builtin_trap();
}
/* Only bus 1 or 3, device/function zero, Command +4 and value 0003. Every
 * request consumes authority, including rejection. Trusted store16 executes
 * exactly one word store or reports failure; failure may have effects. Restore
 * the exact leaf, invalidate and check controls before returning. Interference
 * is terminal. Context/page tables are private and nonaliasing; firmware/AP
 * exclusion and callback serialization are caller assumptions. */
static inline int lab_realtek_bme_window_write(void *context,uint8_t bus,
        uint8_t device,uint8_t function,uint8_t offset,uint16_t value) {
    struct lab_realtek_bme_window *window=context;
    if(!window)return 0;
    unsigned armed=window->armed;window->armed=0;
    uint64_t mapped=UINT64_C(0x80000000e000001b)+((uint64_t)window->bus<<20);
    struct lab_ecam_controls before,after;
    if(armed!=1 || (window->bus!=1 && window->bus!=3) || bus!=window->bus ||
        device || function || offset!=4 || value!=3 || !window->leaf ||
        !window->controls || !window->invalidate || !window->store16 || !window->fault ||
        !window->window || window->window>=UINT64_C(0x1000000) || (window->window&4095))return 0;
    if(!window->controls(window->opaque,&before) ||
       !lab_ecam_controls_match(&before,window->root))return 0;
    uint64_t saved=*window->leaf,ad=UINT64_C(0x60);
    uint64_t expected=window->window|UINT64_C(0x8000000000000003);
    if((saved&~ad)!=expected)return 0;
    *window->leaf=mapped;window->invalidate(window->opaque,window->window);
    int stored=window->store16(window->opaque,window->window+4,3);
    uint64_t observed=*window->leaf;
    *window->leaf=saved;window->invalidate(window->opaque,window->window);
    if(*window->leaf!=saved || (observed&~ad)!=mapped ||
       !window->controls(window->opaque,&after) ||
       !lab_ecam_controls_match(&after,window->root))lab_realtek_bme_window_fault(window);
    return stored!=0;
}
#endif
