#ifndef LEANOS_LAB_QOTOM_BROADCOM_ASSIGN_WINDOW_H
#define LEANOS_LAB_QOTOM_BROADCOM_ASSIGN_WINDOW_H
#include "qotom-broadcom-assign.h"

/* One configuration store is authorized for the assignment variant: the
 * 16-bit PMCSR word of 02:00.0 at offset 44, value 4008 (D0, PME disabled).
 * The request consumes the grant whether it is accepted or not; a rejected
 * request performs no store. A reported store failure may still have had an
 * effect, and the window stays disarmed. */
struct lab_broadcom_assign_window {
    unsigned armed;
    void *opaque;
    int (*store16)(void *,uint8_t,uint8_t,uint8_t,uint8_t,uint16_t);
};
static inline int lab_broadcom_assign_window_write(void *context,uint8_t bus,
        uint8_t device,uint8_t function,uint8_t offset,uint16_t value) {
    struct lab_broadcom_assign_window *window=context;
    if(!window)return 0;
    unsigned armed=window->armed;window->armed=0;
    if(armed!=1 || bus!=2 || device || function ||
       offset!=QOTOM_BROADCOM_ASSIGN_PMCSR_OFFSET || value!=QOTOM_BROADCOM_PMCSR_D0 ||
       !window->store16)return 0;
    return window->store16(window->opaque,2,0,0,QOTOM_BROADCOM_ASSIGN_PMCSR_OFFSET,
        QOTOM_BROADCOM_PMCSR_D0)!=0;
}
#endif
