#ifndef LEANOS_LAB_QOTOM_PM_DELAY_H
#define LEANOS_LAB_QOTOM_PM_DELAY_H
#include "qotom-ecam-firmware.h"
#include "pci-enumeration.h"
#define LAB_PM_DELAY_READ_LIMIT 1000000u
#define LAB_PM_DELAY_TICKS 35797u
struct lab_pm_delay {
    unsigned armed;
    void *opaque;
    int (*read32)(void *,uint16_t,uint32_t *);
};
/* Exact captured root/FADT binding plus fresh LPC identity, captured Command and
 * ACPI-base decode. Caller supplies successful complete firmware copies and
 * serialized configuration reads; this does not exclude firmware mutation. */
static inline int lab_pm_delay_arm(struct lab_pm_delay *timer,
        const struct lab_ecam_firmware_table *tables,uint32_t count,
        pci_enumeration_read config,void *context) {
    if(!timer)return 0;
    timer->armed=0;
    if(!timer->read32 || !config || count<2 || !lab_ecam_firmware_matches(tables,count))return 0;
    /* The pinned fixture's FADT is index 1: 24-bit value, 32-bit SystemIO
     * access at 0x408. The full equality gate above bounds all these bytes. */
    const uint8_t *f=tables[1].bytes;
    if(tables[1].length<220 || f[76]!=8 || f[77]!=4 || f[78] || f[79] ||
       f[91]!=4 || (f[113]&1) || f[208]!=1 || f[209]!=32 || f[210] || f[211]!=3 ||
       f[212]!=8 || f[213]!=4)return 0;
    for(unsigned i=214;i<220;++i)if(f[i])return 0;
    uint32_t raw;
    if(!config(context,0,31,0,0,&raw) || raw!=UINT32_C(0x0f1c8086) ||
       !config(context,0,31,0,4,&raw) || (raw&UINT32_C(0xffff))!=7 ||
       !config(context,0,31,0,0x40,&raw) || raw!=UINT32_C(0x403))return 0;
    timer->armed=1;return 1;
}
/* Only the handoff's 10-ms interval is supported. 3,579,545 Hz yields 35795.45
 * ticks; one tick beyond the ceiling covers unknown phase at the first sample.
 * <=1,000,000 reads, including the initial sample. Modulo-24-bit differences
 * >=half a cycle reject backward/ambiguous samples. Full cycles between reads
 * cannot be detected: a continuous standards-compliant timer and bounded read
 * callbacks are assumptions, not facts established by counter arithmetic.
 * No timer/event register write. Failure revokes the timer context. */
static inline int lab_pm_delay_wait(void *context,uint32_t milliseconds) {
    struct lab_pm_delay *timer=context;
    if(!timer)return 0;
    if(timer->armed!=1 || !timer->read32 || milliseconds!=10) {timer->armed=0;return 0;}
    uint32_t start;
    if(!timer->read32(timer->opaque,0x408,&start) || start>UINT32_C(0xffffff))goto fail;
    uint32_t previous_delta=0;
    for(uint32_t i=1;i<LAB_PM_DELAY_READ_LIMIT;++i) {
        uint32_t current;
        if(!timer->read32(timer->opaque,0x408,&current) || current>UINT32_C(0xffffff))goto fail;
        uint32_t delta=(current-start)&UINT32_C(0xffffff);
        if(delta>=UINT32_C(0x800000) || delta<previous_delta)goto fail;
        previous_delta=delta;
        if(delta>=LAB_PM_DELAY_TICKS)return 1;
    }
fail:
    timer->armed=0;return 0;
}
#endif
