#include <assert.h>
#include <stdio.h>
#include "qotom-broadcom-assign-window.h"

static struct lab_broadcom_assign_window w;
static unsigned stores;
static int store_failed;
static int store16(void *p,uint8_t bus,uint8_t device,uint8_t function,
        uint8_t offset,uint16_t value) {
    assert(p==&w && !w.armed && bus==2 && !device && !function &&
        offset==0x44 && value==QOTOM_BROADCOM_PMCSR_D0);
    ++stores;return !store_failed;
}
static void reset(void) {
    stores=0;store_failed=0;w=(struct lab_broadcom_assign_window){1,&w,store16};
}
static int d0(void) {return lab_broadcom_assign_window_write(&w,2,0,0,0x44,0x4008);}
int main(void) {
    (void)pci_enumerate_segment;
    reset();assert(d0() && !w.armed && stores==1);
    assert(!d0() && stores==1);
    reset();w.armed=0;assert(!d0() && !stores);
    reset();w.armed=2;assert(!d0() && !stores && !w.armed);
    reset();store_failed=1;assert(!d0() && !w.armed && stores==1);
    assert(!d0() && stores==1);
    for(unsigned field=0;field<4;++field)for(unsigned value=0;value<256;++value) {
        unsigned valid[]={2,0,0,0x44};if(value==valid[field])continue;
        reset();valid[field]=value;
        assert(!lab_broadcom_assign_window_write(&w,(uint8_t)valid[0],(uint8_t)valid[1],
            (uint8_t)valid[2],(uint8_t)valid[3],0x4008));
        assert(!w.armed && !stores);
    }
    for(unsigned value=0;value<65536;++value)if(value!=0x4008) {
        reset();assert(!lab_broadcom_assign_window_write(&w,2,0,0,0x44,(uint16_t)value));
        assert(!w.armed && !stores);
        reset();assert(!lab_broadcom_assign_window_write(&w,2,0,0,4,(uint16_t)value));
        assert(!w.armed && !stores);
    }
    reset();w.store16=0;assert(!d0() && !w.armed);
    assert(!lab_broadcom_assign_window_write(NULL,2,0,0,0x44,0x4008));
    puts("PASS Broadcom assign window: one PMCSR D0 store, consumed grant, every other store refused");
}
