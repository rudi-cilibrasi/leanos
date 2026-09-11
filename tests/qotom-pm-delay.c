#include <assert.h>
#include <stdio.h>
#include "qotom-pm-delay.h"
static unsigned reads,config_reads,failed,config_failed,config_changed;
static uint32_t initial,step,config_mutation;
static int backwards,upper;
static int config(void *ctx,uint8_t b,uint8_t d,uint8_t f,uint8_t off,uint32_t *out) {
    (void)ctx;assert(!b && d==31 && !f);++config_reads;
    if(config_reads==config_failed)return 0;
    if(off==0)*out=0x0f1c8086;else if(off==4)*out=7;else {assert(off==0x40);*out=0x403;}
    if(!config_changed || config_reads==config_changed)*out^=config_mutation;
    return 1;
}
static int read32(void *ctx,uint16_t port,uint32_t *out) {
    (void)ctx;assert(port==0x408);++reads;if(reads==failed)return 0;
    *out=(initial+(reads-1)*step)&0xffffff;
    if(backwards==1 && reads==2)*out=(initial-1)&0xffffff;
    if(backwards==2 && reads==3)*out=(initial+step/2)&0xffffff;
    if(upper)*out|=0x1000000;
    return 1;
}
static struct lab_pm_delay timer;
static void reset(void) {
    reads=config_reads=failed=config_failed=0;initial=123;step=10000;
    config_mutation=config_changed=0;backwards=upper=0;
    timer=(struct lab_pm_delay){0,NULL,read32};
}
#define ARM() lab_pm_delay_arm(&timer,lab_ecam_expected_tables,LAB_ECAM_FIRMWARE_TABLE_COUNT,config,NULL)
int main(void) {
    assert(pci_enumerate_segment(NULL,NULL,NULL).status==PCI_ENUMERATION_INVALID_ARGUMENT);
    reset();assert(ARM() && config_reads==3 && !reads);
    assert(lab_pm_delay_wait(&timer,10) && reads==5 && timer.armed);
    for(unsigned i=1;i<=5;++i) {reset();assert(ARM());failed=i;assert(!lab_pm_delay_wait(&timer,10) && !timer.armed && reads==i);}
    reset();assert(ARM());initial=0xfffff0;assert(lab_pm_delay_wait(&timer,10) && reads==5);
    reset();assert(ARM());step=LAB_PM_DELAY_TICKS-1;assert(lab_pm_delay_wait(&timer,10) && reads==3);
    reset();assert(ARM());step=LAB_PM_DELAY_TICKS;assert(lab_pm_delay_wait(&timer,10) && reads==2);
    reset();assert(ARM());step=0;assert(!lab_pm_delay_wait(&timer,10) && reads==LAB_PM_DELAY_READ_LIMIT && !timer.armed);
    reset();assert(ARM());backwards=1;assert(!lab_pm_delay_wait(&timer,10) && reads==2 && !timer.armed);
    reset();assert(ARM());backwards=2;assert(!lab_pm_delay_wait(&timer,10) && reads==3);
    reset();assert(ARM());step=0x800000;assert(!lab_pm_delay_wait(&timer,10) && reads==2);
    reset();assert(ARM());upper=1;assert(!lab_pm_delay_wait(&timer,10) && reads==1);
    for(unsigned i=1;i<=3;++i) {reset();assert(ARM());config_reads=0;config_failed=i;assert(!ARM() && !timer.armed && !reads);}
    for(unsigned i=1;i<=3;++i) {
        reset();config_changed=i;config_mutation=2;
        assert(!ARM() && !timer.armed && config_reads==i && !reads);
    }
    reset();assert(!lab_pm_delay_wait(&timer,10) && !reads);
    reset();assert(ARM());assert(!lab_pm_delay_wait(&timer,0) && !reads && !timer.armed);
    reset();assert(ARM());assert(!lab_pm_delay_arm(&timer,lab_ecam_expected_tables,0,config,NULL) && !timer.armed);
    puts("PASS PM delay: fixed binding, wraparound, conservative tick threshold, stalled/read-failed/ambiguous timer rejection");
}
