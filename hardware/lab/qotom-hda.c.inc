#include "qotom-hda-arm.h"
static __attribute__((noinline)) int lab_hda_load(void *opaque,uint64_t address,
        uint8_t width,uint32_t *value) {
    (void)opaque;
    if(width==1)*value=*(volatile uint8_t *)(uintptr_t)address;
    else if(width==2)*value=*(volatile uint16_t *)(uintptr_t)address;
    else if(width==4)*value=*(volatile uint32_t *)(uintptr_t)address;
    else return 0;
    return 1;
}
static __attribute__((noreturn)) void lab_hda_fault(void *opaque);
static struct lab_hda_window lab_hda_window={
    .controls=lab_ecam_native_controls,.invalidate=lab_ecam_native_invalidate,
    .load=lab_hda_load,.fault=lab_hda_fault
};
static void lab_hda_disarm(void) {
    lab_ecam_window.armed=0;lab_hda_window.armed=0;
}
static __attribute__((noreturn)) void lab_hda_fault(void *opaque) {
    (void)opaque;lab_hda_disarm();pre_admission_fail("qotom-hda");
}
#ifdef LEANOS_QOTOM_HDA_STATE
#include "qotom-hda-state.c.inc"
#endif
static __attribute__((noinline)) void lab_capture_hda(
        const struct lab_ecam_root_view *view,const struct pci_enumeration_header *header) {
    struct qotom_hda_observation result={0};
    uint32_t status=9; /* Local arm rejection, outside helper statuses. */
    lab_hda_disarm();
    if(lab_hda_arm(&lab_hda_window,view,lab_ecam_tables,lab_ecam_table_count,
            (uintptr_t)lab_ecam_aperture,header)) {
        lab_ecam_window.armed=1;
        status=qotom_collect_hda_observation(qotom_ecam_read,&lab_ecam_reader,
            lab_hda_window_read,&lab_hda_window,header,&result);
    }
    lab_hda_disarm();
    serial_puts("LEANOS-LAB/1 HDA profile=qotom-hda-v1 index=5 status=");serial_u64(status);
    serial_puts(" before=");serial_u64(result.control_before);
    serial_puts(" capability=");serial_u64(result.capability);
    serial_puts(" minor=");serial_u64(result.version_minor);
    serial_puts(" major=");serial_u64(result.version_major);
    serial_puts(" interrupt=");serial_u64(result.interrupt);
    serial_puts(" after=");serial_u64(result.control_after);serial_putc('\n');
    if(status!=QOTOM_HDA_OK)pre_admission_fail("qotom-hda");
#ifdef LEANOS_QOTOM_HDA_STATE
    lab_capture_hda_state(view,header,&result);
#endif
}
