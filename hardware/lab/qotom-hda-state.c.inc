#include "qotom-hda-state-arm.h"
static __attribute__((noreturn)) void lab_hda_state_fault(void *opaque);
static struct lab_hda_state_window lab_hda_state_window={
    .controls=lab_ecam_native_controls,.invalidate=lab_ecam_native_invalidate,
    .load=lab_hda_load,.fault=lab_hda_state_fault
};
static void lab_hda_state_disarm(void) {
    lab_hda_disarm();lab_hda_state_window.armed=0;
}
static __attribute__((noreturn)) void lab_hda_state_fault(void *opaque) {
    (void)opaque;lab_hda_state_disarm();pre_admission_fail("qotom-hda-state");
}
#ifdef LEANOS_QOTOM_HDA_BME
#include "qotom-hda-bme.c.inc"
#endif
static __attribute__((noinline)) void lab_capture_hda_state(
        const struct lab_ecam_root_view *view,const struct pci_enumeration_header *header,
        const struct qotom_hda_observation *prior) {
    struct qotom_hda_state result={0};
    uint32_t status=9; /* Global and state arm rejection: 9 and 10. */
    lab_hda_state_disarm();
    if(lab_hda_arm(&lab_hda_window,view,lab_ecam_tables,lab_ecam_table_count,
            (uintptr_t)lab_ecam_aperture,header)) {
        status=10;
        if(lab_hda_state_arm(&lab_hda_state_window,view,lab_ecam_tables,lab_ecam_table_count,
                (uintptr_t)lab_ecam_aperture,header,QOTOM_HDA_OK,prior)) {
            lab_ecam_window.armed=1;
            status=qotom_collect_hda_state(qotom_ecam_read,&lab_ecam_reader,
                lab_hda_window_read,&lab_hda_window,lab_hda_state_window_read,&lab_hda_state_window,
                header,QOTOM_HDA_OK,prior,&result);
        }
    }
    lab_hda_state_disarm();
    serial_puts("LEANOS-LAB/1 HDA-STATE profile=qotom-hda-state-v1 index=5 status=");serial_u64(status);
    serial_puts(" corb=");serial_u64(result.corb);
    serial_puts(" rirb=");serial_u64(result.rirb);
    serial_puts(" position=");serial_u64(result.position);
    for(unsigned i=0;i<8;++i) {
        serial_puts(" stream");serial_u64(i);serial_putc('=');serial_u64(result.streams[i]);
    }
    serial_putc('\n');
    if(status!=QOTOM_HDA_STATE_OK)pre_admission_fail("qotom-hda-state");
#ifdef LEANOS_QOTOM_HDA_BME
    lab_clear_hda_bme(view,header,prior,&result);
#endif
}
