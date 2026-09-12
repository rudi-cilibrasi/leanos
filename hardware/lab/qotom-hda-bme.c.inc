#include "qotom-hda-bme-arm.h"
static __attribute__((noreturn)) void lab_hda_bme_fault(void *opaque);
static struct lab_hda_bme_window lab_hda_bme_writer={
    .controls=lab_ecam_native_controls,.invalidate=lab_ecam_native_invalidate,
    .store16=lab_bme_store16,.fault=lab_hda_bme_fault
};
static void lab_hda_bme_disarm(void) {
    lab_hda_state_disarm();lab_hda_bme_writer.armed=0;
}
static __attribute__((noreturn)) void lab_hda_bme_fault(void *opaque) {
    (void)opaque;lab_hda_bme_disarm();pre_admission_fail("qotom-hda-bme");
}
static __attribute__((noinline)) void lab_clear_hda_bme(
        const struct lab_ecam_root_view *view,const struct pci_enumeration_header *header,
        const struct qotom_hda_observation *caps,const struct qotom_hda_state *prior) {
    struct qotom_hda_bme_result result={0};
    uint32_t status=9; /* Global reader, state reader, writer arms: 9,10,11. */
    lab_hda_bme_disarm();
    if(lab_hda_arm(&lab_hda_window,view,lab_ecam_tables,lab_ecam_table_count,
            (uintptr_t)lab_ecam_aperture,header)) {
        status=10;
        if(lab_hda_state_arm(&lab_hda_state_window,view,lab_ecam_tables,lab_ecam_table_count,
                (uintptr_t)lab_ecam_aperture,header,QOTOM_HDA_OK,caps)) {
            status=11;
            if(lab_hda_bme_arm(&lab_hda_bme_writer,view,lab_ecam_tables,lab_ecam_table_count,
                    (uintptr_t)lab_ecam_aperture,header,QOTOM_HDA_OK,caps,QOTOM_HDA_STATE_OK,prior)) {
                lab_ecam_window.armed=1;
                status=qotom_clear_hda_bme(qotom_ecam_read,&lab_ecam_reader,
                    lab_hda_window_read,&lab_hda_window,lab_hda_state_window_read,&lab_hda_state_window,
                    lab_hda_bme_window_write,&lab_hda_bme_writer,
                    header,QOTOM_HDA_OK,caps,QOTOM_HDA_STATE_OK,prior,&result);
            }
        }
    }
    lab_hda_bme_disarm();
    serial_puts("LEANOS-LAB/1 HDA-BME profile=qotom-hda-bme-v1 index=5 status=");serial_u64(status);
    serial_puts(" attempted=");serial_u64(result.attempted);
    serial_puts(" before=");serial_u64(result.before_command);
    serial_puts(" after=");serial_u64(result.after_command);serial_putc('\n');
    if(status!=QOTOM_HDA_BME_OK)pre_admission_fail("qotom-hda-bme");
}
