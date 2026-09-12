#include "qotom-graphics-bme-arm.h"
static __attribute__((noreturn)) void lab_graphics_bme_fault(void *opaque);
static struct lab_graphics_bme_window lab_graphics_bme_writer={
    .controls=lab_ecam_native_controls,.invalidate=lab_ecam_native_invalidate,
    .store16=lab_bme_store16,.fault=lab_graphics_bme_fault
};
static void lab_graphics_bme_disarm(void) {
    lab_ecam_window.armed=0;lab_graphics_state_reader.armed=0;
    lab_graphics_bme_writer.armed=0;
}
static __attribute__((noreturn)) void lab_graphics_bme_fault(void *opaque) {
    (void)opaque;lab_graphics_bme_disarm();pre_admission_fail("qotom-graphics-bme");
}
static __attribute__((noinline)) void lab_capture_graphics_bme(
        const struct lab_ecam_root_view *view,const struct pci_enumeration_snapshot *snapshot) {
    struct qotom_graphics_bme_result result={0};uint32_t status=9;
    lab_graphics_bme_disarm();
    if(snapshot->count==16 && lab_graphics_state_arm(&lab_graphics_state_reader,
            view,lab_ecam_tables,lab_ecam_table_count,(uintptr_t)lab_ecam_aperture,
            &snapshot->headers[1])) {
        status=10;
        if(lab_graphics_bme_arm(&lab_graphics_bme_writer,view,lab_ecam_tables,
                lab_ecam_table_count,(uintptr_t)lab_ecam_aperture,
                &snapshot->headers[1],QOTOM_GRAPHICS_OK,
                &lab_retained_graphics_state)) {
            lab_ecam_window.armed=1;
            status=qotom_clear_graphics_bme(qotom_ecam_read,&lab_ecam_reader,
                lab_graphics_state_window_read,&lab_graphics_state_reader,
                lab_graphics_bme_window_write,&lab_graphics_bme_writer,
                &snapshot->headers[1],QOTOM_GRAPHICS_OK,
                &lab_retained_graphics_state,&result);
        }
    }
    lab_graphics_bme_disarm();
    serial_puts("LEANOS-LAB/1 GRAPHICS-BME profile=qotom-valleyview-bme-v1 index=1 status=");
    serial_u64(status);serial_puts(" attempted=");serial_u64(result.attempted);
    serial_puts(" before=");serial_u64(result.before_command);
    serial_puts(" after=");serial_u64(result.after_command);serial_putc('\n');
    if(status!=QOTOM_GRAPHICS_BME_OK)pre_admission_fail("qotom-graphics-bme");
    pre_admission_fail("qotom-platform-pending");
}
