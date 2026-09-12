#include "qotom-graphics-state-arm.h"
static __attribute__((noreturn)) void lab_graphics_state_fault(void *opaque);
static struct lab_graphics_state_window lab_graphics_state_reader={
    .controls=lab_ecam_native_controls,.invalidate=lab_ecam_native_invalidate,
    .load32=lab_ecam_native_load32,.fault=lab_graphics_state_fault
};
static void lab_graphics_state_disarm(void) {
    lab_ecam_window.armed=0;lab_graphics_state_reader.armed=0;
}
static __attribute__((noreturn)) void lab_graphics_state_fault(void *opaque) {
    (void)opaque;lab_graphics_state_disarm();pre_admission_fail("qotom-graphics-state");
}
static __attribute__((noinline)) void lab_capture_graphics_state(
        const struct lab_ecam_root_view *view,const struct pci_enumeration_snapshot *snapshot) {
    struct qotom_graphics_state result={0};uint32_t status=7;
    lab_graphics_state_disarm();
    if(snapshot->count==16 && lab_graphics_state_arm(&lab_graphics_state_reader,view,
            lab_ecam_tables,lab_ecam_table_count,(uintptr_t)lab_ecam_aperture,
            &snapshot->headers[1])) {
        lab_ecam_window.armed=1;
        status=qotom_collect_graphics_state(qotom_ecam_read,&lab_ecam_reader,
            lab_graphics_state_window_read,&lab_graphics_state_reader,
            &snapshot->headers[1],&result);
    }
    lab_graphics_state_disarm();
    serial_puts("LEANOS-LAB/1 GRAPHICS-STATE profile=qotom-valleyview-rings-v1 index=1 status=");
    serial_u64(status);serial_puts(" width=30 words=");
    for(unsigned i=0;i<QOTOM_GRAPHICS_SAMPLE_WORDS;++i) {
        if(i)serial_putc(',');
        serial_u64(result.words[i]);
    }
    serial_putc('\n');
    if(status!=QOTOM_GRAPHICS_OK)pre_admission_fail("qotom-graphics-state");
}
