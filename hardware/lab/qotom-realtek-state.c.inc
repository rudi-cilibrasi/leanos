#include "qotom-realtek-state-arm.h"
#include "qotom-realtek-route.h"
static __attribute__((noreturn)) void lab_realtek_state_fault(void *opaque);
static struct lab_realtek_state_window lab_realtek_state_window={
    .controls=lab_ecam_native_controls,.invalidate=lab_ecam_native_invalidate,
    .load=lab_hda_load,.fault=lab_realtek_state_fault
};
#ifdef LEANOS_QOTOM_REALTEK_BME
static struct qotom_realtek_state lab_retained_realtek_state[2];
#include "qotom-realtek-bme.c.inc"
#endif
static void lab_realtek_state_disarm(void) {
    lab_ecam_window.armed=0;lab_realtek_state_window.armed=0;
}
static __attribute__((noreturn)) void lab_realtek_state_fault(void *opaque) {
    (void)opaque;lab_realtek_state_disarm();pre_admission_fail("qotom-realtek-state");
}
static __attribute__((noinline)) void lab_capture_realtek_state(
        const struct lab_ecam_root_view *view,const struct pci_enumeration_snapshot *snapshot) {
#ifdef LEANOS_QOTOM_REALTEK_BME
    for(unsigned port=0;port<2;++port)
        lab_retained_realtek_state[port]=(struct qotom_realtek_state){0};
#endif
    for(unsigned port=0;port<2;++port) {
        const unsigned index=13+port*2,bus=1+port*2,bridge=6+port*2;
        struct qotom_realtek_state result={0};
        uint32_t status=13; /* Local count/index/arm rejection. */
        lab_realtek_state_disarm();
        if(snapshot->count==16 && snapshot->headers[index].bus==bus &&
                lab_realtek_state_arm(&lab_realtek_state_window,view,
                lab_ecam_tables,lab_ecam_table_count,(uintptr_t)lab_ecam_aperture,
                &snapshot->headers[index])) {
            lab_ecam_window.armed=1;
            status=qotom_collect_realtek_routed_state(qotom_ecam_read,&lab_ecam_reader,
                lab_realtek_state_window_read,&lab_realtek_state_window,
                &snapshot->headers[index],&snapshot->headers[bridge],&lab_retained_pci_caps[bridge],
                QOTOM_ROOTPORT_OK,&lab_retained_rootport_bme[port*2],&result);
        }
        lab_realtek_state_disarm();
        serial_puts("LEANOS-LAB/1 REALTEK-STATE profile=qotom-realtek-state-v1 index=");serial_u64(index);
        serial_puts(" status=");serial_u64(status);
        serial_puts(" transmit-before=");serial_u64(result.transmit_before);
        serial_puts(" command-before=");serial_u64(result.command_before);
        serial_puts(" interrupt-mask=");serial_u64(result.interrupt_mask);
        serial_puts(" receive=");serial_u64(result.receive);
        serial_puts(" command-after=");serial_u64(result.command_after);
        serial_puts(" transmit-after=");serial_u64(result.transmit_after);serial_putc('\n');
        if(status!=QOTOM_REALTEK_OK)pre_admission_fail("qotom-realtek-state");
#ifdef LEANOS_QOTOM_REALTEK_BME
        lab_retained_realtek_state[port]=result;
#endif
    }
#ifdef LEANOS_QOTOM_REALTEK_BME
    lab_capture_realtek_bme(view,snapshot);
#endif
}
