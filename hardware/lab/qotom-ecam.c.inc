/* Opt-in diagnostic transport. No device writes or platform admission. */
#include "qotom-ecam-arm.h"
#include "qotom-ecam-native.h"
#include "qotom-ecam-read.h"
static struct lab_ecam_firmware_table lab_ecam_tables[LAB_ECAM_FIRMWARE_TABLE_COUNT];
static uint32_t lab_ecam_table_count;
static uint8_t lab_ecam_aperture[4096] __attribute__((aligned(4096)));
static __attribute__((noreturn)) void lab_ecam_fault(void *opaque) {
    (void)opaque;
    pre_admission_fail("qotom-ecam-transaction");
}
static struct lab_ecam_window lab_ecam_window = {
    .controls = lab_ecam_native_controls,
    .invalidate = lab_ecam_native_invalidate,
    .load32 = lab_ecam_native_load32,
    .fault = lab_ecam_fault
};
#ifdef LEANOS_QOTOM_PCI_DIAGNOSTIC
static struct qotom_ecam_reader lab_ecam_reader = {
    .allocation = {UINT64_C(0xe0000000), 0, 0, 255},
    .access = lab_ecam_window_read, .context = &lab_ecam_window
};
#endif
static void lab_prepare_ecam(void) {
    const struct lab_ecam_root_view view = {
        page_map_level_4_a, page_directory_pointer_a, page_directory_a, page_table_a,
        (uintptr_t)page_map_level_4_a, (uintptr_t)page_directory_pointer_a,
        (uintptr_t)page_directory_a, (uintptr_t)page_table_a
    };
    if (!lab_ecam_arm(&lab_ecam_window, &view, lab_ecam_tables,
                      lab_ecam_table_count, (uintptr_t)lab_ecam_aperture))
        pre_admission_fail("qotom-ecam-arm");
    serial_puts("LEANOS-LAB/1 ECAM-ARM firmware=exact root=checked access=read32\n");
}
