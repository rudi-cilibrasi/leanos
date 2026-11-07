/* The external names patch/madt_admission_unit.c gives the MADT admission (see there). */
#ifndef LEANOS_MADT_ADMISSION_API_H
#define LEANOS_MADT_ADMISSION_API_H
#include "madt_generated_admission.h"

enum madt_generated_status madt_envelope(const uint8_t *bytes, uint32_t length);
enum madt_generated_status madt_entries(const uint8_t *bytes, uint32_t length, uint32_t executing_apic_id,
                                        uint32_t *admitted_apic_id);
enum madt_generated_status madt_result(uint64_t selected_kind, uint64_t selected_address,
                                       uint64_t copied_root_address, uint64_t advertised_count,
                                       uint64_t completed_copies, uint64_t madt_count, uint64_t admission_status,
                                       uint64_t admission_detail, uint64_t admitted_apic_id,
                                       uint64_t executing_apic_id, uint32_t *published_apic_id);
enum madt_generated_status madt_admission(const uint8_t *bytes, uint32_t length, uint32_t executing_apic_id,
                                          uint64_t selected_kind, uint64_t selected_address,
                                          uint64_t copied_root_address, uint64_t advertised_count,
                                          uint64_t completed_copies, uint32_t *published_apic_id);
#endif
