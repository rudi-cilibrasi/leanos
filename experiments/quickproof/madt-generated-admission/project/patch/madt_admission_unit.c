/* The code under test as one library unit: include/madt_generated_admission.h, unchanged.  Its functions are
 * static inline, so this unit gives each an external name: madt_generated_admission, which boot_allocate calls,
 * madt_generated_envelope, which the Qotom production candidate and the lab capture call alone, and the entry
 * stream and the topology admission result, which the admission composes.  Each wrapper only forwards its
 * arguments. */
#include "madt_admission_api.h"

enum madt_generated_status madt_envelope(const uint8_t *bytes, uint32_t length) {
    return madt_generated_envelope(bytes, length);
}

enum madt_generated_status madt_entries(const uint8_t *bytes, uint32_t length, uint32_t executing_apic_id,
                                        uint32_t *admitted_apic_id) {
    return madt_generated_entries(bytes, length, executing_apic_id, admitted_apic_id);
}

enum madt_generated_status madt_result(uint64_t selected_kind, uint64_t selected_address,
                                       uint64_t copied_root_address, uint64_t advertised_count,
                                       uint64_t completed_copies, uint64_t madt_count, uint64_t admission_status,
                                       uint64_t admission_detail, uint64_t admitted_apic_id,
                                       uint64_t executing_apic_id, uint32_t *published_apic_id) {
    return madt_topology_admission_result(selected_kind, selected_address, copied_root_address, advertised_count,
                                          completed_copies, madt_count, admission_status, admission_detail,
                                          admitted_apic_id, executing_apic_id, published_apic_id);
}

enum madt_generated_status madt_admission(const uint8_t *bytes, uint32_t length, uint32_t executing_apic_id,
                                          uint64_t selected_kind, uint64_t selected_address,
                                          uint64_t copied_root_address, uint64_t advertised_count,
                                          uint64_t completed_copies, uint32_t *published_apic_id) {
    return madt_generated_admission(bytes, length, executing_apic_id, selected_kind, selected_address,
                                    copied_root_address, advertised_count, completed_copies, published_apic_id);
}
