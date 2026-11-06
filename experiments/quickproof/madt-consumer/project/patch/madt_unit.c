/* The code under test as one library unit: include/qotom_bsp_consumer.h, unchanged.  Its functions are static
 * inline, so this unit gives qotom_bind_validated_madt_entries, which the Qotom production candidate calls from
 * boot_allocate, an external name.  The wrapper only forwards its arguments. */
#include "madt_api.h"

uint64_t madt_bind(const uint8_t *entries, size_t length, const struct qotom_bsp_observation *observation,
                   struct qotom_bsp_result *out) {
    return qotom_bind_validated_madt_entries(entries, length, observation, out);
}
