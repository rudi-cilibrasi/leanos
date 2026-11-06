#include "../include/qotom_bsp_consumer.h"
uint64_t qotom_bsp_consumer_probe(const uint8_t *entries, size_t length,
        const struct qotom_bsp_observation *observation,
        struct qotom_bsp_result *out) {
    return qotom_bind_validated_madt_entries(entries,length,observation,out);
}
