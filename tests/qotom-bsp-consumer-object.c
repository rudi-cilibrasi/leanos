#include "../include/qotom_bsp_consumer.h"
struct qotom_bsp_result qotom_bsp_consumer_probe(const uint8_t *entries,
        size_t length, const struct qotom_bsp_observation *observation) {
    return qotom_bind_validated_madt_entries(entries,length,observation);
}
