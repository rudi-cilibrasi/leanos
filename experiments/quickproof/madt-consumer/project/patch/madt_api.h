/* The external name patch/madt_unit.c gives the MADT consumer (see there). */
#ifndef LEANOS_MADT_API_H
#define LEANOS_MADT_API_H
#include "qotom_bsp_consumer.h"

uint64_t madt_bind(const uint8_t *entries, size_t length, const struct qotom_bsp_observation *observation,
                   struct qotom_bsp_result *out);
#endif
