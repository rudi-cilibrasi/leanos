/* The external names patch/handoff_unit.c gives the handoff copy and decoder (see there). */
#ifndef LEANOS_HANDOFF_API_H
#define LEANOS_HANDOFF_API_H
#include "boot_handoff_decode.h"

enum boot_handoff_status handoff_extent(boot_handoff_read read, void *context, uint32_t magic,
                                        uint32_t info_address, uint32_t *total);
enum boot_handoff_status handoff_copy(boot_handoff_read read, void *context, uint32_t magic, uint32_t info_address,
                                      uint32_t total, uint64_t *copy, uint32_t *length);
enum boot_handoff_status handoff_projection(uint32_t magic, uint32_t info_address, uint32_t total,
                                            const uint64_t *info, const struct boot_projection_storage *projection,
                                            uint64_t states[2][BOOT_DECODE_WORDS], uint32_t *current);
enum boot_handoff_status handoff_candidate(uint32_t magic, uint32_t info_address, uint32_t total,
                                           uint64_t candidate, const uint64_t *info,
                                           uint64_t states[2][BOOT_DECODE_WORDS], uint32_t *current);
enum boot_handoff_status handoff_project(boot_handoff_read read, void *context, uint32_t magic,
                                         uint32_t info_address, uint32_t total, uint64_t *copy,
                                         const struct boot_projection_storage *projection,
                                         uint64_t states[2][BOOT_DECODE_WORDS], uint32_t *current);
#endif
