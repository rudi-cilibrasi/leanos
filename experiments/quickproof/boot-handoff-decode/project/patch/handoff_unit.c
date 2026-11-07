/* The code under test as one library unit: include/boot_handoff_decode.h, unchanged.  Its functions are static
 * inline, so this unit gives each entry point an external name: boot_handoff_extent and boot_handoff_project, which
 * boot_allocate calls in turn; boot_handoff_decode_candidate, which it calls for each candidate frame; and
 * boot_handoff_stream_copy and boot_handoff_decode_projection, which the project composes and the lab capture calls
 * alone.  Each wrapper only forwards its arguments. */
#include "handoff_api.h"

enum boot_handoff_status handoff_extent(boot_handoff_read read, void *context, uint32_t magic,
                                        uint32_t info_address, uint32_t *total) {
    return boot_handoff_extent(read, context, magic, info_address, total);
}

enum boot_handoff_status handoff_copy(boot_handoff_read read, void *context, uint32_t magic, uint32_t info_address,
                                      uint32_t total, uint64_t *copy, uint32_t *length) {
    return boot_handoff_stream_copy(read, context, magic, info_address, total, copy, length);
}

enum boot_handoff_status handoff_projection(uint32_t magic, uint32_t info_address, uint32_t total,
                                            const uint64_t *info, const struct boot_projection_storage *projection,
                                            uint64_t states[2][BOOT_DECODE_WORDS], uint32_t *current) {
    return boot_handoff_decode_projection(magic, info_address, total, info, projection, states, current);
}

enum boot_handoff_status handoff_candidate(uint32_t magic, uint32_t info_address, uint32_t total,
                                           uint64_t candidate, const uint64_t *info,
                                           uint64_t states[2][BOOT_DECODE_WORDS], uint32_t *current) {
    return boot_handoff_decode_candidate(magic, info_address, total, candidate, info, states, current);
}

enum boot_handoff_status handoff_project(boot_handoff_read read, void *context, uint32_t magic,
                                         uint32_t info_address, uint32_t total, uint64_t *copy,
                                         const struct boot_projection_storage *projection,
                                         uint64_t states[2][BOOT_DECODE_WORDS], uint32_t *current) {
    return boot_handoff_project(read, context, magic, info_address, total, copy, projection, states, current);
}
