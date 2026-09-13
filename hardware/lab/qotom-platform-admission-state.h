#ifndef LEANOS_LAB_QOTOM_PLATFORM_ADMISSION_STATE_H
#define LEANOS_LAB_QOTOM_PLATFORM_ADMISSION_STATE_H
#include <stdint.h>

#include "qotom-platform-profile-inputs.h"

/* Values are published only by the live component gates in the physical
 * Qotom image.  The final platform boundary consumes these observations;
 * profile identifiers remain labels and never stand in for acceptance. */
struct qotom_platform_live_observation {
    uint32_t handoff_length;
    uint8_t pci_accepted;
    uint8_t bsp_accepted;
    uint8_t isolation_control_accepted;
    uint8_t executing_bsp;
    uint8_t advertised_processors;
};

static volatile struct qotom_platform_live_observation qotom_platform_live;

static inline uint32_t qotom_platform_u32(const uint8_t *p) {
    return (uint32_t)p[0] | (uint32_t)p[1] << 8 |
           (uint32_t)p[2] << 16 | (uint32_t)p[3] << 24;
}

/* Match the unique E820 tag byte-for-byte with the retained baseline.  Other
 * Multiboot tags can legitimately move when the linked image changes. */
static __attribute__((unused,noinline,noipa)) int
qotom_platform_memory_map_matches(
        const uint8_t *info, uint32_t available) {
    if (!info || available < 16u || qotom_platform_u32(info) != available ||
        (available & 7u) != 0u || qotom_platform_u32(info + 4u) != 0u)
        return 0;
    uint32_t offset = 8u;
    unsigned maps = 0;
    while (offset <= available - 8u) {
        uint32_t type = qotom_platform_u32(info + offset);
        uint32_t size = qotom_platform_u32(info + offset + 4u);
        if (size < 8u || size > available - offset) return 0;
        uint32_t advance = (size + 7u) & ~7u;
        if (advance > available - offset) return 0;
        if (type == 6u) {
            if (++maps != 1u || size != QOTOM_PLATFORM_MEMORY_MAP_TAG_BYTES)
                return 0;
            for (uint32_t i = 0; i < size; ++i)
                if (info[offset + i] != qotom_platform_memory_map_tag[i])
                    return 0;
        }
        if (type == 0u)
            return size == 8u && offset + advance == available && maps == 1u;
        offset += advance;
    }
    return 0;
}
#endif
