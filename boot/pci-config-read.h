#ifndef LEANOS_PCI_CONFIG_READ_H
#define LEANOS_PCI_CONFIG_READ_H

#include <stdint.h>

/* Configuration mechanism 1, segment zero, conventional 256-byte space.
 * Implemented by pci-config-read.S; privileged x86-64 SysV ABI only.
 */
uint32_t leanos_pci_config_read_dword(uint32_t address);

/* Compatible with pci_enumeration_read. Context is unused. The caller owns
 * output storage, executes on the sole active BSP and guarantees that NMI,
 * SMM and other agents do not access CF8/CFC during the operation. Hardware
 * support for mechanism 1 is a prerequisite, not detected by this adapter.
 * An I/O fault is terminal under caller exception policy, not a false return.
 * UINT32_MAX is a raw read result; it is not distinguishable from absence.
 */
static inline int pci_config_read(void *context, uint8_t bus, uint8_t device,
        uint8_t function, uint8_t offset, uint32_t *value) {
    (void)context;
    if (!value || device >= 32 || function >= 8 || (offset & 3u))
        return 0;
    uint32_t address = UINT32_C(0x80000000) | (uint32_t)bus << 16 |
        (uint32_t)device << 11 | (uint32_t)function << 8 | offset;
    *value = leanos_pci_config_read_dword(address);
    return 1;
}

#endif
