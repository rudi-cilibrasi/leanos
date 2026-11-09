/* The code under test as one library unit: boot/pci-capabilities.h, unchanged.  Its functions are static, so this
 * unit gives pci_collect_capabilities, which the PM, AF and PCI Express observations, the Qotom Broadcom
 * assignment and D3 paths and the lab capture call, an external name.  The wrapper only forwards its arguments. */
#include "caps_api.h"

enum pci_capability_status caps_collect(pci_enumeration_read read, void *context,
                                        const struct pci_enumeration_header *initial,
                                        struct pci_capability_snapshot *snapshot,
                                        struct pci_capability_result *result) {
    return pci_collect_capabilities(read, context, initial, snapshot, result);
}
