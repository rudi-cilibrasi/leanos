/* The code under test as one library unit: boot/pci-enumeration.h, unchanged.  Its functions are static, so this
 * unit gives pci_enumerate_segment, the segment scan of the Qotom PCI diagnostic kernel and of the lab's final PCI
 * admission capture, whose snapshot the inventory checks consume, an external name.  The wrapper only forwards its
 * arguments. */
#include "enum_api.h"

enum pci_enumeration_status enum_scan(pci_enumeration_read read, void *context,
                                      struct pci_enumeration_snapshot *snapshot,
                                      struct pci_enumeration_result *result) {
    return pci_enumerate_segment(read, context, snapshot, result);
}
