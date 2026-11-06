/* The external name patch/caps_unit.c gives the capability walker (see there). */
#ifndef LEANOS_CAPS_API_H
#define LEANOS_CAPS_API_H
#include "pci-capabilities.h"

enum pci_capability_status caps_collect(pci_enumeration_read read, void *context,
                                        const struct pci_enumeration_header *initial,
                                        struct pci_capability_snapshot *snapshot,
                                        struct pci_capability_result *result);
#endif
