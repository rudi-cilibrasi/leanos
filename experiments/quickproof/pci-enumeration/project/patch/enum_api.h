/* The external name patch/enum_unit.c gives the segment scan (see there). */
#ifndef LEANOS_ENUM_API_H
#define LEANOS_ENUM_API_H
#include "pci-enumeration.h"

enum pci_enumeration_status enum_scan(pci_enumeration_read read, void *context,
                                      struct pci_enumeration_snapshot *snapshot,
                                      struct pci_enumeration_result *result);
#endif
