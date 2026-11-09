/* The external name patch/acpi_unit.c gives the ACPI root and table copy pipeline (see there). */
#ifndef LEANOS_ACPI_API_H
#define LEANOS_ACPI_API_H
#include "acpi_table_copy.h"

enum acpi_table_copy_status acpi_pipeline(acpi_physical_copy copy, void *context, uint64_t selected_kind,
                                          uint64_t selected_address,
                                          const struct acpi_table_copy_storage *storage,
                                          struct acpi_table_copy_result *result);
#endif
