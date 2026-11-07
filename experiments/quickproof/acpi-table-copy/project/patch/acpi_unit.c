/* The code under test as one library unit: include/acpi_table_copy.h, unchanged.  Its functions are static
 * inline, so this unit gives acpi_copy_root_and_tables, the pipeline boot_allocate calls, an external name.  The
 * wrapper only forwards its arguments. */
#include "acpi_api.h"

enum acpi_table_copy_status acpi_pipeline(acpi_physical_copy copy, void *context, uint64_t selected_kind,
                                          uint64_t selected_address,
                                          const struct acpi_table_copy_storage *storage,
                                          struct acpi_table_copy_result *result) {
    return acpi_copy_root_and_tables(copy, context, selected_kind, selected_address, storage, result);
}
