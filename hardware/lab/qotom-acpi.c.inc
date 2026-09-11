/* Opt-in read-only firmware observation. No topology or DMA admission. */
#ifdef LEANOS_LAB_DSDT_CAPTURE
#include "acpi-dsdt-address.h"
#endif
static void lab_emit_acpi_table(uint32_t index, const struct copied_acpi_sdt *table) {
    serial_puts("LEANOS-LAB/1 ACPI-TABLE index="); serial_u64(index);
    serial_puts(" address="); serial_u64(table->physical_address);
    serial_puts(" length="); serial_u64(table->length); serial_putc('\n');
    for (uint32_t offset = 0; offset < table->length; offset += 64u) {
        serial_puts("LEANOS-LAB/1 ACPI-DATA offset="); serial_u64(offset);
        serial_puts(" hex=");
        for (uint32_t i = offset; i < table->length && i < offset + 64u; ++i) {
            static const char digits[] = "0123456789abcdef";
            uint8_t value = table->bytes[i];
            serial_putc(digits[value >> 4]); serial_putc(digits[value & 15]);
        }
        serial_putc('\n');
    }
}

static void lab_capture_acpi(void) {
    const uint8_t *original = (const uint8_t *)(uintptr_t)lab_mb2_address;
    uint32_t length = boot_handoff_capture_length(lab_mb2_magic, lab_mb2_address,
        original, lab_mb2_address < BOOT_ACCESSIBLE_LIMIT
            ? BOOT_ACCESSIBLE_LIMIT - lab_mb2_address : 0);
    if (length == 0 || length > 65536u - 36u)
        handoff_fail("lab-acpi-handoff-budget");
    const struct copied_boot_handoff handoff = copy_boot_handoff(
        lab_mb2_magic, lab_mb2_address, length, observe_executing_apic_id());
    const struct boot_decode_state decoded = decode_boot_projection(
        lab_mb2_magic, lab_mb2_address, length, handoff.bytes);
    if (decoded.word[1] != 1 || decoded.word[2] != 0 ||
        (decoded.word[39] != 1 && decoded.word[39] != 2) || decoded.word[40] == 0)
        handoff_fail("lab-acpi-root-selection");
    const struct copied_acpi_sdt root = copy_acpi_sdt(decoded.word[40],
        boot_acpi_root_copy, 65536u - length, 0);
    validate_copied_acpi_sdt(&root, decoded.word[39] == 1 ? "RSDT" : "XSDT");
    const struct acpi_root_entries entries = decode_acpi_root_entries(&root, decoded.word[39]);
    if (entries.count == 0) handoff_fail("lab-acpi-empty-root");
    uint64_t addresses[MAX_ACPI_ROOT_ENTRIES];
    for (uint32_t i = 0; i < entries.count; ++i) {
        addresses[i] = decode_acpi_root_entry(&entries, i);
        if (addresses[i] == root.physical_address) handoff_fail("lab-acpi-root-cycle");
        for (uint32_t j = 0; j < i; ++j)
            if (addresses[i] == addresses[j]) handoff_fail("lab-acpi-duplicate");
    }
    uint32_t remaining = 65536u - length - root.length;
    uint32_t arena_offset = 0;
    for (uint32_t i = 0; i < entries.count; ++i) {
        if (remaining < 36u || arena_offset >= MAX_COPIED_ACPI_TABLE_BYTES)
            handoff_fail("lab-acpi-transport-budget");
        struct copied_acpi_sdt table = copy_acpi_sdt(addresses[i],
            boot_acpi_table_copy + arena_offset, remaining, arena_offset);
        validate_copied_acpi_sdt(&table, 0);
        if (table.physical_address != addresses[i] ||
            table.next_copy_offset > MAX_COPIED_ACPI_TABLE_BYTES)
            handoff_fail("lab-acpi-copy-binding");
        boot_acpi_table_copies[i] = table;
        remaining -= table.length;
        arena_offset = table.next_copy_offset;
    }
#ifdef LEANOS_LAB_DSDT_CAPTURE
    const struct copied_acpi_sdt *fadt = 0;
    for (uint32_t i = 0; i < entries.count; ++i) {
        if (acpi_signature_matches(&boot_acpi_table_copies[i], "FACP")) {
            if (fadt) handoff_fail("lab-acpi-duplicate-fadt");
            fadt = &boot_acpi_table_copies[i];
        }
    }
    uint64_t dsdt_address;
    if (!fadt || !lab_fadt_dsdt_address(fadt->bytes, fadt->length, &dsdt_address))
        handoff_fail("lab-acpi-dsdt-selection");
    if (remaining < 36u || arena_offset >= MAX_COPIED_ACPI_TABLE_BYTES)
        handoff_fail("lab-acpi-dsdt-budget");
    const struct copied_acpi_sdt dsdt = copy_acpi_sdt(dsdt_address,
        boot_acpi_table_copy + arena_offset, remaining, arena_offset);
    validate_copied_acpi_sdt(&dsdt, "DSDT");
    if (dsdt.next_copy_offset > MAX_COPIED_ACPI_TABLE_BYTES ||
        dsdt.physical_address + dsdt.length > UINT64_C(0x100000000))
        handoff_fail("lab-acpi-dsdt-extent");
    for (uint32_t i = 0; i <= entries.count; ++i) {
        const struct copied_acpi_sdt *other = i ? &boot_acpi_table_copies[i - 1] : &root;
        if (dsdt.physical_address < other->physical_address + other->length &&
            other->physical_address < dsdt.physical_address + dsdt.length)
            handoff_fail("lab-acpi-dsdt-overlap");
    }
#endif
    /* Publish only after the complete requested set has been copied. */
    serial_puts("LEANOS-LAB/1 ACPI-BEGIN root-kind="); serial_u64(decoded.word[39]);
    serial_puts(" root-address="); serial_u64(root.physical_address);
    serial_puts(" tables="); serial_u64(entries.count);
#ifdef LEANOS_LAB_DSDT_CAPTURE
    serial_puts(" dsdt=1");
#endif
    serial_putc('\n');
    lab_emit_acpi_table(0, &root);
    for (uint32_t i = 0; i < entries.count; ++i)
        lab_emit_acpi_table(i + 1u, &boot_acpi_table_copies[i]);
#ifdef LEANOS_LAB_DSDT_CAPTURE
    lab_emit_acpi_table(entries.count + 1u, &dsdt);
#endif
    serial_puts("LEANOS-LAB/1 ACPI-END\n");
}
