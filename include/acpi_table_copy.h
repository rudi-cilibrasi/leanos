#ifndef LEANOS_ACPI_TABLE_COPY_H
#define LEANOS_ACPI_TABLE_COPY_H
#include <stdint.h>
#include "boundary-abi.h"

/* The ACPI root and table copy pipeline of boot_allocate (#614): the C between
 * the trusted physical copy and the generated checks.  It copies the selected
 * RSDT/XSDT into its own arena, replays each copy through the generated copy
 * stream, decodes the root's entries, places every table the root lists in the
 * table arena through the generated copy sequence, validates every copy and
 * selects the unique MADT.
 *
 * Every check returns a status, and the caller maps each status to its
 * failure reason (boot/kernel.c: acpi_table_copy_require).  No function here
 * returns or copies a struct by value or uses a global, so QuickProof's
 * clightgen and VST take this header (experiments/quickproof/acpi-table-copy). */

#define ACPI_SDT_HEADER_BYTES UINT32_C(36)
/* BootTopology.maxAcpiSdtBytes and BootTopology.maxAcpiRootEntries. */
#define MAX_COPIED_ACPI_SDT_BYTES UINT32_C(65536)
#define MAX_ACPI_ROOT_ENTRIES UINT32_C(256)

struct copied_acpi_sdt {
    uint64_t physical_address;
    const uint8_t *bytes;
    uint32_t length;
    uint32_t next_copy_offset;
};

struct acpi_root_entries {
    const uint8_t *bytes;
    uint32_t count;
    uint32_t width;
};

/* One status per failure reason of boot_allocate; the comment names it. */
enum acpi_table_copy_status {
    ACPI_TABLE_COPY_OK,
    ACPI_TABLE_COPY_ROOT_SELECTION,       /* topology-root-selection */
    ACPI_TABLE_COPY_SDT_ADDRESS_WIDTH,    /* topology-sdt-address-width */
    ACPI_TABLE_COPY_PHYSICAL,             /* the physical copy failed: topology-sdt-address */
    ACPI_TABLE_COPY_SDT_LENGTH,           /* topology-sdt-length */
    ACPI_TABLE_COPY_BUDGET,               /* topology-table-copy-budget */
    ACPI_TABLE_COPY_LENGTH,               /* topology-table-copy-length */
    ACPI_TABLE_COPY_ADDRESS,              /* topology-table-copy-address */
    ACPI_TABLE_COPY_OFFSET,               /* topology-table-copy-offset */
    ACPI_TABLE_COPY_TERMINAL,             /* topology-table-copy-terminal */
    ACPI_TABLE_COPY_ERROR,                /* topology-table-copy-error */
    ACPI_TABLE_COPY_STATUS,               /* topology-table-copy-status */
    ACPI_TABLE_COPY_NEXT_BYTE,            /* topology-table-copy-next-byte */
    ACPI_TABLE_COPY_EXPOSED,              /* topology-table-copy-exposed */
    ACPI_TABLE_COPY_PARTIAL_CURSOR,       /* topology-table-copy-partial-cursor */
    ACPI_TABLE_COPY_FINAL_CURSOR,         /* topology-table-copy-final-cursor */
    ACPI_TABLE_COPY_ROOT_COPY,            /* topology-root-copy */
    ACPI_TABLE_COPY_SDT_ENVELOPE,         /* topology-sdt-envelope */
    ACPI_TABLE_COPY_SDT_CHECKSUM,         /* topology-sdt-checksum */
    ACPI_TABLE_COPY_ROOT_KIND,            /* topology-root-kind */
    ACPI_TABLE_COPY_ROOT_HEADER,          /* topology-root-header */
    ACPI_TABLE_COPY_ROOT_WIDTH,           /* topology-root-width */
    ACPI_TABLE_COPY_ROOT_ENTRIES,         /* topology-root-entries */
    ACPI_TABLE_COPY_ROOT_VECTOR,          /* topology-root-vector */
    ACPI_TABLE_COPY_ROOT_ENTRY_INDEX,     /* topology-root-entry-index */
    ACPI_TABLE_COPY_ROOT_ENTRY_ADDRESS,   /* topology-root-entry-address */
    ACPI_TABLE_COPY_ROOT_ENTRY_DUPLICATE, /* topology-root-entry-duplicate */
    ACPI_TABLE_COPY_SEQUENCE,             /* topology-table-copy-sequence */
    ACPI_TABLE_COPY_BINDING,              /* topology-table-copy-binding */
    ACPI_TABLE_COPY_STREAM,               /* topology-table-copy-stream */
    ACPI_TABLE_COPY_INCOMPLETE,           /* topology-table-copy-incomplete */
    ACPI_TABLE_COPY_MADT_DUPLICATE,       /* topology-madt-duplicate */
    ACPI_TABLE_COPY_MADT_MISSING,         /* topology-madt-missing */
    ACPI_TABLE_COPY_MADT_SELECTION        /* topology-madt-selection */
};

/* Copy `length` bytes of physical memory at `physical_address` into
 * `destination`, which the caller sized for them; return nonzero when the
 * bytes were copied.  The kernel's copy (copy_acpi_physical_bytes, through a
 * page-table aperture) is a trusted boundary, and it fails the handoff itself
 * instead of returning 0. */
typedef int (*acpi_physical_copy)(void *context, uint64_t physical_address,
                                  uint8_t *destination, uint32_t length);

static inline int acpi_signature_matches(
        const struct copied_acpi_sdt *table, const char signature[4]) {
    return table->length >= 36u &&
        table->bytes[0] == (uint8_t)signature[0] &&
        table->bytes[1] == (uint8_t)signature[1] &&
        table->bytes[2] == (uint8_t)signature[2] &&
        table->bytes[3] == (uint8_t)signature[3];
}

/* Copy one complete ACPI SDT into kernel-owned storage before generated
   validation sees it.  Address translation and this byte copy remain trusted;
   signature, declared-length, checksum, root-entry, and MADT admission checks
   remain the generated boundary's responsibility.  The caller supplies a
   dedicated immutable-after-copy arena so the selected root and candidate
   table cannot alias each other.  The 36-byte header is copied into `header`
   first; the table goes to `destination`, which holds `destination_capacity`
   bytes.  On success the copy is written to `copied`. */
static inline enum acpi_table_copy_status acpi_copy_sdt(
        acpi_physical_copy copy, void *context, uint64_t physical_address,
        uint8_t *header, uint8_t *destination, uint32_t destination_capacity,
        uint32_t current_copy_offset, struct copied_acpi_sdt *copied) {
    if (physical_address > UINT64_C(0xffffffff))
        return ACPI_TABLE_COPY_SDT_ADDRESS_WIDTH;
    if (!copy(context, physical_address, header, ACPI_SDT_HEADER_BYTES))
        return ACPI_TABLE_COPY_PHYSICAL;
    uint32_t length = (uint32_t)header[4] |
        (uint32_t)header[5] << 8 |
        (uint32_t)header[6] << 16 |
        (uint32_t)header[7] << 24;
    if (length < 36u || length > MAX_COPIED_ACPI_SDT_BYTES ||
        length > destination_capacity)
        return ACPI_TABLE_COPY_SDT_LENGTH;
    if (!copy(context, physical_address, destination, length))
        return ACPI_TABLE_COPY_PHYSICAL;
    uint64_t byte_offset = 0;
    uint64_t next_copy_offset = current_copy_offset;
    while (byte_offset < length) {
        const uint32_t remaining = length - (uint32_t)byte_offset;
        const uint32_t chunk_bytes = remaining < 8u ? remaining : 8u;
        uint64_t physical_chunk = 0;
        for (uint32_t byte = 0; byte < chunk_bytes; ++byte)
            physical_chunk |=
                (uint64_t)destination[byte_offset + byte] << (byte * 8u);
        const uint64_t terminal = byte_offset + chunk_bytes == length;
#define COPY_STREAM_QUERY(query) leanos_boot_machine_acpi_copy_stream_step_query( \
            next_copy_offset, physical_address, byte_offset, physical_address, \
            length, byte_offset, physical_chunk, terminal, (query))
        const uint64_t status = COPY_STREAM_QUERY(1);
        const uint64_t error = COPY_STREAM_QUERY(2);
        const uint64_t next_byte = COPY_STREAM_QUERY(4);
        const uint64_t emitted_copy_offset = COPY_STREAM_QUERY(5);
        const uint64_t exposed = COPY_STREAM_QUERY(6);
#undef COPY_STREAM_QUERY
        if (error == 43) return ACPI_TABLE_COPY_BUDGET;
        if (error == 44) return ACPI_TABLE_COPY_LENGTH;
        if (error == 45) return ACPI_TABLE_COPY_ADDRESS;
        if (error == 46) return ACPI_TABLE_COPY_OFFSET;
        if (error == 47) return ACPI_TABLE_COPY_TERMINAL;
        if (error != 0) return ACPI_TABLE_COPY_ERROR;
        if (status != 1) return ACPI_TABLE_COPY_STATUS;
        if (next_byte != byte_offset + chunk_bytes)
            return ACPI_TABLE_COPY_NEXT_BYTE;
        if (exposed != physical_chunk)
            return ACPI_TABLE_COPY_EXPOSED;
        if (!terminal && emitted_copy_offset != next_copy_offset)
            return ACPI_TABLE_COPY_PARTIAL_CURSOR;
        if (terminal && emitted_copy_offset <= next_copy_offset)
            return ACPI_TABLE_COPY_FINAL_CURSOR;
        for (uint32_t byte = 0; byte < chunk_bytes; ++byte)
            destination[byte_offset + byte] =
                (uint8_t)(exposed >> (byte * 8u));
        byte_offset = next_byte;
        if (terminal) next_copy_offset = emitted_copy_offset;
    }
    copied->physical_address = physical_address;
    copied->bytes = destination;
    copied->length = length;
    copied->next_copy_offset = (uint32_t)next_copy_offset;
    return ACPI_TABLE_COPY_OK;
}

/* Admit only the immutable copy: copied header, declared extent, expected
   signature (when supplied), and whole-table ACPI checksum must agree before
   root-entry decoding or MADT selection. */
static inline enum acpi_table_copy_status acpi_validate_copied_sdt(
        const struct copied_acpi_sdt *table, const char *signature) {
    if (table->bytes == 0 || table->length < 36u ||
        ((uint32_t)table->bytes[4] |
         (uint32_t)table->bytes[5] << 8 |
         (uint32_t)table->bytes[6] << 16 |
         (uint32_t)table->bytes[7] << 24) != table->length ||
        (signature != 0 && !acpi_signature_matches(table, signature)))
        return ACPI_TABLE_COPY_SDT_ENVELOPE;
    uint8_t checksum = 0;
    for (uint32_t byte = 0; byte < table->length; ++byte)
        checksum = (uint8_t)(checksum + table->bytes[byte]);
    if (checksum != 0) return ACPI_TABLE_COPY_SDT_CHECKSUM;
    return ACPI_TABLE_COPY_OK;
}

/* Validate every copy, in order, and write the one MADT to `madt`. */
static inline enum acpi_table_copy_status acpi_select_unique_madt(
        const struct copied_acpi_sdt *copies, uint32_t copied_count,
        const struct copied_acpi_sdt **madt) {
    const struct copied_acpi_sdt *selected = 0;
    for (uint32_t index = 0; index < copied_count; ++index) {
        const struct copied_acpi_sdt *candidate = &copies[index];
        const enum acpi_table_copy_status status =
            acpi_validate_copied_sdt(candidate, 0);
        if (status != ACPI_TABLE_COPY_OK) return status;
        if (acpi_signature_matches(candidate, "APIC")) {
            if (selected != 0) return ACPI_TABLE_COPY_MADT_DUPLICATE;
            selected = candidate;
        }
    }
    if (selected == 0) return ACPI_TABLE_COPY_MADT_MISSING;
    *madt = selected;
    return ACPI_TABLE_COPY_OK;
}

/* Bind the copied root payload shape to the generated RSDT/XSDT selection
   before any advertised physical address is translated.  The 256-entry cap
   is the machine rendering of BootTopology.maxAcpiRootEntries. */
static inline enum acpi_table_copy_status acpi_decode_root_entries(
        const struct copied_acpi_sdt *root, uint64_t selected_kind,
        struct acpi_root_entries *entries) {
    uint32_t width;
    if (selected_kind == 1u) width = 4u;
    else if (selected_kind == 2u) width = 8u;
    else return ACPI_TABLE_COPY_ROOT_KIND;
    if (root->length < 36u) return ACPI_TABLE_COPY_ROOT_HEADER;
    const uint32_t payload = root->length - 36u;
    if (payload % width != 0u) return ACPI_TABLE_COPY_ROOT_WIDTH;
    const uint32_t count = payload / width;
    if (count > MAX_ACPI_ROOT_ENTRIES)
        return ACPI_TABLE_COPY_ROOT_ENTRIES;
    entries->bytes = root->bytes + 36u;
    entries->count = count;
    entries->width = width;
    return ACPI_TABLE_COPY_OK;
}

static inline enum acpi_table_copy_status acpi_decode_root_entry(
        const struct acpi_root_entries *entries, uint32_t index,
        uint64_t *address) {
    if (index >= entries->count ||
        (entries->width != 4u && entries->width != 8u))
        return ACPI_TABLE_COPY_ROOT_ENTRY_INDEX;
    uint64_t physical_address = 0;
    const uint8_t *encoded = entries->bytes + index * entries->width;
    for (uint32_t byte = 0; byte < entries->width; ++byte)
        physical_address |= (uint64_t)encoded[byte] << (byte * 8u);
    if (physical_address == 0 || physical_address > UINT64_C(0xffffffff))
        return ACPI_TABLE_COPY_ROOT_ENTRY_ADDRESS;
    *address = physical_address;
    return ACPI_TABLE_COPY_OK;
}

/* Decode every entry of the root into `addresses` and reject a duplicate
   address.  entries->count is at most MAX_ACPI_ROOT_ENTRIES
   (acpi_decode_root_entries). */
static inline enum acpi_table_copy_status acpi_decode_root_addresses(
        const struct acpi_root_entries *entries,
        uint64_t addresses[MAX_ACPI_ROOT_ENTRIES]) {
    for (uint32_t entry = 0; entry < entries->count; ++entry) {
        const enum acpi_table_copy_status status =
            acpi_decode_root_entry(entries, entry, &addresses[entry]);
        if (status != ACPI_TABLE_COPY_OK) return status;
        for (uint32_t prior = 0; prior < entry; ++prior)
            if (addresses[prior] == addresses[entry])
                return ACPI_TABLE_COPY_ROOT_ENTRY_DUPLICATE;
    }
    return ACPI_TABLE_COPY_OK;
}

/* Translate every advertised root entry into a disjoint kernel-owned byte
   range before firmware memory can be scrubbed or reused.  The tables go to
   `arena`, which holds `arena_capacity` bytes, each at the arena cursor padded
   to 8, and table `entry` is described in copies[entry].  The kernel's
   one-MiB arena is a deliberately tighter machine boundary than the model's
   per-table 64-KiB cap: a root whose complete translation does not fit is
   rejected rather than partially admitted. */
static inline enum acpi_table_copy_status acpi_copy_root_tables(
        acpi_physical_copy copy, void *context,
        const struct acpi_root_entries *entries,
        const uint64_t addresses[MAX_ACPI_ROOT_ENTRIES], uint8_t *header,
        uint8_t *arena, uint32_t arena_capacity,
        struct copied_acpi_sdt copies[MAX_ACPI_ROOT_ENTRIES],
        uint32_t *copied_count) {
    if (entries->count == 0)
        return ACPI_TABLE_COPY_SEQUENCE;
    uint32_t arena_offset = 0;
    uint64_t copied_ordinal = 0;
    for (uint32_t entry = 0; entry < entries->count; ++entry) {
        if (arena_offset >= arena_capacity)
            return ACPI_TABLE_COPY_BUDGET;
        struct copied_acpi_sdt *copied = &copies[entry];
        const enum acpi_table_copy_status copy_status = acpi_copy_sdt(
            copy, context, addresses[entry], header, arena + arena_offset,
            arena_capacity - arena_offset, arena_offset, copied);
        if (copy_status != ACPI_TABLE_COPY_OK) return copy_status;
        if (copied->physical_address != addresses[entry] ||
            copied->bytes != arena + arena_offset)
            return ACPI_TABLE_COPY_BINDING;
        const uint32_t padded_length = (copied->length + 7u) & ~7u;
        if (padded_length < copied->length ||
            padded_length > arena_capacity - arena_offset)
            return ACPI_TABLE_COPY_BUDGET;
        if (copied->next_copy_offset != arena_offset + padded_length)
            return ACPI_TABLE_COPY_STREAM;
        arena_offset += padded_length;
        const uint64_t final_table = entry + 1u == entries->count;
        const uint64_t status =
            leanos_boot_machine_acpi_copy_sequence_step_query(
                copied_ordinal, entries->count, entry, 1, final_table, 1);
        const uint64_t error =
            leanos_boot_machine_acpi_copy_sequence_step_query(
                copied_ordinal, entries->count, entry, 1, final_table, 2);
        const uint64_t next_ordinal =
            leanos_boot_machine_acpi_copy_sequence_step_query(
                copied_ordinal, entries->count, entry, 1, final_table, 3);
        if (status != 1 || error != 0 || next_ordinal != entry + 1u)
            return ACPI_TABLE_COPY_SEQUENCE;
        copied_ordinal = next_ordinal;
    }
    if (copied_ordinal != entries->count)
        return ACPI_TABLE_COPY_SEQUENCE;
    *copied_count = entries->count;
    return ACPI_TABLE_COPY_OK;
}

/* The storage the pipeline copies into: none of it may alias another. */
struct acpi_table_copy_storage {
    uint8_t *header;                 /* ACPI_SDT_HEADER_BYTES: each SDT header is read here first */
    uint8_t *root;                   /* the selected root's copy */
    uint32_t root_capacity;          /* bytes of `root` */
    uint8_t *tables;                 /* the copies of the tables the root lists */
    uint32_t table_capacity;         /* bytes of `tables` */
    struct copied_acpi_sdt *copies;  /* MAX_ACPI_ROOT_ENTRIES slots, one per table */
};

/* What the pipeline publishes on ACPI_TABLE_COPY_OK. */
struct acpi_table_copy_result {
    struct copied_acpi_sdt root;          /* the selected root's copy */
    struct acpi_root_entries entries;     /* its entry vector */
    uint32_t table_count;                 /* the tables copied: entries.count */
    const struct copied_acpi_sdt *madt;   /* the unique MADT among copies[0 .. table_count) */
};

/* The pipeline: from the generated RSDT/XSDT selection (kind 1 or 2 and the
   root's physical address) to the unique MADT copy, in boot_allocate's order.
   It writes `result` as it goes; the caller reads it only on
   ACPI_TABLE_COPY_OK. */
static inline enum acpi_table_copy_status acpi_copy_root_and_tables(
        acpi_physical_copy copy, void *context, uint64_t selected_kind,
        uint64_t selected_address,
        const struct acpi_table_copy_storage *storage,
        struct acpi_table_copy_result *result) {
    if ((selected_kind != 1 && selected_kind != 2) || selected_address == 0)
        return ACPI_TABLE_COPY_ROOT_SELECTION;
    struct copied_acpi_sdt *selected_root = &result->root;
    enum acpi_table_copy_status status = acpi_copy_sdt(
        copy, context, selected_address, storage->header, storage->root,
        storage->root_capacity, 0, selected_root);
    if (status != ACPI_TABLE_COPY_OK) return status;
    if (selected_root->physical_address != selected_address ||
        selected_root->bytes != storage->root || selected_root->length < 36u)
        return ACPI_TABLE_COPY_ROOT_COPY;
    status = acpi_validate_copied_sdt(
        selected_root, selected_kind == 1 ? "RSDT" : "XSDT");
    if (status != ACPI_TABLE_COPY_OK) return status;
    struct acpi_root_entries *root_entries = &result->entries;
    status = acpi_decode_root_entries(selected_root, selected_kind,
                                      root_entries);
    if (status != ACPI_TABLE_COPY_OK) return status;
    if (root_entries->bytes != selected_root->bytes + 36u ||
        (root_entries->width != 4u && root_entries->width != 8u))
        return ACPI_TABLE_COPY_ROOT_VECTOR;
    uint64_t root_table_addresses[MAX_ACPI_ROOT_ENTRIES];
    status = acpi_decode_root_addresses(root_entries, root_table_addresses);
    if (status != ACPI_TABLE_COPY_OK) return status;
    uint32_t copied_table_count = 0;
    status = acpi_copy_root_tables(copy, context, root_entries,
        root_table_addresses, storage->header, storage->tables,
        storage->table_capacity, storage->copies, &copied_table_count);
    if (status != ACPI_TABLE_COPY_OK) return status;
    if (copied_table_count != root_entries->count)
        return ACPI_TABLE_COPY_INCOMPLETE;
    const struct copied_acpi_sdt *selected_madt = 0;
    status = acpi_select_unique_madt(storage->copies, copied_table_count,
                                     &selected_madt);
    if (status != ACPI_TABLE_COPY_OK) return status;
    if (!acpi_signature_matches(selected_madt, "APIC"))
        return ACPI_TABLE_COPY_MADT_SELECTION;
    result->table_count = copied_table_count;
    result->madt = selected_madt;
    return ACPI_TABLE_COPY_OK;
}

#endif
