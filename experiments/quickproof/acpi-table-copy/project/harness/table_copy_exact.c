/* Law table_copy_exact.  The physical copy and the two Lean exports the pipeline calls are this harness's: a
   firmware whose every copy may fail, or write any bytes, different ones on every call (so the header of a table
   and its full copy may disagree), and an adversarial Lean that answers every call with any 64-bit value, a
   different one each time, and checks the call.  For every root selection (any kind, any address), any capacities
   of the root and table arenas (each an object of exactly that many bytes, holding any bytes), a 36-byte header
   scratch holding any bytes, 256 zeroed copy slots and a zeroed result, acpi_copy_root_and_tables
   (acpi_pipeline) behaves as follows.  An SDT is the root, whose destination is the root arena and whose copy
   cursor starts at 0, or a table the root lists, whose destination is the table arena from the arena cursor on
   and whose copy cursor starts at the arena cursor.  Statuses are those of include/acpi_table_copy.h without the
   prefix ACPI_TABLE_COPY_.
     - Selection: when kind is neither 1 nor 2, or address is 0, it returns ROOT_SELECTION, and when address is
       2^32 or more, SDT_ADDRESS_WIDTH, without a call.  Otherwise it copies the root, then each table in order.
     - Copies: it calls the copy only with the context it was given and the SDT's address, and in order: with
       the header scratch and 36; then, when the header's bytes 4..7 declare (little-endian) a length L of 36 to
       65536 that fits the destination, with the destination and L.  So every copy stays within its object and
       64 KiB.  It returns PHYSICAL when a copy fails, and SDT_LENGTH, without the second copy, for any other L.
     - Stream: after the full copy it calls the copy stream for each chunk of 8 bytes of the copy in order (the
       last one possibly shorter) five times, for words 1, 2, 4, 5, 6 in order, each time with the carried copy
       cursor, the SDT's address, the chunk's offset, the address again, L, the offset again, the chunk's bytes
       (little-endian) as the firmware copied them, and 1 for the last chunk, 0 before.  The cursor and the
       offset of each later chunk are the answers of words 5 and 4 to the transition before.  It goes on only
       when the answers accept the transition: word 2 is 0, word 1 is 1, word 4 the chunk's end, word 6 the
       chunk, and word 5 the cursor before the last chunk and above it at the last.  At the first transition
       they do not accept it returns the first that applies: BUDGET, LENGTH, ADDRESS, OFFSET or TERMINAL when
       word 2 is 43, 44, 45, 46 or 47; ERROR when it is another nonzero value; STATUS when word 1 is not 1;
       NEXT_BYTE when word 4 is not the chunk's end; EXPOSED when word 6 is not the chunk; PARTIAL_CURSOR when
       word 5 is not the cursor before the last chunk; FINAL_CURSOR when it is not above it at the last.  The
       SDT's final cursor is word 5 of its last transition.
     - Root: after its stream it returns SDT_ENVELOPE unless the copy's bytes 4..7 are L and its signature is
       RSDT for kind 1 and XSDT for kind 2, SDT_CHECKSUM unless its bytes sum to 0 mod 256, ROOT_WIDTH unless
       L - 36 is a multiple of the width (4 for kind 1, 8 for kind 2), ROOT_ENTRIES when that leaves more than 256
       entries, and at the first entry (little-endian, width bytes) that is 0 or 2^32 or more, or equals an
       earlier one, ROOT_ENTRY_ADDRESS or ROOT_ENTRY_DUPLICATE.  With no entry it returns SEQUENCE.
     - Tables: before each table it returns BUDGET when the arena cursor has reached the table arena's capacity.
       After table t's stream it returns BUDGET when the arena cursor advanced by L rounded up to 8 passes the
       capacity, and STREAM unless the final cursor, truncated to 32 bits, is that advanced cursor.  It then
       calls the copy sequence three times, for words 1, 2, 3 in order, each time with the carried ordinal (0,
       then the answer of word 3 to the step before), the entry count, t, 1, and 1 for the last table, 0 before.
       It returns SEQUENCE unless the answers are 1, 0 and t + 1; otherwise the next table starts at the
       advanced arena cursor.  After the last table it calls nothing more.
     - MADT: it then checks the copies in order and, at the first that fails, returns SDT_ENVELOPE when its
       bytes 4..7 are not its L, SDT_CHECKSUM when its bytes do not sum to 0 mod 256, MADT_DUPLICATE when its
       signature is APIC and an earlier one's is.  Then it returns MADT_MISSING when no signature is APIC, else
       OK.
     - Writes: whatever it returns, the root arena and the table arena hold exactly the firmware's bytes where
       it was asked to copy and their prior bytes elsewhere, and the header scratch what the firmware last wrote
       there.  Once the root's stream has ended, the result's root is its address, the root arena, L and its
       final cursor truncated to 32 bits; once table t's has, slot t is its address, the table arena + its
       offset, its L and its final cursor truncated.  Once the root's width and count are accepted, the result's
       entries are the root arena + 36, the count and the width.  Every other slot and result field is
       unchanged: in particular the result names a table count and a MADT only on OK.
     - On OK the result's table count is the entry count, and its MADT the slot of the one table whose
       signature is APIC.  The tables' offsets tile the table arena from 0, in order, each table padded to 8
       and the last ending within the capacity, and each table's final cursor, truncated, is its end.
   So no firmware and no Lean answer can make the pipeline copy outside its storage, admit a table it did not
   replay through the stream, or select a MADT from an unchecked or partial copy.  The firmware and the Lean
   exports below are the reference: they check every call against this protocol, and the law's model
   (harness/table_copy_exact.h) keeps its own copy of what the firmware wrote.  Not claimed: termination (partial
   correctness; every loop is bounded); what the Lean answers mean (the BootTopology theorems); the physical copy
   itself. */
#include <stdlib.h>
#include "quickproof.h"
#include "table_copy_exact.h"

#define HEADER 36u
#define ENTRIES MAX_ACPI_ROOT_ENTRIES

struct law law;

static uint64_t any_u64(void) {
    uint64_t hi = nondet_u32();
    uint64_t lo = nondet_u32();
    return hi << 32 | lo;
}

/* n bytes from p, little-endian. */
static uint64_t little(const uint8_t *p, uint32_t n) {
    uint64_t v = 0;
    for (uint32_t i = 0; i < n; ++i)
        v = v | (uint64_t)p[i] << (8 * i);
    return v;
}

static uint32_t byte_sum(const uint8_t *p, uint32_t n) {
    uint32_t sum = 0;
    for (uint32_t i = 0; i < n; ++i)
        sum = sum + p[i];
    return sum;
}

static uint32_t padded(uint32_t n) { return (n + 7) / 8 * 8; }

static int signature(const uint8_t *p, uint8_t a, uint8_t b, uint8_t c, uint8_t d) {
    return p[0] == a && p[1] == b && p[2] == c && p[3] == d;
}

static void stop(struct law *m, uint32_t verdict) {
    m->expect = EXPECT_NOTHING;
    m->verdict = verdict;
}

static void begin_sdt(struct law *m, uint64_t address, uint8_t *destination, uint8_t *destination_expect,
                      uint32_t capacity, uint64_t cursor) {
    m->sdt_address = address;
    m->destination = destination;
    m->destination_expect = destination_expect;
    m->capacity = capacity;
    m->cursor = cursor;
    m->byte = 0;
    m->word = 0;
    m->expect = EXPECT_HEADER;
}

static void begin_table(struct law *m, uint32_t t) {
    if (m->arena >= m->table_capacity) {
        stop(m, ACPI_TABLE_COPY_BUDGET);
        return;
    }
    m->is_root = 0;
    m->table = t;
    m->offsets[t] = m->arena;
    begin_sdt(m, m->addresses[t], m->tables + m->arena, m->tables_expect + m->arena,
              m->table_capacity - m->arena, m->arena);
}

/* The root's stream ended (its copy is root_expect[0 .. length)): decode it. */
static void root_copied(struct law *m) {
    const uint8_t *r = m->root_expect;
    uint32_t n = m->length;
    m->root_done = 1;
    m->root_length = n;
    m->root_cursor = m->cursor;
    int named = m->kind == 1 ? signature(r, 'R', 'S', 'D', 'T') : signature(r, 'X', 'S', 'D', 'T');
    if (little(r + 4, 4) != n || !named) {
        stop(m, ACPI_TABLE_COPY_SDT_ENVELOPE);
        return;
    }
    if (byte_sum(r, n) % 256 != 0) {
        stop(m, ACPI_TABLE_COPY_SDT_CHECKSUM);
        return;
    }
    uint32_t width = m->kind == 1 ? 4 : 8;
    if ((n - HEADER) % width != 0) {
        stop(m, ACPI_TABLE_COPY_ROOT_WIDTH);
        return;
    }
    uint32_t count = (n - HEADER) / width;
    if (count > ENTRIES) {
        stop(m, ACPI_TABLE_COPY_ROOT_ENTRIES);
        return;
    }
    m->entries_done = 1;
    m->width = width;
    m->count = count;
    for (uint32_t i = 0; i < count; ++i) {
        uint64_t a = little(r + HEADER + i * width, width);
        if (a == 0 || a > 0xffffffffu) {
            stop(m, ACPI_TABLE_COPY_ROOT_ENTRY_ADDRESS);
            return;
        }
        for (uint32_t j = 0; j < i; ++j) {
            if (m->addresses[j] == a) {
                stop(m, ACPI_TABLE_COPY_ROOT_ENTRY_DUPLICATE);
                return;
            }
        }
        m->addresses[i] = a;
    }
    if (count == 0) {
        stop(m, ACPI_TABLE_COPY_SEQUENCE);
        return;
    }
    begin_table(m, 0);
}

/* Table `table`'s stream ended: place it. */
static void table_copied(struct law *m) {
    m->lengths[m->table] = m->length;
    m->finals[m->table] = m->cursor;
    m->ended = m->table + 1;
    uint64_t end = (uint64_t)m->arena + padded(m->length);
    if (end > m->table_capacity) {
        stop(m, ACPI_TABLE_COPY_BUDGET);
        return;
    }
    if ((uint32_t)m->cursor != end) {
        stop(m, ACPI_TABLE_COPY_STREAM);
        return;
    }
    m->arena = (uint32_t)end;
    m->word = 0;
    m->expect = EXPECT_SEQUENCE;
}

static int firmware_copy(void *context, uint64_t physical_address, uint8_t *destination, uint32_t length) {
    struct law *m = &law;
    qp_assert(context == (void *)m);
    qp_assert(m->expect == EXPECT_HEADER || m->expect == EXPECT_BODY);
    qp_assert(physical_address == m->sdt_address);
    uint8_t ok = nondet_u8();
    if (m->expect == EXPECT_HEADER) {
        qp_assert(destination == m->header && length == HEADER);
        if (ok == 0) {
            stop(m, ACPI_TABLE_COPY_PHYSICAL);
            return 0;
        }
        nondet_bytes(destination, HEADER);
        for (uint32_t i = 0; i < HEADER; ++i)
            m->header_expect[i] = destination[i];
        uint64_t declared = little(destination + 4, 4);
        if (declared < HEADER || declared > MAX_COPIED_ACPI_SDT_BYTES || declared > m->capacity) {
            stop(m, ACPI_TABLE_COPY_SDT_LENGTH);
            return ok;
        }
        m->length = (uint32_t)declared;
        m->expect = EXPECT_BODY;
        return ok;
    }
    qp_assert(destination == m->destination && length == m->length);
    qp_assert(length <= m->capacity && length <= MAX_COPIED_ACPI_SDT_BYTES);
    if (ok == 0) {
        stop(m, ACPI_TABLE_COPY_PHYSICAL);
        return 0;
    }
    nondet_bytes(destination, length);
    for (uint32_t i = 0; i < length; ++i)
        m->destination_expect[i] = destination[i];
    m->byte = 0;
    m->word = 0;
    m->expect = EXPECT_STREAM;
    return ok;
}

/* The status after the five answers to the current transition, whose chunk is `chunk`, ends at `end` and is the
   last when `last`; OK when it is accepted. */
static uint32_t transition(struct law *m, uint64_t chunk, uint64_t end, uint64_t last) {
    uint64_t status = m->answer[0], error = m->answer[1], next = m->answer[2], cursor = m->answer[3],
             exposed = m->answer[4];
    if (error == 43) return ACPI_TABLE_COPY_BUDGET;
    if (error == 44) return ACPI_TABLE_COPY_LENGTH;
    if (error == 45) return ACPI_TABLE_COPY_ADDRESS;
    if (error == 46) return ACPI_TABLE_COPY_OFFSET;
    if (error == 47) return ACPI_TABLE_COPY_TERMINAL;
    if (error != 0) return ACPI_TABLE_COPY_ERROR;
    if (status != 1) return ACPI_TABLE_COPY_STATUS;
    if (next != end) return ACPI_TABLE_COPY_NEXT_BYTE;
    if (exposed != chunk) return ACPI_TABLE_COPY_EXPOSED;
    if (!last && cursor != m->cursor) return ACPI_TABLE_COPY_PARTIAL_CURSOR;
    if (last && cursor <= m->cursor) return ACPI_TABLE_COPY_FINAL_CURSOR;
    return ACPI_TABLE_COPY_OK;
}

uint64_t leanos_boot_machine_acpi_copy_stream_step_query(
        uint64_t current_copy_offset, uint64_t current_table_address, uint64_t current_byte_offset,
        uint64_t table_address, uint64_t table_length, uint64_t byte_offset, uint64_t chunk, uint64_t terminal,
        uint64_t word) {
    struct law *m = &law;
    qp_assert(m->expect == EXPECT_STREAM && m->byte < m->length);
    qp_assert(word == (m->word < 2 ? m->word + 1 : m->word + 2));
    uint64_t end = m->length - m->byte < 8 ? m->length : m->byte + 8;
    uint64_t last = end == m->length;
    uint64_t bytes = little(m->destination_expect + m->byte, (uint32_t)(end - m->byte));
    qp_assert(current_copy_offset == m->cursor && current_table_address == m->sdt_address &&
              table_address == m->sdt_address);
    qp_assert(current_byte_offset == m->byte && byte_offset == m->byte && table_length == m->length);
    qp_assert(chunk == bytes && terminal == last);
    uint64_t v = any_u64();
    m->answer[m->word] = v;
    if (m->word < 4) {
        m->word = m->word + 1;
        return v;
    }
    uint32_t verdict = transition(m, bytes, end, last);
    if (verdict != ACPI_TABLE_COPY_OK) {
        stop(m, verdict);
        return v;
    }
    m->byte = m->answer[2];
    m->cursor = m->answer[3];
    m->word = 0;
    if (last) {
        if (m->is_root)
            root_copied(m);
        else
            table_copied(m);
    }
    return v;
}

uint64_t leanos_boot_machine_acpi_copy_sequence_step_query(
        uint64_t current_ordinal, uint64_t advertised_count, uint64_t table_ordinal, uint64_t table_complete,
        uint64_t final_table, uint64_t word) {
    struct law *m = &law;
    qp_assert(m->expect == EXPECT_SEQUENCE && word == m->word + 1);
    qp_assert(current_ordinal == m->ordinal && advertised_count == m->count && table_ordinal == m->table);
    qp_assert(table_complete == 1 && final_table == (m->table + 1 == m->count ? 1u : 0u));
    uint64_t v = any_u64();
    m->answer[m->word] = v;
    if (m->word < 2) {
        m->word = m->word + 1;
        return v;
    }
    if (m->answer[0] != 1 || m->answer[1] != 0 || m->answer[2] != m->table + 1) {
        stop(m, ACPI_TABLE_COPY_SEQUENCE);
        return v;
    }
    m->ordinal = m->answer[2];
    if (m->table + 1 == m->count)
        stop(m, VERDICT_TABLES);
    else
        begin_table(m, m->table + 1);
    return v;
}

/* Every table was copied: the status the pipeline must return, and the MADT's index when OK. */
static uint32_t madt_verdict(struct law *m, uint32_t *madt) {
    uint32_t found = 0;
    for (uint32_t t = 0; t < m->count; ++t) {
        const uint8_t *b = m->tables_expect + m->offsets[t];
        uint32_t n = m->lengths[t];
        if (little(b + 4, 4) != n) return ACPI_TABLE_COPY_SDT_ENVELOPE;
        if (byte_sum(b, n) % 256 != 0) return ACPI_TABLE_COPY_SDT_CHECKSUM;
        if (signature(b, 'A', 'P', 'I', 'C')) {
            if (found) return ACPI_TABLE_COPY_MADT_DUPLICATE;
            found = 1;
            *madt = t;
        }
    }
    return found ? ACPI_TABLE_COPY_OK : ACPI_TABLE_COPY_MADT_MISSING;
}

int main(void) {
    struct law *m = &law;
    m->kind = any_u64();
    m->address = any_u64();
    m->root_capacity = nondet_u32();
    m->table_capacity = nondet_u32();
    m->header = malloc(HEADER);
    m->root = malloc(m->root_capacity);
    m->tables = malloc(m->table_capacity);
    m->root_expect = malloc(m->root_capacity);
    m->tables_expect = malloc(m->table_capacity);
    if (m->header == NULL || m->root == NULL || m->tables == NULL || m->root_expect == NULL ||
        m->tables_expect == NULL)
        return 0;
    nondet_bytes(m->header, HEADER);
    nondet_bytes(m->root, m->root_capacity);
    nondet_bytes(m->tables, m->table_capacity);
    for (uint32_t i = 0; i < HEADER; ++i)
        m->header_expect[i] = m->header[i];
    for (uint32_t i = 0; i < m->root_capacity; ++i)
        m->root_expect[i] = m->root[i];
    for (uint32_t i = 0; i < m->table_capacity; ++i)
        m->tables_expect[i] = m->tables[i];
    struct copied_acpi_sdt copies[ENTRIES];
    for (uint32_t t = 0; t < ENTRIES; ++t) {
        copies[t].physical_address = 0;
        copies[t].bytes = NULL;
        copies[t].length = 0;
        copies[t].next_copy_offset = 0;
    }
    struct acpi_table_copy_storage storage;
    storage.header = m->header;
    storage.root = m->root;
    storage.root_capacity = m->root_capacity;
    storage.tables = m->tables;
    storage.table_capacity = m->table_capacity;
    storage.copies = copies;
    struct acpi_table_copy_result result;
    result.root.physical_address = 0;
    result.root.bytes = NULL;
    result.root.length = 0;
    result.root.next_copy_offset = 0;
    result.entries.bytes = NULL;
    result.entries.count = 0;
    result.entries.width = 0;
    result.table_count = 0;
    result.madt = NULL;
    m->root_done = 0;
    m->entries_done = 0;
    m->ended = 0;
    m->arena = 0;
    m->ordinal = 0;
    m->is_root = 1;
    m->table = 0;
    if ((m->kind != 1 && m->kind != 2) || m->address == 0)
        stop(m, ACPI_TABLE_COPY_ROOT_SELECTION);
    else if (m->address > 0xffffffffu)
        stop(m, ACPI_TABLE_COPY_SDT_ADDRESS_WIDTH);
    else
        begin_sdt(m, m->address, m->root, m->root_expect, m->root_capacity, 0);

    enum acpi_table_copy_status status = acpi_pipeline(firmware_copy, m, m->kind, m->address, &storage, &result);

    qp_assert(m->expect == EXPECT_NOTHING);
    uint32_t madt = 0;
    uint32_t verdict = m->verdict == VERDICT_TABLES ? madt_verdict(m, &madt) : m->verdict;
    qp_assert(status == verdict);
    for (uint32_t i = 0; i < HEADER; ++i)
        qp_assert(m->header[i] == m->header_expect[i]);
    for (uint32_t i = 0; i < m->root_capacity; ++i)
        qp_assert(m->root[i] == m->root_expect[i]);
    for (uint32_t i = 0; i < m->table_capacity; ++i)
        qp_assert(m->tables[i] == m->tables_expect[i]);
    if (m->root_done)
        qp_assert(result.root.physical_address == m->address && result.root.bytes == m->root &&
                  result.root.length == m->root_length && result.root.next_copy_offset == (uint32_t)m->root_cursor);
    else
        qp_assert(result.root.physical_address == 0 && result.root.bytes == NULL && result.root.length == 0 &&
                  result.root.next_copy_offset == 0);
    if (m->entries_done)
        qp_assert(result.entries.bytes == m->root + HEADER && result.entries.count == m->count &&
                  result.entries.width == m->width);
    else
        qp_assert(result.entries.bytes == NULL && result.entries.count == 0 && result.entries.width == 0);
    for (uint32_t t = 0; t < ENTRIES; ++t) {
        if (t < m->ended)
            qp_assert(copies[t].physical_address == m->addresses[t] && copies[t].bytes == m->tables + m->offsets[t] &&
                      copies[t].length == m->lengths[t] && copies[t].next_copy_offset == (uint32_t)m->finals[t]);
        else
            qp_assert(copies[t].physical_address == 0 && copies[t].bytes == NULL && copies[t].length == 0 &&
                      copies[t].next_copy_offset == 0);
    }
    if (status != ACPI_TABLE_COPY_OK) {
        qp_assert(result.table_count == 0 && result.madt == NULL);
        return 0;
    }
    qp_assert(result.table_count == m->count && result.madt == &copies[madt]);
    qp_assert(m->offsets[0] == 0);
    for (uint32_t t = 0; t < m->count; ++t) {
        uint64_t end = (uint64_t)m->offsets[t] + padded(m->lengths[t]);
        qp_assert(t + 1 == m->count ? end <= m->table_capacity : end == m->offsets[t + 1]);
        qp_assert((uint32_t)m->finals[t] == end);
    }
    return 0;
}
