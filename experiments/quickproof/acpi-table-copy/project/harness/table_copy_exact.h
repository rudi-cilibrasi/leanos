/* The state of the law table_copy_exact (harness/table_copy_exact.c): the reference model the law's firmware and
   Lean exports keep while the pipeline runs.  env/table_copy_exact.c reads it too, to shape native and interpreter
   runs; it is part of no theorem through the env. */
#ifndef LEANOS_TABLE_COPY_EXACT_H
#define LEANOS_TABLE_COPY_EXACT_H
#include <stdint.h>
#include "acpi_api.h"

/* The call the pipeline may make next. */
#define EXPECT_HEADER 0u     /* the firmware: the current SDT's 36-byte header, into the header scratch */
#define EXPECT_BODY 1u       /* the firmware: the current SDT, its declared length, into its destination */
#define EXPECT_STREAM 2u     /* the copy stream: the chunk at `byte`, word `word` of 1, 2, 4, 5, 6 */
#define EXPECT_SEQUENCE 3u   /* the copy sequence: table `table`, word `word` of 1, 2, 3 */
#define EXPECT_NOTHING 4u    /* no call: the pipeline must return `verdict` */
#define VERDICT_TABLES 255u  /* `verdict` once every table was copied: main decides on the MADT */

struct law {
    /* The arguments. */
    uint64_t kind, address;
    uint8_t *header, *root, *tables;
    uint32_t root_capacity, table_capacity;
    /* What the header scratch and each arena must hold when the pipeline returns: their prior bytes, and the
       firmware's bytes where the pipeline asked it to copy. */
    uint8_t header_expect[36];
    uint8_t *root_expect, *tables_expect;
    /* The protocol. */
    uint32_t expect, verdict;
    /* The SDT being copied: the root, or table `table`. */
    uint32_t is_root, table;
    uint64_t sdt_address;
    uint8_t *destination, *destination_expect;
    uint32_t capacity, length;   /* its destination's capacity; the length its header declared */
    uint64_t cursor, byte;       /* the carried copy cursor and chunk offset */
    uint32_t word;
    uint64_t answer[5];          /* the answers of the current stream transition or sequence step */
    /* The root: whether its stream ended, and then its length and final cursor; whether its width and count
       were accepted, and then they and its entries. */
    uint32_t root_done, root_length, entries_done, width, count;
    uint64_t root_cursor;
    uint64_t addresses[MAX_ACPI_ROOT_ENTRIES];
    /* The tables: the arena cursor, how many streams ended, each table's offset, length and final cursor; the
       carried ordinal. */
    uint32_t arena, ended;
    uint32_t offsets[MAX_ACPI_ROOT_ENTRIES], lengths[MAX_ACPI_ROOT_ENTRIES];
    uint64_t finals[MAX_ACPI_ROOT_ENTRIES];
    uint64_t ordinal;
};
extern struct law law;
#endif
