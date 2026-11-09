/* The state of the law admission_exact (harness/admission_exact.c): the reference model the law's Lean exports
   keep while the header runs.  env/admission_exact.c reads it too, to shape native and interpreter runs; it is
   part of no theorem through the env. */
#ifndef LEANOS_ADMISSION_EXACT_H
#define LEANOS_ADMISSION_EXACT_H
#include <stdint.h>
#include "madt_admission_api.h"

/* The function main calls. */
#define CALL_ENVELOPE 0u    /* madt_generated_envelope */
#define CALL_ENTRIES 1u     /* madt_generated_entries */
#define CALL_RESULT 2u      /* madt_topology_admission_result */
#define CALL_ADMISSION 3u   /* madt_generated_admission */

/* The call the header may make next. */
#define EXPECT_ENVELOPE 0u  /* the envelope step: byte `at`, word `word` of 0..6 */
#define EXPECT_ENTRIES 1u   /* the entry-stream step: offset `at`, word `word` of 0..15 */
#define EXPECT_RESULT 2u    /* the admission result: word `word` of 0..3 */
#define EXPECT_NOTHING 3u   /* no call: the function must return `verdict` */

struct law {
    /* The arguments: the function, the copy's length, the executing APIC ID and the law's own copy of the
       copy's bytes; the result's ten arguments (in an admission, words 5..9 are set once the entries are). */
    uint32_t call, length, executing;
    uint8_t *copy;
    uint64_t args[10];
    /* The protocol. */
    uint32_t expect, verdict;
    uint64_t at, word;
    uint64_t state[12];    /* the old state of the current transition (the envelope's is words 0..2) */
    uint64_t answer[16];   /* the answers to the current transition or result */
    uint64_t id;           /* on OK: the APIC ID the function must write */
};
extern struct law law;
#endif
