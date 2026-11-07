/* Law admission_exact.  The three Lean exports the header calls are this harness's: an adversarial Lean that
   answers every call with any 64-bit value, a different one each time, and checks the call.  For every MADT copy
   (any length, an object of exactly that many bytes holding any bytes), every executing APIC ID (any 32-bit
   value), any ten result arguments a0..a9 and any prior value of the APIC ID record a function may write, main
   calls one of the four functions of include/madt_generated_admission.h (patch/madt_admission_unit.c), and it
   behaves as follows.  Statuses are those of the header without the prefix MADT_GENERATED_; word k of a
   transition or of the result is the answer to its call for word k.
     - Envelope (madt_generated_envelope): for each byte i of the copy in order, it calls the envelope step
       exactly 7 times, for words 0..6 in order, each with the same old state (offset, declared length, checksum),
       the copy's length, the offset i, byte i and the terminal marker: 1 at the last byte, 0 before.  The old
       state is (0, 0, 0) at byte 0 and words 3, 4, 5 of the previous byte's answers after.  It goes on to the next
       byte only when the answers accept the transition: word 0 is 1, word 1 is 3 at the last byte and 1 before,
       word 2 is 0, word 3 is i + 1 and word 6 is byte i.  At the first transition they do not accept it returns
       the first that applies of ENVELOPE_ABI (word 0), ENVELOPE_STATUS (word 1), ENVELOPE_ERROR (word 2),
       ENVELOPE_NEXT_BYTE (word 3) and ENVELOPE_EXPOSED (word 6), and calls nothing more.  After the last byte (at
       once for an empty copy), with the final state words 3, 4, 5 of the last answers ((0, 0, 0) for an empty
       copy), it returns ENVELOPE_LENGTH unless the final declared length is the copy's length, then
       ENVELOPE_CHECKSUM unless the final checksum is 0, else OK.
     - Entries (madt_generated_entries): when the copy has 44 bytes or fewer, or the executing ID is above 255, it
       returns ENTRIES_BOUNDS without a call.  Otherwise for each offset k from 44 to the copy's last in order, it
       calls the entry-stream step exactly 16 times, for words 0..15 in order, each with the same twelve old state
       words, the copy's length, the executing ID, the offset k and byte k.  The old state is
       [44,0,0,0,0,0,0,256,0,0,0,0] at offset 44 and words 3..14 of the previous byte's answers after.  It goes on
       only when the answers accept the transition: word 0 is 1, word 1 is 3 at the last byte and 1 before, word 2
       is 0, word 3 is k + 1 and word 15 is byte k.  At the first transition they do not accept it returns the
       first that applies of ENTRIES_ABI, ENTRIES_STATUS, ENTRIES_ERROR, ENTRIES_NEXT_OFFSET (word 3) and
       ENTRIES_EXPOSED (word 15), and calls nothing more.  After the last byte, with the final state s0..s11 words
       3..14 of the last answers, it returns ENTRIES_RECORD unless s1..s5 are all 0, then ENTRIES_ENABLED unless s6
       is 1, then ENTRIES_APIC_ID unless s7 is the executing ID, then ENTRIES_SEEN unless one of s8..s11 is
       nonzero; else OK, writing s7 to the APIC ID record.
     - Result (madt_topology_admission_result, with a0..a9): it calls the admission result exactly 4 times, for
       words 0..3 in order, each with a0..a9.  It returns RESULT_ABI unless word 0 is 1, then RESULT_STATUS unless
       word 1 is 1, then RESULT_ERROR unless word 2 is 0, then RESULT_APIC_ID unless word 3 is below 2^32 and
       equal to both a8 and a9; else OK, writing word 3 to the APIC ID record.
     - Admission (madt_generated_admission, with a0..a4): the envelope's calls and status; when that is OK, the
       entries' calls and status; when that is OK too, the result's calls and status, its arguments a0..a4, 1
       (one MADT), 1 and 0 (the accepted admission's status and detail), the entries' s7 and the executing ID.
       It returns the first status that is not OK, or OK, and writes the result's word 3 on OK only.
     - Calls and writes: a function makes no call to the exports but those above; none writes the copy, and one
       writes the APIC ID record only when it returns OK (the envelope never).
   So no Lean answer can make the header skip a byte, ask a transition about another state, offset or byte than
   the ones it carries, go on after a rejected transition, accept a final state the law rejects, or publish an
   APIC ID that the entry stream and the admission result did not both admit.  The Lean exports below are the
   reference: they keep the state the header must carry, check every call against it and decide the status;
   main compares the status, the copy and the APIC ID record.  Not claimed: termination (partial correctness;
   every loop is bounded); what the Lean answers mean (the BootTopology theorems); a NULL copy or APIC ID record
   (the kernel passes its MADT copy and a local). */
#include <stdlib.h>
#include "quickproof.h"
#include "admission_exact.h"

struct law law;

static uint64_t any_u64(void) {
    uint64_t hi = nondet_u32();
    uint64_t lo = nondet_u32();
    return hi << 32 | lo;
}

static void stop(struct law *m, uint32_t verdict) {
    m->expect = EXPECT_NOTHING;
    m->verdict = verdict;
}

/* The entries' turn: their bounds, then offset 44 with the initial state. */
static void begin_entries(struct law *m) {
    if (m->length <= 44 || m->executing > 255) {
        stop(m, MADT_GENERATED_ENTRIES_BOUNDS);
        return;
    }
    for (uint32_t k = 0; k < 12; ++k)
        m->state[k] = 0;
    m->state[0] = 44;
    m->state[7] = 256;
    m->at = 44;
    m->word = 0;
    m->expect = EXPECT_ENTRIES;
}

/* The envelope accepted every byte; its final state is state[0..2]. */
static void envelope_done(struct law *m) {
    if (m->state[1] != m->length) {
        stop(m, MADT_GENERATED_ENVELOPE_LENGTH);
        return;
    }
    if (m->state[2] != 0) {
        stop(m, MADT_GENERATED_ENVELOPE_CHECKSUM);
        return;
    }
    if (m->call == CALL_ENVELOPE)
        stop(m, MADT_GENERATED_OK);
    else
        begin_entries(m);
}

/* The entry stream accepted every byte; its final state is state[0..11]. */
static void entries_done(struct law *m) {
    uint64_t *s = m->state;
    if (s[1] != 0 || s[2] != 0 || s[3] != 0 || s[4] != 0 || s[5] != 0) {
        stop(m, MADT_GENERATED_ENTRIES_RECORD);
        return;
    }
    if (s[6] != 1) {
        stop(m, MADT_GENERATED_ENTRIES_ENABLED);
        return;
    }
    if (s[7] != m->executing) {
        stop(m, MADT_GENERATED_ENTRIES_APIC_ID);
        return;
    }
    if (s[8] == 0 && s[9] == 0 && s[10] == 0 && s[11] == 0) {
        stop(m, MADT_GENERATED_ENTRIES_SEEN);
        return;
    }
    if (m->call == CALL_ENTRIES) {
        m->id = s[7];
        stop(m, MADT_GENERATED_OK);
        return;
    }
    m->args[5] = 1;
    m->args[6] = 1;
    m->args[7] = 0;
    m->args[8] = s[7];
    m->args[9] = m->executing;
    m->word = 0;
    m->expect = EXPECT_RESULT;
}

uint64_t leanos_boot_machine_madt_envelope_byte_step_query(
        uint64_t current_offset, uint64_t declared_length, uint64_t checksum, uint64_t table_length,
        uint64_t byte_offset, uint64_t byte_value, uint64_t terminal, uint64_t word) {
    struct law *m = &law;
    qp_assert(m->expect == EXPECT_ENVELOPE && word == m->word);
    qp_assert(current_offset == m->state[0] && declared_length == m->state[1] && checksum == m->state[2]);
    uint64_t last = m->at + 1 == m->length;
    qp_assert(table_length == m->length && byte_offset == m->at && byte_value == m->copy[m->at]);
    qp_assert(terminal == last);
    uint64_t v = any_u64();
    m->answer[word] = v;
    if (word < 6) {
        m->word = word + 1;
        return v;
    }
    uint64_t *a = m->answer;
    if (a[0] != 1)
        stop(m, MADT_GENERATED_ENVELOPE_ABI);
    else if (a[1] != (last ? 3u : 1u))
        stop(m, MADT_GENERATED_ENVELOPE_STATUS);
    else if (a[2] != 0)
        stop(m, MADT_GENERATED_ENVELOPE_ERROR);
    else if (a[3] != m->at + 1)
        stop(m, MADT_GENERATED_ENVELOPE_NEXT_BYTE);
    else if (a[6] != m->copy[m->at])
        stop(m, MADT_GENERATED_ENVELOPE_EXPOSED);
    else {
        m->state[0] = a[3];
        m->state[1] = a[4];
        m->state[2] = a[5];
        m->at = m->at + 1;
        m->word = 0;
        if (last)
            envelope_done(m);
    }
    return v;
}

uint64_t leanos_boot_machine_madt_entry_stream_byte_step_query(
        uint64_t s0, uint64_t s1, uint64_t s2, uint64_t s3, uint64_t s4, uint64_t s5, uint64_t s6, uint64_t s7,
        uint64_t s8, uint64_t s9, uint64_t s10, uint64_t s11, uint64_t table_length, uint64_t executing_apic_id,
        uint64_t byte_offset, uint64_t byte_value, uint64_t word) {
    struct law *m = &law;
    qp_assert(m->expect == EXPECT_ENTRIES && word == m->word);
    qp_assert(s0 == m->state[0] && s1 == m->state[1] && s2 == m->state[2] && s3 == m->state[3]);
    qp_assert(s4 == m->state[4] && s5 == m->state[5] && s6 == m->state[6] && s7 == m->state[7]);
    qp_assert(s8 == m->state[8] && s9 == m->state[9] && s10 == m->state[10] && s11 == m->state[11]);
    qp_assert(table_length == m->length && executing_apic_id == m->executing);
    qp_assert(byte_offset == m->at && byte_value == m->copy[m->at]);
    uint64_t v = any_u64();
    m->answer[word] = v;
    if (word < 15) {
        m->word = word + 1;
        return v;
    }
    uint64_t last = m->at + 1 == m->length;
    uint64_t *a = m->answer;
    if (a[0] != 1)
        stop(m, MADT_GENERATED_ENTRIES_ABI);
    else if (a[1] != (last ? 3u : 1u))
        stop(m, MADT_GENERATED_ENTRIES_STATUS);
    else if (a[2] != 0)
        stop(m, MADT_GENERATED_ENTRIES_ERROR);
    else if (a[3] != m->at + 1)
        stop(m, MADT_GENERATED_ENTRIES_NEXT_OFFSET);
    else if (a[15] != m->copy[m->at])
        stop(m, MADT_GENERATED_ENTRIES_EXPOSED);
    else {
        for (uint32_t k = 0; k < 12; ++k)
            m->state[k] = a[k + 3];
        m->at = m->at + 1;
        m->word = 0;
        if (last)
            entries_done(m);
    }
    return v;
}

uint64_t leanos_boot_machine_topology_admission_result_query(
        uint64_t selected_kind, uint64_t selected_address, uint64_t copied_root_address, uint64_t advertised_count,
        uint64_t completed_copies, uint64_t madt_count, uint64_t admission_status, uint64_t admission_detail,
        uint64_t admitted_apic_id, uint64_t executing_apic_id, uint64_t word) {
    struct law *m = &law;
    qp_assert(m->expect == EXPECT_RESULT && word == m->word);
    qp_assert(selected_kind == m->args[0] && selected_address == m->args[1] && copied_root_address == m->args[2]);
    qp_assert(advertised_count == m->args[3] && completed_copies == m->args[4] && madt_count == m->args[5]);
    qp_assert(admission_status == m->args[6] && admission_detail == m->args[7]);
    qp_assert(admitted_apic_id == m->args[8] && executing_apic_id == m->args[9]);
    uint64_t v = any_u64();
    m->answer[word] = v;
    if (word < 3) {
        m->word = word + 1;
        return v;
    }
    uint64_t *a = m->answer;
    if (a[0] != 1)
        stop(m, MADT_GENERATED_RESULT_ABI);
    else if (a[1] != 1)
        stop(m, MADT_GENERATED_RESULT_STATUS);
    else if (a[2] != 0)
        stop(m, MADT_GENERATED_RESULT_ERROR);
    else if (a[3] > 0xffffffffu || a[3] != m->args[8] || a[3] != m->args[9])
        stop(m, MADT_GENERATED_RESULT_APIC_ID);
    else {
        m->id = a[3];
        stop(m, MADT_GENERATED_OK);
    }
    return v;
}

int main(void) {
    struct law *m = &law;
    uint8_t call = nondet_u8();
    m->call = call < CALL_ADMISSION ? call : CALL_ADMISSION;
    m->length = nondet_u32();
    m->executing = nondet_u32();
    uint8_t *madt = malloc(m->length);
    m->copy = malloc(m->length);
    if (madt == NULL || m->copy == NULL)
        return 0;
    nondet_bytes(madt, m->length);
    for (uint32_t i = 0; i < m->length; ++i)
        m->copy[i] = madt[i];
    for (uint32_t k = 0; k < 10; ++k)
        m->args[k] = any_u64();
    uint32_t id = nondet_u32();
    uint32_t prior = id;
    m->id = 0;
    m->verdict = MADT_GENERATED_OK;
    m->at = 0;
    m->word = 0;
    for (uint32_t k = 0; k < 12; ++k)
        m->state[k] = 0;
    if (m->call == CALL_RESULT)
        m->expect = EXPECT_RESULT;
    else if (m->call == CALL_ENTRIES)
        begin_entries(m);
    else {
        m->expect = EXPECT_ENVELOPE;
        if (m->length == 0)
            envelope_done(m);
    }

    enum madt_generated_status status;
    if (m->call == CALL_ENVELOPE)
        status = madt_envelope(madt, m->length);
    else if (m->call == CALL_ENTRIES)
        status = madt_entries(madt, m->length, m->executing, &id);
    else if (m->call == CALL_RESULT)
        status = madt_result(m->args[0], m->args[1], m->args[2], m->args[3], m->args[4], m->args[5], m->args[6],
                             m->args[7], m->args[8], m->args[9], &id);
    else
        status = madt_admission(madt, m->length, m->executing, m->args[0], m->args[1], m->args[2], m->args[3],
                                m->args[4], &id);

    qp_assert(m->expect == EXPECT_NOTHING && status == m->verdict);
    for (uint32_t i = 0; i < m->length; ++i)
        qp_assert(madt[i] == m->copy[i]);
    if (status == MADT_GENERATED_OK && m->call != CALL_ENVELOPE)
        qp_assert(id == m->id);
    else
        qp_assert(id == prior);
    return 0;
}
