/* Law consumer_obligations.  The three Lean exports the consumer calls are this harness's: an adversarial Lean that
   answers every call with any 64-bit value, a different one each time, and checks the call.  For every entry span
   (any bytes; any length, the span exactly that long when the consumer accepts the length) and every executing-CPU
   observation, each of the span, the observation and the result record either present or NULL,
   qotom_bind_validated_madt_entries (madt_bind) meets the caller obligations of docs/qotom-madt-consumer-review.md:
     - it reads only the span and the observation, and writes only the result record;
     - with no result record it returns 1 and calls nothing;  with an absent span or observation, a length of 0
       or above 65536 - 44, it returns 1 and publishes status 1, detail 0, offset 44, calling nothing;
     - stream: for each byte i of the span in order, it calls the stream step exactly 16 times, for projections
       0..15 in order, each with the same twelve state words, the table length 44 + length, the observation's
       executing APIC ID, the byte's offset 44 + i and the byte itself.  The state is the initial
       [44,0,0,0,0,0,0,256,0,0,0,0] for the first byte and projections 3..14 of the previous byte's answers after;
     - it goes on to the next byte only when the answers accept the transition: projection 0 is 1, projection 1
       is 3 at the last byte and 1 before it, projection 2 is 0, projection 3 is the next offset and projection 15
       echoes the byte;  on the first transition they reject it returns 2 with projection 2 as the detail when
       projection 0 is 1 and projection 1 is 2, else 3, at that byte's offset, and calls nothing more;
     - after the last byte, it walks the span's records (byte 1 of each its length): when one is shorter than 2
       bytes, runs past the span, or is an NMI record (type 4) other than 6 bytes long, it returns 3 and calls
       nothing more;  else it calls the NMI policy exactly 5 times, for words 0..4 in order, with the number of
       NMI records, the first four of them (little-endian, 0 when absent) and the observation's routing authority;
     - it calls the finish exactly 6 times, for words 0..5 in order, with the last transition's projections 1 and 2,
       the final state, the table length and the observation, exactly when the NMI policy answered 1, 1, 0, 1, 4;
       otherwise it returns 5 with the policy's word 2 as the detail when words 0, 3 and 4 are in range and word 1
       is not 1, else 3;
     - it returns 0 exactly when the finish answered 1, 1, the executing ID, state word 6, the APIC base and 0,
       publishing those three; otherwise it returns 4 with finish word 2 as the detail when words 0 and 5 are 1
       and 0 and word 1 is 2 or 5, else 3;  after the stream, every status names offset state word 0;
     - it publishes the status it returns, and on every status but 0 no APIC ID, processor count or APIC base
       (all 0), and detail 0 where no detail is named above.
   The Lean theorems of LeanOS.QotomMadtStream say what the answers mean; this law is about the C between them.
   Not claimed: termination (partial correctness; every loop is bounded). */
#include <stdlib.h>
#include "quickproof.h"
#include "madt_api.h"

#define MAX_LENGTH (65536u - 44u)

/* What the consumer has asked so far, and what it may ask next.  Phase 0: the stream (byte `byte`, projection
   `word`); 1: the NMI policy (word `word`); 2: the finish (word `word`); 3: nothing more. */
struct oracle {
    const uint8_t *entries;
    uint64_t length, executing, cpuid_edx, available, apic_base, sample_id, routing;
    uint64_t phase, byte, word;
    uint64_t state[12];      /* the old state of the current transition */
    uint64_t answer[16];     /* the stream step's answers for the current transition */
    uint64_t nmi_count, nmi[4];
    uint64_t policy[5];
    uint64_t bound[6];
    uint64_t rejected;       /* the stream stopped at a rejected transition */
};
struct oracle oracle;

static uint64_t any_u64(void) {
    uint64_t hi = nondet_u32();
    uint64_t lo = nondet_u32();
    return hi << 32 | lo;
}

uint64_t leanos_qotom_madt_stream_byte_step_query(
        uint64_t s0, uint64_t s1, uint64_t s2, uint64_t s3, uint64_t s4, uint64_t s5, uint64_t s6, uint64_t s7,
        uint64_t s8, uint64_t s9, uint64_t s10, uint64_t s11, uint64_t table_length, uint64_t executing,
        uint64_t offset, uint64_t byte, uint64_t word) {
    struct oracle *o = &oracle;
    qp_assert(o->phase == 0 && o->byte < o->length && word == o->word);
    qp_assert(s0 == o->state[0] && s1 == o->state[1] && s2 == o->state[2] && s3 == o->state[3]);
    qp_assert(s4 == o->state[4] && s5 == o->state[5] && s6 == o->state[6] && s7 == o->state[7]);
    qp_assert(s8 == o->state[8] && s9 == o->state[9] && s10 == o->state[10] && s11 == o->state[11]);
    qp_assert(table_length == 44 + o->length && executing == o->executing);
    qp_assert(offset == 44 + o->byte && byte == o->entries[o->byte]);
    uint64_t v = any_u64();
    o->answer[word] = v;
    if (word < 15) {
        o->word = word + 1;
        return v;
    }
    uint64_t last = o->byte + 1 == o->length;
    if (o->answer[0] == 1 && o->answer[1] != 2 && o->answer[1] == (last ? 3u : 1u) && o->answer[2] == 0 &&
        o->answer[3] == offset + 1 && o->answer[15] == byte) {
        for (uint64_t k = 0; k < 12; ++k)
            o->state[k] = o->answer[k + 3];
        o->byte = o->byte + 1;
        o->word = 0;
        if (last)
            o->phase = 1;
    } else {
        o->rejected = 1;
        o->phase = 3;
    }
    return v;
}

uint64_t leanos_qotom_madt_nmi_policy_query(uint64_t count, uint64_t first, uint64_t second, uint64_t third,
                                            uint64_t fourth, uint64_t routing, uint64_t word) {
    struct oracle *o = &oracle;
    qp_assert(o->phase == 1 && word == o->word);
    qp_assert(count == o->nmi_count && first == o->nmi[0] && second == o->nmi[1] && third == o->nmi[2] &&
              fourth == o->nmi[3] && routing == o->routing);
    uint64_t v = any_u64();
    o->policy[word] = v;
    if (word < 4) {
        o->word = word + 1;
    } else {
        o->word = 0;
        o->phase = o->policy[0] == 1 && o->policy[1] == 1 && o->policy[2] == 0 && o->policy[3] == 1 &&
                   o->policy[4] == 4 ? 2 : 3;
    }
    return v;
}

uint64_t leanos_qotom_madt_stream_finish_query(
        uint64_t status, uint64_t error, uint64_t s0, uint64_t s1, uint64_t s2, uint64_t s3, uint64_t s4,
        uint64_t s5, uint64_t s6, uint64_t s7, uint64_t s8, uint64_t s9, uint64_t s10, uint64_t s11,
        uint64_t table_length, uint64_t executing, uint64_t cpuid_edx, uint64_t available, uint64_t apic_base,
        uint64_t sample_id, uint64_t word) {
    struct oracle *o = &oracle;
    qp_assert(o->phase == 2 && word == o->word);
    qp_assert(status == o->answer[1] && error == o->answer[2]);
    qp_assert(s0 == o->state[0] && s1 == o->state[1] && s2 == o->state[2] && s3 == o->state[3]);
    qp_assert(s4 == o->state[4] && s5 == o->state[5] && s6 == o->state[6] && s7 == o->state[7]);
    qp_assert(s8 == o->state[8] && s9 == o->state[9] && s10 == o->state[10] && s11 == o->state[11]);
    qp_assert(table_length == 44 + o->length && executing == o->executing && cpuid_edx == o->cpuid_edx &&
              available == o->available && apic_base == o->apic_base && sample_id == o->sample_id);
    uint64_t v = any_u64();
    o->bound[word] = v;
    if (word < 5) {
        o->word = word + 1;
    } else {
        o->word = 0;
        o->phase = 3;
    }
    return v;
}

/* The span's records as the consumer must walk them: 1 when they tile the span, every one at least 2 bytes long
   and every NMI record (type 4) exactly 6, with the count and the first four NMI records packed little-endian. */
static int records_ok(const uint8_t *e, uint64_t length, uint64_t *count, uint64_t nmi[4]) {
    *count = 0;
    for (uint64_t k = 0; k < 4; ++k)
        nmi[k] = 0;
    uint64_t at = 0;
    while (at < length) {
        if (length - at < 2)
            return 0;
        uint64_t n = e[at + 1];
        if (n < 2 || n > length - at)
            return 0;
        if (e[at] == 4) {
            if (n != 6)
                return 0;
            if (*count < 4) {
                uint64_t packed = 0;
                for (uint64_t b = 0; b < 6; ++b)
                    packed = packed | (uint64_t)e[at + b] << (8 * b);
                nmi[*count] = packed;
            }
            *count = *count + 1;
        }
        at = at + n;
    }
    return 1;
}

int main(void) {
    struct oracle *o = &oracle;
    size_t length = nondet_size();
    int valid_length = length != 0 && length <= MAX_LENGTH;
    uint8_t *entries = malloc(valid_length ? length : 1);
    if (entries == NULL)
        return 0;
    nondet_bytes(entries, valid_length ? length : 1);
    struct qotom_bsp_observation observation;
    observation.executing = any_u64();
    observation.cpuid_edx = any_u64();
    observation.available = any_u64();
    observation.apic_base = any_u64();
    observation.sample_id = any_u64();
    observation.interrupt_routing_authority = any_u64();
    struct qotom_bsp_result out;
    out.status = 7;
    out.detail = 7;
    out.offset = 7;
    out.apic_id = 7;
    out.processor_count = 7;
    out.apic_base = 7;
    const uint8_t *entries_arg = nondet_u8() == 0 ? NULL : entries;
    const struct qotom_bsp_observation *observation_arg = nondet_u8() == 0 ? NULL : &observation;
    struct qotom_bsp_result *out_arg = nondet_u8() == 0 ? NULL : &out;

    o->entries = entries;
    o->length = length;
    o->executing = observation.executing;
    o->cpuid_edx = observation.cpuid_edx;
    o->available = observation.available;
    o->apic_base = observation.apic_base;
    o->sample_id = observation.sample_id;
    o->routing = observation.interrupt_routing_authority;
    o->phase = out_arg != NULL && entries_arg != NULL && observation_arg != NULL && valid_length ? 0 : 3;
    o->byte = 0;
    o->word = 0;
    o->state[0] = 44;
    for (uint64_t k = 1; k < 12; ++k)
        o->state[k] = k == 7 ? 256 : 0;
    o->rejected = 0;
    int walk = valid_length ? records_ok(entries, length, &o->nmi_count, o->nmi) : 0;

    uint64_t status = madt_bind(entries_arg, length, observation_arg, out_arg);

    if (out_arg == NULL) {
        qp_assert(status == 1 && o->byte == 0 && o->word == 0);
        return 0;
    }
    qp_assert(out.status == status && status <= 5);
    if (entries_arg == NULL || observation_arg == NULL || !valid_length) {
        qp_assert(status == 1 && out.detail == 0 && out.offset == 44 && o->byte == 0 && o->word == 0);
        qp_assert(out.apic_id == 0 && out.processor_count == 0 && out.apic_base == 0);
        return 0;
    }
    if (status != 0)
        qp_assert(out.apic_id == 0 && out.processor_count == 0 && out.apic_base == 0);
    if (o->rejected) {
        /* The stream stopped at byte o->byte, whose answers are o->answer. */
        uint64_t two = o->answer[0] == 1 && o->answer[1] == 2;
        qp_assert(status == (two ? 2u : 3u) && out.detail == (two ? o->answer[2] : 0));
        qp_assert(out.offset == 44 + o->byte);
        return 0;
    }
    qp_assert(o->byte == length);
    qp_assert(out.offset == o->state[0]);
    if (!walk) {
        qp_assert(o->phase == 1 && o->word == 0 && status == 3 && out.detail == 0);
        return 0;
    }
    qp_assert(o->phase >= 2);
    uint64_t *p = o->policy;
    if (o->phase == 3 && !(p[0] == 1 && p[1] == 1 && p[2] == 0 && p[3] == 1 && p[4] == 4)) {
        uint64_t five = p[0] == 1 && p[3] <= 1 && p[4] <= 4 && p[1] != 1;
        qp_assert(status == (five ? 5u : 3u) && out.detail == (five ? p[2] : 0));
        return 0;
    }
    qp_assert(o->phase == 3 && o->word == 0);
    uint64_t *b = o->bound;
    if (b[0] == 1 && b[1] == 1 && b[2] == o->executing && b[3] == o->state[6] && b[4] == o->apic_base && b[5] == 0) {
        qp_assert(status == 0 && out.detail == 0);
        qp_assert(out.apic_id == b[2] && out.processor_count == b[3] && out.apic_base == b[4]);
        return 0;
    }
    uint64_t four = b[0] == 1 && b[5] == 0 && (b[1] == 2 || b[1] == 5);
    qp_assert(status == (four ? 4u : 3u) && out.detail == (four ? b[2] : 0));
    return 0;
}
