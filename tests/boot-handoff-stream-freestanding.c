#include <stdint.h>
#ifdef LEANOS_HOSTED_REPLAY
#include <stdio.h>
#define RECORD_RESULT(name, value) \
    printf("stream-result %s %llu\n", (name), (unsigned long long)(value))
#define RECORD_INDEXED(operation, index, field, value) \
    printf("stream-result %s-%llu.%s %llu\n", (operation), \
           (unsigned long long)(index), (field), (unsigned long long)(value))
#else
#define RECORD_RESULT(name, value) ((void)(value))
#define RECORD_INDEXED(operation, index, field, value) ((void)(value))
#endif
#ifdef LEANOS_HOSTED_SANITIZER
extern void leanos_register_boundary_target(const char *, void *);
#define REGISTER_BOUNDARY(symbol) \
    leanos_register_boundary_target(#symbol, (void *)(uintptr_t)&symbol)
#endif

#define CHECK_RESULT(name, actual, expected, failure) do { \
    const uint64_t check_result = (actual); \
    RECORD_RESULT((name), check_result); \
    if (check_result != (uint64_t)(expected)) return (failure); \
} while (0)

#define CHECK_INDEXED(operation, index, field, actual, expected, failure) do { \
    const uint64_t check_result = (actual); \
    RECORD_INDEXED((operation), (index), (field), check_result); \
    if (check_result != (uint64_t)(expected)) return (failure); \
} while (0)

extern uint64_t leanos_boot_handoff_stream_init(
    uint64_t, uint64_t, uint64_t, uint64_t, uint64_t);
extern uint64_t leanos_boot_handoff_stream_step(
    uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t,
    uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t);
extern uint64_t leanos_boot_decode_init(
    uint64_t, uint64_t, uint64_t, uint64_t, uint64_t);
extern uint64_t leanos_boot_decode_step(
    uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t,
    uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t,
    uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t,
    uint64_t, uint64_t, uint64_t);
extern uint64_t leanos_boot_projection_entry(
    uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t);
extern uint64_t leanos_boot_projection_manifest(
    uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t,
    uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t,
    uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t);
extern uint64_t leanos_boot_projection_free(uint64_t, uint64_t, uint64_t);
#define U64_8 uint64_t, uint64_t, uint64_t, uint64_t, \
              uint64_t, uint64_t, uint64_t, uint64_t
#define U64_64 U64_8, U64_8, U64_8, U64_8, U64_8, U64_8, U64_8, U64_8
extern uint64_t leanos_boot_projection_finish(
    uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t,
    uint64_t, uint64_t, U64_64);
#undef U64_64
#undef U64_8
extern uint64_t leanos_boot_manifest_candidate(
    uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t,
    uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t,
    uint64_t, uint64_t, uint64_t, uint64_t, uint64_t);
extern uint64_t leanos_boot_decode_init_v5(
    uint64_t, uint64_t, uint64_t, uint64_t, uint64_t);
extern uint64_t leanos_boot_decode_step_v5(
    uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t,
    uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t,
    uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t,
    uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t,
    uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t,
    uint64_t, uint64_t, uint64_t, uint64_t, uint64_t);
extern uint64_t leanos_boot_manifest_start(
    uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t,
    uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t,
    uint64_t, uint64_t, uint64_t, uint64_t);
extern uint64_t leanos_boot_consume_exact_projection(
    uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t);
extern uint64_t leanos_boot_publish_authority(
    uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t);
extern uint64_t leanos_boot_authority_result(
    uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t,
    uint64_t);

struct stream_state {
    uint64_t word[7];
};

struct decode_state { uint64_t word[19]; };
struct decode_state_v5 { uint64_t word[41]; };

static struct decode_state_v5 decode_v5_extent(
        const uint64_t *chunks, uint64_t count) {
    struct decode_state_v5 state, next;
    const uint64_t extent = count * 8;
    for (uint64_t query = 0; query < 41; ++query)
        state.word[query] = leanos_boot_decode_init_v5(
            0x36d76289, 0x1000, extent, 1, query);
    for (uint64_t index = 0; index < count; ++index) {
        for (uint64_t query = 0; query < 41; ++query)
            next.word[query] = leanos_boot_decode_step_v5(
                state.word[0], state.word[1], state.word[2], state.word[3],
                state.word[4], state.word[5], state.word[6], state.word[7],
                state.word[8], state.word[9], state.word[10], state.word[11],
                state.word[12], state.word[13], state.word[14], state.word[15],
                state.word[16], state.word[17], state.word[18], state.word[23],
                state.word[24], state.word[25], state.word[26], state.word[27],
                state.word[28], state.word[29], state.word[30], state.word[31],
                state.word[32], state.word[33], state.word[34], state.word[35],
                state.word[36], state.word[37], state.word[38],
                0x1000, index * 8, chunks[index],
                index + 1 == count, query);
        state = next;
        if (state.word[2] != 0) break;
    }
    return state;
}

static struct decode_state decode_extent(
        const uint64_t *chunks, uint64_t count, uint64_t target) {
    struct decode_state state, next;
    const uint64_t extent = count * 8;
    for (uint64_t query = 0; query < 19; ++query)
        state.word[query] =
            leanos_boot_decode_init(0x36d76289, 0x1000, extent, target, query);
    for (uint64_t index = 0; index < count; ++index) {
        for (uint64_t query = 0; query < 19; ++query)
            next.word[query] = leanos_boot_decode_step(
                state.word[0], state.word[1], state.word[2], state.word[3],
                state.word[4], state.word[5], state.word[6], state.word[7],
                state.word[8], state.word[9], state.word[10], state.word[11],
                state.word[12], state.word[13], state.word[14], state.word[15],
                state.word[16], state.word[17], state.word[18], 0x1000,
                index * 8, chunks[index], index + 1 == count, query);
        state = next;
        if (state.word[2] != 0) break;
    }
    return state;
}

static struct decode_state decode(const uint64_t chunks[12], uint64_t target) {
    return decode_extent(chunks, 12, target);
}

static int expect_decode_error(
        const uint64_t *chunks, uint64_t count, uint64_t expected) {
    const struct decode_state decoded = decode_extent(chunks, count, 1);
    if (decoded.word[0] != 4 || decoded.word[1] != 2 ||
        decoded.word[2] != expected)
        return 0;
    for (uint64_t query = 3; query < 19; ++query)
        if (decoded.word[query] != 0) return 0;
    return 1;
}

static struct decode_state decode_entry_count(uint64_t entry_count) {
    uint64_t chunks[4 + 3 * 257] = {0};
    const uint64_t count = 4 + 3 * entry_count;
    const uint64_t extent = count * 8;
    chunks[0] = extent;
    chunks[1] = ((16 + 24 * entry_count) << 32) | 6;
    chunks[2] = 24;
    for (uint64_t index = 0; index < entry_count; ++index) {
        chunks[3 + 3 * index] = 0;
        chunks[4 + 3 * index] = 0x4000;
        chunks[5 + 3 * index] = 1;
    }
    chunks[count - 1] = UINT64_C(0x0000000800000000);
    return decode_extent(chunks, count, 1);
}

static uint64_t step_query(const struct stream_state *state, uint64_t identity,
                           uint64_t offset, uint64_t count, uint64_t chunk,
                           uint64_t terminal, uint64_t query) {
    return leanos_boot_handoff_stream_step(
        state->word[0], state->word[1], state->word[2], state->word[3],
        state->word[4], state->word[5], state->word[6], identity, offset, count,
        chunk, terminal, query);
}

int check_stream(void) {
#ifdef LEANOS_HOSTED_SANITIZER
    REGISTER_BOUNDARY(leanos_boot_handoff_stream_init);
    REGISTER_BOUNDARY(leanos_boot_handoff_stream_step);
    REGISTER_BOUNDARY(leanos_boot_decode_init);
    REGISTER_BOUNDARY(leanos_boot_decode_step);
    REGISTER_BOUNDARY(leanos_boot_decode_init_v5);
    REGISTER_BOUNDARY(leanos_boot_decode_step_v5);
    REGISTER_BOUNDARY(leanos_boot_projection_entry);
    REGISTER_BOUNDARY(leanos_boot_projection_manifest);
    REGISTER_BOUNDARY(leanos_boot_projection_free);
    REGISTER_BOUNDARY(leanos_boot_projection_finish);
    REGISTER_BOUNDARY(leanos_boot_manifest_candidate);
    REGISTER_BOUNDARY(leanos_boot_manifest_start);
    REGISTER_BOUNDARY(leanos_boot_consume_exact_projection);
    REGISTER_BOUNDARY(leanos_boot_publish_authority);
    REGISTER_BOUNDARY(leanos_boot_authority_result);
#endif
#define ZERO_8 0, 0, 0, 0, 0, 0, 0, 0
#define FINISH_WORDS UINT64_C(0x100), 0, 0, 0, 0, 0, 0, 0, \
                     ZERO_8, ZERO_8, ZERO_8, ZERO_8, ZERO_8, ZERO_8, ZERO_8
#define FINISH_TWO_WORDS UINT64_C(0x500), 0, 0, 0, 0, 0, 0, 0, \
                         ZERO_8, ZERO_8, ZERO_8, ZERO_8, ZERO_8, ZERO_8, ZERO_8
    const uint64_t identity = 0x1000;
    const uint64_t chunks[12] = {
        0x0000000000000060, 0x000000090000002a, 0x00000000000000aa,
        0x0000004000000006, 0x0000000000000018, 0x0000000000001000,
        0x0000000000004000, 0x0000000000000001, 0x0000000000002000,
        0x0000000000001000, 0x0000000000000002, 0x0000000800000000,
    };
    const uint64_t map_and_end[9] = {
        UINT64_C(0x0000004000000006), UINT64_C(0x0000000000000018),
        UINT64_C(0x0000000000001000), UINT64_C(0x0000000000004000),
        UINT64_C(0x0000000000000001), UINT64_C(0x0000000000002000),
        UINT64_C(0x0000000000001000), UINT64_C(0x0000000000000002),
        UINT64_C(0x0000000800000000),
    };
    const uint64_t old_rsdp[4] = {
        UINT64_C(0x0000001c0000000e), UINT64_C(0x2052545020445352),
        UINT64_C(0x002020554d45518f), UINT64_C(0x00000000000f5b70),
    };
    const uint64_t new_rsdp[6] = {
        UINT64_C(0x0000002c0000000f), UINT64_C(0x2052545020445352),
        UINT64_C(0x022020554d45518d), UINT64_C(0x00000024000f5b70),
        UINT64_C(0x00000000000f5c00), UINT64_C(0x0000000000000071),
    };
    struct stream_state state;
    struct stream_state next;

    for (uint64_t query = 0; query < 7; ++query)
        state.word[query] = leanos_boot_handoff_stream_init(
            0x36d76289, identity, 96, identity, query);
    CHECK_RESULT("init.accepted.version", state.word[0], 2, 1);
    CHECK_RESULT("init.accepted.status", state.word[1], 0, 1);
    CHECK_RESULT("init.accepted.error", state.word[2], 0, 1);
    CHECK_RESULT("init.accepted.identity", state.word[3], identity, 1);
    CHECK_RESULT("init.accepted.extent", state.word[4], 96, 1);
    CHECK_RESULT("init.accepted.offset", state.word[5], 0, 1);
    CHECK_RESULT("init.accepted.chain", state.word[6],
                 UINT64_C(0xcbf29ce484222325), 1);

    CHECK_RESULT("init.bad-extent.status",
        leanos_boot_handoff_stream_init(
            0x36d76289, identity, 95, identity, 1), 2, 2);
    CHECK_RESULT("init.identity-mismatch.error",
        leanos_boot_handoff_stream_init(
            0x36d76289, identity, 96, 0x2000, 2), 5, 3);
    CHECK_RESULT("init.address-overflow.error",
        leanos_boot_handoff_stream_init(
            0x36d76289, UINT64_MAX - 7, 16, UINT64_MAX - 7, 2), 14, 13);

    CHECK_RESULT("step.stream-mismatch.error",
        step_query(&state, 0x2000, 0, 8, chunks[0], 0, 2), 8, 4);
    CHECK_RESULT("step.offset-mismatch.error",
        step_query(&state, identity, 8, 8, chunks[0], 0, 2), 9, 5);
    CHECK_RESULT("step.noncanonical-chunk.error",
        step_query(&state, identity, 0, 1, 0x100, 0, 2), 13, 6);
    CHECK_RESULT("step.bad-terminal.error",
        step_query(&state, identity, 0, 8, chunks[0], 1, 2), 12, 7);

    for (uint64_t index = 0; index < 12; ++index) {
        const uint64_t terminal = index == 11;
        CHECK_INDEXED("step.accepted", index, "chunk",
            step_query(&state, identity, index * 8, 8, chunks[index], terminal,
                       7), chunks[index], 8);
        CHECK_INDEXED("step.accepted", index, "count",
            step_query(&state, identity, index * 8, 8, chunks[index], terminal,
                       8), 8, 9);
        for (uint64_t query = 0; query < 7; ++query)
            next.word[query] = step_query(
                &state, identity, index * 8, 8, chunks[index], terminal, query);
        state = next;
    }
    CHECK_RESULT("step.complete.status", state.word[1], 1, 10);
    CHECK_RESULT("step.complete.error", state.word[2], 0, 10);
    CHECK_RESULT("step.complete.offset", state.word[5], 96, 10);
    CHECK_RESULT("step.completed-replay.status",
        step_query(&state, identity, 96, 1, 0, 0, 1), 2, 11);
    CHECK_RESULT("step.completed-replay.chunk",
        step_query(&state, identity, 96, 1, 0, 0, 7), 0, 12);
    struct decode_state decoded = decode(chunks, 1);
    CHECK_RESULT("decode.accepted.version", decoded.word[0], 4, 14);
    CHECK_RESULT("decode.accepted.status", decoded.word[1], 1, 14);
    CHECK_RESULT("decode.accepted.error", decoded.word[2], 0, 14);
    CHECK_RESULT("decode.accepted.phase", decoded.word[7], 7, 14);
    CHECK_RESULT("decode.accepted.entry-count", decoded.word[11], 2, 14);
    CHECK_RESULT("decode.accepted.target-found", decoded.word[14], 1, 14);
    CHECK_RESULT("decode.accepted.target-blocked", decoded.word[15], 0, 14);
    CHECK_RESULT("decode.accepted.tag-count", decoded.word[18], 3, 14);
    uint64_t old_only[14] = {0};
    old_only[0] = sizeof(old_only);
    for (uint64_t index = 0; index < 4; ++index)
        old_only[1 + index] = old_rsdp[index];
    for (uint64_t index = 0; index < 9; ++index)
        old_only[5 + index] = map_and_end[index];
    struct decode_state_v5 decoded_v5 = decode_v5_extent(old_only, 14);
    CHECK_RESULT("decode-v5.old-only.version", decoded_v5.word[0], 5, 42);
    CHECK_RESULT("decode-v5.old-only.error", decoded_v5.word[2], 0, 42);
    CHECK_RESULT("decode-v5.old-only.status", decoded_v5.word[1], 1, 42);
    CHECK_RESULT("decode-v5.old-only.kind", decoded_v5.word[39], 1, 42);
    CHECK_RESULT("decode-v5.old-only.address", decoded_v5.word[40],
                 UINT64_C(0x000f5b70), 42);

    uint64_t new_only[16] = {0};
    new_only[0] = sizeof(new_only);
    for (uint64_t index = 0; index < 6; ++index)
        new_only[1 + index] = new_rsdp[index];
    for (uint64_t index = 0; index < 9; ++index)
        new_only[7 + index] = map_and_end[index];
    decoded_v5 = decode_v5_extent(new_only, 16);
    CHECK_RESULT("decode-v5.new-only.status", decoded_v5.word[1], 1, 43);
    CHECK_RESULT("decode-v5.new-only.error", decoded_v5.word[2], 0, 43);
    CHECK_RESULT("decode-v5.new-only.kind", decoded_v5.word[39], 2, 43);
    CHECK_RESULT("decode-v5.new-only.address", decoded_v5.word[40],
                 UINT64_C(0x000f5c00), 43);

    uint64_t reverse_coherent[20] = {0};
    reverse_coherent[0] = sizeof(reverse_coherent);
    for (uint64_t index = 0; index < 6; ++index)
        reverse_coherent[1 + index] = new_rsdp[index];
    for (uint64_t index = 0; index < 4; ++index)
        reverse_coherent[7 + index] = old_rsdp[index];
    for (uint64_t index = 0; index < 9; ++index)
        reverse_coherent[11 + index] = map_and_end[index];
    decoded_v5 = decode_v5_extent(reverse_coherent, 20);
    CHECK_RESULT("decode-v5.reverse-coherent.status", decoded_v5.word[1], 1, 44);
    CHECK_RESULT("decode-v5.reverse-coherent.error", decoded_v5.word[2], 0, 44);
    CHECK_RESULT("decode-v5.reverse-coherent.kind", decoded_v5.word[39], 2, 44);
    CHECK_RESULT("decode-v5.reverse-coherent.address", decoded_v5.word[40],
                 UINT64_C(0x000f5c00), 44);

    uint64_t forward_coherent[20] = {0};
    forward_coherent[0] = sizeof(forward_coherent);
    for (uint64_t index = 0; index < 4; ++index)
        forward_coherent[1 + index] = old_rsdp[index];
    for (uint64_t index = 0; index < 6; ++index)
        forward_coherent[5 + index] = new_rsdp[index];
    for (uint64_t index = 0; index < 9; ++index)
        forward_coherent[11 + index] = map_and_end[index];
    decoded_v5 = decode_v5_extent(forward_coherent, 20);
    CHECK_RESULT("decode-v5.forward-coherent.status", decoded_v5.word[1], 1, 45);
    CHECK_RESULT("decode-v5.forward-coherent.error", decoded_v5.word[2], 0, 45);
    CHECK_RESULT("decode-v5.forward-coherent.kind", decoded_v5.word[39], 2, 45);
    CHECK_RESULT("decode-v5.forward-coherent.address", decoded_v5.word[40],
                 UINT64_C(0x000f5c00), 45);

    uint64_t duplicate_old[18] = {0};
    duplicate_old[0] = sizeof(duplicate_old);
    for (uint64_t index = 0; index < 4; ++index) {
        duplicate_old[1 + index] = old_rsdp[index];
        duplicate_old[5 + index] = old_rsdp[index];
    }
    for (uint64_t index = 0; index < 9; ++index)
        duplicate_old[9 + index] = map_and_end[index];
    decoded_v5 = decode_v5_extent(duplicate_old, 18);
    CHECK_RESULT("decode-v5.duplicate-old.status", decoded_v5.word[1], 2, 46);
    CHECK_RESULT("decode-v5.duplicate-old.error", decoded_v5.word[2], 13, 46);
    CHECK_RESULT("decode-v5.duplicate-old.kind", decoded_v5.word[39], 0, 46);
    CHECK_RESULT("decode-v5.duplicate-old.address", decoded_v5.word[40], 0, 46);

    uint64_t conflicting_roots[20] = {0};
    uint64_t conflicting_new_rsdp[6];
    for (uint64_t index = 0; index < 6; ++index)
        conflicting_new_rsdp[index] = new_rsdp[index];
    /* Move RSDT by eight bytes and compensate the legacy checksum. */
    conflicting_new_rsdp[2] = UINT64_C(0x022020554d455185);
    conflicting_new_rsdp[3] = UINT64_C(0x00000024000f5b78);
    conflicting_roots[0] = sizeof(conflicting_roots);
    for (uint64_t index = 0; index < 4; ++index)
        conflicting_roots[1 + index] = old_rsdp[index];
    for (uint64_t index = 0; index < 6; ++index)
        conflicting_roots[5 + index] = conflicting_new_rsdp[index];
    for (uint64_t index = 0; index < 9; ++index)
        conflicting_roots[11 + index] = map_and_end[index];
    decoded_v5 = decode_v5_extent(conflicting_roots, 20);
    CHECK_RESULT("decode-v5.conflicting-roots.status", decoded_v5.word[1], 2, 47);
    CHECK_RESULT("decode-v5.conflicting-roots.error", decoded_v5.word[2], 13, 47);
    CHECK_RESULT("decode-v5.conflicting-roots.kind", decoded_v5.word[39], 0, 47);
    CHECK_RESULT("decode-v5.conflicting-roots.address", decoded_v5.word[40], 0, 47);

    uint64_t bad_old_signature[14];
    for (uint64_t index = 0; index < 14; ++index)
        bad_old_signature[index] = old_only[index];
    bad_old_signature[2] ^= 1;
    decoded_v5 = decode_v5_extent(bad_old_signature, 14);
    CHECK_RESULT("decode-v5.bad-old-signature.status", decoded_v5.word[1], 2, 48);
    CHECK_RESULT("decode-v5.bad-old-signature.error", decoded_v5.word[2], 12, 48);
    CHECK_RESULT("decode-v5.bad-old-signature.kind", decoded_v5.word[39], 0, 48);
    CHECK_RESULT("decode-v5.bad-old-signature.address", decoded_v5.word[40], 0, 48);

    uint64_t bad_new_revision[16];
    for (uint64_t index = 0; index < 16; ++index)
        bad_new_revision[index] = new_only[index];
    bad_new_revision[3] =
        (bad_new_revision[3] & UINT64_C(0x00ffffffffffffff)) |
        UINT64_C(0x0100000000000000);
    decoded_v5 = decode_v5_extent(bad_new_revision, 16);
    CHECK_RESULT("decode-v5.bad-new-revision.status", decoded_v5.word[1], 2, 49);
    CHECK_RESULT("decode-v5.bad-new-revision.error", decoded_v5.word[2], 12, 49);
    CHECK_RESULT("decode-v5.bad-new-revision.kind", decoded_v5.word[39], 0, 49);
    CHECK_RESULT("decode-v5.bad-new-revision.address", decoded_v5.word[40], 0, 49);

    uint64_t bad_old_tag_size[14];
    for (uint64_t index = 0; index < 14; ++index)
        bad_old_tag_size[index] = old_only[index];
    bad_old_tag_size[1] = UINT64_C(0x0000001b0000000e);
    decoded_v5 = decode_v5_extent(bad_old_tag_size, 14);
    CHECK_RESULT("decode-v5.bad-old-tag-size.status", decoded_v5.word[1], 2, 50);
    CHECK_RESULT("decode-v5.bad-old-tag-size.error", decoded_v5.word[2], 12, 50);
    CHECK_RESULT("decode-v5.bad-old-tag-size.kind", decoded_v5.word[39], 0, 50);
    CHECK_RESULT("decode-v5.bad-old-tag-size.address", decoded_v5.word[40], 0, 50);

    uint64_t bad_old_checksum[14];
    for (uint64_t index = 0; index < 14; ++index)
        bad_old_checksum[index] = old_only[index];
    bad_old_checksum[3] ^= 1;
    decoded_v5 = decode_v5_extent(bad_old_checksum, 14);
    CHECK_RESULT("decode-v5.bad-old-checksum.status", decoded_v5.word[1], 2, 51);
    CHECK_RESULT("decode-v5.bad-old-checksum.error", decoded_v5.word[2], 12, 51);
    CHECK_RESULT("decode-v5.bad-old-checksum.kind", decoded_v5.word[39], 0, 51);
    CHECK_RESULT("decode-v5.bad-old-checksum.address", decoded_v5.word[40], 0, 51);

    uint64_t bad_new_extended_checksum[16];
    for (uint64_t index = 0; index < 16; ++index)
        bad_new_extended_checksum[index] = new_only[index];
    bad_new_extended_checksum[6] ^= 1;
    decoded_v5 = decode_v5_extent(bad_new_extended_checksum, 16);
    CHECK_RESULT("decode-v5.bad-new-extended-checksum.status", decoded_v5.word[1], 2, 52);
    CHECK_RESULT("decode-v5.bad-new-extended-checksum.error", decoded_v5.word[2], 12, 52);
    CHECK_RESULT("decode-v5.bad-new-extended-checksum.kind", decoded_v5.word[39], 0, 52);
    CHECK_RESULT("decode-v5.bad-new-extended-checksum.address", decoded_v5.word[40], 0, 52);

    uint64_t bad_new_reserved[16];
    for (uint64_t index = 0; index < 16; ++index)
        bad_new_reserved[index] = new_only[index];
    bad_new_reserved[6] |= UINT64_C(0x0000000000000100);
    decoded_v5 = decode_v5_extent(bad_new_reserved, 16);
    CHECK_RESULT("decode-v5.bad-new-reserved.status", decoded_v5.word[1], 2, 53);
    CHECK_RESULT("decode-v5.bad-new-reserved.error", decoded_v5.word[2], 12, 53);
    CHECK_RESULT("decode-v5.bad-new-reserved.kind", decoded_v5.word[39], 0, 53);
    CHECK_RESULT("decode-v5.bad-new-reserved.address", decoded_v5.word[40], 0, 53);

    uint64_t nonzero_new_padding[16];
    for (uint64_t index = 0; index < 16; ++index)
        nonzero_new_padding[index] = new_only[index];
    nonzero_new_padding[6] |= UINT64_C(0xa5a5a5a500000000);
    decoded_v5 = decode_v5_extent(nonzero_new_padding, 16);
    CHECK_RESULT("decode-v5.nonzero-new-padding.status", decoded_v5.word[1], 1, 54);
    CHECK_RESULT("decode-v5.nonzero-new-padding.error", decoded_v5.word[2], 0, 54);
    CHECK_RESULT("decode-v5.nonzero-new-padding.kind", decoded_v5.word[39], 2, 54);
    CHECK_RESULT("decode-v5.nonzero-new-padding.address", decoded_v5.word[40],
                 UINT64_C(0x000f5c00), 54);
    CHECK_RESULT("projection.entry.usable",
        leanos_boot_projection_entry(0x1000, 0x4000, 1, 0, 0, 0, 3),
        0x1e, 14);
    CHECK_RESULT("projection.entry.blocked",
        leanos_boot_projection_entry(0x2000, 0x1000, 2, 0, 0, 0, 4),
        0x4, 14);
    CHECK_RESULT("projection.free.precedence",
        leanos_boot_projection_free(0x1e, 0x4, 0x2), 0x18, 14);
    CHECK_RESULT("projection.manifest.status",
        leanos_boot_projection_manifest(
            0, 0, 0x100000, 0x100000, 0x200000,
            0x110000, 0x1000, 0x120000, 0x1000, 0x130000, 0x1000,
            0x140000, 0x1000, 0x141000, 0x4000, 0x180000, 0x2000,
            0x300000, 96, 1), 1, 14);
    CHECK_RESULT("projection.manifest.low-memory-mask",
        leanos_boot_projection_manifest(
            0, 0, 0x100000, 0x100000, 0x200000,
            0x110000, 0x1000, 0x120000, 0x1000, 0x130000, 0x1000,
            0x140000, 0x1000, 0x141000, 0x4000, 0x180000, 0x2000,
            0x300000, 96, 3), UINT64_MAX, 14);
    CHECK_RESULT("projection.finish.status",
        leanos_boot_projection_finish(1, 0, 1, 0, 2, 0x5000, 7, 1,
                                      FINISH_WORDS), 1, 14);
    CHECK_RESULT("projection.finish.frame",
        leanos_boot_projection_finish(1, 0, 1, 0, 2, 0x5000, 7, 3,
                                      FINISH_WORDS), 8, 14);
    CHECK_RESULT("projection.finish.owner",
        leanos_boot_projection_finish(1, 0, 1, 0, 2, 0x5000, 7, 4,
                                      FINISH_WORDS), 7, 14);
    CHECK_RESULT("projection.finish.candidate-token",
        leanos_boot_projection_finish(1, 0, 1, 0, 2, 0x5000, 7, 7,
                                      FINISH_WORDS), 9, 14);
    CHECK_RESULT("projection.finish.next-frame",
        leanos_boot_projection_finish(1, 0, 1, 0, 2, 0x5000, 7, 8,
                                      FINISH_TWO_WORDS), 10, 14);
    CHECK_RESULT("projection.finish.decode-rejection",
        leanos_boot_projection_finish(2, 9, 1, 0, 0, 0, 7, 2,
                                      FINISH_WORDS), 1, 14);
    CHECK_RESULT("projection.finish.manifest-rejection",
        leanos_boot_projection_finish(1, 0, 2, 1, 2, 0x5000, 7, 2,
                                      FINISH_WORDS), 2, 14);
    CHECK_RESULT("projection.finish.rejection-no-frame",
        leanos_boot_projection_finish(2, 9, 1, 0, 0, 0, 7, 3,
                                      FINISH_WORDS), 0, 14);
    CHECK_RESULT("projection.finish.empty-entry-rejection",
        leanos_boot_projection_finish(1, 0, 1, 0, 0, 0x5000, 7, 2,
                                      FINISH_WORDS), 3, 14);
    CHECK_RESULT("projection.forged-frame-no-publication",
        leanos_boot_publish_authority(8, 8, 1, 0, 0, 1, 1), 0, 14);
    decoded = decode(chunks, 2);
    CHECK_RESULT("decode.reserved-target.status", decoded.word[1], 1, 15);
    CHECK_RESULT("decode.reserved-target.target-found", decoded.word[14], 1, 15);
    CHECK_RESULT("decode.reserved-target.target-blocked", decoded.word[15], 1, 15);
    uint64_t high_reserved[12];
    for (uint64_t index = 0; index < 12; ++index)
        high_reserved[index] = chunks[index];
    high_reserved[8] = 0x100000000;
    high_reserved[9] = 0x10000000000;
    decoded = decode(high_reserved, 1);
    CHECK_RESULT("decode.high-reserved.status", decoded.word[1], 1, 18);
    CHECK_RESULT("decode.high-reserved.usable-end", decoded.word[17], 0x5000, 18);
    uint64_t malformed[12];
    for (uint64_t index = 0; index < 12; ++index) malformed[index] = chunks[index];
    malformed[0] |= 0x100000000;
    decoded = decode(malformed, 1);
    CHECK_RESULT("decode.malformed.status", decoded.word[1], 2, 16);
    CHECK_RESULT("decode.malformed.error", decoded.word[2], 3, 16);
    const uint64_t malformed_tag_size[2] = {
        16, UINT64_C(0x000000040000002a),
    };
    const uint64_t duplicate_map[5] = {
        40, UINT64_C(0x0000001000000006), 24,
        UINT64_C(0x0000001000000006), UINT64_C(0x0000000800000000),
    };
    const uint64_t bad_map_layout[4] = {
        32, UINT64_C(0x0000001000000006), 32,
        UINT64_C(0x0000000800000000),
    };
    const uint64_t zero_length_entry[7] = {
        56, UINT64_C(0x0000002800000006), 24, 0, 0, 1,
        UINT64_C(0x0000000800000000),
    };
    const uint64_t reserved_entry_word[7] = {
        56, UINT64_C(0x0000002800000006), 24, 0, 0x1000,
        UINT64_C(0x0000000100000001), UINT64_C(0x0000000800000000),
    };
    const uint64_t overflowing_entry[7] = {
        56, UINT64_C(0x0000002800000006), 24, UINT64_MAX, 2, 1,
        UINT64_C(0x0000000800000000),
    };
    const uint64_t missing_map[2] = {
        16, UINT64_C(0x0000000800000000),
    };
    const uint64_t missing_end[2] = {
        16, UINT64_C(0x000000080000002a),
    };
    CHECK_RESULT("decode.malformed-tag-size.rejects",
        expect_decode_error(malformed_tag_size, 2, 4), 1, 34);
    CHECK_RESULT("decode.duplicate-map.rejects",
        expect_decode_error(duplicate_map, 5, 6), 1, 35);
    CHECK_RESULT("decode.bad-map-layout.rejects",
        expect_decode_error(bad_map_layout, 4, 7), 1, 36);
    CHECK_RESULT("decode.zero-length-entry.rejects",
        expect_decode_error(zero_length_entry, 7, 9), 1, 37);
    CHECK_RESULT("decode.reserved-entry-word.rejects",
        expect_decode_error(reserved_entry_word, 7, 9), 1, 38);
    CHECK_RESULT("decode.overflowing-entry.rejects",
        expect_decode_error(overflowing_entry, 7, 9), 1, 39);
    CHECK_RESULT("decode.missing-map.rejects",
        expect_decode_error(missing_map, 2, 10), 1, 40);
    CHECK_RESULT("decode.missing-end.rejects",
        expect_decode_error(missing_end, 2, 11), 1, 41);
    uint64_t too_many_tags_fixture[70] = {0};
    too_many_tags_fixture[0] = 560;
    for (uint64_t index = 1; index <= 63; ++index)
        too_many_tags_fixture[index] = 0x000000080000002a;
    too_many_tags_fixture[64] = 0x0000002800000006;
    too_many_tags_fixture[65] = 24;
    too_many_tags_fixture[66] = 0;
    too_many_tags_fixture[67] = 0x4000;
    too_many_tags_fixture[68] = 1;
    too_many_tags_fixture[69] = 0x0000000800000000;
    decoded = decode_extent(too_many_tags_fixture, 70, 1);
    CHECK_RESULT("decode.too-many-tags.version", decoded.word[0], 4, 19);
    CHECK_RESULT("decode.too-many-tags.status", decoded.word[1], 2, 19);
    CHECK_RESULT("decode.too-many-tags.error", decoded.word[2], 5, 19);
    const uint64_t accepted_entry_counts[] = {128, 129, 256};
    for (uint64_t index = 0; index < 3; ++index) {
        const uint64_t entry_count = accepted_entry_counts[index];
        decoded = decode_entry_count(entry_count);
        CHECK_INDEXED("decode.entry-limit", entry_count, "version",
                      decoded.word[0], 4, 20 + index);
        CHECK_INDEXED("decode.entry-limit", entry_count, "status",
                      decoded.word[1], 1, 20 + index);
        CHECK_INDEXED("decode.entry-limit", entry_count, "error",
                      decoded.word[2], 0, 20 + index);
        CHECK_INDEXED("decode.entry-limit", entry_count, "phase",
                      decoded.word[7], 7, 20 + index);
        CHECK_INDEXED("decode.entry-limit", entry_count, "entry-count",
                      decoded.word[11], entry_count, 20 + index);
        CHECK_INDEXED("decode.entry-limit", entry_count, "tag-count",
                      decoded.word[18], 2, 20 + index);
    }
    decoded = decode_entry_count(257);
    CHECK_RESULT("decode.entry-limit-257.version", decoded.word[0], 4, 23);
    CHECK_RESULT("decode.entry-limit-257.status", decoded.word[1], 2, 23);
    CHECK_RESULT("decode.entry-limit-257.error", decoded.word[2], 8, 23);
    CHECK_RESULT("decode.entry-limit-257.tag-count", decoded.word[18], 0, 23);
    uint64_t manifest = leanos_boot_manifest_candidate(
        800, 0, 0x100000, 0x100000, 0x200000,
        0x110000, 0x1000, 0x120000, 0x1000, 0x130000, 0x1000,
        0x140000, 0x1000, 0x141000, 0x4000, 0x180000, 0x2000,
        0x300000, 96);
    CHECK_RESULT("manifest.accepted.candidate", manifest, 1, 17);
    CHECK_RESULT("consume.accepted.frame",
        leanos_boot_consume_exact_projection(4096, 800, 1, 1, 0, manifest),
        800, 17);
    CHECK_RESULT("consume.retains-first-frame",
        leanos_boot_consume_exact_projection(800, 801, 1, 1, 0, manifest),
        800, 17);
    CHECK_RESULT("publish.accepted.next-frame",
        leanos_boot_publish_authority(800, 800, 1, 1, 0, manifest, 1),
        801, 17);
    CHECK_RESULT("authority-result.accepted.status",
        leanos_boot_authority_result(800, 800, 1, 1, 0, manifest, 1, 1),
        1, 17);
    CHECK_RESULT("authority-result.accepted.frame",
        leanos_boot_authority_result(800, 800, 1, 1, 0, manifest, 1, 3),
        800, 17);
    CHECK_RESULT("authority-result.accepted.publication",
        leanos_boot_authority_result(800, 800, 1, 1, 0, manifest, 1, 4),
        801, 17);
    CHECK_RESULT("publish.rescan-mismatch.next-frame",
        leanos_boot_publish_authority(800, 801, 1, 1, 0, manifest, 1),
        0, 17);
    CHECK_RESULT("authority-result.rejection-no-frame",
        leanos_boot_authority_result(800, 801, 1, 1, 0, manifest, 1, 3),
        0, 17);
    CHECK_RESULT("authority-result.rejection-no-publication",
        leanos_boot_authority_result(800, 801, 1, 1, 0, manifest, 1, 4),
        0, 17);
    CHECK_RESULT("authority-result.mutated-status-no-frame",
        leanos_boot_authority_result(800, 800, 2, 1, 0, manifest, 1, 3),
        0, 17);
    CHECK_RESULT("authority-result.mutated-usable-no-publication",
        leanos_boot_authority_result(800, 800, 1, 0, 0, manifest, 1, 4),
        0, 17);
    CHECK_RESULT("authority-result.mutated-blocked-no-publication",
        leanos_boot_authority_result(800, 800, 1, 1, 1, manifest, 1, 4),
        0, 17);
    CHECK_RESULT("authority-result.mutated-manifest-no-publication",
        leanos_boot_authority_result(800, 800, 1, 1, 0, 0, 1, 4),
        0, 17);
    CHECK_RESULT("authority-result.mutated-scrub-no-publication",
        leanos_boot_authority_result(800, 800, 1, 1, 0, manifest, 0, 4),
        0, 17);
    uint64_t gap_start = leanos_boot_manifest_start(
        0, 0x100000, 0x200000, 0x100000,
        0x210000, 0x1000, 0x220000, 0x1000, 0x230000, 0x1000,
        0x240000, 0x1000, 0x241000, 0x4000, 0x280000, 0x2000,
        0x300000, 96);
    manifest = leanos_boot_manifest_candidate(
        gap_start, 0, 0x100000, 0x200000, 0x100000,
        0x210000, 0x1000, 0x220000, 0x1000, 0x230000, 0x1000,
        0x240000, 0x1000, 0x241000, 0x4000, 0x280000, 0x2000,
        0x300000, 96);
    CHECK_RESULT("manifest.gap.start", gap_start, 256, 24);
    CHECK_RESULT("manifest.gap.candidate", manifest, 1, 24);
    CHECK_RESULT("consume.gap.frame",
        leanos_boot_consume_exact_projection(
            4096, gap_start, 1, 1, 0, manifest), 256, 24);
    const uint64_t zero_entry_fixture[4] = {
        32, UINT64_C(0x0000001000000006), 24,
        UINT64_C(0x0000000800000000),
    };
    decoded = decode_extent(zero_entry_fixture, 4, 1);
    CHECK_RESULT("decode.zero-entry.version", decoded.word[0], 4, 25);
    CHECK_RESULT("decode.zero-entry.status", decoded.word[1], 1, 25);
    CHECK_RESULT("decode.zero-entry.error", decoded.word[2], 0, 25);
    CHECK_RESULT("decode.zero-entry.phase", decoded.word[7], 7, 25);
    CHECK_RESULT("decode.zero-entry.entry-count", decoded.word[11], 0, 25);
    CHECK_RESULT("decode.zero-entry.target-found", decoded.word[14], 0, 25);
    CHECK_RESULT("decode.zero-entry.target-blocked", decoded.word[15], 0, 25);
    CHECK_RESULT("decode.zero-entry.tag-count", decoded.word[18], 2, 25);
    CHECK_RESULT("consume.zero-entry.frame",
        leanos_boot_consume_exact_projection(
            4096, 1, decoded.word[1], decoded.word[14],
            decoded.word[15], 1), 4096, 25);
    CHECK_RESULT("publish.zero-entry.next-frame",
        leanos_boot_publish_authority(
            4096, 4096, decoded.word[1], decoded.word[14], decoded.word[15],
            1, 1), 0, 25);
    const uint64_t peer_overlap[][18] = {
        {0, 0x100000, 0x200000, 0x100000,
         0x240000, 0x1000, 0x220000, 0x1000, 0x230000, 0x1000,
         0x240000, 0x1000, 0x241000, 0x4000, 0x280000, 0x2000,
         0x300000, 96},
        {0, 0x100000, 0x200000, 0x100000,
         0x210000, 0x1000, 0x241000, 0x1000, 0x230000, 0x1000,
         0x240000, 0x1000, 0x241000, 0x4000, 0x280000, 0x2000,
         0x300000, 96},
        {0, 0x100000, 0x200000, 0x100000,
         0x210000, 0x1000, 0x220000, 0x1000, 0x240000, 0x1000,
         0x240000, 0x1000, 0x241000, 0x4000, 0x280000, 0x2000,
         0x300000, 96},
        {0, 0x100000, 0x200000, 0x100000,
         0x210000, 0x1000, 0x220000, 0x1000, 0x230000, 0x1000,
         0x240000, 0x1000, 0x241000, 0x4000, 0x241000, 0x2000,
         0x300000, 96},
    };
    for (uint64_t peer = 0; peer < 4; ++peer) {
        const uint64_t *range = peer_overlap[peer];
        CHECK_INDEXED("manifest.peer-overlap", peer, "candidate",
            leanos_boot_manifest_candidate(
                256, range[0], range[1], range[2], range[3], range[4],
                range[5], range[6], range[7], range[8], range[9], range[10],
                range[11], range[12], range[13], range[14], range[15],
                range[16], range[17]), 0, 26 + peer);
    }
    const uint64_t image_at_limit = leanos_boot_manifest_candidate(
        256, 0, 0x100000, 0xf00000, 0x100000,
        0xf10000, 0x1000, 0xf20000, 0x1000, 0xf30000, 0x1000,
        0xf40000, 0x1000, 0xf41000, 0x4000, 0xf80000, 0x2000,
        0x300000, 96);
    CHECK_RESULT("manifest.image-at-limit.candidate", image_at_limit, 1, 30);
    CHECK_RESULT("consume.image-at-limit.frame",
        leanos_boot_consume_exact_projection(
            4096, 256, 1, 1, 0, image_at_limit), 256, 30);
    const uint64_t info_at_limit = leanos_boot_manifest_candidate(
        256, 0, 0x100000, 0xf00000, 0x100000,
        0xf10000, 0x1000, 0xf20000, 0x1000, 0xf30000, 0x1000,
        0xf40000, 0x1000, 0xf41000, 0x4000, 0xf80000, 0x2000,
        0xffffa0, 96);
    CHECK_RESULT("manifest.info-at-limit.candidate", info_at_limit, 1, 31);
    CHECK_RESULT("publish.info-at-limit.next-frame",
        leanos_boot_publish_authority(256, 256, 1, 1, 0,
                                      info_at_limit, 1), 257, 31);
    const uint64_t image_past_limit = leanos_boot_manifest_candidate(
        256, 0, 0x100000, 0xf00000, 0x100001,
        0xf10000, 0x1000, 0xf20000, 0x1000, 0xf30000, 0x1000,
        0xf40000, 0x1000, 0xf41000, 0x4000, 0xf80000, 0x2000,
        0x300000, 96);
    CHECK_RESULT("manifest.image-past-limit.candidate",
        image_past_limit, 0, 32);
    CHECK_RESULT("manifest.image-past-limit.start",
        leanos_boot_manifest_start(
            0, 0x100000, 0xf00000, 0x100001,
            0xf10000, 0x1000, 0xf20000, 0x1000, 0xf30000, 0x1000,
            0xf40000, 0x1000, 0xf41000, 0x4000, 0xf80000, 0x2000,
            0x300000, 96), 4096, 32);
    CHECK_RESULT("consume.image-past-limit.frame",
        leanos_boot_consume_exact_projection(
            4096, 256, 1, 1, 0, image_past_limit), 4096, 32);
    const uint64_t info_past_limit = leanos_boot_manifest_candidate(
        256, 0, 0x100000, 0x200000, 0x100000,
        0x210000, 0x1000, 0x220000, 0x1000, 0x230000, 0x1000,
        0x240000, 0x1000, 0x241000, 0x4000, 0x280000, 0x2000,
        0xfffff0, 96);
    CHECK_RESULT("manifest.info-past-limit.candidate",
        info_past_limit, 0, 33);
    CHECK_RESULT("manifest.info-past-limit.start",
        leanos_boot_manifest_start(
            0, 0x100000, 0x200000, 0x100000,
            0x210000, 0x1000, 0x220000, 0x1000, 0x230000, 0x1000,
            0x240000, 0x1000, 0x241000, 0x4000, 0x280000, 0x2000,
            0xfffff0, 96), 4096, 33);
    CHECK_RESULT("publish.info-past-limit.next-frame",
        leanos_boot_publish_authority(4096, 4096, 1, 1, 0,
                                      info_past_limit, 1), 0, 33);
    return 0;
}

#ifdef LEANOS_HOSTED_REPLAY
int main(void) {
    const int status = check_stream();
    printf("stream-result %d\n", status);
    return status;
}
#else
__attribute__((naked, noreturn)) void _start(void) {
    __asm__ volatile(
        "andq $-16, %rsp\n"
        "call check_stream\n"
        "movq %rax, %rdi\n"
        "movq $60, %rax\n"
        "syscall\n");
}
#endif
