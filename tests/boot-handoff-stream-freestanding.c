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
extern uint64_t leanos_boot_manifest_candidate(
    uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t,
    uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t,
    uint64_t, uint64_t, uint64_t, uint64_t, uint64_t);
extern uint64_t leanos_boot_manifest_start(
    uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t,
    uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t,
    uint64_t, uint64_t, uint64_t, uint64_t);
extern uint64_t leanos_boot_select_frame(
    uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t);
extern uint64_t leanos_boot_publish_authority(
    uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t);

struct stream_state {
    uint64_t word[7];
};

struct decode_state { uint64_t word[19]; };

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
    REGISTER_BOUNDARY(leanos_boot_manifest_candidate);
    REGISTER_BOUNDARY(leanos_boot_manifest_start);
    REGISTER_BOUNDARY(leanos_boot_select_frame);
    REGISTER_BOUNDARY(leanos_boot_publish_authority);
#endif
    const uint64_t identity = 0x1000;
    const uint64_t chunks[12] = {
        0x0000000000000060, 0x000000090000002a, 0x00000000000000aa,
        0x0000004000000006, 0x0000000000000018, 0x0000000000001000,
        0x0000000000004000, 0x0000000000000001, 0x0000000000002000,
        0x0000000000001000, 0x0000000000000002, 0x0000000800000000,
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
    CHECK_RESULT("select.accepted.frame",
        leanos_boot_select_frame(4096, 800, 1, 1, 0, manifest), 800, 17);
    CHECK_RESULT("publish.accepted.next-frame",
        leanos_boot_publish_authority(800, 800, 1, 1, 0, manifest, 1),
        801, 17);
    CHECK_RESULT("publish.rescan-mismatch.next-frame",
        leanos_boot_publish_authority(800, 801, 1, 1, 0, manifest, 1),
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
    CHECK_RESULT("select.gap.frame",
        leanos_boot_select_frame(4096, gap_start, 1, 1, 0, manifest), 256, 24);
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
    CHECK_RESULT("select.zero-entry.frame",
        leanos_boot_select_frame(4096, 1, decoded.word[1], decoded.word[14],
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
    CHECK_RESULT("select.image-at-limit.frame",
        leanos_boot_select_frame(4096, 256, 1, 1, 0, image_at_limit),
        256, 30);
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
    CHECK_RESULT("select.image-past-limit.frame",
        leanos_boot_select_frame(4096, 256, 1, 1, 0,
                                 image_past_limit), 4096, 32);
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
