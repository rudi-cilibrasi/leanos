#include <stdint.h>

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
    uint64_t, uint64_t);
extern uint64_t leanos_boot_manifest_candidate(
    uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t,
    uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t,
    uint64_t, uint64_t, uint64_t, uint64_t, uint64_t);
extern uint64_t leanos_boot_select_frame(
    uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t);
extern uint64_t leanos_boot_publish_authority(
    uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t);

struct stream_state {
    uint64_t word[7];
};

struct decode_state { uint64_t word[18]; };

static struct decode_state decode(const uint64_t chunks[12], uint64_t target) {
    struct decode_state state, next;
    for (uint64_t query = 0; query < 18; ++query)
        state.word[query] =
            leanos_boot_decode_init(0x36d76289, 0x1000, 96, target, query);
    for (uint64_t index = 0; index < 12; ++index) {
        for (uint64_t query = 0; query < 18; ++query)
            next.word[query] = leanos_boot_decode_step(
                state.word[0], state.word[1], state.word[2], state.word[3],
                state.word[4], state.word[5], state.word[6], state.word[7],
                state.word[8], state.word[9], state.word[10], state.word[11],
                state.word[12], state.word[13], state.word[14], state.word[15],
                state.word[16], state.word[17], 0x1000, index * 8,
                chunks[index], index == 11, query);
        state = next;
        if (state.word[2] != 0) break;
    }
    return state;
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
    if (state.word[0] != 2 || state.word[1] != 0 || state.word[2] != 0 ||
        state.word[3] != identity || state.word[4] != 96 ||
        state.word[5] != 0 || state.word[6] != 0xcbf29ce484222325)
        return 1;

    if (leanos_boot_handoff_stream_init(
            0x36d76289, identity, 95, identity, 1) != 2)
        return 2;
    if (leanos_boot_handoff_stream_init(
            0x36d76289, identity, 96, 0x2000, 2) != 5)
        return 3;
    if (leanos_boot_handoff_stream_init(
            0x36d76289, UINT64_MAX - 7, 16, UINT64_MAX - 7, 2) != 14)
        return 13;

    if (step_query(&state, 0x2000, 0, 8, chunks[0], 0, 2) != 8)
        return 4;
    if (step_query(&state, identity, 8, 8, chunks[0], 0, 2) != 9)
        return 5;
    if (step_query(&state, identity, 0, 1, 0x100, 0, 2) != 13)
        return 6;
    if (step_query(&state, identity, 0, 8, chunks[0], 1, 2) != 12)
        return 7;

    for (uint64_t index = 0; index < 12; ++index) {
        const uint64_t terminal = index == 11;
        if (step_query(&state, identity, index * 8, 8, chunks[index], terminal,
                       7) != chunks[index])
            return 8;
        if (step_query(&state, identity, index * 8, 8, chunks[index], terminal,
                       8) != 8)
            return 9;
        for (uint64_t query = 0; query < 7; ++query)
            next.word[query] = step_query(
                &state, identity, index * 8, 8, chunks[index], terminal, query);
        state = next;
    }
    if (state.word[1] != 1 || state.word[2] != 0 || state.word[5] != 96)
        return 10;
    if (step_query(&state, identity, 96, 1, 0, 0, 1) != 2)
        return 11;
    if (step_query(&state, identity, 96, 1, 0, 0, 7) != 0)
        return 12;
    struct decode_state decoded = decode(chunks, 1);
    if (decoded.word[0] != 3 || decoded.word[1] != 1 ||
        decoded.word[2] != 0 || decoded.word[7] != 7 ||
        decoded.word[11] != 2 || decoded.word[14] != 1 ||
        decoded.word[15] != 0)
        return 14;
    decoded = decode(chunks, 2);
    if (decoded.word[1] != 1 || decoded.word[14] != 1 ||
        decoded.word[15] != 1)
        return 15;
    uint64_t high_reserved[12];
    for (uint64_t index = 0; index < 12; ++index)
        high_reserved[index] = chunks[index];
    high_reserved[8] = 0x100000000;
    high_reserved[9] = 0x10000000000;
    decoded = decode(high_reserved, 1);
    if (decoded.word[1] != 1 || decoded.word[17] != 0x5000)
        return 18;
    uint64_t malformed[12];
    for (uint64_t index = 0; index < 12; ++index) malformed[index] = chunks[index];
    malformed[2] = 0x1aa;
    decoded = decode(malformed, 1);
    if (decoded.word[1] != 2 || decoded.word[2] != 5)
        return 16;
    uint64_t manifest = leanos_boot_manifest_candidate(
        800, 0, 0x100000, 0x100000, 0x200000,
        0x110000, 0x1000, 0x120000, 0x1000, 0x130000, 0x1000,
        0x140000, 0x1000, 0x141000, 0x4000, 0x180000, 0x2000,
        0x300000, 96);
    if (manifest != 1 ||
        leanos_boot_select_frame(4096, 800, 1, 1, 0, manifest) != 800 ||
        leanos_boot_publish_authority(800, 800, 1, 1, 0, manifest, 1) != 801 ||
        leanos_boot_publish_authority(800, 801, 1, 1, 0, manifest, 1) != 0)
        return 17;
    return 0;
}

__attribute__((naked, noreturn)) void _start(void) {
    __asm__ volatile(
        "andq $-16, %rsp\n"
        "call check_stream\n"
        "movq %rax, %rdi\n"
        "movq $60, %rax\n"
        "syscall\n");
}
