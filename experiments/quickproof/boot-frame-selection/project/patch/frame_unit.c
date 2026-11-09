/* The code under test as one library unit: include/boot_frame_selection.h, unchanged.  Its functions are static
 * inline, so this unit gives each of its seven steps an external name, in the order boot_allocate calls them:
 * boot_frame_terminal, boot_frame_select, boot_frame_cross_check, boot_frame_scrub_selected,
 * boot_frame_publication_result, boot_frame_publication_check and, in the frame-budget scenario,
 * boot_frame_rescan.  Each wrapper only forwards its arguments. */
#include "frame_api.h"

enum boot_frame_status frame_terminal(const uint64_t *manifest, const uint64_t *decoded, const uint64_t *usable,
                                      const uint64_t *blocked, uint64_t *reserved, uint64_t *terminal) {
    return boot_frame_terminal(manifest, decoded, usable, blocked, reserved, terminal);
}

enum boot_frame_status frame_select(boot_frame_decode decode, void *context, const uint64_t *manifest,
                                    uint32_t take_next, uint64_t states[2][BOOT_FRAME_DECODE_WORDS],
                                    uint64_t *selected, uint64_t *selected_manifest, uint64_t *next,
                                    uint32_t *decoder_status) {
    return boot_frame_select(decode, context, manifest, take_next, states, selected, selected_manifest, next,
                             decoder_status);
}

enum boot_frame_status frame_cross_check(const uint64_t *terminal, const uint64_t *decoded, uint64_t selected,
                                         const uint64_t *state, uint64_t selected_manifest) {
    return boot_frame_cross_check(terminal, decoded, selected, state, selected_manifest);
}

enum boot_frame_status frame_scrub_selected(boot_frame_scrub scrub, void *context, uint64_t selected) {
    return boot_frame_scrub_selected(scrub, context, selected);
}

void frame_publication_result(uint64_t selected, const uint64_t *state, uint64_t selected_manifest,
                              uint64_t *publication) {
    boot_frame_publication_result(selected, state, selected_manifest, publication);
}

enum boot_frame_status frame_publication_check(uint64_t selected, const uint64_t *publication) {
    return boot_frame_publication_check(selected, publication);
}

enum boot_frame_status frame_rescan(boot_frame_decode decode, void *context, const uint64_t *manifest,
                                    const uint64_t *decoded, uint64_t published, uint64_t next, uint64_t *state,
                                    uint64_t *rescan, uint32_t *decoder_status) {
    return boot_frame_rescan(decode, context, manifest, decoded, published, next, state, rescan, decoder_status);
}
