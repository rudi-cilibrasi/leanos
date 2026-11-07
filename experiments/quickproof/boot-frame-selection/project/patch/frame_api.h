/* The external names patch/frame_unit.c gives the frame selection, scrub and publication (see there). */
#ifndef LEANOS_FRAME_API_H
#define LEANOS_FRAME_API_H
#include "boot_frame_selection.h"

enum boot_frame_status frame_terminal(const uint64_t *manifest, const uint64_t *decoded, const uint64_t *usable,
                                      const uint64_t *blocked, uint64_t *reserved, uint64_t *terminal);
enum boot_frame_status frame_select(boot_frame_decode decode, void *context, const uint64_t *manifest,
                                    uint32_t take_next, uint64_t states[2][BOOT_FRAME_DECODE_WORDS],
                                    uint64_t *selected, uint64_t *selected_manifest, uint64_t *next,
                                    uint32_t *decoder_status);
enum boot_frame_status frame_cross_check(const uint64_t *terminal, const uint64_t *decoded, uint64_t selected,
                                         const uint64_t *state, uint64_t selected_manifest);
enum boot_frame_status frame_scrub_selected(boot_frame_scrub scrub, void *context, uint64_t selected);
void frame_publication_result(uint64_t selected, const uint64_t *state, uint64_t selected_manifest,
                              uint64_t *publication);
enum boot_frame_status frame_publication_check(uint64_t selected, const uint64_t *publication);
enum boot_frame_status frame_rescan(boot_frame_decode decode, void *context, const uint64_t *manifest,
                                    const uint64_t *decoded, uint64_t published, uint64_t next, uint64_t *state,
                                    uint64_t *rescan, uint32_t *decoder_status);
#endif
