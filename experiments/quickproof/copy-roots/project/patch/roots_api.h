/* The external names patch/roots_unit.c gives the two builders and the window scan (see there). */
#ifndef LEANOS_ROOTS_API_H
#define LEANOS_ROOTS_API_H
#include "frame_copy_window.h"

enum qotom_root_build_status roots_build(
        const struct qotom_root_pages *source, uint64_t source_phys,
        struct qotom_root_pages *closed, uint64_t closed_phys,
        struct qotom_root_pages *copy, uint64_t copy_phys,
        const uint64_t *protected_frames, size_t protected_count,
        const struct qotom_copy_alias *aliases, size_t alias_count,
        struct qotom_root_build_result *result);

enum frame_window_status window_build(
        const struct qotom_root_pages *source, uint64_t source_phys,
        struct qotom_root_pages *closed, uint64_t closed_phys,
        const uint64_t *protected_frames, size_t protected_count,
        const struct frame_window *w, struct qotom_root_build_result *first, int *built);

int window_root_exact(
        const struct qotom_root_pages *root, uint64_t root_phys,
        const struct qotom_root_pages *closed, uint64_t closed_phys,
        const uint64_t *protected_frames, size_t protected_count,
        const struct frame_window *w, int writable);
#endif
