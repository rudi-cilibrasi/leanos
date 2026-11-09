/* The code under test as one library unit: include/qotom_copy_root_builder.h and include/frame_copy_window.h,
 * unchanged.  Their functions are static, so this unit gives the three the laws call external names: the kernel
 * and the Qotom lab images call qotom_build_copy_roots and frame_window_build, and the production image also
 * calls frame_window_root_exact on its own.  Each wrapper only forwards its arguments. */
#include "roots_api.h"

enum qotom_root_build_status roots_build(
        const struct qotom_root_pages *source, uint64_t source_phys,
        struct qotom_root_pages *closed, uint64_t closed_phys,
        struct qotom_root_pages *copy, uint64_t copy_phys,
        const uint64_t *protected_frames, size_t protected_count,
        const struct qotom_copy_alias *aliases, size_t alias_count,
        struct qotom_root_build_result *result) {
    return qotom_build_copy_roots(source, source_phys, closed, closed_phys, copy, copy_phys,
        protected_frames, protected_count, aliases, alias_count, result);
}

enum frame_window_status window_build(
        const struct qotom_root_pages *source, uint64_t source_phys,
        struct qotom_root_pages *closed, uint64_t closed_phys,
        const uint64_t *protected_frames, size_t protected_count,
        const struct frame_window *w, struct qotom_root_build_result *first, int *built) {
    return frame_window_build(source, source_phys, closed, closed_phys, protected_frames,
        protected_count, w, first, built);
}

int window_root_exact(
        const struct qotom_root_pages *root, uint64_t root_phys,
        const struct qotom_root_pages *closed, uint64_t closed_phys,
        const uint64_t *protected_frames, size_t protected_count,
        const struct frame_window *w, int writable) {
    return frame_window_root_exact(root, root_phys, closed, closed_phys, protected_frames,
        protected_count, w, writable);
}
