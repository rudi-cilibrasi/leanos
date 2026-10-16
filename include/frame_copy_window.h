#ifndef LEANOS_FRAME_COPY_WINDOW_H
#define LEANOS_FRAME_COPY_WINDOW_H

/* Frame copy windows (issue #569; LeanOS.FrameCopyWindow,
 * docs/frame-copy-window.md).
 *
 * A port holder's window is one or two whole pages of its own memory.  For
 * each holder the kernel builds two window roots from one source root,
 * before any subject runs:
 *
 *   fetch root  the closed root plus writable supervisor no-execute aliases
 *               of the window's frames at the alias slots;
 *   send root   the same aliases read-only.
 *
 * The closed root is the source with every present leaf of a protected
 * (user) frame removed, so neither window root maps another subject's
 * frame, and neither grants user access or execution to any user frame.
 * A copy asks the generated operand leanos_frame_window_operand for the
 * alias address, then calls frame_window_transfer (boot/boot.S),
 * which selects the window root, moves the frame with one string move and
 * reselects the caller's root.
 *
 * This header builds the roots with the reviewed builder
 * (qotom_copy_root_builder.h) and checks every leaf of each result.  It
 * cannot establish the completeness of the protected inventory or that the
 * alias slots are unused by the kernel; its caller names both. */

#include "qotom_copy_root_builder.h"

#define FRAME_WINDOW_MAX_BYTES 1514u
#define FRAME_WINDOW_MAX_PAGES 2u

/* boot/boot.S: select `window_root`, copy `length` bytes (at most
 * FRAME_WINDOW_MAX_BYTES) from `source` to `destination`, reselect
 * `resume_root`.  Halts unless IF, CR4.PGE and CR4.PCIDE are clear, both
 * roots are nonzero, page aligned and below 16 MiB, and each CR3 load reads
 * back.  Returns `length`. */
extern uint64_t frame_window_transfer(uint64_t resume_root, uint64_t window_root,
    uint64_t destination, uint64_t source, uint64_t length);

/* One port holder's window and its two roots. */
struct frame_window {
    struct qotom_root_pages *fetch;
    struct qotom_root_pages *send;
    uint64_t base;   /* first byte of the window, page aligned */
    uint64_t limit;  /* one past its last byte: one or two pages */
    uint64_t slot;   /* page number of the first alias slot */
};

enum frame_window_status {
    FRAME_WINDOW_OK,
    FRAME_WINDOW_GEOMETRY,
    FRAME_WINDOW_BUILD,
    FRAME_WINDOW_REBUILD,
    FRAME_WINDOW_SCAN
};

static inline uint64_t frame_window_pages(const struct frame_window *w) {
    return (w->limit - w->base) / 4096u;
}

/* The reviewed geometry (LeanOS.FrameCopyWindow.geometryOk). */
static inline int frame_window_geometry_ok(const struct frame_window *w) {
    return (w->base & 4095u) == 0 && w->base < w->limit &&
        w->limit <= UINT64_C(0x1000000) &&
        (w->limit - w->base == 4096u || w->limit - w->base == 8192u) &&
        w->slot != 0 && w->slot <= QOTOM_ROOT_LEAVES &&
        w->slot + frame_window_pages(w) <= QOTOM_ROOT_LEAVES;
}

/* `root` has the source hierarchy's shape, equals `closed` at every page
 * outside the alias slots, and maps exactly the window's frames at the alias
 * slots, supervisor and no-execute, writable exactly when `writable`; and
 * `closed` maps no protected frame at all. */
static inline int frame_window_root_exact(const struct qotom_root_pages *root,
        const struct qotom_root_pages *closed, const uint64_t *protected_frames,
        size_t protected_count, const struct frame_window *w, int writable) {
    if (!qotom_root_source_ancestors(root) || !qotom_root_source_ancestors(closed))
        return 0;
    const uint64_t pages = frame_window_pages(w);
    for (size_t page = 0; page < QOTOM_ROOT_LEAVES; ++page) {
        uint64_t closed_leaf = closed->pt[page];
        if ((closed_leaf & QOTOM_ROOT_PRESENT) && qotom_root_protected_frame(
                (closed_leaf & QOTOM_ROOT_ADDRESS_MASK) >> 12, protected_frames,
                protected_count))
            return 0;
        uint64_t leaf = root->pt[page];
        if (page >= w->slot && page < w->slot + pages) {
            uint64_t frame = (w->base >> 12) + (page - w->slot);
            uint64_t expected = (frame << 12) | QOTOM_ROOT_PRESENT | QOTOM_ROOT_NX |
                (writable ? QOTOM_ROOT_WRITABLE : 0);
            if (leaf != expected) return 0;
        } else if (leaf != closed_leaf) {
            return 0;
        }
    }
    return 1;
}

/* Build both of `w`'s roots from `source`, rewriting `closed` each time, and
 * check them leaf by leaf.  Every rebuild must reproduce the first build's
 * counts, which `first` holds once `*built` is set. */
static inline enum frame_window_status frame_window_build(
        const struct qotom_root_pages *source, struct qotom_root_pages *closed,
        const uint64_t *protected_frames, size_t protected_count,
        const struct frame_window *w, struct qotom_root_build_result *first, int *built) {
    if (!frame_window_geometry_ok(w)) return FRAME_WINDOW_GEOMETRY;
    struct qotom_copy_alias aliases[FRAME_WINDOW_MAX_PAGES];
    const uint64_t pages = frame_window_pages(w);
    for (int writable = 1; writable >= 0; --writable) {
        for (uint64_t i = 0; i < pages; ++i)
            aliases[i] = (struct qotom_copy_alias){
                w->slot + i, (w->base >> 12) + i, (uint64_t)writable };
        struct qotom_root_build_result result;
        struct qotom_root_pages *root = writable ? w->fetch : w->send;
        if (qotom_build_copy_roots(source, closed, root, protected_frames, protected_count,
                aliases, (size_t)pages, &result) != QOTOM_ROOT_BUILD_OK)
            return FRAME_WINDOW_BUILD;
        if (*built) {
            if (result.protected_count != first->protected_count ||
                result.removed_aliases != first->removed_aliases ||
                result.retained_present != first->retained_present)
                return FRAME_WINDOW_REBUILD;
        } else {
            *first = result;
            *built = 1;
        }
        if (result.alias_count != pages ||
            !frame_window_root_exact(root, closed, protected_frames, protected_count, w,
                writable))
            return FRAME_WINDOW_SCAN;
    }
    return FRAME_WINDOW_OK;
}

#endif
