#ifndef LEANOS_COMPOSITE_DISPATCHER_H
#define LEANOS_COMPOSITE_DISPATCHER_H

#include <stdint.h>

/*
 * Version-one scalar ABI for LeanOS.CompositeDispatcher.dispatch.
 *
 * Input words are ordered as the canonical name of a complete bounded
 * CompositeState, command tag, then arguments 0..3. Lean reconstructs the
 * complete state by authoritative replay; callers cannot supply individual
 * state projections or post-state fragments. Result word zero canonically
 * names the exact typed authoritativeGate result and next state. Result word
 * one is the exact returned handle for an accepted attached receipt and zero
 * for every other result.
 *
 * All fields are logical uint64_t values. There are no caller-owned buffers,
 * so state/result aliasing, alignment, pointer identity, and partial writes are
 * inapplicable. Calls are pure, reentrant, and have no generated state cell.
 * Exactly six input words are required by the surrounding corpus format;
 * truncation is rejected by that caller before this scalar function is called.
 *
 * Every state and command word has ABI version 1 in bits 0..7. State bits
 * 8..15 select one canonical state and all upper bits are reserved. Command
 * tags use bits 8..15 to select one command selector and all upper bits are
 * reserved; several families share a selector and let the state token choose
 * its meaning. Arguments not named by a command must be zero. A success
 * result word zero uses bits 0..7 for the version, 8..15 for the next-state
 * selector, 16..23 for the typed-reply selector, and reserves bits 24..63.
 * Error words are closed values and never authorize an operation.
 *
 * Every constant of this vocabulary -- the fixed scalars, the state,
 * command, and reply selectors, the frame-budget flush authorizations, the
 * error words, and the selector counts -- is generated into
 * composite-tokens.h from LeanOS.BoundaryVocabulary by evaluating the same
 * encoders and canonical-edge tables the dispatcher proofs use. Nothing in
 * this header restates a word; a token that is not generated does not exist.
 * The exported entry points are declared by the generated boundary-abi.h,
 * whose prototypes are read from the Lean @[export] attributes.
 */
#include "composite-tokens.h"
#include "boundary-abi.h"

/*
 * Notes on the generated tokens.
 *
 * Typed reply/effect meanings for the bounded direct mapping branches:
 * LEANOS_COMPOSITE_REPLY_PAGE_UNMAPPED authorizes exactly
 * StaleTranslation.Effect.page(2, 7), while
 * LEANOS_COMPOSITE_REPLY_PAGE_PROTECTED authorizes exactly Effect.page(2, 8).
 * The rejection replies are complete-state stutters and authorize
 * Effect.none. These are scalar meanings of Lean-replayed states, not
 * mutable C shadow state.
 *
 * In-flight revocation (#175): the seed has subject 1 current with a
 * delegated revoke-only authority on endpoint 10; every state token is exact
 * authoritative replay from that kernel-owned seed. The offer, receipt, and
 * fresh-copy tags are shared with the mixed corpus; the state token selects
 * the family. Revocation words are raw slot selectors resolved in the
 * kernel-derived current subject; the lineage root identity, the receiving
 * subject, and the replacement generation are never caller-supplied.
 * LEANOS_COMPOSITE_REPLY_INFLIGHT_LINEAGE_REVOKED means the exact accepted
 * subtree revocation that also canceled the sealed child;
 * LEANOS_COMPOSITE_REPLY_INFLIGHT_CANCELED_RECEIPT_REJECTED denies the later
 * receipt with the typed empty rejection and no value word. No reply in this
 * family ever publishes a handle in result word one.
 *
 * LEANOS_FRAME_BUDGET_TERMINATE_FLUSH_TOKEN and
 * LEANOS_FRAME_BUDGET_RELEASE_FLUSH_TOKEN are the exact full-state/command
 * authorizations for the two frame-retiring edges.
 *
 * The invalidation publication sequence retains the published pre-state while
 * an effect is pending. Prepare replies name the checked page/space/flush
 * effect and its fresh logical ticket. An exact acknowledgement advances to
 * the successor; malformed, stale-ticket, wrong-effect, and wrong-state inputs
 * cannot publish. Reuse is enabled only after acknowledged release and
 * destruction. The object-11 reuse is a bounded fixture, not allocator policy.
 *
 * leanos_composite_dispatch_value is the result-word-one accessor. It must be
 * invoked with the same immutable six inputs as leanos_composite_dispatch.
 * Zero is an unambiguous no-value marker because canonical capability handles
 * reserve generation zero. leanos_frame_budget_mapping_page is the generated
 * policy query for the issue-112 machine publication leaf, and
 * leanos_frame_budget_invalidation_effect the generated full-flush
 * authorization; zero denies every noncanonical pair.
 * leanos_validate_q35_dma_snapshot is the allocation-free generated
 * validation of the exact canonical q35 DMA snapshot; each manifest slot
 * supplies identity and control words in the compact format documented by
 * LeanOS.CompositeDispatcher.
 */

#endif
