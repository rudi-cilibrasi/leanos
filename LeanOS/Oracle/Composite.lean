import LeanOS.Oracle.Vector
import LeanOS.CompositeDispatcher

/-!
# Oracle corpus: the stateful composite dispatcher

The rows of `CompositeDispatcher.dispatch`: the scenario and hostile-encoding
rows, the canonical mixed, invalidation, boot capability-transfer, and
in-flight revocation edge sets with their negatives, and their trace checks.
The frame-budget and spawn families use the same adapter in their own modules.
-/
namespace LeanOS.Oracle

open LeanOS
set_option maxRecDepth 4096

def composite (id : String) (state tag arg0 arg1 arg2 arg3 : UInt64) : Vector :=
  { id, adapter := "CompositeDispatcher.stateful",
    words := [state, tag, arg0, arg1, arg2, arg3],
    expected := CompositeDispatcher.dispatch state tag arg0 arg1 arg2 arg3,
    expectedValue := CompositeDispatcher.dispatchValue state tag arg0 arg1 arg2 arg3 }

private def mixedEdgeId : CompositeDispatcher.MixedReplyId → String
  | .transferOffered => "composite.mixed-transfer-offer"
  | .transferAccepted => "composite.mixed-transfer-accept"
  | .sealedHandleRejected => "composite.mixed-transfer-pre-receipt-denial"
  | .delegatedSendAccepted => "composite.mixed-transfer-delegated-send"
  | .delegatedReceiveRejected =>
      "composite.mixed-transfer-excess-receive-denial"
  | .transferredCapabilityRevoked => "composite.mixed-capability-revoke"
  | .staleHandleRejected => "composite.mixed-stale-handle-reject"
  | .freshCapabilityCopied => "composite.mixed-capability-copy"
  | .syscallMapped => "composite.mixed-syscall-map"
  | .directMapped => "composite.mixed-direct-map"
  | .unknownSyscallRejected => "composite.mixed-unknown-syscall-reject"
  | .nonblockingSent => "composite.mixed-nonblocking-send"
  | .nonblockingReceived => "composite.mixed-nonblocking-receive"
  | .blockingReceiverBlocked => "composite.mixed-blocking-receive"
  | .blockingReceiverWoken => "composite.mixed-blocking-send"
  | .timerSwitched => "composite.mixed-timer-switch"
  | .userFaultCleaned => "composite.mixed-user-fault-cleanup"
  | .fatalEntered => "composite.mixed-fatal-entry"
  | .postFatalRejected => "composite.mixed-post-fatal-reject"
  | .pageUnmapped => "composite.mixed-page-unmapped"
  | .unmappedPageRejected => "composite.mixed-unmapped-page-reject"
  | .pageProtected => "composite.mixed-page-protected"
  | .protectAmplificationRejected => "composite.mixed-protect-amplification-reject"

/-- The hosted representation of one canonical accepted mixed edge.  State,
command arguments, and expected reply all come from the same edge definition
used by `mixedCanonicalEdges_refine`. -/
def mixedEdgeVector (edge : CompositeDispatcher.CanonicalMixedEdge) : Vector :=
  let words := CompositeDispatcher.encodeMixedCommand edge.command
  composite (mixedEdgeId edge.reply)
    (CompositeDispatcher.encodeMixedState edge.state)
    words.tag words.arg0 words.arg1 words.arg2 words.arg3

def mixedVectors : List Vector :=
  CompositeDispatcher.mixedCanonicalEdges.map mixedEdgeVector

private def capabilityTransferBootEdgeId :
    CompositeDispatcher.CapabilityTransferBootCommandId → String
  | .offer => "composite.boot-transfer-subject-one-offer"
  | .switchToSubjectTwo => "composite.boot-transfer-switch-subject-two"
  | .rejectSealedHandle => "composite.boot-transfer-sealed-denial"
  | .accept => "composite.boot-transfer-subject-two-accept"
  | .delegatedSend => "composite.boot-transfer-delegated-send"
  | .rejectDelegatedReceive => "composite.boot-transfer-receive-denial"

def capabilityTransferBootEdgeVector
    (edge : CompositeDispatcher.CanonicalCapabilityTransferBootEdge) : Vector :=
  let words :=
    CompositeDispatcher.encodeCapabilityTransferBootCommand edge.command
  composite (capabilityTransferBootEdgeId edge.command)
    (CompositeDispatcher.encodeCapabilityTransferBootState edge.state)
    words.tag words.arg0 words.arg1 words.arg2 words.arg3

def capabilityTransferBootVectors : List Vector :=
  CompositeDispatcher.capabilityTransferBootEdges.map
    capabilityTransferBootEdgeVector

private def inFlightRevocationEdgeId :
    CompositeDispatcher.InFlightRevocationReplyId → String
  | .childOffered => "composite.inflight-revocation-offer"
  | .revocationWithoutAuthorityRejected =>
      "composite.inflight-revocation-missing-authority-denial"
  | .wrongLineageRootRejected => "composite.inflight-revocation-wrong-root-denial"
  | .lineageRevoked => "composite.inflight-revocation-revoke"
  | .repeatedRevocationRejected => "composite.inflight-revocation-repeat-denial"
  | .offerAfterRevocationRejected => "composite.inflight-revocation-stale-offer-denial"
  | .subjectTwoRestored => "composite.inflight-revocation-switch-subject-two"
  | .canceledReceiptRejected => "composite.inflight-revocation-canceled-receipt-denial"
  | .destinationReplaced => "composite.inflight-revocation-replace-slot"
  | .canceledHandleReplayRejected =>
      "composite.inflight-revocation-canceled-handle-denial"
  | .replacementUsed => "composite.inflight-revocation-fresh-send"

def inFlightRevocationEdgeVector
    (edge : CompositeDispatcher.CanonicalInFlightRevocationEdge) : Vector :=
  let words := CompositeDispatcher.encodeInFlightRevocationCommand edge.command
  composite (inFlightRevocationEdgeId edge.reply)
    (CompositeDispatcher.encodeInFlightRevocationState edge.state)
    words.tag words.arg0 words.arg1 words.arg2 words.arg3

def inFlightRevocationVectors : List Vector :=
  CompositeDispatcher.inFlightRevocationCanonicalEdges.map inFlightRevocationEdgeVector

/-- Hostile records for the in-flight revocation family: the revocation words
replayed against the pre-offer seed token, the mixed corpus's post-receipt
revocation spliced into this family's subject-2 state, and subject 2's receipt
words presented while subject 1 is still the current subject.  None can select
an edge; the state token, not the caller, decides who is acting. -/
def inFlightRevocationNegativeVectors : List Vector := [
  composite "composite.inflight-revocation-stale-state-replay" 0x6001 0x5201 2 1 1 0,
  composite "composite.inflight-revocation-cross-trace-splice" 0x6301 0x2201 0 2 3 0,
  composite "composite.inflight-revocation-receipt-before-switch" 0x6201 0x2101
    0x30000 3 0 0]

private def invalidationEdgeId :
    CompositeDispatcher.InvalidationReplyId → String
  | .wrongOwnerRejected => "composite.invalidation-wrong-owner-reject"
  | .protectPending => "composite.invalidation-protect-pending"
  | .protectMismatchRejected => "composite.invalidation-protect-effect-mismatch"
  | .protectedState => "composite.invalidation-protect-ack"
  | .releasePending => "composite.invalidation-release-pending"
  | .releaseMismatchRejected => "composite.invalidation-release-effect-mismatch"
  | .released => "composite.invalidation-release-ack"
  | .staleReleaseRejected => "composite.invalidation-stale-release-reject"
  | .destroyPending => "composite.invalidation-destroy-pending"
  | .destroyed => "composite.invalidation-destroy-ack"
  | .switchPending => "composite.invalidation-switch-pending"
  | .switched => "composite.invalidation-switch-ack"
  | .reused => "composite.invalidation-reuse-published"
  | .unmapPending => "composite.invalidation-unmap-pending"
  | .unmappedState => "composite.invalidation-unmap-ack"
  | .switchAwayPending => "composite.invalidation-switch-away-pending"
  | .switchedAway => "composite.invalidation-switch-away-ack"
  | .switchBackPending => "composite.invalidation-switch-back-pending"
  | .switchedBack => "composite.invalidation-switch-back-ack"

def invalidationEdgeVector
    (edge : CompositeDispatcher.CanonicalInvalidationEdge) : Vector :=
  let words := CompositeDispatcher.encodeInvalidationCommand edge.command
  composite (invalidationEdgeId edge.reply)
    (CompositeDispatcher.encodeInvalidationState edge.state)
    words.tag words.arg0 words.arg1 words.arg2 words.arg3

def invalidationVectors : List Vector :=
  CompositeDispatcher.invalidationCanonicalEdges.map invalidationEdgeVector

def invalidationNegativeVectors : List Vector :=
  [composite "composite.invalidation-malformed-effect"
      0x1d01 0x3501 1 1 7 1,
   composite "composite.invalidation-mismatched-state"
      0x1f01 0x3501 1 1 7 0,
   composite "composite.invalidation-stale-ticket-replay"
      0x2501 0x3d01 3 0 0 1]

/-- The composite scenario and hostile-encoding rows: oracle rows 292--313. -/
def compositeScenarioVectors : List Vector := [
  composite "composite.create-subject" 0x0001 0x0101 1 0 0 0,
  composite "composite.reject-unknown-syscall" 0x0101 0x0201 99 0 0 0,
  composite "composite.reject-malformed-map" 0x0201 0x0301 0 0 0 0,
  composite "composite.observe-scheduler" 0x0301 0x0401 0 0 0 0,
  composite "composite.terminate-subject" 0x0401 0x0501 1 0 0 0,
  composite "composite.enter-fatal-kernel-fault" 0x0501 0x0601 0 0 0 0,
  composite "composite.reject-post-fatal-schedule" 0x0601 0x0701 0 0 0 0,
  composite "composite.reject-stale-map-handle" 0x0101 0x0801 0x10000 7 1 0,
  composite "composite.reject-nonblocking-receive-handle" 0x0101 0x0901
    0x10000 0 0 0,
  composite "composite.reject-capability-copy" 0x0101 0x0a01 0 0 1 0,
  composite "composite.reject-blocking-cancel" 0x0101 0x0b01 0 0 0 0,
  composite "composite.reject-deferred-drain" 0x0101 0x0c01 0 0 0 0,
  composite "composite.stale-state-replay" 0x0001 0x0201 99 0 0 0,
  composite "composite.cross-trace-splice" 0x0201 0x0401 0 0 0 0,
  composite "composite.noncanonical-argument" 0x0101 0x0201 99 1 0 0,
  composite "composite.wrong-state-version" 0x0002 0x0101 1 0 0 0,
  composite "composite.reserved-state-bits" 0x10001 0x0101 1 0 0 0,
  composite "composite.wrong-command-version" 0x0001 0x0102 1 0 0 0,
  composite "composite.reserved-command-bits" 0x0001 0x10001 1 0 0 0,
  composite "composite.forged-context-argument" 0x0001 0x0101 1 1 0 0,
  composite "composite.maximum-words" 0xffffffffffffffff 0xffffffffffffffff
    0xffffffffffffffff 0xffffffffffffffff 0xffffffffffffffff 0xffffffffffffffff,
  composite "composite.unknown-command" 0x0101 0x0001 0 0 0 0]

theorem hosted_inFlight_revocation_vectors_refine :
    ∀ edge ∈ CompositeDispatcher.inFlightRevocationCanonicalEdges, edge.Refines :=
  CompositeDispatcher.inFlightRevocationCanonicalEdges_refine

/-- The in-flight revocation trace (oracle rows 398--408) publishes its
offer, both authority denials, the revocation, both post-revocation denials,
the switch to subject 2, the canceled-receipt denial, the replacement, the
canceled-handle denial, and the fresh send. -/
theorem composite_inFlight_revocation_trace_agrees :
    (inFlightRevocationVectors[0]).expected = 0x206101 ∧
    (inFlightRevocationVectors[1]).expected = 0x506101 ∧
    (inFlightRevocationVectors[2]).expected = 0x516101 ∧
    (inFlightRevocationVectors[3]).expected = 0x526201 ∧
    (inFlightRevocationVectors[4]).expected = 0x536201 ∧
    (inFlightRevocationVectors[5]).expected = 0x546201 ∧
    (inFlightRevocationVectors[6]).expected = 0x556301 ∧
    (inFlightRevocationVectors[7]).expected = 0x216301 ∧
    (inFlightRevocationVectors[8]).expected = 0x246401 ∧
    (inFlightRevocationVectors[9]).expected = 0x566401 ∧
    (inFlightRevocationVectors[10]).expected = 0x576501 := by
  native_decide

/-- The in-flight revocation negatives (oracle rows 409--411) reject the
pre-offer replay of the revocation words as a wrong sequence, the spliced
mixed-corpus revocation as an unknown command for this family, and the
premature receipt as a wrong sequence. -/
theorem composite_inFlight_revocation_negatives_reject :
    (inFlightRevocationNegativeVectors[0]).expected = 0xff06 ∧
    (inFlightRevocationNegativeVectors[1]).expected = 0xff04 ∧
    (inFlightRevocationNegativeVectors[2]).expected = 0xff06 := by
  native_decide

/-- Consequently every hosted mixed vector is backed by the non-circular
scalar-to-authoritative refinement theorem for its source edge. -/
theorem hosted_mixed_vectors_refine :
    ∀ edge ∈ CompositeDispatcher.mixedCanonicalEdges, edge.Refines :=
  CompositeDispatcher.mixedCanonicalEdges_refine

theorem hosted_invalidation_vectors_refine :
    ∀ edge ∈ CompositeDispatcher.invalidationCanonicalEdges, edge.Refines :=
  CompositeDispatcher.invalidationCanonicalEdges_refine

/-- The invalidation trace (oracle rows 337--355) and its malformed-effect,
mismatched-state, and stale-ticket negatives (rows 356--358). -/
theorem composite_invalidation_trace_agrees :
    (invalidationVectors[0]).expected = 0x321b01 ∧
    (invalidationVectors[1]).expected = 0x331c01 ∧
    (invalidationVectors[4]).expected = 0x361f01 ∧
    (invalidationVectors[8]).expected = 0x3a2301 ∧
    (invalidationVectors[10]).expected = 0x3c2501 ∧
    (invalidationVectors[12]).expected = 0x3e2701 ∧
    (invalidationVectors[13]).expected = 0x3f2801 ∧
    (invalidationVectors[14]).expected = 0x402901 ∧
    (invalidationVectors[15]).expected = 0x412a01 ∧
    (invalidationVectors[16]).expected = 0x422b01 ∧
    (invalidationVectors[17]).expected = 0x432c01 ∧
    (invalidationVectors[18]).expected = 0x442d01 ∧
    (invalidationNegativeVectors[0]).expected = 0xff05 ∧
    (invalidationNegativeVectors[1]).expected = 0xff06 ∧
    (invalidationNegativeVectors[2]).expected = 0xff05 := by
  native_decide

/-- The hosted scalar ABI rejects replaying release ticket 1 as the later
switch acknowledgement even though both require the same `.flush` effect. -/
theorem composite_invalidation_same_effect_replay_rejected :
    (invalidationNegativeVectors[2]).expected = 0xff05 := by
  native_decide

/-- The mixed trace (oracle rows 314--336). -/
theorem composite_mixed_trace_agrees :
    (mixedVectors[0]).expected = 0x200901 ∧
    (mixedVectors[1]).expected = 0x470901 ∧
    (mixedVectors[3]).expected = 0x482f01 ∧
    (mixedVectors[4]).expected = 0x492f01 ∧
    (mixedVectors[8]).expected = 0x250e01 ∧
    (mixedVectors[13]).expected = 0x2a1301 ∧
    (mixedVectors[15]).expected = 0x2c1501 ∧
    (mixedVectors[16]).expected = 0x2d1601 ∧
    (mixedVectors[18]).expected = 0x2f1801 ∧
    (mixedVectors[21]).expected = 0x452e01 ∧
    (mixedVectors[22]).expected = 0x462e01 := by
  native_decide

end LeanOS.Oracle
