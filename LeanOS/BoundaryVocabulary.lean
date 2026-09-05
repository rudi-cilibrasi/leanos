import LeanOS.CompositeDispatcher
import LeanOS.FrameBudgetScenario

/-!
# Boundary vocabulary

The single Lean-owned source of every scalar constant that the C side of the
composite-dispatcher boundary names: canonical state selectors, command
selectors, typed reply words, frame-budget flush authorizations, the closed
error words, and the fixed corpus-shape scalars.  Every word is evaluated from
the same encoder or canonical-edge table the dispatcher proofs use, so a
C-side constant can only differ from the model by failing to be generated.
The `leanos-oracle tokens` command emits this table and the build renders it into
the generated `composite-tokens.h` header; the checked-in
`include/leanos/composite-dispatcher.h` keeps only prose and includes that
header.  Names are the C spellings without the `LEANOS_` prefix; the words are
the model's.  The renderer, compiler, and consumers remain trusted integration
steps, exactly as for the generated corpus header.
-/
namespace LeanOS.BoundaryVocabulary

open LeanOS.CompositeDispatcher

/-- How a word is spelled as a C literal. -/
inductive Literal where
  | hex (width : Nat)
  | decimal
  | unsigned
  deriving DecidableEq, Repr

structure Token where
  kind : String
  name : String
  word : UInt64
  literal : Literal
  deriving Repr

private def hexString (value : Nat) (width : Nat) : String :=
  let digits := Nat.toDigits 16 value
  String.ofList (List.replicate (width - digits.length) '0' ++ digits)

def Token.render (token : Token) : String :=
  match token.literal with
  | .hex width => s!"UINT64_C(0x{hexString token.word.toNat width})"
  | .decimal => s!"UINT64_C({token.word})"
  | .unsigned => s!"{token.word}U"

/-- The exact returned handle published by an accepted attached receipt in
the mixed and boot-transfer traces; every other result publishes zero. -/
def deliveredHandle : UInt64 := 0x60003

/-- Words per corpus row: one state, one command tag, four arguments. -/
def inputWords : Nat := 6

private def state (name : String) (word : UInt64) : Token :=
  ⟨"STATE", s!"COMPOSITE_STATE_{name}", word, .hex 4⟩

private def command (name : String) (words : CommandWords) : Token :=
  ⟨"COMMAND", s!"COMPOSITE_COMMAND_{name}", words.tag, .hex 4⟩

private def budgetCommand (name : String) (tag : UInt64) : Token :=
  ⟨"COMMAND", s!"COMPOSITE_COMMAND_BUDGET_{name}", tag, .hex 4⟩

private def reply (name : String) (word : UInt64) : Token :=
  ⟨"REPLY", s!"COMPOSITE_REPLY_{name}", word, .hex 6⟩

private def error (name : String) (reason : DecodeError) : Token :=
  ⟨"ERROR", s!"COMPOSITE_ERROR_{name}", errorWord reason, .hex 4⟩

/-- The control word of the canonical boot-transfer edge driven by a
command, taken from the same edge table the refinement theorems quantify
over. -/
def bootTransferControl (command : CapabilityTransferBootCommandId) : UInt64 :=
  match capabilityTransferBootEdges.find? (fun edge => edge.command = command) with
  | some edge => edge.control
  | none => 0

def scalars : List Token := [
  ⟨"SCALAR", "COMPOSITE_ABI_VERSION", abiVersion, .decimal⟩,
  ⟨"SCALAR", "COMPOSITE_INPUT_WORDS", inputWords.toUInt64, .unsigned⟩,
  ⟨"SCALAR", "COMPOSITE_RESULT_WORDS", 2, .unsigned⟩,
  ⟨"SCALAR", "COMPOSITE_RESULT_CONTROL_WORD", 0, .unsigned⟩,
  ⟨"SCALAR", "COMPOSITE_RESULT_VALUE_WORD", 1, .unsigned⟩,
  ⟨"SCALAR", "COMPOSITE_NO_VALUE", 0, .decimal⟩,
  ⟨"SCALAR", "COMPOSITE_DELIVERED_HANDLE", deliveredHandle, .hex 5⟩]

def states : List Token := [
  state "INITIAL" (encodeStateId .initial),
  state "SUBJECT_CREATED" (encodeStateId .subjectCreated),
  state "UNKNOWN_SYSCALL_REJECTED" (encodeStateId .unknownSyscallRejected),
  state "MALFORMED_MAP_REJECTED" (encodeStateId .malformedMapRejected),
  state "SCHEDULER_OBSERVED" (encodeStateId .schedulerObserved),
  state "SUBJECT_TERMINATED" (encodeStateId .subjectTerminated),
  state "FATAL_ENTERED" (encodeStateId .fatalEntered),
  state "POST_FATAL_REJECTED" (encodeStateId .postFatalRejected),
  state "MIXED_INITIAL" (encodeMixedState .initial),
  state "TRANSFER_OFFERED" (encodeMixedState .transferOffered),
  state "TRANSFER_ACCEPTED" (encodeMixedState .transferAccepted),
  state "TRANSFER_REVOKED" (encodeMixedState .transferredCapabilityRevoked),
  state "STALE_HANDLE_REJECTED" (encodeMixedState .staleHandleRejected),
  state "FRESH_CAPABILITY_COPIED" (encodeMixedState .freshCapabilityCopied),
  state "SYSCALL_MAPPED" (encodeMixedState .syscallMapped),
  state "DIRECT_MAPPED" (encodeMixedState .directMapped),
  state "MIXED_UNKNOWN_SYSCALL_REJECTED" (encodeMixedState .unknownSyscallRejected),
  state "NONBLOCKING_SENT" (encodeMixedState .nonblockingSent),
  state "NONBLOCKING_RECEIVED" (encodeMixedState .nonblockingReceived),
  state "BLOCKING_RECEIVER_BLOCKED" (encodeMixedState .blockingReceiverBlocked),
  state "BLOCKING_RECEIVER_WOKEN" (encodeMixedState .blockingReceiverWoken),
  state "TIMER_SWITCHED" (encodeMixedState .timerSwitched),
  state "USER_FAULT_CLEANED" (encodeMixedState .userFaultCleaned),
  state "MIXED_FATAL_ENTERED" (encodeMixedState .fatalEntered),
  state "MIXED_POST_FATAL_REJECTED" (encodeMixedState .postFatalRejected),
  state "PAGE_UNMAPPED" (encodeMixedState .pageUnmapped),
  state "INVALIDATION_INITIAL" (encodeInvalidationState .initial),
  state "INVALIDATION_WRONG_OWNER_REJECTED" (encodeInvalidationState .wrongOwnerRejected),
  state "INVALIDATION_PROTECT_PENDING" (encodeInvalidationState .protectPending),
  state "INVALIDATION_PROTECT_MISMATCH_REJECTED"
    (encodeInvalidationState .protectMismatchRejected),
  state "INVALIDATION_PROTECTED" (encodeInvalidationState .protectedState),
  state "INVALIDATION_RELEASE_PENDING" (encodeInvalidationState .releasePending),
  state "INVALIDATION_RELEASE_MISMATCH_REJECTED"
    (encodeInvalidationState .releaseMismatchRejected),
  state "INVALIDATION_RELEASED" (encodeInvalidationState .released),
  state "INVALIDATION_STALE_RELEASE_REJECTED" (encodeInvalidationState .staleReleaseRejected),
  state "INVALIDATION_DESTROY_PENDING" (encodeInvalidationState .destroyPending),
  state "INVALIDATION_DESTROYED" (encodeInvalidationState .destroyed),
  state "INVALIDATION_SWITCH_PENDING" (encodeInvalidationState .switchPending),
  state "INVALIDATION_SWITCHED" (encodeInvalidationState .switched),
  state "INVALIDATION_REUSED" (encodeInvalidationState .reused),
  state "INVALIDATION_UNMAP_PENDING" (encodeInvalidationState .unmapPending),
  state "INVALIDATION_UNMAPPED" (encodeInvalidationState .unmappedState),
  state "INVALIDATION_SWITCH_AWAY_PENDING" (encodeInvalidationState .switchAwayPending),
  state "INVALIDATION_SWITCHED_AWAY" (encodeInvalidationState .switchedAway),
  state "INVALIDATION_SWITCH_BACK_PENDING" (encodeInvalidationState .switchBackPending),
  state "INVALIDATION_SWITCHED_BACK" (encodeInvalidationState .switchedBack),
  state "PAGE_PROTECTED" (encodeMixedState .pageProtected),
  state "DELEGATED_SEND_ACCEPTED" (encodeMixedState .delegatedSendAccepted),
  state "BUDGET_INITIAL" (FrameBudgetScenario.encodeState .initial),
  state "BUDGET_A_ALLOCATED" (FrameBudgetScenario.encodeState .aAllocated),
  state "BUDGET_A_EXHAUSTED" (FrameBudgetScenario.encodeState .aExhausted),
  state "BUDGET_B_SELECTED" (FrameBudgetScenario.encodeState .bSelected),
  state "BUDGET_B_ALLOCATED" (FrameBudgetScenario.encodeState .bAllocated),
  state "BUDGET_A_TERMINATED" (FrameBudgetScenario.encodeState .aTerminated),
  state "BUDGET_B_FRESH" (FrameBudgetScenario.encodeState .bFresh),
  state "BUDGET_STALE_DENIED" (FrameBudgetScenario.encodeState .staleDenied),
  state "BUDGET_COMPLETE" (FrameBudgetScenario.encodeState .complete),
  state "BUDGET_A_RELEASED" (FrameBudgetScenario.encodeState .aReleased),
  state "BUDGET_RELEASE_DENIED" (FrameBudgetScenario.encodeState .releaseDenied),
  state "BUDGET_RELEASE_COMPLETE" (FrameBudgetScenario.encodeState .releaseComplete),
  state "BOOT_TRANSFER_SUBJECT_ONE" (encodeCapabilityTransferBootState .subjectOne),
  state "BOOT_TRANSFER_OFFERED" (encodeCapabilityTransferBootState .offeredBySubjectOne),
  state "BOOT_TRANSFER_SUBJECT_TWO" (encodeCapabilityTransferBootState .subjectTwo),
  state "BOOT_TRANSFER_ACCEPTED" (encodeCapabilityTransferBootState .acceptedBySubjectTwo),
  state "BOOT_TRANSFER_SENT" (encodeCapabilityTransferBootState .delegatedSendBySubjectTwo),
  state "INFLIGHT_SUBJECT_ONE_ARMED" (encodeInFlightRevocationState .subjectOneArmed),
  state "INFLIGHT_CHILD_OFFERED" (encodeInFlightRevocationState .childOffered),
  state "INFLIGHT_LINEAGE_REVOKED" (encodeInFlightRevocationState .lineageRevoked),
  state "INFLIGHT_SUBJECT_TWO_RESTORED" (encodeInFlightRevocationState .subjectTwoRestored),
  state "INFLIGHT_DESTINATION_REPLACED" (encodeInFlightRevocationState .destinationReplaced),
  state "INFLIGHT_REPLACEMENT_USED" (encodeInFlightRevocationState .replacementUsed)]

def commands : List Token := [
  command "CREATE_SUBJECT_ONE" (encodeCommand .createSubjectOne),
  command "REJECT_UNKNOWN_SYSCALL" (encodeCommand .rejectUnknownSyscall),
  command "REJECT_MALFORMED_MAP" (encodeCommand .rejectMalformedMap),
  command "OBSERVE_SCHEDULER" (encodeCommand .observeScheduler),
  command "TERMINATE_SUBJECT_ONE" (encodeCommand .terminateSubjectOne),
  command "ENTER_FATAL_KERNEL_FAULT" (encodeCommand .enterFatalKernelFault),
  command "ATTEMPT_POST_FATAL_SCHEDULE" (encodeCommand .attemptPostFatalSchedule),
  command "REJECT_STALE_MAP_HANDLE" (encodeCommand .rejectStaleMapHandle),
  command "REJECT_NONBLOCKING_RECEIVE" (encodeCommand .rejectNonblockingReceiveHandle),
  command "REJECT_CAPABILITY_COPY" (encodeCommand .rejectCapabilityCopy),
  command "REJECT_BLOCKING_CANCEL" (encodeCommand .rejectBlockingCancel),
  command "REJECT_DEFERRED_DRAIN" (encodeCommand .rejectDeferredDrain),
  command "TRANSFER_OFFER" (encodeMixedCommand .offerTransfer),
  command "TRANSFER_ACCEPT" (encodeMixedCommand .acceptTransfer),
  command "REVOKE_TRANSFERRED" (encodeMixedCommand .revokeTransferredCapability),
  command "REJECT_STALE_REUSED_HANDLE" (encodeMixedCommand .rejectStaleReusedHandle),
  command "COPY_FRESH_CAPABILITY" (encodeMixedCommand .copyFreshCapability),
  command "ACCEPTED_SYSCALL_MAP" (encodeMixedCommand .acceptedSyscallMap),
  command "ACCEPTED_DIRECT_MAP" (encodeMixedCommand .acceptedDirectMap),
  command "REJECT_MIXED_UNKNOWN_SYSCALL" (encodeMixedCommand .rejectUnknownSyscall),
  command "NONBLOCKING_SEND" (encodeMixedCommand .nonblockingSend),
  command "NONBLOCKING_RECEIVE" (encodeMixedCommand .nonblockingReceive),
  command "BLOCKING_RECEIVE" (encodeMixedCommand .blockingReceive),
  command "BLOCKING_SEND" (encodeMixedCommand .blockingSend),
  command "TIMER_SWITCH" (encodeMixedCommand .timerSwitch),
  command "USER_FAULT_CLEANUP" (encodeMixedCommand .cleanupUserFault),
  command "ENTER_MIXED_FATAL" (encodeMixedCommand .enterFatalKernelFault),
  command "ATTEMPT_MIXED_POST_FATAL" (encodeMixedCommand .attemptPostFatalSchedule),
  command "ACCEPTED_SYSCALL_UNMAP" (encodeMixedCommand .acceptedSyscallUnmap),
  command "REJECT_UNMAPPED_PAGE_UNMAP" (encodeMixedCommand .rejectUnmappedPageUnmap),
  command "INVALIDATION_REJECT_WRONG_OWNER" (encodeInvalidationCommand .rejectWrongOwnerProtect),
  command "INVALIDATION_PREPARE_PROTECT" (encodeInvalidationCommand .prepareProtect),
  command "INVALIDATION_REJECT_PROTECT_MISMATCH"
    (encodeInvalidationCommand .rejectProtectEffectMismatch),
  command "INVALIDATION_ACK_PROTECT" (encodeInvalidationCommand .acknowledgeProtect),
  command "INVALIDATION_PREPARE_RELEASE" (encodeInvalidationCommand .prepareRelease),
  command "INVALIDATION_REJECT_RELEASE_MISMATCH"
    (encodeInvalidationCommand .rejectReleaseEffectMismatch),
  command "INVALIDATION_ACK_RELEASE" (encodeInvalidationCommand .acknowledgeRelease),
  command "INVALIDATION_REJECT_STALE_RELEASE" (encodeInvalidationCommand .rejectStaleRelease),
  command "INVALIDATION_PREPARE_DESTROY" (encodeInvalidationCommand .prepareDestroy),
  command "INVALIDATION_ACK_DESTROY" (encodeInvalidationCommand .acknowledgeDestroy),
  command "INVALIDATION_PREPARE_SWITCH" (encodeInvalidationCommand .prepareSwitch),
  command "INVALIDATION_ACK_SWITCH" (encodeInvalidationCommand .acknowledgeSwitch),
  command "INVALIDATION_PUBLISH_REUSE" (encodeInvalidationCommand .publishReuse),
  command "INVALIDATION_PREPARE_UNMAP" (encodeInvalidationCommand .prepareUnmap),
  command "INVALIDATION_ACK_UNMAP" (encodeInvalidationCommand .acknowledgeUnmap),
  command "INVALIDATION_PREPARE_SWITCH_AWAY" (encodeInvalidationCommand .prepareSwitchAway),
  command "INVALIDATION_ACK_SWITCH_AWAY" (encodeInvalidationCommand .acknowledgeSwitchAway),
  command "INVALIDATION_PREPARE_SWITCH_BACK" (encodeInvalidationCommand .prepareSwitchBack),
  command "INVALIDATION_ACK_SWITCH_BACK" (encodeInvalidationCommand .acknowledgeSwitchBack),
  command "ACCEPTED_PROTECT" (encodeMixedCommand .acceptedProtect),
  command "REJECT_PROTECT_AMPLIFICATION" (encodeMixedCommand .rejectProtectAmplification),
  command "REJECT_SEALED_HANDLE_BEFORE_RECEIPT"
    (encodeMixedCommand .rejectSealedHandleBeforeReceipt),
  command "USE_DELEGATED_SEND" (encodeMixedCommand .useDelegatedSend),
  command "REJECT_DELEGATED_RECEIVE" (encodeMixedCommand .rejectDelegatedReceive),
  command "BOOT_TRANSFER_SWITCH_SUBJECT_TWO"
    (encodeCapabilityTransferBootCommand .switchToSubjectTwo),
  command "INFLIGHT_REJECT_REVOCATION_WITHOUT_AUTHORITY"
    (encodeInFlightRevocationCommand .rejectRevocationWithoutAuthority),
  command "INFLIGHT_REJECT_WRONG_LINEAGE_ROOT"
    (encodeInFlightRevocationCommand .rejectWrongLineageRoot),
  command "INFLIGHT_REVOKE_LINEAGE" (encodeInFlightRevocationCommand .revokeLineage),
  command "INFLIGHT_REJECT_REPEATED_REVOCATION"
    (encodeInFlightRevocationCommand .rejectRepeatedRevocation),
  command "INFLIGHT_REJECT_OFFER_AFTER_REVOCATION"
    (encodeInFlightRevocationCommand .rejectOfferAfterRevocation),
  command "INFLIGHT_SWITCH_TO_SUBJECT_TWO" (encodeInFlightRevocationCommand .switchToSubjectTwo),
  command "INFLIGHT_REJECT_CANCELED_HANDLE_REPLAY"
    (encodeInFlightRevocationCommand .rejectCanceledHandleReplay),
  command "INFLIGHT_USE_REPLACEMENT_HANDLE"
    (encodeInFlightRevocationCommand .useReplacementHandle),
  budgetCommand "ALLOCATE_A" (FrameBudgetScenario.encodeCommand .allocateA),
  budgetCommand "RETRY_A" (FrameBudgetScenario.encodeCommand .retryA),
  budgetCommand "SELECT_B" (FrameBudgetScenario.encodeCommand .selectB),
  budgetCommand "ALLOCATE_B" (FrameBudgetScenario.encodeCommand .allocateB),
  budgetCommand "TERMINATE_A" (FrameBudgetScenario.encodeCommand .terminateA),
  budgetCommand "PUBLISH_FRESH_B" (FrameBudgetScenario.encodeCommand .publishFreshB),
  budgetCommand "DENY_STALE_A" (FrameBudgetScenario.encodeCommand .denyStaleA),
  budgetCommand "COMPLETE" (FrameBudgetScenario.encodeCommand .complete),
  budgetCommand "RELEASE_A" (FrameBudgetScenario.encodeCommand .releaseA),
  budgetCommand "REPEAT_RELEASE_A" (FrameBudgetScenario.encodeCommand .repeatReleaseA),
  budgetCommand "COMPLETE_RELEASED" (FrameBudgetScenario.encodeCommand .completeReleased)]

def replies : List Token := [
  reply "PAGE_UNMAPPED" (encodeMixedReply .pageUnmapped),
  reply "UNMAPPED_PAGE_REJECTED" (encodeMixedReply .unmappedPageRejected),
  reply "PAGE_PROTECTED" (encodeMixedReply .pageProtected),
  reply "PROTECT_AMPLIFICATION_REJECTED" (encodeMixedReply .protectAmplificationRejected),
  reply "TRANSFER_OFFERED" (encodeMixedReply .transferOffered),
  reply "TRANSFER_ACCEPTED" (encodeMixedReply .transferAccepted),
  reply "SEALED_HANDLE_REJECTED" (encodeMixedReply .sealedHandleRejected),
  reply "DELEGATED_SEND_ACCEPTED" (encodeMixedReply .delegatedSendAccepted),
  reply "DELEGATED_RECEIVE_REJECTED" (encodeMixedReply .delegatedReceiveRejected),
  reply "TRANSFER_REVOKED" (encodeMixedReply .transferredCapabilityRevoked),
  reply "STALE_HANDLE_REJECTED" (encodeMixedReply .staleHandleRejected),
  reply "FRESH_CAPABILITY_COPIED" (encodeMixedReply .freshCapabilityCopied),
  reply "SYSCALL_MAPPED" (encodeMixedReply .syscallMapped),
  reply "DIRECT_MAPPED" (encodeMixedReply .directMapped),
  reply "MIXED_UNKNOWN_SYSCALL_REJECTED" (encodeMixedReply .unknownSyscallRejected),
  reply "NONBLOCKING_SENT" (encodeMixedReply .nonblockingSent),
  reply "NONBLOCKING_RECEIVED" (encodeMixedReply .nonblockingReceived),
  reply "BLOCKING_RECEIVER_BLOCKED" (encodeMixedReply .blockingReceiverBlocked),
  reply "BLOCKING_RECEIVER_WOKEN" (encodeMixedReply .blockingReceiverWoken),
  reply "TIMER_SWITCHED" (encodeMixedReply .timerSwitched),
  reply "USER_FAULT_CLEANED" (encodeMixedReply .userFaultCleaned),
  reply "MIXED_FATAL_ENTERED" (encodeMixedReply .fatalEntered),
  reply "MIXED_POST_FATAL_REJECTED" (encodeMixedReply .postFatalRejected),
  reply "BOOT_TRANSFER_OFFERED" (bootTransferControl .offer),
  reply "BOOT_TRANSFER_SWITCHED" (bootTransferControl .switchToSubjectTwo),
  reply "BOOT_TRANSFER_SEALED_HANDLE_REJECTED" (bootTransferControl .rejectSealedHandle),
  reply "BOOT_TRANSFER_ACCEPTED" (bootTransferControl .accept),
  reply "BOOT_TRANSFER_DELEGATED_SEND" (bootTransferControl .delegatedSend),
  reply "BOOT_TRANSFER_DELEGATED_RECEIVE_REJECTED" (bootTransferControl .rejectDelegatedReceive),
  reply "INFLIGHT_CHILD_OFFERED" (encodeInFlightRevocationReply .childOffered),
  reply "INFLIGHT_REVOCATION_WITHOUT_AUTHORITY_REJECTED"
    (encodeInFlightRevocationReply .revocationWithoutAuthorityRejected),
  reply "INFLIGHT_WRONG_LINEAGE_ROOT_REJECTED"
    (encodeInFlightRevocationReply .wrongLineageRootRejected),
  reply "INFLIGHT_LINEAGE_REVOKED" (encodeInFlightRevocationReply .lineageRevoked),
  reply "INFLIGHT_REPEATED_REVOCATION_REJECTED"
    (encodeInFlightRevocationReply .repeatedRevocationRejected),
  reply "INFLIGHT_OFFER_AFTER_REVOCATION_REJECTED"
    (encodeInFlightRevocationReply .offerAfterRevocationRejected),
  reply "INFLIGHT_SUBJECT_TWO_RESTORED" (encodeInFlightRevocationReply .subjectTwoRestored),
  reply "INFLIGHT_CANCELED_RECEIPT_REJECTED"
    (encodeInFlightRevocationReply .canceledReceiptRejected),
  reply "INFLIGHT_DESTINATION_REPLACED" (encodeInFlightRevocationReply .destinationReplaced),
  reply "INFLIGHT_CANCELED_HANDLE_REPLAY_REJECTED"
    (encodeInFlightRevocationReply .canceledHandleReplayRejected),
  reply "INFLIGHT_REPLACEMENT_USED" (encodeInFlightRevocationReply .replacementUsed),
  reply "INVALIDATION_WRONG_OWNER_REJECTED" (encodeInvalidationReply .wrongOwnerRejected),
  reply "INVALIDATION_PROTECT_PENDING" (encodeInvalidationReply .protectPending),
  reply "INVALIDATION_PROTECT_MISMATCH_REJECTED"
    (encodeInvalidationReply .protectMismatchRejected),
  reply "INVALIDATION_PROTECTED" (encodeInvalidationReply .protectedState),
  reply "INVALIDATION_RELEASE_PENDING" (encodeInvalidationReply .releasePending),
  reply "INVALIDATION_RELEASE_MISMATCH_REJECTED"
    (encodeInvalidationReply .releaseMismatchRejected),
  reply "INVALIDATION_RELEASED" (encodeInvalidationReply .released),
  reply "INVALIDATION_STALE_RELEASE_REJECTED" (encodeInvalidationReply .staleReleaseRejected),
  reply "INVALIDATION_DESTROY_PENDING" (encodeInvalidationReply .destroyPending),
  reply "INVALIDATION_DESTROYED" (encodeInvalidationReply .destroyed),
  reply "INVALIDATION_SWITCH_PENDING" (encodeInvalidationReply .switchPending),
  reply "INVALIDATION_SWITCHED" (encodeInvalidationReply .switched),
  reply "INVALIDATION_REUSED" (encodeInvalidationReply .reused),
  reply "INVALIDATION_UNMAP_PENDING" (encodeInvalidationReply .unmapPending),
  reply "INVALIDATION_UNMAPPED" (encodeInvalidationReply .unmappedState),
  reply "INVALIDATION_SWITCH_AWAY_PENDING" (encodeInvalidationReply .switchAwayPending),
  reply "INVALIDATION_SWITCHED_AWAY" (encodeInvalidationReply .switchedAway),
  reply "INVALIDATION_SWITCH_BACK_PENDING" (encodeInvalidationReply .switchBackPending),
  reply "INVALIDATION_SWITCHED_BACK" (encodeInvalidationReply .switchedBack)]

def flushTokens : List Token := [
  ⟨"TOKEN", "FRAME_BUDGET_TERMINATE_FLUSH_TOKEN", FrameBudgetScenario.terminateFlushToken, .hex 10⟩,
  ⟨"TOKEN", "FRAME_BUDGET_RELEASE_FLUSH_TOKEN", FrameBudgetScenario.releaseFlushToken, .hex 10⟩]

def errors : List Token := [
  error "WRONG_VERSION" .wrongVersion,
  error "RESERVED_BITS" .reservedBits,
  error "UNKNOWN_STATE" .unknownState,
  error "UNKNOWN_COMMAND" .unknownCommand,
  error "NONCANONICAL_ARGUMENTS" .noncanonicalArguments,
  error "INVALID_SEQUENCE" .invalidSequence]

def stateWords : List UInt64 := states.map Token.word
def commandWords : List UInt64 := commands.map Token.word
def replyWords : List UInt64 := replies.map Token.word
def errorWords : List UInt64 := errors.map Token.word

/-- Distinct canonical state selectors. -/
def stateCount : Nat := stateWords.eraseDups.length
/-- Distinct command selectors; several families share a selector and let
the state token choose the meaning. -/
def commandSelectorCount : Nat := commandWords.eraseDups.length
def counts : List Token := [
  ⟨"COUNT", "COMPOSITE_STATE_COUNT", stateCount.toUInt64, .unsigned⟩,
  ⟨"COUNT", "COMPOSITE_COMMAND_COUNT", commandSelectorCount.toUInt64, .unsigned⟩]

/-- Every token, in the order the generated header lists them. -/
def tokens : List Token :=
  scalars ++ counts ++ states ++ commands ++ replies ++ flushTokens ++ errors

theorem state_words_nodup : stateWords.Nodup := by decide
theorem reply_words_nodup : replyWords.Nodup := by decide
theorem error_words_nodup : errorWords.Nodup := by decide

theorem state_count_is_state_tokens : stateCount = states.length := by decide

theorem stateId_covered (s : StateId) : encodeStateId s ∈ stateWords := by
  cases s <;> decide
theorem mixedStateId_covered (s : MixedStateId) : encodeMixedState s ∈ stateWords := by
  cases s <;> decide
theorem invalidationStateId_covered (s : InvalidationStateId) :
    encodeInvalidationState s ∈ stateWords := by
  cases s <;> decide
theorem budgetStateId_covered (s : FrameBudgetScenario.StateId) :
    FrameBudgetScenario.encodeState s ∈ stateWords := by
  cases s <;> decide
theorem capabilityTransferBootStateId_covered (s : CapabilityTransferBootStateId) :
    encodeCapabilityTransferBootState s ∈ stateWords := by
  cases s <;> decide
theorem inFlightRevocationStateId_covered (s : InFlightRevocationStateId) :
    encodeInFlightRevocationState s ∈ stateWords := by
  cases s <;> decide

theorem commandId_covered (c : CommandId) : (encodeCommand c).tag ∈ commandWords := by
  cases c <;> decide
theorem mixedCommandId_covered (c : MixedCommandId) :
    (encodeMixedCommand c).tag ∈ commandWords := by
  cases c <;> decide
theorem invalidationCommandId_covered (c : InvalidationCommandId) :
    (encodeInvalidationCommand c).tag ∈ commandWords := by
  cases c <;> decide
theorem capabilityTransferBootCommandId_covered (c : CapabilityTransferBootCommandId) :
    (encodeCapabilityTransferBootCommand c).tag ∈ commandWords := by
  cases c <;> decide
theorem inFlightRevocationCommandId_covered (c : InFlightRevocationCommandId) :
    (encodeInFlightRevocationCommand c).tag ∈ commandWords := by
  cases c <;> decide
theorem budgetCommand_covered (c : FrameBudgetScenario.Command) :
    FrameBudgetScenario.encodeCommand c ∈ commandWords := by
  cases c <;> decide

theorem mixedReplyId_covered (r : MixedReplyId) : encodeMixedReply r ∈ replyWords := by
  cases r <;> decide
theorem invalidationReplyId_covered (r : InvalidationReplyId) :
    encodeInvalidationReply r ∈ replyWords := by
  cases r <;> decide
theorem inFlightRevocationReplyId_covered (r : InFlightRevocationReplyId) :
    encodeInFlightRevocationReply r ∈ replyWords := by
  cases r <;> decide
theorem capabilityTransferBootEdges_covered :
    ∀ edge ∈ capabilityTransferBootEdges, edge.control ∈ replyWords := by
  decide

theorem decodeError_covered (e : DecodeError) : errorWord e ∈ errorWords := by
  cases e <;> decide

end LeanOS.BoundaryVocabulary
