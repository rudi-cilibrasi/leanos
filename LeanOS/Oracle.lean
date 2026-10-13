import LeanOS.BootInterruptPhase
import LeanOS.KernelTransition
import LeanOS.Syscall
import LeanOS.IPCSyscall
import LeanOS.Preemption
import LeanOS.BootMemoryMapStreamAuthority
import LeanOS.Interrupt
import LeanOS.InterruptEntry
import LeanOS.BlockingIPC
import LeanOS.CapabilityReuse
import LeanOS.ExtendedState
import LeanOS.PrivilegeEntryControl
import LeanOS.FaultDispatch
import LeanOS.DirectPortIO
import LeanOS.StaleTranslation
import LeanOS.CompositeDispatcher
import LeanOS.SpawnBoundary
import LeanOS.SpawnSyscall
import LeanOS.ChildLoader
import LeanOS.IOTLB
import LeanOS.NotifyReply
import LeanOS.UserCopyPolicy
import LeanOS.ConsoleServer
import LeanOS.EndpointDirectory
import LeanOS.FaultHandler
import LeanOS.KeyboardEcho
import LeanOS.TimerServer
import LeanOS.FrameServer
import LeanOS.BoundaryVocabulary
import LeanOS.SerialProtocol
import LeanOS.Oracle.Scalar
import LeanOS.Oracle.Interrupt
import LeanOS.Oracle.Composite
import LeanOS.Oracle.FrameBudget
import LeanOS.Oracle.IOTLB
import LeanOS.Oracle.Services
import LeanOS.Oracle.Spawn

/-!
# Bounded scalar boundary oracle

This is the canonical, version-two corpus for the currently exported
fixed-width adapters.  Expected words are evaluated from the adapter
definitions, not copied into a C harness.  The corpus is deliberately finite;
it is differential integration evidence, not a refinement theorem.

The corpus checks live with their adapter families in the
`LeanOS.Oracle.*` modules (issue #558) so the families elaborate in parallel;
this module fixes their stable order, the row layout, and the emitter.
-/
namespace LeanOS.Oracle

open LeanOS
set_option maxRecDepth 4096

structure AdapterSpec where
  name : String
  id : Nat
  cSymbol : String
  arity : Nat

private def adapter (name : String) (id : Nat) (cSymbol : String) (arity : Nat) : AdapterSpec :=
  { name, id, cSymbol, arity }

/-- The Lean-owned numeric and C-dispatch vocabulary consumed by both hosted
and boot replay. Unknown names are intentionally absent so generation fails
closed instead of silently selecting another adapter. -/
def adapters : List AdapterSpec := [
  adapter "KernelTransition" 0 "leanos_boot_transition" 2,
  adapter "Syscall.scalar" 1 "leanos_syscall_demo" 4,
  adapter "IPCSyscall.scalar" 2 "leanos_ipc_demo" 4,
  adapter "Preemption.scalar" 3 "leanos_preemption_demo" 4,
  adapter "Preemption.resumable" 4 "leanos_resumable_preemption_demo" 5,
  adapter "BootAllocation.scalar" 5 "leanos_boot_consume_exact_projection" 6,
  adapter "Interrupt.userReturn" 6 "leanos_user_return_demo" 5,
  adapter "BlockingIPC.scalar" 7 "leanos_blocking_ipc_demo" 5,
  adapter "CapabilityReuse.scalar" 8 "leanos_capability_reuse_demo" 5,
  adapter "Interrupt.entry" 9 "leanos_entry_demo" 5,
  adapter "ExtendedState.denialDispatch" 10 "leanos_extended_state_denial_demo" 6,
  adapter "PrivilegeEntryControl.scalar" 11 "leanos_privilege_entry_control_demo" 6,
  adapter "FaultDispatch.scalar" 12 "leanos_fault_dispatch_demo" 6,
  adapter "DirectPortIO.scalar" 13 "leanos_direct_port_io_demo" 6,
  adapter "Interrupt.nmi" 14 "leanos_nmi_demo" 5,
  adapter "Interrupt.bootPhase" 15 "leanos_boot_phase_demo" 5,
  adapter "StaleTranslation.scalar" 16 "leanos_stale_translation_demo" 6,
  adapter "Interrupt.pageFault" 17 "leanos_page_fault_demo" 5,
  adapter "CompositeDispatcher.stateful" 18 "leanos_composite_dispatch" 6,
  adapter "IOTLB.scalar" 19 "leanos_iotlb_publication_demo" 6,
  adapter "BlockingIPC.event" 20 "leanos_blocking_ipc_event" 3,
  adapter "NotifyReply.event" 21 "leanos_notify_reply_event" 4,
  adapter "UserCopy.policy" 22 "leanos_user_copy_policy" 6,
  adapter "ConsoleServer.authorize" 23 "leanos_console_authorize" 2,
  adapter "EndpointDirectory.resolve" 24 "leanos_directory_resolve" 2,
  adapter "FaultHandler.route" 25 "leanos_fault_handler_route" 4,
  adapter "KeyboardEcho.deviceAuthorize" 26 "leanos_device_authorize" 2,
  adapter "TimerServer.decide" 27 "leanos_timer_server_decide" 3,
  adapter "FrameServer.check" 28 "leanos_frame_server_check" 6,
  adapter "FrameServer.view" 29 "leanos_frame_server_view" 6,
  adapter "SpawnSyscall.step" 30 "leanos_spawn_syscall" 6,
  adapter "SpawnSyscall.value" 31 "leanos_spawn_syscall_value" 6,
  adapter "ChildLoader.source" 32 "leanos_loader_source" 5,
  adapter "ChildLoader.decide" 33 "leanos_loader_decide" 6]

/-- The corpus blocks in their stable order.  Each family module owns its
blocks; a new adapter appends a block here and nothing else moves. -/
def blocks : List (List Vector) :=
  [scalarVectors, interruptVectors, compositeScenarioVectors, mixedVectors,
    invalidationVectors, invalidationNegativeVectors, budgetVectors,
    iotlbPublicationVectors, capabilityTransferBootVectors, inFlightRevocationVectors,
    inFlightRevocationNegativeVectors, blockingIpcEventVectors,
    bootTransitionClassVectors, notifyReplyVectors, userCopyPolicyVectors,
    consoleAuthorizeVectors, directoryResolveVectors, faultHandlerVectors,
    deviceAuthorizeVectors, timerServerVectors, frameServerVectors,
    frameServerViewVectors, spawnEdgeVectors, spawnNegativeVectors,
    spawnSyscallVectors, loaderVectors]

/-- Stable ordering is part of schema version one. -/
def vectors : List Vector := blocks.flatten

theorem corpus_shape : vectors.length = 692 := by decide

/-- Dropping the first `k` blocks' rows from a concatenation leaves the
concatenation of the remaining blocks. -/
theorem drop_lengths_flatten {α : Type} :
    ∀ (bs : List (List α)) (k : Nat),
      bs.flatten.drop ((bs.take k).map List.length).sum = (bs.drop k).flatten
  | [], _ => by simp
  | _ :: _, 0 => by simp
  | b :: bs, k + 1 => by
      simp only [List.take_succ_cons, List.map_cons, List.sum_cons, List.flatten_cons,
        List.drop_succ_cons, ← List.drop_drop, List.drop_left]
      exact drop_lengths_flatten bs k

/-- The oracle rows from the start of block `k` are that block followed by the
blocks after it, so each layout theorem below checks one block's offset and
identity instead of re-reducing the whole corpus. -/
theorem rows_at {k n : Nat} {l : List Vector} {rest : List (List Vector)}
    (offset : ((blocks.take k).map List.length).sum = n)
    (block : blocks.drop k = l :: rest) :
    vectors.drop n = l ++ rest.flatten := by
  rw [← offset, vectors, drop_lengths_flatten, block, List.flatten_cons]

/-- Oracle indices 419--434 are the boot-transition classification grid. -/
theorem hosted_boot_transition_class_vectors_exact :
    (vectors.drop 419).take bootTransitionClassVectors.length =
      bootTransitionClassVectors := by
  rw [rows_at (k := 12) (n := 419) rfl rfl, List.take_left]

/-- Oracle indices 435--447 are the notification/reply corpus (#471). -/
theorem hosted_notify_reply_vectors_exact :
    (vectors.drop 435).take notifyReplyVectors.length = notifyReplyVectors := by
  rw [rows_at (k := 13) (n := 435) rfl rfl, List.take_left]

/-- Oracle indices 448--461 are the user-copy range checks (#478). -/
theorem hosted_user_copy_policy_vectors_exact :
    (vectors.drop 448).take userCopyPolicyVectors.length = userCopyPolicyVectors := by
  rw [rows_at (k := 14) (n := 448) rfl rfl, List.take_left]

/-- Oracle indices 462--480 are the console-server authority corpus (#472). -/
theorem hosted_console_authorize_vectors_exact :
    (vectors.drop 462).take consoleAuthorizeVectors.length = consoleAuthorizeVectors := by
  rw [rows_at (k := 15) (n := 462) rfl rfl, List.take_left]

/-- Oracle indices 481--500 are the endpoint-directory rights corpus (#485). -/
theorem hosted_directory_resolve_vectors_exact :
    (vectors.drop 481).take directoryResolveVectors.length = directoryResolveVectors := by
  rw [rows_at (k := 16) (n := 481) rfl rfl, List.take_left]

/-- Oracle indices 501--511 are the fault-handler route corpus (#488). -/
theorem hosted_fault_handler_vectors_exact :
    (vectors.drop 501).take faultHandlerVectors.length = faultHandlerVectors := by
  rw [rows_at (k := 17) (n := 501) rfl rfl, List.take_left]

/-- Oracle indices 512--523 are the keyboard-echo device-authority corpus
(#493). -/
theorem hosted_device_authorize_vectors_exact :
    (vectors.drop 512).take deviceAuthorizeVectors.length = deviceAuthorizeVectors := by
  rw [rows_at (k := 18) (n := 512) rfl rfl, List.take_left]

/-- Oracle indices 524--539 are the timer-server decision corpus (#487). -/
theorem hosted_timer_server_vectors_exact :
    (vectors.drop 524).take timerServerVectors.length = timerServerVectors := by
  rw [rows_at (k := 19) (n := 524) rfl rfl, List.take_left]

/-- Oracle indices 540--555 are the frame-server decision-check corpus (#486). -/
theorem hosted_frame_server_vectors_exact :
    (vectors.drop 540).take frameServerVectors.length = frameServerVectors := by
  rw [rows_at (k := 20) (n := 540) rfl rfl, List.take_left]

/-- Oracle indices 556--563 are the frame-server view corpus (#486). -/
theorem hosted_frame_server_view_vectors_exact :
    (vectors.drop 556).take frameServerViewVectors.length = frameServerViewVectors := by
  rw [rows_at (k := 21) (n := 556) rfl rfl, List.take_left]

/-- Oracle indices 564--617 are the spawn family's edges, in the order of
`SpawnBoundary.edges`, and 618--631 its hostile encodings (ADR 0010 gate
item 5). -/
theorem hosted_spawn_vectors_exact :
    (vectors.drop 564).take (spawnEdgeVectors.length + spawnNegativeVectors.length) =
      spawnEdgeVectors ++ spawnNegativeVectors := by
  rw [rows_at (k := 22) (n := 564) rfl rfl, List.flatten_cons, ← List.append_assoc]
  exact List.take_left' List.length_append

/-- Oracle indices 632--667 are the ring-3 spawn syscall's corpus (#489). -/
theorem hosted_spawn_syscall_vectors_exact :
    (vectors.drop 632).take spawnSyscallVectors.length = spawnSyscallVectors := by
  rw [rows_at (k := 24) (n := 632) rfl rfl, List.take_left]

/-- Oracle indices 668--691 are the run-time loader's corpus (#492). -/
theorem hosted_loader_vectors_exact :
    vectors.drop 668 = loaderVectors := by
  rw [rows_at (k := 25) (n := 668) rfl rfl]
  simp only [List.flatten_nil, List.append_nil]

/-- Oracle indices 314--336 are definitionally the complete canonical mixed
edge corpus, rather than a second hand-maintained scalar table. -/
theorem hosted_mixed_vectors_exact :
    (vectors.drop 314).take 23 =
      CompositeDispatcher.mixedCanonicalEdges.map mixedEdgeVector := by
  rw [rows_at (k := 3) (n := 314) rfl rfl]
  exact List.take_left' rfl

theorem hosted_budget_vectors_exact :
    (vectors.drop 359).take budgetVectors.length = budgetVectors := by
  rw [rows_at (k := 6) (n := 359) rfl rfl, List.take_left]

theorem hosted_iotlb_publication_vectors_exact :
    (vectors.drop 383).take iotlbPublicationVectors.length =
      iotlbPublicationVectors := by
  rw [rows_at (k := 7) (n := 383) rfl rfl, List.take_left]

theorem hosted_capability_transfer_boot_vectors_exact :
    (vectors.drop 392).take capabilityTransferBootVectors.length =
      capabilityTransferBootVectors := by
  rw [rows_at (k := 8) (n := 392) rfl rfl, List.take_left]

/-- Oracle indices 398--408 are definitionally the in-flight revocation
corpus: offer, two revocation-authority denials, accepted lineage revocation,
repeated-revocation and stale-offer denials, the switch to subject 2, the
canceled receipt denial, same-slot replacement, canceled-handle denial, and
the fresh-handle send. -/
theorem hosted_inFlight_revocation_vectors_exact :
    vectors.drop 398 = inFlightRevocationVectors ++ inFlightRevocationNegativeVectors ++
      blockingIpcEventVectors ++ bootTransitionClassVectors ++ notifyReplyVectors ++
        userCopyPolicyVectors ++ consoleAuthorizeVectors ++ directoryResolveVectors ++
        faultHandlerVectors ++ deviceAuthorizeVectors ++ timerServerVectors ++
          frameServerVectors ++ frameServerViewVectors ++ spawnEdgeVectors ++
            spawnNegativeVectors ++ spawnSyscallVectors ++ loaderVectors := by
  rw [rows_at (k := 9) (n := 398) rfl rfl]
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil, List.append_assoc]
/-- Oracle rows 0--85 are the scheduler, syscall, and IPC family's rows. -/
theorem hosted_scalar_vectors_exact :
    vectors.take scalarVectors.length = scalarVectors := by
  show (vectors.drop 0).take scalarVectors.length = scalarVectors
  rw [rows_at (k := 0) (n := 0) rfl rfl, List.take_left]

/-- Oracle rows 86--291 are the interrupt, entry, and fault family's rows. -/
theorem hosted_interrupt_vectors_exact :
    (vectors.drop 86).take interruptVectors.length = interruptVectors := by
  rw [rows_at (k := 1) (n := 86) rfl rfl, List.take_left]

/-- Oracle rows 292--313 are the composite scenario and hostile-encoding rows. -/
theorem hosted_composite_scenario_vectors_exact :
    (vectors.drop 292).take compositeScenarioVectors.length =
      compositeScenarioVectors := by
  rw [rows_at (k := 2) (n := 292) rfl rfl, List.take_left]

/-- The canceled child never reaches result word one: every in-flight
revocation record publishes the no-value word, including the denied receipt. -/
theorem composite_inFlight_revocation_values_zero :
    ((vectors.drop 398).take 166).all (fun vector => vector.expectedValue = 0) = true := by
  native_decide

/-- Oracle indices 337--355 are the exact stateful invalidation publication
corpus, including independent accepted-unmap and switch-away/back branches;
356--358 are malformed-effect, mismatched-state, and stale-ticket negatives. -/
theorem hosted_invalidation_vectors_exact :
    (vectors.drop 337).take 22 =
      CompositeDispatcher.invalidationCanonicalEdges.map invalidationEdgeVector ++
        invalidationNegativeVectors := by
  rw [rows_at (k := 4) (n := 337) rfl rfl, List.flatten_cons, ← List.append_assoc]
  exact List.take_left' List.length_append

/-- Before the spawn family, only the accepted hosted-mixed receipt and the
independently modeled machine A-to-B receipt publish a value word. All
data-only successes, scheduling edges, and rejections publish zero. In the
spawn family exactly the ten accepted edges whose hosted-oracle value is
nonzero publish one: two kernel grants (the generation), four spawns (the
control word), two frame grants and two terminations (the frames). -/
theorem composite_result_values_exact :
    (vectors[316]).id = "composite.mixed-transfer-accept" ∧
    (vectors[316]).expectedValue = 0x60003 ∧
    (vectors[395]).id = "composite.boot-transfer-subject-two-accept" ∧
    (vectors[395]).expectedValue = 0x60003 ∧
    ((vectors.take 564).filter (fun vector => vector.expectedValue ≠ 0)).length = 2 ∧
    ((vectors.drop 564).filter (fun vector => vector.expectedValue ≠ 0)).length = 10 := by
  native_decide

private def interruptEntryAdapterAgrees (vector : Vector) : Bool :=
  match vector.adapter, vector.words with
  | "Interrupt.entry", [descriptor, frame, stack, context, cleanup] =>
      InterruptEntry.entryDemo descriptor frame stack context cleanup = vector.expected
  | _, _ => true

theorem interrupt_entry_adapter_agrees_with_model :
    vectors.all interruptEntryAdapterAgrees = true := by
  native_decide

private def faultDispatchAdapterAgrees (vector : Vector) : Bool :=
  match vector.adapter, vector.words with
  | "FaultDispatch.scalar", [rawVector, origin, current, active, ready, context] =>
      FaultDispatch.faultDispatchDemo rawVector origin current active ready context =
        vector.expected
  | _, _ => true

/-- Every bounded fault/dispatch vector couples the allocation-free exported
adapter to an expectation evaluated by the authoritative normalized-entry,
lifecycle-cleanup, scheduler-selection, context-bank, and TLB transition. -/
theorem fault_dispatch_adapter_agrees_with_model :
    vectors.all faultDispatchAdapterAgrees = true := by
  native_decide

private def userReturnAdapterAgrees (vector : Vector) : Bool :=
  match vector.adapter, vector.words with
  | "Interrupt.userReturn", [mode, rip, rsp, selectors, flags] =>
      Interrupt.userReturnDemo mode rip rsp selectors flags = vector.expected
  | _, _ => true

/-- Every checked user-return vector couples the freestanding exported adapter
to an expectation evaluated through the authoritative validator. -/
theorem user_return_adapter_agrees_with_model :
    vectors.all userReturnAdapterAgrees = true := by
  native_decide

private def wordsText : List UInt64 → String
  | [] => ""
  | [word] => toString word
  | word :: rest => toString word ++ "," ++ wordsText rest

def line (index : Nat) (vector : Vector) : String :=
  s!"{index}\t{vector.id}\t{vector.adapter}\t{wordsText vector.words}\t{vector.expected}\t{vector.expectedValue}"

def emit : IO Unit := do
  let revision := (← IO.getEnv "LEANOS_SOURCE_REVISION").getD "unknown"
  IO.println "leanos-oracle\t2"
  IO.println s!"source-revision\t{revision}"
  for entry in adapters do
    IO.println s!"adapter-id\t{entry.name}\t{entry.id}\t{entry.cSymbol}\t{entry.arity}"
  for entry in vectors.zipIdx do
    IO.println (line entry.2 entry.1)

/-- The boundary vocabulary rows: one `token` line per generated C constant,
rendered from the same encoders the corpus above is evaluated with. -/
def emitTokens : IO Unit := do
  let revision := (← IO.getEnv "LEANOS_SOURCE_REVISION").getD "unknown"
  IO.println "leanos-vocabulary\t1"
  IO.println s!"source-revision\t{revision}"
  for token in BoundaryVocabulary.tokens do
    IO.println s!"token\t{token.kind}\t{token.name}\t{token.word}\t{token.render}"

/-- The serial protocol rows: one `record` line per versioned record identity
with its C/shell symbol and the exact guest line prefix. -/
def emitSerial : IO Unit := do
  let revision := (← IO.getEnv "LEANOS_SOURCE_REVISION").getD "unknown"
  IO.println "leanos-serial-protocol\t1"
  IO.println s!"source-revision\t{revision}"
  for family in SerialProtocol.families do
    IO.println
      s!"family\t{family.version}\tLEANOS_SERIAL_FAMILY_{family.version}\tLEANOS/{family.version}"
  for record in SerialProtocol.records do
    IO.println
      s!"record\t{record.1}\t{record.2}\t{SerialProtocol.symbolName record}\t{SerialProtocol.prefixText record}"
  for record in SerialProtocol.preAdmissionBootRecords do
    IO.println s!"pre-admission-boot-record\t{record.1}\t{record.2}"
  for record in SerialProtocol.preAdmissionPhaseRecords do
    IO.println s!"pre-admission-record\t{record.1}\t{record.2}"
  for reason in SerialProtocol.preAdmissionRejectionReasons do
    IO.println s!"pre-admission-reason\t{reason}"
  for reason in SerialProtocol.preAdmissionBootallocRejectionReasons do
    IO.println s!"pre-admission-bootalloc-reason\t{reason}"

end LeanOS.Oracle

def main (args : List String) : IO Unit :=
  match args with
  | [] => LeanOS.Oracle.emit
  | ["tokens"] => LeanOS.Oracle.emitTokens
  | ["serial"] => LeanOS.Oracle.emitSerial
  | _ => throw <| IO.userError "usage: leanos-oracle [tokens|serial]"