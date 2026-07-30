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

/-!
# Bounded scalar boundary oracle

This is the canonical, version-one corpus for the currently exported
fixed-width adapters.  Expected words are evaluated from the adapter
definitions, not copied into a C harness.  The corpus is deliberately finite;
it is differential integration evidence, not a refinement theorem.
-/
namespace LeanOS.Oracle

open LeanOS
set_option maxRecDepth 4096

structure Vector where
  id : String
  adapter : String
  words : List UInt64
  expected : UInt64
  deriving Repr

private def boot (id : String) (state command : UInt64) : Vector :=
  { id, adapter := "KernelTransition", words := [state, command],
    expected := KernelTransition.bootTransition state command }

private def syscall (id : String) (number arg0 arg1 arg2 : UInt64) : Vector :=
  { id, adapter := "Syscall.scalar", words := [number, arg0, arg1, arg2],
    expected := Syscall.syscallDemo number arg0 arg1 arg2 }

private def ipc (id : String) (caller operation word0 word1 : UInt64) : Vector :=
  { id, adapter := "IPCSyscall.scalar", words := [caller, operation, word0, word1],
    expected := IPCSyscall.ipcDemo caller operation word0 word1 }

private def preemption (id : String) (vector current queued armed : UInt64) : Vector :=
  { id, adapter := "Preemption.scalar", words := [vector, current, queued, armed],
    expected := Preemption.preemptionDemo vector current queued armed }

private def resumable (id : String) (leg targetDescriptor savedDescriptor
    targetRegisterMarker savedRegisterMarker : UInt64) : Vector :=
  { id, adapter := "Preemption.resumable",
    words := [leg, targetDescriptor, savedDescriptor, targetRegisterMarker,
      savedRegisterMarker],
    expected := Preemption.resumableDemo leg targetDescriptor savedDescriptor
      targetRegisterMarker savedRegisterMarker }

private def bootAllocation (id : String)
    (current candidate status usable blocked manifest : UInt64) :
    Vector :=
  { id, adapter := "BootAllocation.scalar",
    words := [current, candidate, status, usable, blocked, manifest],
    expected := BootMemoryMapStreamAuthority.selectFrame
      current candidate status usable blocked manifest }

private def userReturn (id : String) (mode rip rsp selectors flags : UInt64) : Vector :=
  { id, adapter := "Interrupt.userReturn", words := [mode, rip, rsp, selectors, flags],
    expected := Interrupt.userReturnModelExpected mode rip rsp selectors flags }

private def blockingIPC (id : String) (phase operation caller word0 word1 : UInt64) : Vector :=
  { id, adapter := "BlockingIPC.scalar", words := [phase, operation, caller, word0, word1],
    expected := if 10 ≤ operation then
      BlockingIPC.blockingIpcModelRejection phase operation caller word0 word1
    else BlockingIPC.blockingIpcDemo phase operation caller word0 word1 }

private def capabilityReuse (id : String) (phase caller word word0 word1 : UInt64) : Vector :=
  { id, adapter := "CapabilityReuse.scalar", words := [phase, caller, word, word0, word1],
    expected := CapabilityReuse.modelExpected phase caller word word0 word1 }

private def interruptEntry (id : String) (descriptor frame stack context cleanup : UInt64) :
    Vector :=
  { id, adapter := "Interrupt.entry", words := [descriptor, frame, stack, context, cleanup],
    expected := InterruptEntry.entryModelExpected descriptor frame stack context cleanup }

private def pageFault (id : String) (error address mode context controls : UInt64) :
    Vector :=
  { id, adapter := "Interrupt.pageFault",
    words := [error, address, mode, context, controls],
    expected := InterruptEntry.pageFaultModelExpected error address mode context controls }

private def extendedState (id : String) (policy mode vector current active normalized : UInt64) :
    Vector :=
  { id, adapter := "ExtendedState.denialDispatch",
    words := [policy, mode, vector, current, active, normalized],
    expected := ExtendedState.denialMachineGateModel policy mode vector current active normalized }

private def privilegeEntryControl (id : String) (cpu control event vector normalized cr3 : UInt64) :
    Vector :=
  { id, adapter := "PrivilegeEntryControl.scalar",
    words := [cpu, control, event, vector, normalized, cr3],
    expected := PrivilegeEntryControl.controlModelExpected cpu control event vector normalized cr3 }

private def faultDispatch (id : String) (vector origin current active ready context : UInt64) :
    Vector :=
  { id, adapter := "FaultDispatch.scalar",
    words := [vector, origin, current, active, ready, context],
    expected := FaultDispatch.faultDispatchModelExpected
      vector origin current active ready context }

private def directPortIO (id : String) (stored live originPurpose port directionWidth
    value : UInt64) : Vector :=
  { id, adapter := "DirectPortIO.scalar",
    words := [stored, live, originPurpose, port, directionWidth, value],
    expected := DirectPortIO.directPortIOModelExpected
      stored live originPurpose port directionWidth value }

private def nmi (id : String) (descriptor frame stack context control : UInt64) : Vector :=
  { id, adapter := "Interrupt.nmi", words := [descriptor, frame, stack, context, control],
    expected := InterruptEntry.nmiModelExpected descriptor frame stack context control }

private def staleTranslation (id : String) (kind actor addressSpace page aux selector : UInt64) :
    Vector :=
  { id, adapter := "StaleTranslation.scalar",
    words := [kind, actor, addressSpace, page, aux, selector],
    expected := StaleTranslation.staleTranslationModelExpected
      kind actor addressSpace page aux selector }

private def composite (id : String) (state tag arg0 arg1 arg2 arg3 : UInt64) : Vector :=
  { id, adapter := "CompositeDispatcher.stateful",
    words := [state, tag, arg0, arg1, arg2, arg3],
    expected := CompositeDispatcher.dispatch state tag arg0 arg1 arg2 arg3 }

private def mixedEdgeId : CompositeDispatcher.MixedReplyId → String
  | .transferOffered => "composite.mixed-transfer-offer"
  | .transferAccepted => "composite.mixed-transfer-accept"
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

/-- Issue-112's canonical budget sequence and hostile encodings use the same
stateful export as the mixed composite trace. -/
def budgetVectors : List Vector := [
  composite "frame-budget.a-allocate" 0x4001 0x4001 10 0 0 0,
  composite "frame-budget.a-at-limit" 0x4101 0x4101 11 1 0 0,
  composite "frame-budget.select-b" 0x4201 0x4201 0 0 0 0,
  composite "frame-budget.b-peer-allocate" 0x4301 0x4301 20 0 0 0,
  composite "frame-budget.terminate-a" 0x4401 0x4401 0 0 0 0,
  composite "frame-budget.b-fresh-publication" 0x4501 0x4501 21 1 0 0,
  composite "frame-budget.stale-a-handle-denied" 0x4601 0x4601 0x10000 0 0 0,
  composite "frame-budget.complete" 0x4701 0x4701 0 0 0 0,
  composite "frame-budget.release-a" 0x4101 0x4801 0 0 0 0,
  composite "frame-budget.repeated-release" 0x4901 0x4901 0 0 0 0,
  composite "frame-budget.release-complete" 0x4a01 0x4a01 0 0 0 0,
  composite "frame-budget.repeated-a-retry" 0x4201 0x4101 11 1 0 0,
  composite "frame-budget.occupied-slot" 0x4101 0x4001 10 0 0 0,
  composite "frame-budget.repeated-termination" 0x4501 0x4401 0 0 0 0,
  composite "frame-budget.aggregate-global-inconsistency" 0x4c01 0x4301 20 0 0 0,
  composite "frame-budget.malformed-budget-state" 0x4002 0x4001 10 0 0 0,
  composite "frame-budget.caller-context-forgery" 0x4201 0x4201 1 2 0 0,
  composite "frame-budget.user-selects-charge-owner" 0x4001 0x4001 10 0 1 0,
  composite "frame-budget.stale-generation" 0x4601 0x4601 0x20000 0 0 0,
  composite "frame-budget.output-state-replay" 0x4101 0x4301 20 0 0 0,
  composite "frame-budget.cross-trace-splice" 0x1001 0x4501 21 1 0 0,
  composite "frame-budget.unknown-operation" 0x4001 0x3f01 0 0 0 0,
  composite "frame-budget.reserved-command" 0x4001 0x5001 0 0 0 0,
  composite "frame-budget.maximum-words" 0xffffffffffffffff 0xffffffffffffffff
    0xffffffffffffffff 0xffffffffffffffff 0xffffffffffffffff 0xffffffffffffffff]

/-- A malformed budget-state ABI version is rejected before range routing, so
the differential corpus cannot silently bless a continuity misclassification. -/
theorem malformed_budget_state_is_wrong_version :
    (budgetVectors[15]).id = "frame-budget.malformed-budget-state" ∧
    (budgetVectors[15]).expected = 0xff01 := by
  native_decide

private def nmiUserFrame : UInt64 :=
  0x23 + 0x1b * 256 + 0x10000 + 0x20000 + 0x40000

private def nmiKernelFrame : UInt64 :=
  0x08 + 0x10 * 256 + 0x10000 + 0x20000

private def nmiContextRunning : UInt64 := 1 + 1 * 256 + 2 * 0x10000
private def nmiContextHandling : UInt64 := nmiContextRunning + 0x4000000
private def nmiContextHalted : UInt64 := nmiContextRunning + 0x8000000

private def nmiControl : UInt64 :=
  2 + 40 * 512 + 0x20000 + 0x40000 + 1 * 0x80000 + 1 * 0x8000000

private def nmiFrameAddress : UInt64 := 0x903fd8

/-- Opaque business token; every boot-phase result must carry it unchanged. -/
private def bootPhaseBusiness : UInt64 := 0x5a

private def bootPhase (id : String)
    (phase operation detail latchWord : UInt64) : Vector :=
  { id, adapter := "Interrupt.bootPhase",
    words := [phase, operation, detail, latchWord, bootPhaseBusiness],
    expected := BootInterruptPhase.bootPhaseModelExpected phase operation detail
      latchWord bootPhaseBusiness }

/-- Stable ordering is part of schema version one. -/
def vectors : List Vector := [
  boot "boot.accept" 0 1,
  boot "boot.ready-reject" 1 1,
  boot "boot.bad-state" 2 1,
  boot "boot.bad-command" 0 18446744073709551615,
  syscall "syscall.accept" 0 (12 * 65536) 7 1,
  syscall "syscall.unknown" 99 0 0 0,
  syscall "syscall.bad-permission" 0 (12 * 65536) 7 4,
  syscall "syscall.boundary" 18446744073709551615 18446744073709551615
    18446744073709551615 18446744073709551615,
  ipc "ipc.sender-receive-denied" 1 4 1279607118 20307,
  ipc "ipc.sender-send" 1 3 1279607118 20307,
  ipc "ipc.receiver-send-denied" 2 3 1279607118 20307,
  ipc "ipc.receiver-receive" 2 4 1279607118 20307,
  ipc "ipc.malformed-boundary" 18446744073709551615 18446744073709551615
    18446744073709551615 18446744073709551615,
  preemption "preemption.accept" 32 1 2 1,
  preemption "preemption.masked" 32 1 2 0,
  preemption "preemption.wrong-vector" 14 1 2 1,
  preemption "preemption.resume" 32 2 1 1,
  preemption "preemption.forged-current" 32 2 3 1,
  resumable "resumable.a-to-b" 1 0x202 0x101 0xde 0x1c,
  resumable "resumable.b-to-a" 2 0x101 0x202 0x1c 0xde,
  resumable "resumable.cross-restored" 2 0x102 0x202 0x1c 0xde,
  bootAllocation "boot-allocation.accept" 4096 512 1 1 0 1,
  bootAllocation "boot-allocation.parser-rejected" 4096 512 2 1 0 1,
  bootAllocation "boot-allocation.parser-incomplete" 4096 512 0 1 0 1,
  bootAllocation "boot-allocation.no-usable-coverage" 4096 512 1 0 0 1,
  bootAllocation "boot-allocation.nonusable-overlap" 4096 512 1 1 1 1,
  bootAllocation "boot-allocation.no-eligible-frame" 4096 4096 1 1 0 1,
  bootAllocation "boot-allocation.manifest-rejected" 4096 512 1 1 0 0,
  bootAllocation "boot-allocation.first-selection-stable" 511 512 1 1 0 1,
  userReturn "user-return.initial" 1 0x400100 0x500ff8 0x1b0023 0x202,
  userReturn "user-return.syscall-resume" 2 0x400100 0x500ff8 0x1b0023 0x202,
  userReturn "user-return.scheduler-restore" 3 0x400100 0x500ff8 0x1b0023 0x202,
  userReturn "user-return.empty-stack-cursor" 1 0x400100 0x501000 0x1b0023 0x202,
  userReturn "user-return.zero-purpose" 0 0x400100 0x500ff8 0x1b0023 0x202,
  userReturn "user-return.unsupported-contained-fault" 4 0x400100 0x500ff8 0x1b0023 0x202,
  userReturn "user-return.max-purpose" 18446744073709551615 0x400100 0x500ff8 0x1b0023 0x202,
  userReturn "user-return.noncanonical-rip" 1 0x800000000000 0x500ff8 0x1b0023 0x202,
  userReturn "user-return.noncanonical-rsp" 1 0x400100 0x800000000000 0x1b0023 0x202,
  userReturn "user-return.wrong-cs" 1 0x400100 0x500ff8 0x1b0008 0x202,
  userReturn "user-return.wrong-ss" 1 0x400100 0x500ff8 0x100023 0x202,
  userReturn "user-return.kernel-origin" 7 0x400100 0x500ff8 0x1b0023 0x202,
  userReturn "user-return.iopl" 1 0x400100 0x500ff8 0x1b0023 0x1202,
  userReturn "user-return.nt" 1 0x400100 0x500ff8 0x1b0023 0x4202,
  userReturn "user-return.vm" 1 0x400100 0x500ff8 0x1b0023 0x20202,
  userReturn "user-return.ac" 1 0x400100 0x500ff8 0x1b0023 0x40202,
  userReturn "user-return.df" 1 0x400100 0x500ff8 0x1b0023 0x602,
  userReturn "user-return.if-cleared" 1 0x400100 0x500ff8 0x1b0023 0x2,
  userReturn "user-return.stale-subject" 8 0x400100 0x500ff8 0x1b0023 0x202,
  userReturn "user-return.stale-address-space" 9 0x400100 0x500ff8 0x1b0023 0x202,
  userReturn "user-return.wrong-cr3" 10 0x400100 0x500ff8 0x1b0023 0x202,
  userReturn "user-return.wrong-frame-subject" 11 0x400100 0x500ff8 0x1b0023 0x202,
  userReturn "user-return.wrong-frame-address-space" 12 0x400100 0x500ff8 0x1b0023 0x202,
  userReturn "user-return.fatal-mode" 6 0x400100 0x500ff8 0x1b0023 0x202,
  userReturn "user-return.code-outside-subject" 1 0x401000 0x500ff8 0x1b0023 0x202,
  userReturn "user-return.stack-outside-subject" 1 0x400100 0x501001 0x1b0023 0x202,
  userReturn "user-return.diagnostic-recovery" 5 0x400100 0x500ff8 0x1b0023 0x202,
  userReturn "user-return.validate-then-mutate" 13 0x400100 0x500ff8 0x1b0023 0x202,
  blockingIPC "blocking-ipc.block-b" 0 1 2 0x4c45414e 0x4f53,
  blockingIPC "blocking-ipc.send-wake-b" 1 2 1 0x4c45414e 0x4f53,
  blockingIPC "blocking-ipc.dispatch-b" 2 3 1 0x4c45414e 0x4f53,
  blockingIPC "blocking-ipc.deliver-b" 3 4 2 0x4c45414e 0x4f53,
  blockingIPC "blocking-ipc.wrong-caller" 1 2 2 0x4c45414e 0x4f53,
  blockingIPC "blocking-ipc.wrong-phase" 0 2 1 0x4c45414e 0x4f53,
  blockingIPC "blocking-ipc.forged-payload" 3 4 2 0 0x4f53,
  blockingIPC "blocking-ipc.empty-wrong-subject" 0 10 9 0x4c45414e 0x4f53,
  blockingIPC "blocking-ipc.missing-receive" 0 11 2 0x4c45414e 0x4f53,
  blockingIPC "blocking-ipc.missing-send" 1 12 1 0x4c45414e 0x4f53,
  blockingIPC "blocking-ipc.stale-endpoint" 0 13 2 0x4c45414e 0x4f53,
  blockingIPC "blocking-ipc.full-wait-queue" 0 14 2 0x4c45414e 0x4f53,
  blockingIPC "blocking-ipc.full-ready-queue" 1 15 1 0x4c45414e 0x4f53,
  blockingIPC "blocking-ipc.duplicate-block" 0 16 2 0x4c45414e 0x4f53,
  blockingIPC "blocking-ipc.duplicate-wake" 1 17 1 0x4c45414e 0x4f53,
  blockingIPC "blocking-ipc.wrong-endpoint" 0 18 2 0x4c45414e 0x4f53,
  blockingIPC "blocking-ipc.forged-sender" 3 19 2 1 0x4f53,
  blockingIPC "blocking-ipc.cancel-before-send" 1 20 1 0x4c45414e 0x4f53,
  capabilityReuse "capability-reuse.initial" 0 1 (2 * 65536) 0xCAFE 0xBEEF,
  capabilityReuse "capability-reuse.cleared-slot" 1 1 (2 * 65536) 0xCAFE 0xBEEF,
  capabilityReuse "capability-reuse.stale-generation" 2 1 (2 * 65536) 0xCAFE 0xBEEF,
  capabilityReuse "capability-reuse.fresh-generation" 3 1 (3 * 65536) 0xCAFE 0xBEEF,
  capabilityReuse "capability-reuse.wrong-subject" 2 0 (3 * 65536) 0xCAFE 0xBEEF,
  capabilityReuse "capability-reuse.malformed-generation" 2 1 18446744073709551615
    0xCAFE 0xBEEF,
  capabilityReuse "capability-reuse.high-generation-alias" 2 1
    ((4294967296 + 2) * 65536) 0xCAFE 0xBEEF,
  capabilityReuse "capability-reuse.wrong-kind" 4 1 (4 * 65536) 0xCAFE 0xBEEF,
  capabilityReuse "capability-reuse.invalid-state-five" 5 1 (3 * 65536) 0xCAFE 0xBEEF,
  capabilityReuse "capability-reuse.generation-exhausted" 6 1 0 0xCAFE 0xBEEF,
  capabilityReuse "capability-reuse.boundary-payload" 3 1 (3 * 65536)
    18446744073709551615 18446744073709551615,
  interruptEntry "entry.syscall" 32896 291 0x800000 257 3,
  interruptEntry "entry.user-invalid-opcode" 1542 291 0x800000 257 3,
  interruptEntry "entry.user-device-not-available" 1799 291 0x800000 257 3,
  interruptEntry "entry.user-page-fault" 69134 291 0x800000 257 3,
  interruptEntry "entry.timer" 8224 291 0x800000 257 3,
  interruptEntry "entry.kernel-diagnostic" 69134 8 0x800000 257 3,
  interruptEntry "entry.wrong-stub" 32640 291 0x800000 257 3,
  interruptEntry "entry.wrong-dpl-vector" 32846 291 0x800000 257 3,
  interruptEntry "entry.missing-error" 3598 291 0x800000 257 3,
  interruptEntry "entry.spurious-error" 98464 291 0x800000 257 3,
  interruptEntry "entry.truncated" 32896 803 0x800000 257 3,
  interruptEntry "entry.misaligned" 32896 291 0x800008 257 3,
  interruptEntry "entry.forged-user-words-kernel-shape" 32896 35 0x800000 257 3,
  interruptEntry "entry.unexpected-user-shape" 69134 264 0x800000 257 3,
  interruptEntry "entry.stack-low" 32896 291 0x7ffff0 257 3,
  interruptEntry "entry.stack-high" 32896 291 0x803ff0 257 3,
  interruptEntry "entry.nested" 32896 291 0x800000 257 7,
  interruptEntry "entry.ac-uncleared" 32896 291 0x800000 257 2,
  interruptEntry "entry.df-uncleared" 32896 291 0x800000 257 1,
  extendedState "extended-state.dispatch-peer" 1 0 7 1 1 1,
  extendedState "extended-state.policy-mismatch" 0 0 7 1 1 1,
  extendedState "extended-state.kernel-origin" 1 2 7 1 1 1,
  extendedState "extended-state.dispatch-invariant" 1 3 7 1 1 1,
  extendedState "extended-state.idle" 1 4 7 1 1 1,
  extendedState "extended-state.stale-binding" 1 0 7 1 1 2,
  extendedState "extended-state.dispatch-peer-ud" 1 6 6 1 1 1,
  privilegeEntryControl "entry-control.accepted" 1 0 0 0 0 0,
  privilegeEntryControl "entry-control.cpu-intel" 2 0 0 0 0 0,
  privilegeEntryControl "entry-control.cpu-unsupported" 3 0 0 0 0 0,
  privilegeEntryControl "entry-control.mode-protected32" 4 0 0 0 0 0,
  privilegeEntryControl "entry-control.mode-compatibility" 5 0 0 0 0 0,
  privilegeEntryControl "entry-control.syscall-unexposed" 6 0 0 0 0 0,
  privilegeEntryControl "entry-control.sysenter-unexposed" 7 0 0 0 0 0,
  privilegeEntryControl "entry-control.efer-sce-set" 1 1 0 0 0 0,
  privilegeEntryControl "entry-control.star-mutated" 1 2 0 0 0 0,
  privilegeEntryControl "entry-control.lstar-mutated" 1 3 0 0 0 0,
  privilegeEntryControl "entry-control.cstar-mutated" 1 4 0 0 0 0,
  privilegeEntryControl "entry-control.sfmask-mutated" 1 5 0 0 0 0,
  privilegeEntryControl "entry-control.sysenter-cs-mutated" 1 6 0 0 0 0,
  privilegeEntryControl "entry-control.sysenter-esp-mutated" 1 7 0 0 0 0,
  privilegeEntryControl "entry-control.sysenter-eip-mutated" 1 8 0 0 0 0,
  privilegeEntryControl "entry-control.writes-incomplete" 1 9 0 0 0 0,
  privilegeEntryControl "entry-control.readback-mismatch" 1 10 0 0 0 0,
  privilegeEntryControl "entry-control.manifest-missing" 1 11 0 0 0 0,
  privilegeEntryControl "entry-control.extended-policy-relaxed" 1 12 0 0 0 0,
  privilegeEntryControl "entry-control.return-accepted" 1 0 1 0 0 0,
  privilegeEntryControl "entry-control.user-syscall-ud" 1 0 2 6 1 1,
  privilegeEntryControl "entry-control.user-sysenter-ud" 1 0 3 6 1 1,
  privilegeEntryControl "entry-control.user-syscall-gp" 1 0 2 13 1 1,
  privilegeEntryControl "entry-control.kernel-syscall-ud" 1 0 4 6 1 1,
  privilegeEntryControl "entry-control.stale-subject" 1 0 2 6 2 1,
  privilegeEntryControl "entry-control.stale-cr3" 1 0 2 6 1 2,
  privilegeEntryControl "entry-control.live-policy-relaxed" 1 0 8 6 1 1,
  privilegeEntryControl "entry-control.alternate-target" 1 0 9 6 1 1,
  privilegeEntryControl "entry-control.user-stack" 1 0 10 6 1 1,
  privilegeEntryControl "entry-control.error-shape" 1 0 11 6 1 1,
  privilegeEntryControl "entry-control.int80-as-denial" 1 0 6 128 1 1,
  privilegeEntryControl "entry-control.post-fatal" 1 0 7 6 1 1,
  faultDispatch "fault-dispatch.accept-a-to-b" 14 3 1 1 2 2,
  faultDispatch "fault-dispatch.kernel-origin" 14 0 1 1 2 2,
  faultDispatch "fault-dispatch.malformed-frame" 14 4 1 1 2 2,
  faultDispatch "fault-dispatch.wrong-vector" 13 3 1 1 2 2,
  faultDispatch "fault-dispatch.stale-current" 14 3 3 1 2 2,
  faultDispatch "fault-dispatch.wrong-address-space" 14 3 1 3 2 2,
  faultDispatch "fault-dispatch.empty-ready" 14 3 1 1 0 0,
  faultDispatch "fault-dispatch.already-terminated" 14 3 0 1 2 2,
  faultDispatch "fault-dispatch.stale-context" 14 3 1 1 2 3,
  faultDispatch "fault-dispatch.peer-context-resource-witness" 14 3 1 1 2 2,
  directPortIO "direct-port.user-denied" 0 0 0 0x3f8 1 65,
  directPortIO "direct-port.nonzero-iopl" 1 1 0 0x3f8 1 65,
  directPortIO "direct-port.short-tss-limit" 2 2 0 0x3f8 1 65,
  directPortIO "direct-port.extended-tss-limit" 3 3 0 0x3f8 1 65,
  directPortIO "direct-port.in-range-map-base" 4 4 0 0x3f8 1 65,
  directPortIO "direct-port.exposed-bitmap" 5 5 0 0x3f8 1 65,
  directPortIO "direct-port.not-kernel-configured" 6 6 0 0x3f8 1 65,
  directPortIO "direct-port.readback-missing" 7 7 0 0x3f8 1 65,
  directPortIO "direct-port.stale-readback" 0 7 0 0x3f8 1 65,
  directPortIO "direct-port.kernel-serial-output" 0 0 1 0x3f8 1 65,
  directPortIO "direct-port.kernel-serial-input" 0 0 1 0x3fd 0 0,
  directPortIO "direct-port.kernel-pic-output" 0 0 2 0x20 1 0x20,
  directPortIO "direct-port.kernel-pit-output" 0 0 3 0x43 1 0x36,
  directPortIO "direct-port.kernel-debug-exit" 0 0 4 0xf4 1 0x11,
  directPortIO "direct-port.wrong-purpose" 0 0 1 0x20 1 0x20,
  directPortIO "direct-port.wrong-port" 0 0 1 0x3f7 1 65,
  directPortIO "direct-port.wrong-direction" 0 0 1 0x3f8 0 0,
  directPortIO "direct-port.wrong-word-width" 0 0 1 0x3f8 3 65,
  directPortIO "direct-port.wrong-dword-width" 0 0 1 0x3f8 5 65,
  directPortIO "direct-port.byte-normalization" 0 0 1 0x3f8 1 0x100,
  directPortIO "direct-port.user-input-word" 0 0 0 0x3f8 2 0,
  directPortIO "direct-port.user-input-dword" 0 0 0 0x3f8 4 0,
  directPortIO "direct-port.invalid-origin" 0 0 5 0x3f8 1 65,
  directPortIO "direct-port.invalid-direction-width" 0 0 1 0x3f8 6 65,
  directPortIO "direct-port.invalid-stored-control" 0xffffffffffffffff 0 1 0x3f8 1 65,
  directPortIO "direct-port.invalid-live-control" 0 0xffffffffffffffff 1 0x3f8 1 65,
  directPortIO "direct-port.invalid-port" 0 0 1 0xffffffffffffffff 1 65,
  directPortIO "direct-port.post-validation-relaxation" 0 5 0 0x3f8 1 65,
  interruptEntry "entry.user-general-protection" 68877 291 0x800000 257 3,
  nmi "nmi.user-running" 0 nmiUserFrame nmiFrameAddress nmiContextRunning nmiControl,
  nmi "nmi.kernel-handling" 0 nmiKernelFrame nmiFrameAddress nmiContextHandling nmiControl,
  nmi "nmi.kernel-halted-normalized" 0 nmiKernelFrame nmiFrameAddress
    nmiContextHalted nmiControl,
  nmi "nmi.wrong-descriptor" 1 nmiUserFrame nmiFrameAddress nmiContextRunning nmiControl,
  nmi "nmi.wrong-target" 0 nmiUserFrame nmiFrameAddress nmiContextRunning (nmiControl + 1),
  nmi "nmi.spurious-error" 0 nmiUserFrame nmiFrameAddress nmiContextRunning
    (nmiControl + 0x100),
  nmi "nmi.wrong-frame-bytes" 0 nmiUserFrame nmiFrameAddress nmiContextRunning
    (nmiControl - 0x200),
  nmi "nmi.misaligned" 0 nmiUserFrame 0x903fd0 nmiContextRunning nmiControl,
  nmi "nmi.wrong-stack-identity" 0 nmiUserFrame nmiFrameAddress
    (nmiContextRunning + 0x10000) nmiControl,
  nmi "nmi.frame-not-at-stack-top" 0 nmiUserFrame 0x903fc8
    nmiContextRunning nmiControl,
  nmi "nmi.wrong-origin" 0 (nmiUserFrame - 0x40000) nmiFrameAddress
    nmiContextRunning nmiControl,
  nmi "nmi.wrong-selectors" 0 (nmiUserFrame + 4) nmiFrameAddress
    nmiContextRunning nmiControl,
  nmi "nmi.noncanonical" 0 (nmiUserFrame - 0x10000) nmiFrameAddress
    nmiContextRunning nmiControl,
  nmi "nmi.privileged-state" 0 nmiUserFrame nmiFrameAddress nmiContextRunning
    (nmiControl - 0x20000),
  nmi "nmi.stale-context" 0 nmiUserFrame nmiFrameAddress
    (nmiContextRunning + 1) nmiControl,
  nmi "nmi.invalid-bounds-code" 0 nmiUserFrame nmiFrameAddress
    (nmiContextRunning + 3 * 0x1000000) nmiControl,
  nmi "nmi.invalid-mode-code" 0 nmiUserFrame nmiFrameAddress
    (nmiContextRunning + 3 * 0x4000000) nmiControl,
  interruptEntry "entry.user-divide-error" 0 291 0x800000 257 3,
  interruptEntry "entry.user-breakpoint" 771 291 0x800000 257 3,
  interruptEntry "entry.kernel-divide-error" 0 8 0x800000 257 3,
  interruptEntry "entry.kernel-breakpoint" 771 8 0x800000 257 3,
  interruptEntry "entry.spurious-error-divide-error" 65536 291 0x800000 257 3,
  interruptEntry "entry.spurious-error-breakpoint" 66307 291 0x800000 257 3,
  interruptEntry "entry.wrong-restart-breakpoint" 771 1315 0x800000 257 3,
  interruptEntry "entry.wrong-restart-page-fault" 69134 1315 0x800000 257 3,
  faultDispatch "fault-dispatch.accept-divide-error" 0 3 1 1 2 2,
  faultDispatch "fault-dispatch.accept-breakpoint" 3 3 1 1 2 2,
  faultDispatch "fault-dispatch.divide-error-idle" 0 3 1 1 0 0,
  faultDispatch "fault-dispatch.breakpoint-multi-survivor" 3 3 1 1 3 2,
  faultDispatch "fault-dispatch.page-fault-multi-survivor" 14 3 1 1 3 2,
  faultDispatch "fault-dispatch.kernel-origin-divide-error" 0 0 1 1 2 2,
  faultDispatch "fault-dispatch.kernel-origin-breakpoint" 3 0 1 1 2 2,
  faultDispatch "fault-dispatch.malformed-divide-error" 0 4 1 1 2 2,
  faultDispatch "fault-dispatch.wrong-restart-breakpoint" 3 5 1 1 2 2,
  faultDispatch "fault-dispatch.wrong-restart-page-fault" 14 5 1 1 2 2,
  faultDispatch "fault-dispatch.swapped-reason-divide-error" 0 6 1 1 2 2,
  faultDispatch "fault-dispatch.swapped-reason-page-fault" 14 6 1 1 2 2,
  faultDispatch "fault-dispatch.stale-current-divide-error" 0 3 3 1 2 2,
  faultDispatch "fault-dispatch.stale-address-space-breakpoint" 3 3 1 3 2 2,
  faultDispatch "fault-dispatch.stale-context-breakpoint" 3 3 1 1 2 3,
  bootPhase "bootphase.publish-bootstrap32" 0 1 0 0,
  bootPhase "bootphase.publish-bootstrap64" 1 2 0 0,
  bootPhase "bootphase.publish-runtime" 2 3 7 0,
  bootPhase "bootphase.runtime-missing-tss" 2 3 6 0,
  bootPhase "bootphase.skip-bootstrap32" 0 2 0 0,
  bootPhase "bootphase.backward-bootstrap32" 2 1 0 0,
  bootPhase "bootphase.premature-runtime" 1 3 7 0,
  bootPhase "bootphase.nmi-bootstrap32" 1 4 2 0,
  bootPhase "bootphase.nmi-bootstrap64" 2 4 2 0,
  bootPhase "bootphase.error-fault-bootstrap64" 2 4 (13 + 256) 0,
  bootPhase "bootphase.noerror-fault-bootstrap32" 1 4 6 0,
  bootPhase "bootphase.double-fault-bootstrap64" 2 4 (8 + 256) 0,
  bootPhase "bootphase.user-claim-early" 1 4 (14 + 256 + 512) 0,
  bootPhase "bootphase.inherited-window" 0 4 2 0,
  bootPhase "bootphase.runtime-delegated" 3 4 2 0,
  bootPhase "bootphase.repeated-after-latch" 4 4 2 1,
  bootPhase "bootphase.publish-after-latch" 4 1 0 1,
  bootPhase "bootphase.invalid-phase-code" 9 4 2 0,
  staleTranslation "stale-translation.unmap-accept" 0 0 1 7 0 0,
  staleTranslation "stale-translation.protect-downgrade" 1 0 1 7 1 0,
  staleTranslation "stale-translation.unmap-wrong-owner" 0 1 1 7 0 0,
  staleTranslation "stale-translation.protect-wrong-owner" 1 1 1 7 1 0,
  staleTranslation "stale-translation.release-flush" 2 0 0 0 0 0,
  staleTranslation "stale-translation.destroy-space" 3 0 0 0 1 0,
  staleTranslation "stale-translation.switch-away" 4 0 2 0 0 0,
  staleTranslation "stale-translation.switch-back" 4 0 1 0 0 0,
  staleTranslation "stale-translation.unmap-unmapped" 0 0 1 9 0 0,
  staleTranslation "stale-translation.reuse-old-page-absent" 0 0 1 7 0 1,
  staleTranslation "stale-translation.protect-write-amplify" 1 0 1 7 2 0,
  staleTranslation "stale-translation.destroy-wrong-subject" 3 1 0 0 1 0,
  staleTranslation "stale-translation.release-wrong-slot" 2 0 0 0 1 0,
  staleTranslation "stale-translation.switch-unknown-space" 4 0 99 0 0 0,
  staleTranslation "stale-translation.malformed-kind" 9 0 1 7 0 0,
  pageFault "page-fault.user-read-not-present" 4 0x400123 0 0x10000101 123,
  pageFault "page-fault.user-write-not-present" 6 0x400123 0 0x10000101 123,
  pageFault "page-fault.user-execute-not-present" 20 0x400123 0 0x10000101 123,
  pageFault "page-fault.user-read-protection" 5 0x400123 0 0x10000101 123,
  pageFault "page-fault.user-write-protection" 7 0x400123 0 0x10000101 123,
  pageFault "page-fault.user-execute-protection" 21 0x400123 0 0x10000101 123,
  pageFault "page-fault.kernel-read" 0 0xffff800000001234 1 0x10000101 123,
  pageFault "page-fault.reserved-bit" 12 0x400123 0 0x10000101 123,
  pageFault "page-fault.unsupported-bit-5-pk" 36 0x400123 0 0x10000101 123,
  pageFault "page-fault.unsupported-bit-6-shadow-stack" 68 0x400123 0
    0x10000101 123,
  pageFault "page-fault.unsupported-bit-7" 132 0x400123 0 0x10000101 123,
  pageFault "page-fault.unsupported-bit-8" 260 0x400123 0 0x10000101 123,
  pageFault "page-fault.unsupported-bit-9" 516 0x400123 0 0x10000101 123,
  pageFault "page-fault.unsupported-bit-10" 1028 0x400123 0 0x10000101 123,
  pageFault "page-fault.unsupported-bit-11" 2052 0x400123 0 0x10000101 123,
  pageFault "page-fault.unsupported-bit-12" 4100 0x400123 0 0x10000101 123,
  pageFault "page-fault.unsupported-bit-13" 8196 0x400123 0 0x10000101 123,
  pageFault "page-fault.unsupported-bit-14" 16388 0x400123 0 0x10000101 123,
  pageFault "page-fault.unsupported-bit-15-sgx" 32772 0x400123 0
    0x10000101 123,
  pageFault "page-fault.wrong-cr2" 4 0x401123 0 0x10000101 123,
  pageFault "page-fault.wrong-vector" 4 0x400123 2 0x10000101 123,
  pageFault "page-fault.wrong-stub" 4 0x400123 3 0x10000101 123,
  pageFault "page-fault.missing-error" 4 0x400123 4 0x10000101 123,
  pageFault "page-fault.malformed-frame" 4 0x400123 5 0x10000101 123,
  pageFault "page-fault.privilege-mismatch" 0 0x400123 0 0x10000101 123,
  pageFault "page-fault.nested" 4 0x400123 0 0x10000101 127,
  pageFault "page-fault.low-canonical-boundary" 4 0x7fffffffffff 0 0x10000101 123,
  pageFault "page-fault.upper-canonical-boundary" 4 0xffff800000000000 0
    0x10000101 123,
  pageFault "page-fault.noncanonical-boundary" 4 0x800000000000 0 0x10000101 123,
  pageFault "page-fault.authority-subject-mutated" 4 0x400123 0 0x10000102 123,
  pageFault "page-fault.authority-space-mutated" 4 0x400123 0 0x10000201 123,
  pageFault "page-fault.authority-cr3-mutated" 4 0x400123 0 0x10010101 123,
  pageFault "page-fault.authority-wp-mutated" 4 0x400123 0 0x10000101 115,
  pageFault "page-fault.authority-nxe-mutated" 4 0x400123 0 0x10000101 107,
  pageFault "page-fault.authority-smep-mutated" 4 0x400123 0 0x10000101 91,
  pageFault "page-fault.authority-smap-mutated" 4 0x400123 0 0x10000101 59,
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
  composite "composite.unknown-command" 0x0101 0x0001 0 0 0 0] ++
  mixedVectors ++ budgetVectors

theorem corpus_shape : vectors.length = 354 := by decide
/-- Oracle indices 314--329 are definitionally the complete canonical mixed
edge corpus, rather than a second hand-maintained scalar table. -/
theorem hosted_mixed_vectors_exact :
    (vectors.drop 314).take 16 =
      CompositeDispatcher.mixedCanonicalEdges.map mixedEdgeVector := by
  rfl

theorem hosted_budget_vectors_exact :
    vectors.drop 330 = budgetVectors := by rfl

theorem hosted_budget_canonical_sequence :
    FrameBudgetScenario.run .initial FrameBudgetScenario.canonicalCommands =
      some .complete :=
  FrameBudgetScenario.canonical_sequence_complete

/-- Consequently every hosted mixed vector is backed by the non-circular
scalar-to-authoritative refinement theorem for its source edge. -/
theorem hosted_mixed_vectors_refine :
    ∀ edge ∈ CompositeDispatcher.mixedCanonicalEdges, edge.Refines :=
  CompositeDispatcher.mixedCanonicalEdges_refine

theorem composite_mixed_trace_agrees :
    (vectors[314]).expected = 0x200901 ∧
    (vectors[319]).expected = 0x250e01 ∧
    (vectors[324]).expected = 0x2a1301 ∧
    (vectors[326]).expected = 0x2c1501 ∧
    (vectors[327]).expected = 0x2d1601 ∧
    (vectors[329]).expected = 0x2f1801 := by
  native_decide
theorem boot_decoder_roundtrip_cold :
    KernelTransition.encodeState KernelTransition.initialState = 0 := by rfl
theorem boot_accept_agrees : (vectors[0]).expected = 1 := by native_decide
theorem every_rejection_agrees :
    (vectors[1]).expected = 0 ∧ (vectors[2]).expected = 0 ∧
    (vectors[3]).expected = 0 ∧ (vectors[5]).expected = 0 ∧
    (vectors[6]).expected = 0 ∧ (vectors[7]).expected = 0 ∧
    (vectors[8]).expected = 0 ∧ (vectors[10]).expected = 0 ∧
    (vectors[12]).expected = 0 := by native_decide
theorem syscall_accept_agrees : (vectors[4]).expected = 1 := by native_decide
theorem ipc_scenario_agrees :
    (vectors[8]).expected = 0 ∧ (vectors[9]).expected = 1 ∧
    (vectors[10]).expected = 0 ∧ (vectors[11]).expected = 2 := by native_decide
theorem preemption_scenario_agrees :
    (vectors[13]).expected = 0x0000000200000002 ∧
    (vectors[14]).expected = 0 ∧ (vectors[15]).expected = 0 ∧
    (vectors[16]).expected = 0x0000000100000001 ∧
    (vectors[17]).expected = 0 := by native_decide
theorem resumable_scenario_agrees :
    (vectors[18]).expected = 0x1c0101de020202 ∧
    (vectors[19]).expected = 0xde02021c010101 ∧
    (vectors[20]).expected = 0 := by native_decide
theorem user_return_scenario_agrees :
    (vectors[29]).expected = 1 ∧ (vectors[30]).expected = 1 ∧
    (vectors[31]).expected = 1 ∧ (vectors[32]).expected = 1 ∧
    ((vectors.drop 33).take 24).all (fun vector => vector.expected = 0) = true := by
  native_decide

theorem blocking_ipc_scenario_agrees :
    (vectors[57]).expected = BlockingIPC.encodeBootEvent 1 1 1 1 0 ∧
    (vectors[58]).expected = BlockingIPC.encodeBootEvent 2 2 1 1 0 ∧
    (vectors[59]).expected = BlockingIPC.encodeBootEvent 3 3 2 2 0 ∧
    (vectors[60]).expected = BlockingIPC.encodeBootEvent 4 4 2 2 1 ∧
    (vectors[61]).expected = 0 ∧ (vectors[62]).expected = 0 ∧
    (vectors[63]).expected = 0 ∧
    ((vectors.drop 64).take 11).all (fun vector => vector.expected ≠ 0) = true := by
  native_decide

theorem capability_reuse_scenario_agrees :
    (vectors[75]).expected = CapabilityReuse.encodeScenarioEvent 1 1 11
      CapabilityReuse.staleHandle 10 ∧
    (vectors[76]).expected = CapabilityReuse.encodeScenarioEvent 2 2 15
      CapabilityReuse.currentHandle 11 ∧
    (vectors[77]).expected = CapabilityReuse.encodeScenarioEvent 3 3 8
      CapabilityReuse.staleHandle 11 ∧
    (vectors[78]).expected = CapabilityReuse.encodeScenarioEvent 4 4 5
      CapabilityReuse.currentHandle 11 ∧
    (vectors[79]).expected = 0 ∧ (vectors[80]).expected = 0 ∧
    (vectors[81]).expected = 0 ∧
    (vectors[82]).expected = CapabilityReuse.encodeScenarioEvent 5 0 8
      { slot := 0, identity := 4 } 7 ∧
    (vectors[83]).expected = 0 ∧
    (vectors[84]).expected = CapabilityReuse.encodeScenarioEvent 6 0 1
      { slot := 1, identity := 0 } 12 ∧
    (vectors[85]).expected = CapabilityReuse.encodeScenarioEvent 4 4 5
      CapabilityReuse.currentHandle 11 := by
  native_decide

theorem interrupt_entry_scenario_agrees :
    ((vectors.drop 86).take 6).all (fun vector => vector.expected ≠ 0) = true ∧
    ((vectors.drop 92).take 13).all (fun vector => vector.expected = 0) = true := by
  native_decide

private def interruptEntryAdapterAgrees (vector : Vector) : Bool :=
  match vector.adapter, vector.words with
  | "Interrupt.entry", [descriptor, frame, stack, context, cleanup] =>
      InterruptEntry.entryDemo descriptor frame stack context cleanup = vector.expected
  | _, _ => true

theorem interrupt_entry_adapter_agrees_with_model :
    vectors.all interruptEntryAdapterAgrees = true := by
  native_decide

theorem general_protection_entry_scenario_agrees :
    (vectors[182]).adapter = "Interrupt.entry" ∧
    (vectors[182]).expected ≠ 0 := by
  native_decide

theorem extended_state_dispatch_scenario_agrees :
    (vectors[105]).expected = 0x3f00000000000102 ∧
    (vectors[106]).expected = 0 ∧
    (vectors[107]).expected = 0 ∧
    (vectors[108]).expected = 0 ∧
    (vectors[109]).expected = 1 ∧
    (vectors[110]).expected = 0 ∧
    (vectors[111]).expected = 0x3f00000000000102 := by
  native_decide

theorem privilege_entry_control_scenario_agrees :
    (vectors[112]).expected = 1 ∧
    ((vectors.drop 113).take 18).all (fun vector => vector.expected = 0) = true ∧
    (vectors[131]).expected = 0xa001 ∧
    (vectors[132]).expected = 0xd001 ∧
    (vectors[133]).expected = 0xd001 ∧
    ((vectors.drop 134).take 9).all (fun vector =>
      vector.expected ≥ 0xf000) = true ∧
    (vectors[143]).expected = 0xff00 := by
  native_decide

private def privilegeEntryControlAdapterAgrees (vector : Vector) : Bool :=
  match vector.adapter, vector.words with
  | "PrivilegeEntryControl.scalar", [cpu, control, event, vectorWord, normalized, cr3] =>
      PrivilegeEntryControl.controlDemo cpu control event vectorWord normalized cr3 =
        vector.expected
  | _, _ => true

/-- The entry-control differential corpus is the 32-vector block beginning at
index 112, immediately before the fault-dispatch block. -/
theorem privilege_entry_control_corpus_shape :
    ((vectors.drop 112).take 32).length = 32 := by
  decide

/-- Every entry-control scalar result agrees with the independently evaluated
rich control model on the complete finite entry-control corpus. -/
theorem privilege_entry_control_adapter_agrees_with_model :
    ((vectors.drop 112).take 32).all privilegeEntryControlAdapterAgrees = true := by
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

private def directPortIOAdapterAgrees (vector : Vector) : Bool :=
  match vector.adapter, vector.words with
  | "DirectPortIO.scalar", [stored, live, originPurpose, port, directionWidth, value] =>
      DirectPortIO.directPortIODemo stored live originPurpose port directionWidth value =
        vector.expected
  | _, _ => true

/-- The canonical direct-port block covers accepted controls, every named
control mutation, stale live state, all direction/width classes, exact and
wrong kernel purposes, malformed scalar words, and post-validation relaxation. -/
theorem direct_port_io_corpus_shape :
    ((vectors.drop 154).take 28).length = 28 := by
  decide

theorem direct_port_io_adapter_agrees_with_model :
    ((vectors.drop 154).take 28).all directPortIOAdapterAgrees = true := by
  native_decide

private def nmiAdapterAgrees (vector : Vector) : Bool :=
  match vector.adapter, vector.words with
  | "Interrupt.nmi", [descriptor, frame, stack, context, control] =>
      InterruptEntry.nmiDemo descriptor frame stack context control = vector.expected
  | _, _ => true

/-- The generated-C NMI block contains three normalized interrupted modes and
one vector for every rejection constructor reachable from the reviewed,
compile-time-valid terminal manifest or canonical scalar decoder.
`invalidManifest` is intentionally not runtime-selectable through this scalar
boundary.  The accepted halted snapshot tests normalization only: the
authoritative dispatcher short-circuits an already-halted state before calling
the normalizer and retains its original terminal record. -/
theorem nmi_corpus_shape : ((vectors.drop 183).take 17).length = 17 := by
  decide

theorem nmi_corpus_id_inventory :
    List.map (fun vector => vector.id) ((vectors.drop 183).take 17) =
      ["nmi.user-running", "nmi.kernel-handling", "nmi.kernel-halted-normalized",
        "nmi.wrong-descriptor", "nmi.wrong-target", "nmi.spurious-error",
        "nmi.wrong-frame-bytes", "nmi.misaligned", "nmi.wrong-stack-identity",
        "nmi.frame-not-at-stack-top", "nmi.wrong-origin", "nmi.wrong-selectors",
        "nmi.noncanonical", "nmi.privileged-state", "nmi.stale-context",
        "nmi.invalid-bounds-code", "nmi.invalid-mode-code"] := by
  native_decide

theorem nmi_adapter_agrees_with_model :
    ((vectors.drop 183).take 17).all nmiAdapterAgrees = true := by
  native_decide

theorem nmi_accepted_modes_agree :
    (vectors[183]).expected = 0x101000101 ∧
    (vectors[184]).expected = 0x101010001 ∧
    (vectors[185]).expected = 0x101020001 := by
  native_decide

theorem nmi_noncanonical_context_codes_rejected :
    (vectors[198]).expected = 0x800000000000000e ∧
      (vectors[199]).expected = 0x800000000000000f := by
  native_decide

theorem nmi_rejection_codes_agree :
    List.map (fun vector => vector.expected) ((vectors.drop 186).take 14) =
      List.map (fun reason => 0x8000000000000000 + reason.code)
        InterruptEntry.NmiRejectReason.runtimeInventory := by
  native_decide

/-- The contained user-fault class block appended for vectors 0 and 3: two
accepted CPL3 entry vectors, kernel-origin/spurious-error/wrong-restart entry
rejections, and the composite fault-dispatch corpus binding the typed reason
codes into the encoded outcome. -/
theorem user_fault_class_corpus_shape :
    ((vectors.drop 200).take 23).length = 23 := by
  decide

theorem user_fault_class_entry_scenario_agrees :
    (vectors[200]).expected ≠ 0 ∧ (vectors[201]).expected ≠ 0 ∧
      ((vectors.drop 202).take 6).all (fun vector => vector.expected = 0) = true := by
  native_decide

/-- Accepted #DE/#BP dispatch words carry the exact reason code in bits
40--47 over the unchanged version-one witness layout; kernel-origin,
malformed, and wrong-restart forms are terminal words while swapped-shape and
stale bindings reject to zero. -/
theorem user_fault_class_dispatch_scenario_agrees :
    (vectors[208]).expected = 0x100ff020202 ∧
      (vectors[209]).expected = 0x200ff020202 ∧
      (vectors[210]).expected = 0x10000000001 ∧
      (vectors[211]).expected = 0x2003f020202 ∧
      (vectors[212]).expected = 0x3f020202 ∧
      ((vectors.drop 213).take 5).all
        (fun vector => vector.expected = 0x8000000000000002) = true ∧
      ((vectors.drop 218).take 5).all (fun vector => vector.expected = 0) = true := by
  native_decide

private def bootPhaseAdapterAgrees (vector : Vector) : Bool :=
  match vector.adapter, vector.words with
  | "Interrupt.bootPhase", [phase, operation, detail, latchWord, business] =>
      InterruptEntry.bootPhaseDemo phase operation detail latchWord business =
        vector.expected
  | _, _ => true

/-- The generated-C boot-phase block covers every publication step, each wrong
or premature publication, bootstrap NMI and representative error-code shapes in
both bootstrap phases, the typed unowned inherited window, runtime delegation,
repeated terminal events, attempted progress after the latch, and a malformed
phase code. -/
theorem boot_phase_corpus_shape : ((vectors.drop 223).take 18).length = 18 := by
  decide

theorem boot_phase_corpus_id_inventory :
    List.map (fun vector => vector.id) ((vectors.drop 223).take 18) =
      ["bootphase.publish-bootstrap32", "bootphase.publish-bootstrap64",
        "bootphase.publish-runtime", "bootphase.runtime-missing-tss",
        "bootphase.skip-bootstrap32", "bootphase.backward-bootstrap32",
        "bootphase.premature-runtime", "bootphase.nmi-bootstrap32",
        "bootphase.nmi-bootstrap64", "bootphase.error-fault-bootstrap64",
        "bootphase.noerror-fault-bootstrap32", "bootphase.double-fault-bootstrap64",
        "bootphase.user-claim-early", "bootphase.inherited-window",
        "bootphase.runtime-delegated", "bootphase.repeated-after-latch",
        "bootphase.publish-after-latch", "bootphase.invalid-phase-code"] := by
  native_decide

/-- Every boot-phase scalar result agrees with the expectation evaluated from
the rich finite phase model on the complete boot-phase corpus. -/
theorem boot_phase_adapter_agrees_with_model :
    ((vectors.drop 223).take 18).all bootPhaseAdapterAgrees = true := by
  native_decide

/-- The three orderly publications are the only accepted rows; both bootstrap
NMI rows latch the absorbing terminal record; delegation and the post-latch
rows carry the unchanged business token. -/
theorem boot_phase_expected_classes_agree :
    (vectors[223]).expected = 0x5a0101 ∧
    (vectors[224]).expected = 0x5a0201 ∧
    (vectors[225]).expected = 0x5a0301 ∧
    (vectors[226]).expected = 0x18005a0202 ∧
    (vectors[230]).expected = 0x25a0102 ∧
    (vectors[231]).expected = 0x25a0202 ∧
    (vectors[237]).expected = 0x25a0004 ∧
    (vectors[238]).expected = 0x5a0003 ∧
    (vectors[239]).expected = 0x5a0003 ∧
    (vectors[240]).expected = 0x8000000000000021 := by
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

private def staleTranslationAdapterAgrees (vector : Vector) : Bool :=
  match vector.adapter, vector.words with
  | "StaleTranslation.scalar", [kind, actor, addressSpace, page, aux, selector] =>
      StaleTranslation.staleTranslationDemo kind actor addressSpace page aux selector =
        vector.expected
  | _, _ => true

/-- The stale-translation block is the 15-vector tail appended for issue #126:
accepted unmap/protect, wrong-owner rejections, release/destroy/switch effects,
unmapped-page and post-reuse rejections, permission amplification, and a
malformed encoding. -/
theorem stale_translation_corpus_shape :
    ((vectors.drop 241).take 15).length = 15 := by decide

/-- Every stale-translation scalar result agrees with the independently
evaluated authoritative `step` over the exact 15-vector block. -/
theorem stale_translation_adapter_agrees_with_model :
    ((vectors.drop 241).take 15).all staleTranslationAdapterAgrees = true := by native_decide

/-- Accepted transitions carry their exact effect word (accepted bit 32,
affected-absent bit 33, effect tag/space/page), wrong-owner and post-reuse
requests request no invalidation, and the malformed encoding is a no-op. -/
theorem stale_translation_scenario_agrees :
    (vectors[241]).expected = 0x300070101 ∧
    (vectors[242]).expected = 0x300070101 ∧
    (vectors[243]).expected = 0x200000000 ∧
    (vectors[244]).expected = 0x200000000 ∧
    (vectors[245]).expected = 0x300000003 ∧
    (vectors[246]).expected = 0x300000102 ∧
    (vectors[247]).expected = 0x300000003 ∧
    (vectors[248]).expected = 0x300000003 ∧
    (vectors[249]).expected = 0x200000000 ∧
    (vectors[250]).expected = 0x200000000 ∧
    (vectors[255]).expected = 0 := by native_decide

private def pageFaultAdapterAgrees (vector : Vector) : Bool :=
  match vector.adapter, vector.words with
  | "Interrupt.pageFault", [error, address, mode, context, controls] =>
      InterruptEntry.pageFaultDemo error address mode context controls = vector.expected
  | _, _ => true

theorem page_fault_corpus_shape : ((vectors.drop 256).take 36).length = 36 := by
  decide

theorem page_fault_adapter_agrees_with_model :
    ((vectors.drop 256).take 36).all pageFaultAdapterAgrees = true := by
  native_decide

/-- Dropping any authority-bearing input changes the accepted executable
witness, so the rich-model corpus cannot agree with an erasing adapter. -/
theorem page_fault_subject_mutation_attested :
    (vectors[256]).expected ≠ (vectors[285]).expected := by native_decide
theorem page_fault_space_mutation_attested :
    (vectors[256]).expected ≠ (vectors[286]).expected := by native_decide
theorem page_fault_cr3_mutation_attested :
    (vectors[256]).expected ≠ (vectors[287]).expected := by native_decide
theorem page_fault_wp_mutation_attested :
    (vectors[256]).expected ≠ (vectors[288]).expected := by native_decide
theorem page_fault_nxe_mutation_attested :
    (vectors[256]).expected ≠ (vectors[289]).expected := by native_decide
theorem page_fault_smep_mutation_attested :
    (vectors[256]).expected ≠ (vectors[290]).expected := by native_decide
theorem page_fault_smap_mutation_attested :
    (vectors[256]).expected ≠ (vectors[291]).expected := by native_decide

theorem page_fault_authority_mutations_attested :
    (vectors[256]).expected ≠ (vectors[285]).expected ∧
    (vectors[256]).expected ≠ (vectors[286]).expected ∧
    (vectors[256]).expected ≠ (vectors[287]).expected ∧
    (vectors[256]).expected ≠ (vectors[288]).expected ∧
    (vectors[256]).expected ≠ (vectors[289]).expected ∧
    (vectors[256]).expected ≠ (vectors[290]).expected ∧
    (vectors[256]).expected ≠ (vectors[291]).expected :=
  ⟨page_fault_subject_mutation_attested, page_fault_space_mutation_attested,
    page_fault_cr3_mutation_attested, page_fault_wp_mutation_attested,
    page_fault_nxe_mutation_attested, page_fault_smep_mutation_attested,
    page_fault_smap_mutation_attested⟩

private def wordsText : List UInt64 → String
  | [] => ""
  | [word] => toString word
  | word :: rest => toString word ++ "," ++ wordsText rest

def line (index : Nat) (vector : Vector) : String :=
  s!"{index}\t{vector.id}\t{vector.adapter}\t{wordsText vector.words}\t{vector.expected}"

def emit : IO Unit := do
  let revision := (← IO.getEnv "LEANOS_SOURCE_REVISION").getD "unknown"
  IO.println "leanos-oracle\t1"
  IO.println s!"source-revision\t{revision}"
  for entry in vectors.zipIdx do
    IO.println (line entry.2 entry.1)

end LeanOS.Oracle

def main : IO Unit := LeanOS.Oracle.emit
