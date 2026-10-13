import LeanOS.Oracle.Vector
import LeanOS.BootInterruptPhase
import LeanOS.InterruptEntry
import LeanOS.ExtendedState
import LeanOS.PrivilegeEntryControl
import LeanOS.FaultDispatch
import LeanOS.DirectPortIO
import LeanOS.StaleTranslation

/-!
# Oracle corpus: interrupt, entry, and fault adapters

The oracle rows of interrupt entry, extended-state denial dispatch, privilege
entry control, fault dispatch, direct port I/O, NMI, boot-phase publication,
stale translation, and page faults, with their adapter-agreement and scenario
checks.  `LeanOS.Oracle` places `interruptVectors` at row 86.
-/
namespace LeanOS.Oracle

open LeanOS
set_option maxRecDepth 4096

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

/-- The interrupt-entry, extended-state, entry-control, fault-dispatch,
direct-port, NMI, boot-phase, stale-translation, and page-fault rows:
oracle rows 86--291, so position `i` here is oracle row `86 + i`. -/
def interruptVectors : List Vector := [
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
  pageFault "page-fault.authority-smap-mutated" 4 0x400123 0 0x10000101 59]

theorem interrupt_entry_scenario_agrees :
    ((interruptVectors.drop 0).take 6).all (fun vector => vector.expected ≠ 0) = true ∧
    ((interruptVectors.drop 6).take 13).all (fun vector => vector.expected = 0) = true := by
  native_decide

theorem general_protection_entry_scenario_agrees :
    (interruptVectors[96]).adapter = "Interrupt.entry" ∧
    (interruptVectors[96]).expected ≠ 0 := by
  native_decide

theorem extended_state_dispatch_scenario_agrees :
    (interruptVectors[19]).expected = 0x3f00000000000102 ∧
    (interruptVectors[20]).expected = 0 ∧
    (interruptVectors[21]).expected = 0 ∧
    (interruptVectors[22]).expected = 0 ∧
    (interruptVectors[23]).expected = 1 ∧
    (interruptVectors[24]).expected = 0 ∧
    (interruptVectors[25]).expected = 0x3f00000000000102 := by
  native_decide

theorem privilege_entry_control_scenario_agrees :
    (interruptVectors[26]).expected = 1 ∧
    ((interruptVectors.drop 27).take 18).all (fun vector => vector.expected = 0) = true ∧
    (interruptVectors[45]).expected = 0xa001 ∧
    (interruptVectors[46]).expected = 0xd001 ∧
    (interruptVectors[47]).expected = 0xd001 ∧
    ((interruptVectors.drop 48).take 9).all (fun vector =>
      vector.expected ≥ 0xf000) = true ∧
    (interruptVectors[57]).expected = 0xff00 := by
  native_decide

private def privilegeEntryControlAdapterAgrees (vector : Vector) : Bool :=
  match vector.adapter, vector.words with
  | "PrivilegeEntryControl.scalar", [cpu, control, event, vectorWord, normalized, cr3] =>
      PrivilegeEntryControl.controlDemo cpu control event vectorWord normalized cr3 =
        vector.expected
  | _, _ => true

/-- The entry-control differential corpus is the 32-vector block beginning at
position 26 (oracle row 112), immediately before the fault-dispatch block. -/
theorem privilege_entry_control_corpus_shape :
    ((interruptVectors.drop 26).take 32).length = 32 := by
  decide

/-- Every entry-control scalar result agrees with the independently evaluated
rich control model on the complete finite entry-control corpus. -/
theorem privilege_entry_control_adapter_agrees_with_model :
    ((interruptVectors.drop 26).take 32).all privilegeEntryControlAdapterAgrees = true := by
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
    ((interruptVectors.drop 68).take 28).length = 28 := by
  decide

theorem direct_port_io_adapter_agrees_with_model :
    ((interruptVectors.drop 68).take 28).all directPortIOAdapterAgrees = true := by
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
theorem nmi_corpus_shape : ((interruptVectors.drop 97).take 17).length = 17 := by
  decide

theorem nmi_corpus_id_inventory :
    List.map (fun vector => vector.id) ((interruptVectors.drop 97).take 17) =
      ["nmi.user-running", "nmi.kernel-handling", "nmi.kernel-halted-normalized",
        "nmi.wrong-descriptor", "nmi.wrong-target", "nmi.spurious-error",
        "nmi.wrong-frame-bytes", "nmi.misaligned", "nmi.wrong-stack-identity",
        "nmi.frame-not-at-stack-top", "nmi.wrong-origin", "nmi.wrong-selectors",
        "nmi.noncanonical", "nmi.privileged-state", "nmi.stale-context",
        "nmi.invalid-bounds-code", "nmi.invalid-mode-code"] := by
  native_decide

theorem nmi_adapter_agrees_with_model :
    ((interruptVectors.drop 97).take 17).all nmiAdapterAgrees = true := by
  native_decide

theorem nmi_accepted_modes_agree :
    (interruptVectors[97]).expected = 0x101000101 ∧
    (interruptVectors[98]).expected = 0x101010001 ∧
    (interruptVectors[99]).expected = 0x101020001 := by
  native_decide

theorem nmi_noncanonical_context_codes_rejected :
    (interruptVectors[112]).expected = 0x800000000000000e ∧
      (interruptVectors[113]).expected = 0x800000000000000f := by
  native_decide

theorem nmi_rejection_codes_agree :
    List.map (fun vector => vector.expected) ((interruptVectors.drop 100).take 14) =
      List.map (fun reason => 0x8000000000000000 + reason.code)
        InterruptEntry.NmiRejectReason.runtimeInventory := by
  native_decide

/-- The contained user-fault class block appended for vectors 0 and 3: two
accepted CPL3 entry vectors, kernel-origin/spurious-error/wrong-restart entry
rejections, and the composite fault-dispatch corpus binding the typed reason
codes into the encoded outcome. -/
theorem user_fault_class_corpus_shape :
    ((interruptVectors.drop 114).take 23).length = 23 := by
  decide

theorem user_fault_class_entry_scenario_agrees :
    (interruptVectors[114]).expected ≠ 0 ∧ (interruptVectors[115]).expected ≠ 0 ∧
      ((interruptVectors.drop 116).take 6).all (fun vector => vector.expected = 0) = true := by
  native_decide

/-- Accepted #DE/#BP dispatch words carry the exact reason code in bits
40--47 over the unchanged version-one witness layout; kernel-origin,
malformed, and wrong-restart forms are terminal words while swapped-shape and
stale bindings reject to zero. -/
theorem user_fault_class_dispatch_scenario_agrees :
    (interruptVectors[122]).expected = 0x100ff020202 ∧
      (interruptVectors[123]).expected = 0x200ff020202 ∧
      (interruptVectors[124]).expected = 0x10000000001 ∧
      (interruptVectors[125]).expected = 0x2003f020202 ∧
      (interruptVectors[126]).expected = 0x3f020202 ∧
      ((interruptVectors.drop 127).take 5).all
        (fun vector => vector.expected = 0x8000000000000002) = true ∧
      ((interruptVectors.drop 132).take 5).all (fun vector => vector.expected = 0) = true := by
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
theorem boot_phase_corpus_shape : ((interruptVectors.drop 137).take 18).length = 18 := by
  decide

theorem boot_phase_corpus_id_inventory :
    List.map (fun vector => vector.id) ((interruptVectors.drop 137).take 18) =
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
    ((interruptVectors.drop 137).take 18).all bootPhaseAdapterAgrees = true := by
  native_decide

/-- The three orderly publications are the only accepted rows; both bootstrap
NMI rows latch the absorbing terminal record; delegation and the post-latch
rows carry the unchanged business token. -/
theorem boot_phase_expected_classes_agree :
    (interruptVectors[137]).expected = 0x5a0101 ∧
    (interruptVectors[138]).expected = 0x5a0201 ∧
    (interruptVectors[139]).expected = 0x5a0301 ∧
    (interruptVectors[140]).expected = 0x18005a0202 ∧
    (interruptVectors[144]).expected = 0x25a0102 ∧
    (interruptVectors[145]).expected = 0x25a0202 ∧
    (interruptVectors[151]).expected = 0x25a0004 ∧
    (interruptVectors[152]).expected = 0x5a0003 ∧
    (interruptVectors[153]).expected = 0x5a0003 ∧
    (interruptVectors[154]).expected = 0x8000000000000021 := by
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
    ((interruptVectors.drop 155).take 15).length = 15 := by decide

/-- Every stale-translation scalar result agrees with the independently
evaluated authoritative `step` over the exact 15-vector block. -/
theorem stale_translation_adapter_agrees_with_model :
    ((interruptVectors.drop 155).take 15).all staleTranslationAdapterAgrees = true := by native_decide

/-- Accepted transitions carry their exact effect word (accepted bit 32,
affected-absent bit 33, effect tag/space/page), wrong-owner and post-reuse
requests request no invalidation, and the malformed encoding is a no-op. -/
theorem stale_translation_scenario_agrees :
    (interruptVectors[155]).expected = 0x300070101 ∧
    (interruptVectors[156]).expected = 0x300070101 ∧
    (interruptVectors[157]).expected = 0x200000000 ∧
    (interruptVectors[158]).expected = 0x200000000 ∧
    (interruptVectors[159]).expected = 0x300000003 ∧
    (interruptVectors[160]).expected = 0x300000102 ∧
    (interruptVectors[161]).expected = 0x300000003 ∧
    (interruptVectors[162]).expected = 0x300000003 ∧
    (interruptVectors[163]).expected = 0x200000000 ∧
    (interruptVectors[164]).expected = 0x200000000 ∧
    (interruptVectors[169]).expected = 0 := by native_decide

private def pageFaultAdapterAgrees (vector : Vector) : Bool :=
  match vector.adapter, vector.words with
  | "Interrupt.pageFault", [error, address, mode, context, controls] =>
      InterruptEntry.pageFaultDemo error address mode context controls = vector.expected
  | _, _ => true

theorem page_fault_corpus_shape : ((interruptVectors.drop 170).take 36).length = 36 := by
  decide

theorem page_fault_adapter_agrees_with_model :
    ((interruptVectors.drop 170).take 36).all pageFaultAdapterAgrees = true := by
  native_decide

/-- Dropping any authority-bearing input changes the accepted executable
witness, so the rich-model corpus cannot agree with an erasing adapter. -/
theorem page_fault_subject_mutation_attested :
    (interruptVectors[170]).expected ≠ (interruptVectors[199]).expected := by native_decide
theorem page_fault_space_mutation_attested :
    (interruptVectors[170]).expected ≠ (interruptVectors[200]).expected := by native_decide
theorem page_fault_cr3_mutation_attested :
    (interruptVectors[170]).expected ≠ (interruptVectors[201]).expected := by native_decide
theorem page_fault_wp_mutation_attested :
    (interruptVectors[170]).expected ≠ (interruptVectors[202]).expected := by native_decide
theorem page_fault_nxe_mutation_attested :
    (interruptVectors[170]).expected ≠ (interruptVectors[203]).expected := by native_decide
theorem page_fault_smep_mutation_attested :
    (interruptVectors[170]).expected ≠ (interruptVectors[204]).expected := by native_decide
theorem page_fault_smap_mutation_attested :
    (interruptVectors[170]).expected ≠ (interruptVectors[205]).expected := by native_decide

theorem page_fault_authority_mutations_attested :
    (interruptVectors[170]).expected ≠ (interruptVectors[199]).expected ∧
    (interruptVectors[170]).expected ≠ (interruptVectors[200]).expected ∧
    (interruptVectors[170]).expected ≠ (interruptVectors[201]).expected ∧
    (interruptVectors[170]).expected ≠ (interruptVectors[202]).expected ∧
    (interruptVectors[170]).expected ≠ (interruptVectors[203]).expected ∧
    (interruptVectors[170]).expected ≠ (interruptVectors[204]).expected ∧
    (interruptVectors[170]).expected ≠ (interruptVectors[205]).expected :=
  ⟨page_fault_subject_mutation_attested, page_fault_space_mutation_attested,
    page_fault_cr3_mutation_attested, page_fault_wp_mutation_attested,
    page_fault_nxe_mutation_attested, page_fault_smep_mutation_attested,
    page_fault_smap_mutation_attested⟩

end LeanOS.Oracle
