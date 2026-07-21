import LeanOS.KernelTransition
import LeanOS.Syscall
import LeanOS.IPCSyscall
import LeanOS.Preemption
import LeanOS.BootAllocation
import LeanOS.Interrupt
import LeanOS.InterruptEntry
import LeanOS.BlockingIPC
import LeanOS.CapabilityReuse
import LeanOS.ExtendedState
import LeanOS.PrivilegeEntryControl
import LeanOS.FaultDispatch
import LeanOS.DirectPortIO

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

private def bootAllocation (id : String) (magic infoBytes entryBytes selected flags : UInt64) :
    Vector :=
  { id, adapter := "BootAllocation.scalar", words := [magic, infoBytes, entryBytes, selected, flags],
    expected := BootAllocation.check magic infoBytes entryBytes selected flags }

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
  bootAllocation "boot-allocation.accept" BootAllocation.multiboot2Magic 128 24 512 15,
  bootAllocation "boot-allocation.wrong-magic" 0 128 24 512 15,
  bootAllocation "boot-allocation.truncated" BootAllocation.multiboot2Magic 8 24 512 15,
  bootAllocation "boot-allocation.misaligned-size" BootAllocation.multiboot2Magic 127 24 512 15,
  bootAllocation "boot-allocation.bad-entry-size" BootAllocation.multiboot2Magic 128 16 512 15,
  bootAllocation "boot-allocation.fixed-width-overflow" BootAllocation.multiboot2Magic
    18446744073709551615 24 512 15,
  bootAllocation "boot-allocation.no-eligible-frame" BootAllocation.multiboot2Magic 128 24 4096 15,
  bootAllocation "boot-allocation.publish-before-scrub" BootAllocation.multiboot2Magic 128 24 512 11,
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
    (nmiContextRunning + 3 * 0x4000000) nmiControl]

theorem corpus_shape : vectors.length = 200 := by decide
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
  s!"{index}\t{vector.id}\t{vector.adapter}\t{wordsText vector.words}\t{vector.expected}"

def emit : IO Unit := do
  let revision := (← IO.getEnv "LEANOS_SOURCE_REVISION").getD "unknown"
  IO.println "leanos-oracle\t1"
  IO.println s!"source-revision\t{revision}"
  for entry in vectors.zipIdx do
    IO.println (line entry.2 entry.1)

end LeanOS.Oracle

def main : IO Unit := LeanOS.Oracle.emit
