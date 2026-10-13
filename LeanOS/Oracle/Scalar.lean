import LeanOS.Oracle.Vector
import LeanOS.KernelTransition
import LeanOS.Syscall
import LeanOS.IPCSyscall
import LeanOS.Preemption
import LeanOS.BootMemoryMapStreamAuthority
import LeanOS.Interrupt
import LeanOS.BlockingIPC
import LeanOS.CapabilityReuse

/-!
# Oracle corpus: scheduler, syscall, and IPC adapters

The oracle rows of the boot transition, the syscall and IPC demonstrations,
preemption, boot allocation, user return, blocking IPC, and capability reuse,
with their scenario checks.  `LeanOS.Oracle` places `scalarVectors` at row 0.
-/
namespace LeanOS.Oracle

open LeanOS
set_option maxRecDepth 4096

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

private def blockingIPCEvent (id : String) (step operation caller : UInt64) : Vector :=
  { id, adapter := "BlockingIPC.event", words := [step, operation, caller],
    expected := BlockingIPC.blockingIpcEvent step operation caller }

private def capabilityReuse (id : String) (phase caller word word0 word1 : UInt64) : Vector :=
  { id, adapter := "CapabilityReuse.scalar", words := [phase, caller, word, word0, word1],
    expected := CapabilityReuse.modelExpected phase caller word word0 word1 }

/-- The boot, syscall, IPC, preemption, boot-allocation, user-return,
blocking-IPC, and capability-reuse rows: oracle rows 0--85, the head of
the stable order, so a row's position here is its oracle row. -/
def scalarVectors : List Vector := [
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
    18446744073709551615 18446744073709551615]

/-- The repeating event-exchange witness: its four accepted edges and three
refusals (wrong caller, wrong step, a step outside 0–3). -/
def blockingIpcEventVectors : List Vector := [
  blockingIPCEvent "blocking-ipc-event.block-b" 0 1 2,
  blockingIPCEvent "blocking-ipc-event.send-wake-b" 1 2 1,
  blockingIPCEvent "blocking-ipc-event.dispatch-b" 2 3 1,
  blockingIPCEvent "blocking-ipc-event.deliver-b" 3 4 2,
  blockingIPCEvent "blocking-ipc-event.wrong-caller" 1 2 2,
  blockingIPCEvent "blocking-ipc-event.wrong-step" 0 2 1,
  blockingIPCEvent "blocking-ipc-event.out-of-cycle" 4 1 2]

/-- Rung 2 of the #470 ladder: `leanos_boot_transition` over the whole input
classification. Each argument ranges over the boundary words 0, 1, 2 and
2^64 − 1, which cover its equivalence classes (the accepting word, the
other model encoding, words that encode nothing, and the maximum word). -/
def bootTransitionClassWords : List UInt64 := [0, 1, 2, 0xffffffffffffffff]

def bootTransitionClassVectors : List Vector :=
  bootTransitionClassWords.flatMap fun state =>
    bootTransitionClassWords.map fun command =>
      boot s!"boot.class.state-{state}.command-{command}" state command

theorem boot_decoder_roundtrip_cold :
    KernelTransition.encodeState KernelTransition.initialState = 0 := by rfl
theorem boot_accept_agrees : (scalarVectors[0]).expected = 1 := by native_decide
theorem every_rejection_agrees :
    (scalarVectors[1]).expected = 0 ∧ (scalarVectors[2]).expected = 0 ∧
    (scalarVectors[3]).expected = 0 ∧ (scalarVectors[5]).expected = 0 ∧
    (scalarVectors[6]).expected = 0 ∧ (scalarVectors[7]).expected = 0 ∧
    (scalarVectors[8]).expected = 0 ∧ (scalarVectors[10]).expected = 0 ∧
    (scalarVectors[12]).expected = 0 := by native_decide
theorem syscall_accept_agrees : (scalarVectors[4]).expected = 1 := by native_decide
theorem ipc_scenario_agrees :
    (scalarVectors[8]).expected = 0 ∧ (scalarVectors[9]).expected = 1 ∧
    (scalarVectors[10]).expected = 0 ∧ (scalarVectors[11]).expected = 2 := by native_decide
theorem preemption_scenario_agrees :
    (scalarVectors[13]).expected = 0x0000000200000002 ∧
    (scalarVectors[14]).expected = 0 ∧ (scalarVectors[15]).expected = 0 ∧
    (scalarVectors[16]).expected = 0x0000000100000001 ∧
    (scalarVectors[17]).expected = 0 := by native_decide
theorem resumable_scenario_agrees :
    (scalarVectors[18]).expected = 0x1c0101de020202 ∧
    (scalarVectors[19]).expected = 0xde02021c010101 ∧
    (scalarVectors[20]).expected = 0 := by native_decide
theorem user_return_scenario_agrees :
    (scalarVectors[29]).expected = 1 ∧ (scalarVectors[30]).expected = 1 ∧
    (scalarVectors[31]).expected = 1 ∧ (scalarVectors[32]).expected = 1 ∧
    ((scalarVectors.drop 33).take 24).all (fun vector => vector.expected = 0) = true := by
  native_decide

theorem blocking_ipc_scenario_agrees :
    (scalarVectors[57]).expected = BlockingIPC.encodeBootEvent 1 1 1 1 0 ∧
    (scalarVectors[58]).expected = BlockingIPC.encodeBootEvent 2 2 1 1 0 ∧
    (scalarVectors[59]).expected = BlockingIPC.encodeBootEvent 3 3 2 2 0 ∧
    (scalarVectors[60]).expected = BlockingIPC.encodeBootEvent 4 4 2 2 1 ∧
    (scalarVectors[61]).expected = 0 ∧ (scalarVectors[62]).expected = 0 ∧
    (scalarVectors[63]).expected = 0 ∧
    ((scalarVectors.drop 64).take 11).all (fun vector => vector.expected ≠ 0) = true := by
  native_decide

theorem capability_reuse_scenario_agrees :
    (scalarVectors[75]).expected = CapabilityReuse.encodeScenarioEvent 1 1 11
      CapabilityReuse.staleHandle 10 ∧
    (scalarVectors[76]).expected = CapabilityReuse.encodeScenarioEvent 2 2 15
      CapabilityReuse.currentHandle 11 ∧
    (scalarVectors[77]).expected = CapabilityReuse.encodeScenarioEvent 3 3 8
      CapabilityReuse.staleHandle 11 ∧
    (scalarVectors[78]).expected = CapabilityReuse.encodeScenarioEvent 4 4 5
      CapabilityReuse.currentHandle 11 ∧
    (scalarVectors[79]).expected = 0 ∧ (scalarVectors[80]).expected = 0 ∧
    (scalarVectors[81]).expected = 0 ∧
    (scalarVectors[82]).expected = CapabilityReuse.encodeScenarioEvent 5 0 8
      { slot := 0, identity := 4 } 7 ∧
    (scalarVectors[83]).expected = 0 ∧
    (scalarVectors[84]).expected = CapabilityReuse.encodeScenarioEvent 6 0 1
      { slot := 1, identity := 0 } 12 ∧
    (scalarVectors[85]).expected = CapabilityReuse.encodeScenarioEvent 4 4 5
      CapabilityReuse.currentHandle 11 := by
  native_decide

end LeanOS.Oracle
