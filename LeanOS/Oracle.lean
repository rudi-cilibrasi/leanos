import LeanOS.KernelTransition
import LeanOS.Syscall
import LeanOS.IPCSyscall
import LeanOS.Preemption
import LeanOS.BootAllocation
import LeanOS.Interrupt
import LeanOS.BlockingIPC
import LeanOS.CapabilityReuse

/-!
# Bounded scalar boundary oracle

This is the canonical, version-one corpus for the currently exported
fixed-width adapters.  Expected words are evaluated from the adapter
definitions, not copied into a C harness.  The corpus is deliberately finite;
it is differential integration evidence, not a refinement theorem.
-/
namespace LeanOS.Oracle

open LeanOS

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
  capabilityReuse "capability-reuse.fresh-generation" 2 1 (3 * 65536) 0xCAFE 0xBEEF,
  capabilityReuse "capability-reuse.wrong-subject" 2 0 (3 * 65536) 0xCAFE 0xBEEF,
  capabilityReuse "capability-reuse.malformed-generation" 2 1 18446744073709551615
    0xCAFE 0xBEEF,
  capabilityReuse "capability-reuse.wrong-kind" 3 1 (4 * 65536) 0xCAFE 0xBEEF,
  capabilityReuse "capability-reuse.generation-exhausted" 4 1 0 0xCAFE 0xBEEF,
  capabilityReuse "capability-reuse.boundary-payload" 2 1 (3 * 65536)
    18446744073709551615 18446744073709551615]

theorem corpus_shape : vectors.length = 84 := by decide
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
    (vectors[75]).expected = 11 ∧ (vectors[76]).expected = 8 ∧
    (vectors[77]).expected = 8 ∧ (vectors[78]).expected = 5 ∧
    (vectors[79]).expected = 8 ∧ (vectors[80]).expected = 8 ∧
    (vectors[81]).expected = 8 ∧ (vectors[82]).expected = 0 ∧
    (vectors[83]).expected = 5 := by
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
