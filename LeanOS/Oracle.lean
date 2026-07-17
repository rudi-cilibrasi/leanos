import LeanOS.KernelTransition
import LeanOS.Syscall
import LeanOS.IPCSyscall
import LeanOS.Preemption
import LeanOS.BootAllocation

/-!
# Bounded scalar boundary oracle

This is the canonical, version-one corpus for the four currently exported
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

private def bootAllocation (id : String) (magic infoBytes entryBytes selected flags : UInt64) :
    Vector :=
  { id, adapter := "BootAllocation.scalar", words := [magic, infoBytes, entryBytes, selected, flags],
    expected := BootAllocation.check magic infoBytes entryBytes selected flags }

/-- Stable ordering is part of schema version one. -/
def vectors : List Vector := [
  boot "boot.accept" 0 1,
  boot "boot.ready-reject" 1 1,
  boot "boot.bad-state" 2 1,
  boot "boot.bad-command" 0 18446744073709551615,
  syscall "syscall.accept" 0 0 7 1,
  syscall "syscall.unknown" 99 0 0 0,
  syscall "syscall.bad-permission" 0 0 7 4,
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
  bootAllocation "boot-allocation.accept" BootAllocation.multiboot2Magic 128 24 512 15,
  bootAllocation "boot-allocation.wrong-magic" 0 128 24 512 15,
  bootAllocation "boot-allocation.truncated" BootAllocation.multiboot2Magic 8 24 512 15,
  bootAllocation "boot-allocation.misaligned-size" BootAllocation.multiboot2Magic 127 24 512 15,
  bootAllocation "boot-allocation.bad-entry-size" BootAllocation.multiboot2Magic 128 16 512 15,
  bootAllocation "boot-allocation.fixed-width-overflow" BootAllocation.multiboot2Magic
    18446744073709551615 24 512 15,
  bootAllocation "boot-allocation.no-eligible-frame" BootAllocation.multiboot2Magic 128 24 4096 15,
  bootAllocation "boot-allocation.publish-before-scrub" BootAllocation.multiboot2Magic 128 24 512 11]

theorem corpus_shape : vectors.length = 26 := by decide
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
