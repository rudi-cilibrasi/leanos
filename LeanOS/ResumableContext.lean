import LeanOS.Interrupt
import LeanOS.Scheduler

/-!
# Kernel-owned resumable context values

The data type is shared by resumable preemption and blocking IPC.  Transition
policy remains in those modules; this file only prevents either subsystem from
depending on the other's proof implementation in order to exchange the exact
same typed continuation.
-/
namespace LeanOS.ResumableContext

abbrev SubjectId := Scheduler.SubjectId
abbrev AddressSpaceId := Scheduler.AddressSpaceId

structure Registers where
  accumulator : UInt64
  base : UInt64
  count : UInt64
  data : UInt64
  source : UInt64
  destination : UInt64
  basePointer : UInt64
  r8 : UInt64
  r9 : UInt64
  r10 : UInt64
  r11 : UInt64
  r12 : UInt64
  r13 : UInt64
  r14 : UInt64
  r15 : UInt64
  deriving BEq, DecidableEq, Repr

inductive ContextKind where | initial | suspended
  deriving BEq, DecidableEq, Repr

/-- Ownership fields are kernel metadata, never copied from user registers. -/
structure Context where
  owner : SubjectId
  addressSpace : AddressSpaceId
  frame : Interrupt.HardwareFrame
  registers : Registers
  kind : ContextKind
  deriving DecidableEq, Repr

end LeanOS.ResumableContext
