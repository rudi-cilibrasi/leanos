import LeanOS.FailStop

open LeanOS

/-! A public composite operation must not carry a caller-supplied trusted
context.  If it did, changing only that attacker-selected context would change
the subsystem dispatch term, so the composite attacker-erasure contract would
not be derivable by construction. -/

def callerSuppliedSyscall (state : FailStop.CompositeState)
    (context : Syscall.TrustedContext) (call : Syscall.UntrustedCall) :
    Syscall.Outcome :=
  Syscall.dispatch state.virtualMemory context call

example (state : FailStop.CompositeState) (call : Syscall.UntrustedCall)
    (first second : Syscall.TrustedContext) :
    callerSuppliedSyscall state first call =
      callerSuppliedSyscall state second call := by
  exact Eq.refl (callerSuppliedSyscall state first call)
