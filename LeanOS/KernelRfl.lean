import Lean

/-!
# Kernel-checked reflexivity

`kernel_rfl` closes a goal `a = b` with `Eq.refl a` once the kernel's
definitional-equality checker accepts `a ≡ b`.  It adds no trust: the kernel
checks the finished proof again when the enclosing declaration is added,
exactly as it would after `rfl`.

It exists for evidence theorems that replay a concrete trace over an arbitrary
background state.  The elaborator's `isDefEq` caches weak-head normal forms
only for closed terms, so a trace whose state mentions a free variable has
every shared subterm re-reduced at each use; the kernel checks the same
equality without that blow-up.
-/

namespace LeanOS

open Lean Elab Tactic Meta in
/-- Close `a = b` by `Eq.refl a` after the kernel, rather than the elaborator,
decides that `a` and `b` are definitionally equal.  The kernel re-checks the
resulting proof when the declaration is added. -/
elab "kernel_rfl" : tactic => liftMetaFinishingTactic fun goal => goal.withContext do
  let target ← whnfR (← instantiateMVars (← goal.getType))
  let some (_, lhs, rhs) := target.eq?
    | throwError "kernel_rfl: the goal is not an equality{indentExpr target}"
  match Kernel.isDefEq (← getEnv) (← getLCtx) lhs rhs with
  | .ok true => goal.assign (← mkEqRefl lhs)
  | .ok false =>
    throwError "kernel_rfl: the kernel rejects{indentExpr lhs}\nas definitionally equal to{indentExpr rhs}"
  | .error error => throwKernelException error

end LeanOS
