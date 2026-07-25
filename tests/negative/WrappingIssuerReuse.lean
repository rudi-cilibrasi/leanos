import LeanOS.BoundedLifecycle

/-!
Deliberately invalid fixture: a modulo-wrapping issuer that recycles subject
identities instead of failing closed with the typed `exhausted` result.  On a
concrete trace the wrapped counter re-issues a terminated identity, so the
stale-lifetime conclusion proved for the bounded issuer
(`BoundedLifecycle.runOperations_dead_subject_stays_dead`) is false for this
policy and this file must never type-check.
-/
namespace LeanOS.WrappingIssuerReuse

open LeanOS

/-- Tiny hostile machine width. -/
def wrapRadix : Nat := 4

/-- Hostile issuance policy: wrap the counter modulo `wrapRadix` the way an
unchecked machine counter would, never reporting exhaustion. -/
def wrappingIssue (issuer : LifetimeIssuer.Issuer .subject) :
    Nat × LifetimeIssuer.Issuer .subject :=
  let identity := issuer.next % wrapRadix
  (identity, { next := (identity + 1) % wrapRadix })

/-- Hostile creation: installs the wrapped identity directly, as a wrapped
bounded implementation of the history would. -/
def wrappingCreateSubject (runtime : BoundedLifecycle.Runtime) :
    BoundedLifecycle.Runtime × Nat :=
  let (identity, issuer) := wrappingIssue runtime.subjectIssuer
  ({ runtime with
      subjectIssuer := issuer
      lifecycle := { runtime.lifecycle with
        capabilities := { runtime.lifecycle.capabilities with
          subjects := SubjectLifecycle.setBool runtime.lifecycle.capabilities.subjects
            identity true }
        issuedSubjects := SubjectLifecycle.setBool runtime.lifecycle.issuedSubjects
          identity true } },
    identity)

private def step1 := wrappingCreateSubject BoundedLifecycle.sampleRuntime
private def step2 := wrappingCreateSubject step1.1
private def step3 := wrappingCreateSubject step2.1
private def dead := BoundedLifecycle.terminateSubject step3.1 1
private def step4 := wrappingCreateSubject dead.1
private def step5 := wrappingCreateSubject step4.1

/-- The wrapping issuer cannot satisfy the stale-lifetime theorem: identity 1
was terminated, yet the recycled counter makes exactly that identity live
again two creations later. -/
example :
    dead.2 = .accepted ∧
      step5.2 = 1 ∧
      dead.1.lifecycle.capabilities.subjects 1 = false ∧
      step5.1.lifecycle.capabilities.subjects 1 = false := by
  native_decide

end LeanOS.WrappingIssuerReuse
