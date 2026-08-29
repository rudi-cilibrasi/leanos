import LeanOS.BoundedLifecycle

namespace LeanOS.NegativeFixtures.WrappingIssuerReuse

open LeanOS

def wrapRadix : Nat := 4

def wrappingIssue (issuer : LifetimeIssuer.Issuer .subject) :
    Nat × LifetimeIssuer.Issuer .subject :=
  let identity := issuer.next % wrapRadix
  (identity, { next := (identity + 1) % wrapRadix })

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

/- A wrapping issuer recycles a terminated identity instead of failing closed. -/
/--
error: Tactic `native_decide` evaluated that the proposition
  dead.snd = SubjectLifecycle.Result.accepted ∧
    step5.snd = 1 ∧
      dead.fst.lifecycle.capabilities.subjects 1 = false ∧ step5.fst.lifecycle.capabilities.subjects 1 = false
is false
-/
#guard_msgs in
example :
    dead.2 = .accepted ∧
      step5.2 = 1 ∧
      dead.1.lifecycle.capabilities.subjects 1 = false ∧
      step5.1.lifecycle.capabilities.subjects 1 = false := by
  native_decide

end LeanOS.NegativeFixtures.WrappingIssuerReuse
