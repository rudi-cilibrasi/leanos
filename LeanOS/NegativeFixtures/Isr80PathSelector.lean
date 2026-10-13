import LeanOS.Isr80PathSelector

open LeanOS.Isr80PathSelector

namespace LeanOS.NegativeFixtures.Isr80PathSelector

/- Issue #560: a reply word equal to a former magic value must not change
`isr80`'s path.  Each attempt below claims that an ordinary reply carrying
one of those values leaves the reply path, in an image that handles every
path; the kernel refutes every one. -/

def zeroFrame : Fin 20 → UInt64 := fun _ => 0

/- The old claim: some former magic value still selects the switch path it
used to select. -/
/--
error: Tactic `decide` proved that the proposition
  ∃ magic,
    magic ∈ formerMagic ∧
      dispatch allPaths (enter { reply := magic.fst, path := Path.reply } zeroFrame) = Target.path magic.snd
is false
-/
#guard_msgs in
example : ∃ magic ∈ formerMagic,
    dispatch allPaths (enter { reply := magic.1, path := .reply } zeroFrame) =
      .path magic.2 := by
  decide

/- Nor does any former magic value move a reply off the reply path. -/
/--
error: Tactic `decide` proved that the proposition
  ∃ magic,
    magic ∈ formerMagic ∧
      dispatch allPaths (enter { reply := magic.fst, path := Path.reply } zeroFrame) ≠ Target.path Path.reply
is false
-/
#guard_msgs in
example : ∃ magic ∈ formerMagic,
    dispatch allPaths (enter { reply := magic.1, path := .reply } zeroFrame) ≠
      .path .reply := by
  decide

/- The reviewed ladder cannot be shown to depend on the reply word: two
steps with the same path and different reply words select the same target. -/
/--
error: unsolved goals
step : Step
frame : Fin 20 → UInt64
w : UInt64
⊢ False
-/
#guard_msgs in
example (step : Step) (frame : Fin 20 → UInt64) (w : UInt64) :
    dispatch allPaths (enter { step with reply := w } frame) ≠
      dispatch allPaths (enter step frame) := by
  rw [dispatch_function_of_step_path allPaths { step with reply := w } step
    frame frame rfl]
  simp

/- The same claim against the old ladder, which compared the reply word,
would not be refuted: there an ordinary reply equal to `0xbeef` left the
reply path.  Claiming the old ladder was reply-independent fails. -/
/--
error: Tactic `decide` proved that the proposition
  legacyDispatch (48879, Path.blockBEnterA) (enter { reply := 48879, path := Path.reply } zeroFrame) =
    Target.path Path.reply
is false
-/
#guard_msgs in
example : legacyDispatch (0xbeef, .blockBEnterA)
    (enter { reply := 0xbeef, path := .reply } zeroFrame) = .path .reply := by
  decide

end LeanOS.NegativeFixtures.Isr80PathSelector
