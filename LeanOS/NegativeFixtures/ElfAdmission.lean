import LeanOS.ElfAdmission

namespace LeanOS.NegativeFixtures.ElfAdmission

open LeanOS.ElfAdmission

private def writableText : Candidate :=
  withHeaders [{ text with flags := flagRead + flagWrite + flagExecute }, data]

/- A writable and executable text segment cannot be admitted. -/
/--
error: Tactic `native_decide` evaluated that the proposition
  (admit (encode writableText)).isOk = true
is false
-/
#guard_msgs in
example : (admit (encode writableText)).isOk = true := by
  native_decide

private def entryInData : Candidate :=
  { sample with entry := userWindowStart + pageBytes }

/- An entry point in the data segment cannot be relabeled as a text entry. -/
/--
error: Tactic `native_decide` evaluated that the proposition
  (admit (encode entryInData)).toOption = some (planOf entryInData)
is false
-/
#guard_msgs in
example : (admit (encode entryInData)).toOption = some (planOf entryInData) := by
  native_decide

/- The plan of an admitted file cannot drop its data segment. -/
/--
error: Tactic `native_decide` evaluated that the proposition
  (admit (encode sample)).toOption =
    some { fileBytes := 256, entry := sample.entry, segments := List.take 1 (planOf sample).segments }
is false
-/
#guard_msgs in
example : (admit (encode sample)).toOption =
    some { fileBytes := 256, entry := sample.entry, segments := (planOf sample).segments.take 1 } := by
  native_decide

end LeanOS.NegativeFixtures.ElfAdmission
