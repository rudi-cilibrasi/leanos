import LeanOS.UserCopyAliases

/-!
Translate validated byte locations into dedicated copy-alias operands. These
operands preserve byte order and offsets; they never reuse the original user
virtual pointer. The proofs concern a successfully prepared, stable plan. Root
installation, instruction execution and cached translations remain separate.
-/
namespace LeanOS.UserCopyOperands

open LeanOS.UserCopy LeanOS.UserCopyAliases LeanOS.VirtualMapping LeanOS.X86PageTable

structure Operand where
  page : VirtualPage
  offset : Nat
  deriving DecidableEq, Repr

/-- Total construction; authority is supplied by the accepted-plan proofs,
not by applying this function to an arbitrary unvalidated location. -/
def operand (plan : Plan) (base : VirtualPage) (location : Location) : Operand :=
  { page := base + plan.frames.idxOf location.frame, offset := location.offset }

def operands (plan : Plan) (base : VirtualPage) : List Operand :=
  plan.locations.map (operand plan base)

theorem frame_index_lookup (frames : List PhysicalFrame) frame (h : frame ∈ frames) :
    frames[frames.idxOf frame]? = some frame := by
  induction frames with
  | nil => simp at h
  | cons first rest ih =>
      by_cases he : frame = first
      · subst frame; simp
      · have hr : frame ∈ rest := by simpa [he] using h
        simp [List.idxOf_cons, cond_eq_ite, beq_iff_eq, Ne.symm he, ih hr]

theorem location_frame_in_plan state context start length access closed base protectedFrames plan location
    (h : prepare state context start length access closed base protectedFrames = .ok plan)
    (hl : location ∈ plan.locations) : location.frame ∈ plan.frames := by
  rw [(prepared_validated _ _ _ _ _ _ _ _ _ h).2.1]
  simp only [List.mem_eraseDups, List.mem_map]
  exact ⟨location, hl, rfl⟩

/-- Every accepted byte uses exactly one of the two reserved virtual pages. -/
theorem operand_in_slots state context start length access closed base protectedFrames plan location
    (h : prepare state context start length access closed base protectedFrames = .ok plan)
    (hl : location ∈ plan.locations) :
    (operand plan base location).page = base ∨ (operand plan base location).page = base + 1 := by
  have hm := location_frame_in_plan _ _ _ _ _ _ _ _ _ _ h hl
  have hi := List.idxOf_lt_length_of_mem hm
  have hb := (prepared_validated _ _ _ _ _ _ _ _ _ h).2.2.1
  have hz : plan.frames.idxOf location.frame = 0 ∨ plan.frames.idxOf location.frame = 1 := by omega
  rcases hz with hz | hz <;> simp [operand, hz]

/-- An alias operand resolves to precisely the validated physical frame and
retains the request's direction-specific permissions. -/
theorem operand_leaf_exact state context start length access closed base protectedFrames plan location
    (h : prepare state context start length access closed base protectedFrames = .ok plan)
    (hl : location ∈ plan.locations) :
    plan.table.leaf (operand plan base location).page = some (aliasLeaf location.frame access) := by
  have hp := prepared_validated _ _ _ _ _ _ _ _ _ h
  have hm := location_frame_in_plan _ _ _ _ _ _ _ _ _ _ h hl
  have hi := List.idxOf_lt_length_of_mem hm
  have hb := hp.2.2.1
  have hf := frame_index_lookup plan.frames location.frame hm
  have hz : plan.frames.idxOf location.frame = 0 ∨ plan.frames.idxOf location.frame = 1 := by omega
  rw [hp.2.2.2]
  rcases hz with hz | hz <;> simp [operand, project, frameLeaf, hz] at hf ⊢ <;> exact ⟨location.frame, hf, rfl⟩

/-- The emitted sequence has one operand per requested byte, including none
for a zero-length request. Mapping the list preserves its validated order. -/
theorem operands_length state context start length access closed base protectedFrames plan
    (h : prepare state context start length access closed base protectedFrames = .ok plan) :
    (operands plan base).length = length := by
  simp only [operands, List.length_map]
  exact validate_length _ _ _ _ _ _ (prepared_validated _ _ _ _ _ _ _ _ _ h).1

/-- Whole-request validation supplies the original authorized byte address for
each location; empty requests contain no locations. -/
theorem validated_location_authorized state context start length access locations location
    (h : validate state context start length access = .ok locations)
    (hl : location ∈ locations) :
    ∃ address, start.toNat ≤ address ∧ address < start.toNat + length ∧
      byteLocation state context address access = .ok location := by
  simp only [validate] at h
  split at h <;> try contradiction
  split at h
  · simp_all
  split at h <;> try contradiction
  split at h <;> try contradiction
  exact validateLoop_authorized _ _ _ _ _ _ h _ hl

/-- A validated offset always lies inside its 4 KiB physical page. -/
theorem validated_offset_bound state context start length access locations location
    (h : validate state context start length access = .ok locations)
    (hl : location ∈ locations) : location.offset < pageBytes := by
  obtain ⟨address, _, _, ha⟩ := validated_location_authorized _ _ _ _ _ _ _ h hl
  cases ht : translate state.virtual context.caller context.activeAddressSpace (address / pageBytes) access with
  | error reason =>
      simp only [byteLocation, ht] at ha
      change Except.error (CopyError.translation reason) = Except.ok location at ha
      contradiction
  | ok frame =>
      simp only [byteLocation, ht] at ha
      change Except.ok ({ virtualPage := address / pageBytes, frame := frame, offset := address % pageBytes } : Location) = Except.ok location at ha
      injection ha with he
      subst location
      exact Nat.mod_lt address (by decide)

/-- Alias operand offsets preserve exactly the validated physical-byte offset,
and remain inside the selected page. -/
theorem operand_offset_exact state context start length access closed base protectedFrames plan location
    (h : prepare state context start length access closed base protectedFrames = .ok plan)
    (hl : location ∈ plan.locations) :
    (operand plan base location).offset = location.offset ∧
      (operand plan base location).offset < pageBytes := by
  exact ⟨rfl, validated_offset_bound _ _ _ _ _ _ _
    (prepared_validated _ _ _ _ _ _ _ _ _ h).1 hl⟩

/-- Selecting a transfer byte preserves the corresponding validated location;
no reordering or additional operand is introduced. -/
theorem operands_at plan base (index : Nat) :
    (operands plan base)[index]? = (plan.locations[index]?).map (operand plan base) := by
  simp [operands]

/-- Any completed operand prefix corresponds to the same location prefix used
by the partial-copy model. -/
theorem operands_prefix plan base completed :
    (operands plan base).take completed =
      (plan.locations.take completed).map (operand plan base) := by
  simp [operands, List.map_take]

end LeanOS.UserCopyOperands
