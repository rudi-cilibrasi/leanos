import LeanOS.KernelUserRoot

open LeanOS.X86PageTable LeanOS.KernelUserRoot

private def supervisorRead : AccessContext :=
  { privilege := .supervisor, kind := .read, writeProtect := true,
    nxEnable := true, smep := true, smap := false, ac := false }

private def source : PageTable :=
  { pml4 := ⟨true, true, true⟩, pdpt := ⟨true, true, true⟩,
    pd := ⟨true, true, true⟩
    leaf := fun page =>
      if page == 1 then some ⟨7, true, false, true, true, true⟩
      else if page == 2 then some ⟨7, true, true, false, false, true⟩
      else if page == 3 then some ⟨8, true, true, false, false, true⟩
      else none }

-- With SMAP absent, the user mapping and its supervisor alias are both readable.
example : classify source 1 supervisorRead = .ok 7 := by rfl
example : classify source 2 supervisorRead = .ok 7 := by rfl
-- Filtering the physical frame removes both aliases, regardless of U/S flags.
example : classify (close source [7]) 1 supervisorRead = .error .notPresent := by rfl
example : classify (close source [7]) 2 supervisorRead = .error .notPresent := by rfl
example : classify (close source [7]) 2 { supervisorRead with kind := .write } =
    .error .notPresent := by rfl
example : classify (close source [7]) 2 { supervisorRead with kind := .execute } =
    .error .notPresent := by rfl
-- An unrelated supervisor mapping keeps its frame and permissions.
example : classify (close source [7]) 3 supervisorRead = .ok 8 := by rfl
example : (close source [7]).leaf 3 = source.leaf 3 := by rfl
-- An incomplete inventory cannot establish exclusion: this is a precondition.
example : classify (close source []) 2 supervisorRead = .ok 7 := by rfl
-- Applying cleanup twice does not recreate a mapping.
example : (close (close source [7]) [7]).leaf 2 = none := by rfl
