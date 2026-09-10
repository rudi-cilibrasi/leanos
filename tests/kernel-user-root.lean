import LeanOS.KernelRootPublication

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


open LeanOS.KernelRootPublication
private def stale : State :=
  { table := source, cache := [{ page := 2, context := supervisorRead, frame := 7 }] }
private def disabled : Controls := { pcid := false, globalPages := false }
-- Removing a mapping without invalidation leaves a real cached authorization.
example : access (replaceOnly stale (close source [7])) 2 supervisorRead = .ok 7 := by rfl
-- The same root still requires a reload when its mappings have changed.
example : (publish (replaceOnly stale (close source [7])) (close source [7]) disabled).effect =
  .reloadRoot := by rfl
example : access (publish stale (close source [7]) disabled).state 2 supervisorRead =
  .error .notPresent := by rfl
example : (publish stale (close source [7]) disabled).state.cache = [] := by rfl
example : access (publish stale (close source [7]) disabled).state 3 supervisorRead = .ok 8 := by rfl
-- A cache entry is specific to its admitted access context.
example : access (replaceOnly stale (close source [7])) 2 { supervisorRead with kind := .write } =
  .error .notPresent := by rfl
-- All unsupported control combinations reject with no effect or mutation.
example : (publish stale (close source [7]) ⟨true, false⟩).accepted = false := by rfl
example : (publish stale (close source [7]) ⟨false, true⟩).state = stale := by rfl
example : (publish stale (close source [7]) ⟨true, true⟩).effect = .none := by rfl
-- Rejection must not be mistaken for closure: the original hit is still usable.
example : access (publish stale (close source [7]) ⟨true, false⟩).state 2 supervisorRead = .ok 7 := by rfl
