import LeanOS.DMAQuarantine

open LeanOS DMAQuarantine

-- Acceptance accounts for the entry, so a universal absent claim is false.
example (accepted : AcceptedSnapshot) (entry : ManifestEntry) (hentry : entry ∈ q35Manifest) :
    ¬ ∃ function ∈ accepted.snapshot.functions, function.bdf = entry.bdf := by
  exact accepted_accounts_every_manifest_entry accepted entry hentry
