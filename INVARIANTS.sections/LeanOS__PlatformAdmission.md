# Closed platform admission

This module selects exactly one complete q35 or Qotom platform manifest from a closed identifier and version. It rejects mixed components before granting the bounded CPL3 authority, then carries the selected profile unchanged through a finite runtime whose explicit AP-start operation can only enter an absorbing halt.

- `profile_ids_distinct` — The numeric identities of the q35 version-one and Qotom J1900 CLBTM210 version-two profiles are different.
- `accepted_identifies_complete_profile` — Every successful admission implies that every supplied component and acceptance word matches the complete manifest selected by the returned profile.
- `accepted_profile_unique` — One raw platform observation cannot be admitted as two different profiles.
- `cross_profile_firmware_splice_rejected` — Replacing the q35 firmware-root identity with the Qotom identity produces the stable firmware-root rejection.
- `runtime_preserves_profile` — Every single modeled runtime operation leaves the admitted profile identity unchanged.
- `runtime_never_publishes_ap_start` — A runtime that has not published an AP start still has not published one after any operation, including an attempted AP start.
- `forbidden_ap_start_fail_stops` — An AP-start attempt from an admitted initial runtime enters the typed forbidden-AP-start halt and leaves the AP-start field false.
- `halted_absorbing` — Once the platform runtime is halted, every operation returns the exact same state.
- `run_preserves_profile` — Every finite modeled operation sequence preserves the admitted profile identity.
- `run_never_publishes_ap_start` — Every finite modeled operation sequence starting with no AP start keeps the AP-start field false.
