# The one list of record names the boot images print and the checkers expect

Every line the kernel writes to its serial port during a scenario starts with a versioned record prefix, `LEANOS/<version> <TAG>`, and the scripts that judge a boot look for exactly those prefixes. This file is the single Lean-owned list of every such family version and record tag. The build renders it into the C header the kernel and assembly compile against and into the shell fragment the runner scripts source, so no C file, assembly file, runner, checker, or fake-guest fixture spells a record identity by hand. The theorems below check that the list is sound: no two families share a version number, no record identity appears twice, every pre-admission rejection reason is unique, every scenario-specific pre-admission boot and later phase identity is unique and belongs to the protocol vocabulary, and every family names at least one record.

- `family_versions_nodup` — No two protocol families share a version number, so a `LEANOS/<version>` prefix identifies exactly one family.
- `records_nodup` — No record identity (family version paired with tag) appears twice in the vocabulary, so a generated macro or shell variable names exactly one record.
- `pre_admission_rejection_reasons_nodup` — No pre-admission failure reason appears twice, so the generated bare-metal rejection vocabulary classifies each admitted reason exactly once.
- `pre_admission_bootalloc_rejection_reasons_nodup` — No boot-allocation rejection reason appears twice, so the generated classifier binds each terminal allocation failure to one canonical reason.
- `pre_admission_boot_records_nodup` — No scenario-specific boot identity appears twice in the pre-admission set.
- `pre_admission_boot_records_are_protocol_records` — Every scenario-specific pre-admission boot identity is an existing version-and-tag pair in the serial protocol vocabulary.
- `pre_admission_phase_records_nodup` — No post-boot record identity appears twice in the generated pre-admission phase set.
- `pre_admission_phase_records_are_protocol_records` — Every post-boot pre-admission phase identity belongs to the serial protocol vocabulary.
- `families_nonempty` — Every family in the vocabulary lists at least one record, so no version number is reserved without a record that uses it.
