# The one list of record names the boot images print and the checkers expect

Every line the kernel writes to its serial port during a scenario starts with a versioned record prefix, `LEANOS/<version> <TAG>`, and the scripts that judge a boot look for exactly those prefixes. This file is the single Lean-owned list of every such family version and record tag. The build renders it into the C header the kernel and assembly compile against and into the shell fragment the runner scripts source, so no C file, assembly file, runner, checker, or fake-guest fixture spells a record identity by hand. The theorems below check that the list is sound: no two families share a version number, no record identity appears twice, and every family names at least one record.

- `family_versions_nodup` — No two protocol families share a version number, so a `LEANOS/<version>` prefix identifies exactly one family.
- `records_nodup` — No record identity (family version paired with tag) appears twice in the vocabulary, so a generated macro or shell variable names exactly one record.
- `families_nonempty` — Every family in the vocabulary lists at least one record, so no version number is reserved without a record that uses it.
