# Toolchain compatibility evidence

## Claims and scope

The canonical `gcc-reference` profile defines release bytes. A candidate or
supported profile establishes a narrower claim: the same source passes the
reviewed proof, generated-boundary, final-ELF, and guest contracts under that
exact stack. The compiler, linker, firmware, emulator, adapters, and validators
remain trusted integration components, not Lean-verified implementations.
[ADR 0014](adr/0014-toolchain-compatibility-profiles.md) defines these claims.

The separate **Toolchain compatibility** workflow runs daily at 04:23 UTC, on
manual dispatch, and on pull requests changing build, proof, boundary, test, or
workflow inputs. It selects every registry entry, including the canonical
baseline. A candidate failure stays visibly failed but is not a required
admission check and cannot publish or replace release artifacts. Existing
required GCC and Clang lanes are unchanged. Scheduled workflows start running
after this workflow reaches the default branch.

## Evidence tier

Every profile declares `evidence_tier: compatibility-v1`. The runner first
checks its declared container digest, architecture, installed package pins,
and active Lean/C compilers. It then builds the Lean library and negative
fixtures, requires the controlled `sorry` proof to fail, and replays the hosted
generated-boundary inventory with adapter mutations. The selected image build
checks its generated interface and final-ELF policy; explicit ELF and serial
negative fixtures follow. Finally, the runner executes and independently
verifies PR-tier emulator shard 0 of 4, using the existing deterministic matrix
selection. It stops at the first failed phase and retains a failed report.

The cross-profile job requires one successful report for every current profile,
the current checkout revision and registry hash, every evidence phase, and the
exact selected guest scenario inventory. It rehashes retained oracle output,
hosted results, serial vocabulary, and ELF ownership policy before comparing
them. Each guest runner has already checked its exact protocol and expected
debug-exit outcome. It does not equate different ISO hashes, instruction
addresses, or arbitrary compiler output. A missing artifact, canceled lane,
changed contract, or matching failure from every profile cannot become success.

Reports and per-phase logs are retained for 30 days in
`toolchain-compatibility-PROFILE` artifacts. The report records exact profile
data, source and registry identity, timestamps, completed phases, semantic
hashes, and guest outcomes. Download the artifacts before their expiry when
preparing a promotion review. This bounded tier is not the full release matrix
and is not a substitute for canonical independent-runner byte comparison.

To inspect selection and run a profile inside its declared x86-64 container:

```sh
python3 scripts/toolchain-compatibility.py matrix
export LEANOS_CI_IMAGE_DIGEST=sha256:THE_REVIEWED_DIGEST
python3 scripts/toolchain-compatibility.py run --profile clang-reference
python3 scripts/toolchain-compatibility.py compare downloaded/*/report.json
```

The digest variable is an assertion supplied by the digest-pinned CI job, not
independent proof of a local container's identity. Local callers must use the
actual declared image. Keep each run in a separate clean checkout; the runner
uses the project's normal `build/` paths.

## Introducing and promoting a profile

Register a new stable ID with `candidate` status, an immutable image digest,
exact component inventory, and named interface policies. An optional
`apt_packages` list supplies the complete package-name inventory at independent
exact versions; omission inherits `canonical_apt_packages`. Compiler and shared
tool declarations must agree with that selected inventory. A canonical entry
cannot override the canonical inventory. No workflow resolves `latest`, installs
ambient upgrades, or automatically blesses a newly observed compiler layout.

The current adapters admit Lean 4.32.0 with GCC 13 or Clang 18 and their reviewed
ELF shapes. Another Lean interface or compiler family/major needs a reviewed
resolver and adapter change plus controlled negatives; adding a version string
alone is insufficient. Scheduled observation exercises registered immutable
stacks, including their availability. It does not scrape upstream releases or
predict which future unregistered package version will break. A maintainer
must first publish and register the exact stack to observe it.

Observe unchanged candidate pins and adapters for at least 14 consecutive UTC
days. Require a successful scheduled matrix on every day; missing or canceled
days break continuity, and failure or changed pins/adapters restart observation.
Preserve links and downloaded reports with source revisions and registry hashes
so changes to unrelated source do not obscure what was tested. Record maximum
and typical lane duration, all attempted runs, and any diagnosis. An unrelated
registry edit is acceptable only when the review confirms that the candidate's
pins and adapters were unchanged.

Promotion is a separate reviewed PR. Include that history, complete integration
evidence beyond this bounded tier, and confirmation that runner availability
and runtime fit the required lane budget. Change the status to `supported` and
explicitly wire its required lane into the admission policy. Merely changing
status does not configure GitHub required checks. Existing supported profiles
are not retroactively demoted by this observation policy.

Retire a profile in a separate PR after its replacement is admitted: remove its
required lane and registry entry together, document the reason and replacement,
and preserve its historical evidence in the PR. Never retire the canonical
profile implicitly. A canonical migration requires an explicit release-input
change, independent-runner reproducibility, and updated deployment consumers.

## Engineering note — 2026-09-06

Equal results are insufficient if both runners skipped the same test or failed
in the same way. Compatibility comparison therefore checks completeness against
the repository-owned scenario selection before comparing successful results.
Likewise, compiler normalization is a small reviewed policy, not an instruction
to ignore all differing bytes. Keeping these checks separate lets tool versions
change without weakening the boundary that the evidence is meant to test.
