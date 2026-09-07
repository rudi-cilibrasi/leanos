# ADR 0014: Toolchain compatibility profiles

## Status

Accepted incrementally. The registry records the existing GCC and Clang lanes;
the compatibility workflow adds scheduled observation and a bounded evidence
tier. New component versions still require reviewed, immutable profiles.

## Decision

Separate two claims that a single undifferentiated "supported toolchain" cannot
state precisely:

- one **canonical** profile defines the byte-reproducible reference image; and
- explicit **supported** or **candidate** profiles may establish semantic
  compatibility without requiring their bytes to equal the canonical profile.

`scripts/toolchain-profiles.json` is the reviewed profile registry. Every
profile pins the reference OS and architecture, CI image digest, Lean
toolchain, exact compiler package and observed compiler version, shared image
tools, and versioned Lean/C and final-ELF interface policies. Floating version
ranges and an unversioned or automatically inferred interface are invalid.
There is exactly one canonical profile and it is the default.

The initial registry names the existing GCC 13 environment
`gcc-reference` and the existing Clang 18 environment `clang-reference`. GCC
remains the sole canonical release profile. Clang remains a supported
compatibility profile: it must pass the hosted generated-C boundary, final-ELF
policy, selected QEMU protocol, and, for promoted complete evidence, an
independent same-profile byte-reproducibility comparison. This is meaningful
integration evidence, but it is not a claim that GCC and Clang emit equal
bytes or that either compiler preserves Lean semantics in general.

`LEANOS_TOOLCHAIN_PROFILE` selects a profile. The build resolver checks the
observed compiler family and exact version before compilation, then writes a
deterministic `TOOLCHAIN_PROFILE.json` selection record. That record and the
profile-registry hash are retained in compiler diagnostics, embedded into each
ISO, included in reproducibility and emulator-evidence bundles, and published
with release evidence. A compiler/profile mismatch fails before an image can
be admitted.

Final-ELF normalization is also profile-bound. The GCC profile admits only the
GCC reference layout. The Clang profile adds only the already reviewed Clang
18 site alternatives. Merely installing a compiler with a familiar family or
major version does not select those exceptions.

## Compatibility and promotion policy

Profile status orders evidence, not numerical versions:

1. A **candidate** is exactly pinned and may run non-blocking scheduled or pull
   request evidence.
2. A **supported** profile passes its declared semantic interfaces and required
   integration matrix. Its outputs may differ from the canonical profile.
3. The single **canonical** profile additionally defines release bytes and is
   the subject of the repository's reference reproducibility claim.

Changing a pin creates a reviewed profile change; it does not silently widen an
existing profile. Promoting a future candidate requires a separate pull request
that records its evidence history, makes its required lanes blocking, and
reviews any new interface policy. Replacing the canonical profile additionally
requires an explicit release/reproducibility migration.

The `compatibility-v1` tier runs all Lean library modules, controlled proof and
adapter failures, hosted generated boundaries, a selected image build with
profile-bound final-ELF policy, ELF and serial-validator negatives, and PR-tier
emulator shard 0 of 4. The workflow runs daily and on relevant pull-request
changes. It compares same-revision oracle results, protocol vocabulary, and the
reviewed ELF ownership policy only after each profile passes the production
validators. Exact guest transcripts and debug-exit status are checked by the
existing scenario runners; binary hashes and address-bearing transcript bytes
are not compared across compilers. This is bounded integration evidence, not
equivalence of every execution or every release scenario.

Promotion requires at least 14 consecutive UTC days of successful scheduled
evidence for unchanged profile pins and adapters. Missing, canceled, or failed
days do not count; a changed profile or failed day restarts the window. The
promotion review records run links, profile and registry identities, source
revisions, and measured runtime within the 60-minute lane budget. Before making
a new profile required, run the complete integration tier and review its runner
availability and worst observed runtime. Do not add candidate job names to
required checks. Detailed admission and retirement steps are in the
[compatibility guide](../toolchain-compatibility.md).

## Consequences

LeanOS can distinguish "same inputs reproduce the reference bytes" from "this
other exact stack passes the admitted semantic boundaries." A broken optional
candidate need not invalidate canonical releases, while a supported profile
cannot pass by accidentally borrowing another compiler's ELF exceptions.

The registry does not prove compiler correctness, cross-compiler semantic
equivalence, or compatibility with arbitrary patch releases. The current
profiles still share most of one pinned container stack. Pages now builds in the
pinned canonical environment and deploys a revision-bound bundle, rather than
independently reinstalling exact apt packages on a mutable runner. Adding
profiles increases evidence and maintenance cost,
so each one needs a stated purpose and explicit interfaces rather than a broad
version range.
