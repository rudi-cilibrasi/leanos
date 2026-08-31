# ADR 0014: Toolchain compatibility profiles

## Status

Accepted incrementally; this first slice records the existing GCC and Clang
lanes. Candidate-profile automation and promotion history remain future work in
issue #275.

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
requires an explicit release/reproducibility migration. The larger scheduled
candidate matrix should be coordinated with issue #266 so it does not recreate
unbounded per-commit CI cost.

## Consequences

LeanOS can distinguish "same inputs reproduce the reference bytes" from "this
other exact stack passes the admitted semantic boundaries." A broken optional
candidate need not invalidate canonical releases, while a supported profile
cannot pass by accidentally borrowing another compiler's ELF exceptions.

The registry does not prove compiler correctness, cross-compiler semantic
equivalence, or compatibility with arbitrary patch releases. The current
profiles still share most of one pinned container stack, and mutable external
publishing inputs such as the Pages dependency installation need their own
follow-up hardening. Adding profiles increases evidence and maintenance cost,
so each one needs a stated purpose and explicit interfaces rather than a broad
version range.
