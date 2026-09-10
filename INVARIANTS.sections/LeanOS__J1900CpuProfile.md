# Checking the measured J1900 CPU capabilities

The selector checks a versioned snapshot of five processor-identification queries against the measured Qotom J1900 profile. These proofs concern the supplied words and the selection logic; they do not prove that the hardware queries ran, that control registers were configured, or that the machine can safely run user programs.

- `selection_requires_all_checks` — A successful selection means none of the selector's version, presence, identity, or feature checks rejected the supplied snapshot.
- `selection_does_not_authorize_cpl3` — Selecting the CPU profile leaves permission to enter user mode disabled. Other platform and isolation requirements still need to be established.
- `selection_requires_measured_capabilities` — Successful selection requires the supplied legacy and extended feature masks, SMEP support, and the measured absence of XSAVE, OSXSAVE, AVX, and SMAP; the result cannot simply assert those capabilities without checking the snapshot.
