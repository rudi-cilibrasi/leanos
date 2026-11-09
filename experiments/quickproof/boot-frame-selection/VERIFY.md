# Verification of /tmp/claude-1001/-home-ruclaw-src-leanos/b9e1665f-65a4-4878-8f5f-b19c4976f77a/scratchpad/leanos-quickproof.D7Qgzv/boot_frame_selection-proof at b0494ceaf016

- date: 2026-11-09 10:55
- framework: quickproof/ at fab76ef826ae (not a release tag of this verifier's repository)
- framework trusted files (16: the statement, the libc, the translation chain): identical to this verifier (/opt/quickproof)
- contract commit: 65cfc3162226 (`contract`)
- files changed since the contract: 48; frozen files changed: none
- regenerated code.v: identical to the committed files
- the statements compared with: the contract commit's own files with no proof in them (none) and its unit files (src/units.v or src/units/*.v); generated again: src/contracts/frame_selection_exact.v
- elaborated statement and whole_prog of `frame_selection_exact`: identical to the contract
- `Admitted`/`admit`/`Axiom`/`Parameter`/`Conjecture` in the Coq sources of the proof (src/ and the other files of _CoqProject; comments excluded): none
- `Print Assumptions` was printed once for all theorems together (of a definition that names each of them): the axioms given for each theorem are those of all of them, an upper bound of its own
- the framework after the translation and the builds: unchanged
- the run: 6 build jobs on 12 CPUs, load 2.6 at the start; checks before the build 0 min, the build and probes 41 min, the contract commit 0 min, in all 42 min

| theorem | result | Print Assumptions |
|---|---|---|
| `frame_selection_exact` | PROVED | ClassicalDedekindReals.sig_not_dec, ClassicalDedekindReals.sig_forall_dec, Axioms.prop_ext, lib.Axioms.proof_irr, library.mem_mgr, library.malloc_token_valid_pointer, library.malloc_token_local_facts, library.malloc_token, FunctionalExtensionality.functional_extensionality_dep, Eqdep.Eq_rect_eq.eq_rect_eq, library.create_mem_mgr, Classical_Prop.classic, Ensembles.Extensionality_Ensembles |

PASS means: the frozen files, the regenerated Clight and every statement are those of the contract, every statement is QuickProof.Contract.harness_safe on this verifier's framework, and every claimed theorem is proved.

**Verdict: PASS (exit 0).**
