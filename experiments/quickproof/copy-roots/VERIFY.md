# Verification of TMP/copy_roots-proof at c869517fa8ea

- date: 2026-11-06 07:30
- framework: quickproof/ at fab76ef826ae (not a release tag of this verifier's repository)
- framework trusted files (16: the statement, the libc, the translation chain): identical to this verifier (/opt/quickproof)
- contract commit: 916b01028600 (`contract`)
- files changed since the contract: 38; frozen files changed: none
- regenerated code.v: identical to the committed files
- the statements compared with: the contract commit's own files with no proof in them (none) and its unit files (src/units.v or src/units/*.v); generated again: src/contracts/copy_roots_exact.v, src/contracts/suite.v, src/contracts/window_roots_isolated.v, src/contracts/window_scan_exact.v
- elaborated statement and whole_prog of `copy_roots_exact`: identical to the contract
- elaborated statement and whole_prog of `suite`: identical to the contract
- elaborated statement and whole_prog of `window_roots_isolated`: identical to the contract
- elaborated statement and whole_prog of `window_scan_exact`: identical to the contract
- `Admitted`/`admit`/`Axiom`/`Parameter`/`Conjecture` in the Coq sources of the proof (src/ and the other files of _CoqProject; comments excluded): none
- `Print Assumptions` was printed once for all theorems together (of a definition that names each of them): the axioms given for each theorem are those of all of them, an upper bound of its own
- the framework after the translation and the builds: unchanged
- the run: 6 build jobs on 12 CPUs, load 5.6 at the start; checks before the build 0 min, the build and probes 52 min, the contract commit 0 min, in all 53 min

| theorem | result | Print Assumptions |
|---|---|---|
| `copy_roots_exact` | PROVED | ClassicalDedekindReals.sig_not_dec, ClassicalDedekindReals.sig_forall_dec, Axioms.prop_ext, lib.Axioms.proof_irr, library.mem_mgr, library.malloc_token, FunctionalExtensionality.functional_extensionality_dep, Eqdep.Eq_rect_eq.eq_rect_eq, Classical_Prop.classic, Ensembles.Extensionality_Ensembles |
| `suite` | PROVED | ClassicalDedekindReals.sig_not_dec, ClassicalDedekindReals.sig_forall_dec, Axioms.prop_ext, lib.Axioms.proof_irr, library.mem_mgr, library.malloc_token, FunctionalExtensionality.functional_extensionality_dep, Eqdep.Eq_rect_eq.eq_rect_eq, Classical_Prop.classic, Ensembles.Extensionality_Ensembles |
| `window_roots_isolated` | PROVED | ClassicalDedekindReals.sig_not_dec, ClassicalDedekindReals.sig_forall_dec, Axioms.prop_ext, lib.Axioms.proof_irr, library.mem_mgr, library.malloc_token, FunctionalExtensionality.functional_extensionality_dep, Eqdep.Eq_rect_eq.eq_rect_eq, Classical_Prop.classic, Ensembles.Extensionality_Ensembles |
| `window_scan_exact` | PROVED | ClassicalDedekindReals.sig_not_dec, ClassicalDedekindReals.sig_forall_dec, Axioms.prop_ext, lib.Axioms.proof_irr, library.mem_mgr, library.malloc_token, FunctionalExtensionality.functional_extensionality_dep, Eqdep.Eq_rect_eq.eq_rect_eq, Classical_Prop.classic, Ensembles.Extensionality_Ensembles |

PASS means: the frozen files, the regenerated Clight and every statement are those of the contract, every statement is QuickProof.Contract.harness_safe on this verifier's framework, and every claimed theorem is proved.

**Verdict: PASS (exit 0).**
