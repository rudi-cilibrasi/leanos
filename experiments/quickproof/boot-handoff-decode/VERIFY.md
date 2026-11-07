# Verification of /tmp/claude-1001/-home-ruclaw-src-leanos/d6372f14-0fe3-40f9-be45-4cef73fe2915/scratchpad/leanos-quickproof.xiWFqA/boot_handoff_decode-proof at 8b46d8997637

- date: 2026-11-07 15:24
- framework: quickproof/ at fab76ef826ae (not a release tag of this verifier's repository)
- framework trusted files (16: the statement, the libc, the translation chain): identical to this verifier (/opt/quickproof)
- contract commit: 617fdf3209c9 (`contract`)
- files changed since the contract: 47; frozen files changed: none
- regenerated code.v: identical to the committed files
- the statements compared with: the contract commit's own files with no proof in them (none) and its unit files (src/units.v or src/units/*.v); generated again: src/contracts/handoff_decode_exact.v
- elaborated statement and whole_prog of `handoff_decode_exact`: identical to the contract
- `Admitted`/`admit`/`Axiom`/`Parameter`/`Conjecture` in the Coq sources of the proof (src/ and the other files of _CoqProject; comments excluded): none
- `Print Assumptions` was printed once for all theorems together (of a definition that names each of them): the axioms given for each theorem are those of all of them, an upper bound of its own
- the framework after the translation and the builds: unchanged
- the run: 6 build jobs on 12 CPUs, load 4.0 at the start; checks before the build 0 min, the build and probes 28 min, the contract commit 0 min, in all 28 min

| theorem | result | Print Assumptions |
|---|---|---|
| `handoff_decode_exact` | PROVED | ClassicalDedekindReals.sig_not_dec, ClassicalDedekindReals.sig_forall_dec, Axioms.prop_ext, lib.Axioms.proof_irr, library.mem_mgr, library.malloc_token_valid_pointer, library.malloc_token_local_facts, library.malloc_token, FunctionalExtensionality.functional_extensionality_dep, Eqdep.Eq_rect_eq.eq_rect_eq, library.create_mem_mgr, Classical_Prop.classic, Ensembles.Extensionality_Ensembles |

PASS means: the frozen files, the regenerated Clight and every statement are those of the contract, every statement is QuickProof.Contract.harness_safe on this verifier's framework, and every claimed theorem is proved.

**Verdict: PASS (exit 0).**
