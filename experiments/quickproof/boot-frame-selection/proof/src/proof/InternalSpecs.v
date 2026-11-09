(* Specifications of the seven functions of include/boot_frame_selection.h (static inline, each kept as a function
   by clightgen), and Gprog, the specifications the body proofs are stated against.  A starting point for the
   body proofs, which may revise them; the interface the law depends on (the oracle, the callees and the seven
   wrappers) is FrameSpecs.v.

   Each wrapper of patch/frame_unit.c only forwards its arguments to one of the header's functions, so each of
   them has its wrapper's specification: one step of Defs, from start to its return.  Their loops are phases of
   the step's run, from the model's progress at an iteration's start to the next (the body proofs' invariants):
   - boot_frame_terminal: block b of the overlay at Go (ExpectManifest b ms me fw nil) m, after the blocks before
     it (reserved words 0 .. b - 1 and the free words fw written), then Go (ExpectFinish 0 ms me fw) m; word q
     of the terminal result at Go (ExpectFinish q ms me fw) m, after words 0 .. q - 1, then
     Return (terminal_check x m) m;
   - boot_frame_select: candidate c at Go (ExpectDecode c k f fm) m, with the scan k and the selection (f, fm)
     so far in the locals scan, first and first_manifest (second is 4096 until the scan stops), and each way out
     of the loop at select_done (a break) or next_candidate after candidate 4095 (the loop's end);
   - boot_frame_publication_result: word q at Go (ExpectAuthority q) m, then Return S_OK m.
   The model's memory changes only through Defs' with_* functions, so what a phase leaves alone is plain. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import LeanosFrameSelection.frame.code.
Require Import LeanosFrameSelection.proof.Defs.
Require Import LeanosFrameSelection.proof.FrameSpecs.
#[local] Existing Instance FrameSpecs.CS.

Definition boot_terminal_spec Ora := terminal_pre_post Ora _boot_frame_terminal.
Definition boot_select_spec Ora := select_pre_post Ora _boot_frame_select.
Definition boot_cross_check_spec Ora := cross_check_pre_post Ora _boot_frame_cross_check.
Definition boot_scrub_selected_spec Ora := scrub_selected_pre_post Ora _boot_frame_scrub_selected.
Definition boot_publication_result_spec Ora := publication_result_pre_post Ora _boot_frame_publication_result.
Definition boot_publication_check_spec Ora := publication_check_pre_post Ora _boot_frame_publication_check.
Definition boot_rescan_spec Ora := rescan_pre_post Ora _boot_frame_rescan.

Definition Gprog (Ora: ORA) : funspecs :=
  [manifest_spec Ora; free_spec Ora; finish_spec Ora; candidate_spec Ora; consume_spec Ora; authority_spec Ora;
   boot_terminal_spec Ora; boot_select_spec Ora; boot_cross_check_spec Ora; boot_scrub_selected_spec Ora;
   boot_publication_result_spec Ora; boot_publication_check_spec Ora; boot_rescan_spec Ora;
   frame_terminal_spec Ora; frame_select_spec Ora; frame_cross_check_spec Ora; frame_scrub_selected_spec Ora;
   frame_publication_result_spec Ora; frame_publication_check_spec Ora; frame_rescan_spec Ora].
