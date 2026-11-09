(* The bodies of the three steps that check without a loop: boot_frame_cross_check and
   boot_frame_publication_check (no call: the model's start returns their check, Defs.cross_check and
   publication_check), and boot_frame_scrub_selected (one call of the scrub, then the model's ExpectScrub). *)
Require Import VST.floyd.proofauto.
Require Import LeanosFrameSelection.frame.code.
Require Import LeanosFrameSelection.proof.Defs.
Require Import LeanosFrameSelection.proof.FrameSpecs.
Require Import LeanosFrameSelection.proof.InternalSpecs.
Require Import LeanosFrameSelection.proof.FsLemmas.
#[local] Existing Instance FrameSpecs.CS.
Local Open Scope Z_scope.

(* A return of a check C of a step that makes no call: the memory as it was. *)
Ltac cret x C := forward; Exists (@nil answer) (C x (i_mem x)) (i_mem x); entailer!; unfold C; zb; reflexivity.

(* A return after the answers of a run R (returns x L = Some (_, _)): its history L. *)
Ltac ret_from R st m := match type of R with returns _ ?L = _ => Exists L st m end.

Lemma body_boot_frame_cross_check (Ora: ORA) :
  semax_body Vprog (Gprog Ora) f_boot_frame_cross_check (boot_cross_check_spec Ora).
Proof.
  start_function.
  rename H into HC, H0 into IX.
  destruct (inputs_facts x IX) as (_ & US & USM & _ & _ & _ & _ & LD & UD & _ & _ & _ & _ & MO).
  pose proof MO as (_ & _ & LT & UT & _).
  destruct (mem_state (i_mem x) 0 MO ltac:(lia)) as [L0 U0].
  assert (R: returns x nil = Some (cross_check x (i_mem x), i_mem x))
    by (apply returns_nil; unfold start; rewrite HC; reflexivity).
  forward_if. { w64. cret x cross_check. } w64.
  forward. forward_if. { w64. cret x cross_check. } w64.
  forward. forward_if. { w64. cret x cross_check. } w64.
  forward. forward. forward_if. { w64. cret x cross_check. } w64.
  forward. forward. forward_if. { w64. cret x cross_check. } w64.
  forward. forward_if. { w64. cret x cross_check. } w64.
  forward. forward_if. { w64. cret x cross_check. } w64.
  forward_if. { w64. cret x cross_check. } w64.
  cret x cross_check.
Qed.

Lemma body_boot_frame_publication_check (Ora: ORA) :
  semax_body Vprog (Gprog Ora) f_boot_frame_publication_check (boot_publication_check_spec Ora).
Proof.
  start_function.
  rename H into HC, H0 into IX.
  destruct (inputs_facts x IX) as (_ & US & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MO).
  pose proof MO as (_ & _ & _ & _ & _ & _ & LP & UP & _).
  assert (R: returns x nil = Some (publication_check x (i_mem x), i_mem x))
    by (apply returns_nil; unfold start; rewrite HC; reflexivity).
  forward. forward_if. { w64. cret x publication_check. } w64.
  forward. forward_if. { w64. cret x publication_check. } w64.
  forward. forward_if. { w64. cret x publication_check. } w64.
  forward. forward_if. { w64. cret x publication_check. } w64.
  forward. forward_if. { w64. cret x publication_check. } w64.
  cret x publication_check.
Qed.

Lemma body_boot_frame_scrub_selected (Ora: ORA) :
  semax_body Vprog (Gprog Ora) f_boot_frame_scrub_selected (boot_scrub_selected_spec Ora).
Proof.
  start_function.
  rename H into HC, H0 into IX.
  assert (R0: run x (start x) nil = Some (Go ExpectScrub (i_mem x)))
    by (cbn [run]; unfold start; rewrite HC; reflexivity).
  forward_call (gv, dctx, sctx, sp, x, @nil answer, i_selected x).
  { apply (next_call_go _ _ _ _ R0). }
  Intros v. rename H into Uv.
  pose proof (run_word x (start x) nil ExpectScrub (i_mem x) v R0 ltac:(intros; discriminate)) as R1.
  cbn [expected step reply_value] in R1.
  pose proof (returns_return _ _ _ _ R1) as R.
  forward_if.
  { w64. forward. ret_from R S_SCRUB (i_mem x). entailer!; zb_in R; exact R. }
  w64. forward. ret_from R S_OK (i_mem x). entailer!; zb_in R; exact R.
Qed.
