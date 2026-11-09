(* The bodies of the seven wrappers main calls (patch/frame_unit.c): each forwards its arguments to one function
   of the header, which has the wrapper's specification (InternalSpecs.v). *)
Require Import VST.floyd.proofauto.
Require Import LeanosFrameSelection.frame.code.
Require Import LeanosFrameSelection.proof.Defs.
Require Import LeanosFrameSelection.proof.FrameSpecs.
Require Import LeanosFrameSelection.proof.InternalSpecs.
#[local] Existing Instance FrameSpecs.CS.
Local Open Scope Z_scope.

Lemma body_frame_terminal (Ora: ORA) :
  semax_body Vprog (Gprog Ora) f_frame_terminal (frame_terminal_spec Ora).
Proof.
  start_function.
  forward_call (gv, dctx, sctx, sp, x, mp, dp, up, bp, rp, tp, rsh, wsh).
  Intros vret. destruct vret as [[h st] m]. cbn [fst snd] in *.
  forward.
  Exists h st m. entailer!.
Qed.

Lemma body_frame_select (Ora: ORA) :
  semax_body Vprog (Gprog Ora) f_frame_select (frame_select_spec Ora).
Proof.
  start_function.
  forward_call (gv, decode, dctx, sctx, sp, x, mp, selp, smp, np, dsp, rsh, wsh).
  Intros vret. destruct vret as [[h st] m]. cbn [fst snd] in *.
  forward.
  Exists h st m. entailer!.
Qed.

Lemma body_frame_cross_check (Ora: ORA) :
  semax_body Vprog (Gprog Ora) f_frame_cross_check (frame_cross_check_spec Ora).
Proof.
  start_function.
  forward_call (gv, dctx, sctx, sp, x, tp, dp, p0, rsh).
  Intros vret. destruct vret as [[h st] m]. cbn [fst snd] in *.
  forward.
  Exists h st m. entailer!.
Qed.

Lemma body_frame_scrub_selected (Ora: ORA) :
  semax_body Vprog (Gprog Ora) f_frame_scrub_selected (frame_scrub_selected_spec Ora).
Proof.
  start_function.
  forward_call (gv, scrub, dctx, sctx, sp, x).
  Intros vret. destruct vret as [[h st] m]. cbn [fst snd] in *.
  forward.
  Exists h st m. entailer!.
Qed.

Lemma body_frame_publication_result (Ora: ORA) :
  semax_body Vprog (Gprog Ora) f_frame_publication_result (frame_publication_result_spec Ora).
Proof.
  start_function.
  forward_call (gv, dctx, sctx, sp, x, p0, pp, rsh, wsh).
  Intros vret. destruct vret as [h m]. cbn [fst snd] in *.
  Exists h m. entailer!.
Qed.

Lemma body_frame_publication_check (Ora: ORA) :
  semax_body Vprog (Gprog Ora) f_frame_publication_check (frame_publication_check_spec Ora).
Proof.
  start_function.
  forward_call (gv, dctx, sctx, sp, x, pp, rsh).
  Intros vret. destruct vret as [[h st] m]. cbn [fst snd] in *.
  forward.
  Exists h st m. entailer!.
Qed.

Lemma body_frame_rescan (Ora: ORA) :
  semax_body Vprog (Gprog Ora) f_frame_rescan (frame_rescan_spec Ora).
Proof.
  start_function.
  forward_call (gv, decode, dctx, sctx, sp, x, mp, dp, rp, dsp, rsh, wsh).
  Intros vret. destruct vret as [[h st] m]. cbn [fst snd] in *.
  forward.
  Exists h st m. entailer!.
Qed.
