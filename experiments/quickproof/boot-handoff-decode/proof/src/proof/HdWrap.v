(* The bodies of the five wrappers main calls (patch/handoff_unit.c): each forwards its arguments to one function
   of the header.  handoff_extent, handoff_candidate and handoff_project have their callee's specification; the
   copy and the projection alone start their callee's phase at the model's start. *)
Require Import VST.floyd.proofauto.
Require Import LeanosHandoff.handoff.code.
Require Import LeanosHandoff.proof.Defs.
Require Import LeanosHandoff.proof.HandoffSpecs.
Require Import LeanosHandoff.proof.InternalSpecs.
Require Import LeanosHandoff.proof.HdLemmas.
#[local] Existing Instance HandoffSpecs.CS.
Local Open Scope Z_scope.

Lemma body_handoff_extent (Ora: ORA) :
  semax_body Vprog (Gprog Ora) f_handoff_extent (extent_spec Ora).
Proof.
  start_function.
  forward_call (gv, read, ctx, rctx, x, tp, tsh).
  Intros vret. destruct vret as [[h st] T]. cbn [fst snd] in *.
  forward.
  Exists h st T. entailer!.
Qed.

Lemma body_handoff_candidate (Ora: ORA) :
  semax_body Vprog (Gprog Ora) f_handoff_candidate (candidate_spec Ora).
Proof.
  start_function.
  forward_call (gv, ctx, rctx, x, ip, ish, sp, ssh, curp, cursh).
  Intros vret. destruct vret as [[h st] m]. cbn [fst snd] in *.
  forward.
  Exists h st m. entailer!.
Qed.

Lemma body_handoff_project (Ora: ORA) :
  semax_body Vprog (Gprog Ora) f_handoff_project (project_spec Ora).
Proof.
  start_function.
  forward_call (gv, read, ctx, rctx, record, x, h, T, cp, csh, pp, psh, up, bp, rp, bsh, sp, ssh, curp, cursh).
  Intros vret. destruct vret as [[h' st] m]. cbn [fst snd] in *.
  forward.
  Exists h' st m. entailer!.
Qed.

Lemma copy_end_alone (x: inputs) (st: Z) (m: mem) : i_call x = FCopy -> copy_end x st m = Return st m.
Proof. intros C. unfold copy_end. rewrite C. destruct (Z.eqb_spec st S_OK); subst; reflexivity. Qed.

Lemma body_handoff_copy (Ora: ORA) :
  semax_body Vprog (Gprog Ora) f_handoff_copy (copy_spec Ora).
Proof.
  start_function.
  rename H into HC, H0 into IX, H1 into EF, H2 into LC.
  assert (R0: run x (start x) [] = Some (Go (ExpectStreamInit nil) (initial x)))
    by (cbn [run]; unfold start; rewrite HC; reflexivity).
  forward_call (gv, read, ctx, rctx, x, @nil answer, initial x, cp, csh, lp, lsh, vi (i_length_record x)).
  Intros vret. destruct vret as [[hs st] c]. cbn [fst snd] in *. rewrite app_nil_l in *.
  forward.
  Exists hs st (with_copy (initial x) c).
  entailer!.
  - split; [ apply returns_return; rewrite copy_end_alone in H by auto; auto | unfold keeps; rewrite HC; repeat split ].
  - unfold out_length_record, is_copy. rewrite HC. cbn [andb].
    destruct (st =? S_OK); apply derives_refl.
Qed.

Lemma projection_end_alone (x: inputs) (st: Z) (m: mem) : i_call x = FProjection -> projection_end x st m = Return st m.
Proof. intros C. unfold projection_end. rewrite C. destruct (Z.eqb_spec st S_OK); subst; reflexivity. Qed.

Lemma body_handoff_projection (Ora: ORA) :
  semax_body Vprog (Gprog Ora) f_handoff_projection (projection_spec Ora).
Proof.
  start_function.
  rename H into HC, H0 into IX, H1 into EF, H2 into LI.
  assert (D: decoded x (initial x) = i_info x) by (unfold decoded; rewrite HC; reflexivity).
  assert (MO: mem_ok (initial x)).
  { destruct IX as (_ & _ & _ & _ & U & B & R & S & F & _). unfold mem_ok; cbn. repeat split; auto. }
  assert (R0: run x (start x) [] = Some (begin_decode x (initial x)))
    by (cbn [run]; unfold start; rewrite HC; reflexivity).
  assert (P: projection x = true) by (unfold projection; rewrite HC; reflexivity).
  assert (L8: m_total (initial x) / 8 <= Zlength (decoded x (initial x))) by (rewrite D, LI; cbn; lia).
  rewrite <- LI, <- D.
  forward_call (gv, ctx, rctx, record, x, @nil answer, initial x, ip, ish, pp, psh, up, bp, rp, bsh, sp, ssh,
                curp, cursh, vi (i_current_record x)).
  Intros vret. destruct vret as [[[[[[hs st] u] b] r] ss] i]. cbn [fst snd] in *. rewrite app_nil_l in *.
  forward.
  Exists hs st (with_states (with_bitmaps (initial x) u b r) ss i).
  rewrite D, LI.
  entailer!.
  - split; [ apply returns_return; rewrite projection_end_alone in H by auto; auto | unfold keeps; rewrite HC; repeat split ].
  - unfold out_current_record, is_copy. rewrite HC. cbn [andb negb].
    destruct (st =? S_OK); apply derives_refl.
Qed.
