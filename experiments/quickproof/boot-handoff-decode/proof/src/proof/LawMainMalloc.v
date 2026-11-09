(* Law handoff_decode_exact: main's eight mallocs (the copy and copy_expect, the words a decoder alone reads and
   info_expect, the three bitmaps, the two states) and its return when one fails; then the fills (fill_ok). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env QuickProof.Assembly.
Require Import LeanosHandoff.harness.handoff_decode_exact.code.
Require Import LeanosHandoff.proof.Defs.
Require Import LeanosHandoff.proof.HandoffSpecs.
Require Import LeanosHandoff.proof.LawProg LeanosHandoff.proof.LawDefs LeanosHandoff.proof.LawFacts
  LeanosHandoff.proof.LawLib LeanosHandoff.proof.LawLib2 LeanosHandoff.proof.LawZero
  LeanosHandoff.proof.LawMainDefs LeanosHandoff.proof.LawMainPre.
Local Open Scope Z_scope.
Local Open Scope bool_scope.
#[local] Existing Instance LawProg.LCS.

Lemma drop_TT: forall P: mpred, (P * TT)%logic |-- TT.
Proof. intros. apply TT_right. Qed.

Lemma tail_malloc {Espec: OracleKind} (TF: @fill_ok Espec): @malloc_ok Espec.
Proof.
  intros gv cc mg ad T0 cd vtr vlr vcr vpj Hx.
  unfold malloc_pre, s_malloc. start_tail_main.
  set (X := x0 cc mg ad T0 cd).
  pose proof Hx as (Rcc & Rmg & Rad & Rtt & Rcd & Ext). unfold u32_ok, u64_ok in Rmg, Rad, Rtt, Rcd.
  assert (Rcl: copy_len X = 0 \/ copy_len X = 8192)
    by (unfold copy_len; destruct (i_call X); auto).
  assert (Ril: 0 <= info_len X <= 8192).
  { unfold info_len, is_alloc, X, x0; cbn [i_call i_total]. destruct (call_of cc) eqn:C; try lia;
      (assert (N: cc <> 0) by (intro; subst; discriminate); destruct (Ext N) as [E1 E2];
       split; [ apply Z.div_pos | apply Z.div_le_upper_bound ]; lia). }
  assert (Eil: info_len X = if cc =? 0 then 0 else T0 / 8).
  { unfold info_len, is_alloc, X, x0, call_of; cbn [i_call i_total].
    assert (cc = 0 \/ cc = 1 \/ cc = 2 \/ cc = 3) as [-> | [-> | [-> | ->]]] by lia; reflexivity. }
  forward_call (tarray tulong (copy_len X), gv).
  { entailer!. simpl. rewrite ?Z.max_r by lia. do 3 f_equal. lia. }
  { simpl. rewrite Z.max_r by lia. destruct Rcl as [-> | ->]; rep_lia. }
  Intros cp. change (if eq_dec cp nullval then emp else _) with (mres (tarray tulong (copy_len X)) cp).
  forward_call (tarray tulong (copy_len X), gv).
  { entailer!. simpl. rewrite ?Z.max_r by lia. do 3 f_equal. lia. }
  { simpl. rewrite Z.max_r by lia. destruct Rcl as [-> | ->]; rep_lia. }
  Intros cep. change (if eq_dec cep nullval then emp else _) with (mres (tarray tulong (copy_len X)) cep).
  unfold fields0, lraw. Intros.
  replace (call_code (i_call X)) with cc by (unfold X; rewrite x0_call, call_code_of by lia; reflexivity).
  forward.
  forward_if (temp _t'12 (vi (info_len X))).
  { forward. entailer!. all: rewrite Eil; destruct (Z.eqb_spec cc 0); [ reflexivity | exfalso; u64c; lia ]. }
  { forward. forward. entailer!. all: rewrite Eil; destruct (Z.eqb_spec cc 0); [ exfalso; u64c; lia | ].
    all: change (i_total X) with T0; unfold Int.divu; rewrite !Int.unsigned_repr by rep_lia; reflexivity. }
  forward.
  forward_call (tarray tulong (info_len X), gv).
  { entailer!. simpl. rewrite ?Z.max_r by lia. do 3 f_equal. lia. }
  { simpl. rewrite Z.max_r by lia. rep_lia. }
  Intros ip. change (if eq_dec ip nullval then emp else _) with (mres (tarray tulong (info_len X)) ip).
  forward_call (tarray tulong (info_len X), gv).
  { entailer!. simpl. rewrite ?Z.max_r by lia. do 3 f_equal. lia. }
  { simpl. rewrite Z.max_r by lia. rep_lia. }
  Intros iep. change (if eq_dec iep nullval then emp else _) with (mres (tarray tulong (info_len X)) iep).
  forward_call (tarray tulong 64, gv).
  { simpl. rep_lia. }
  Intros up. change (if eq_dec up nullval then emp else _) with (mres (tarray tulong 64) up).
  forward_call (tarray tulong 64, gv).
  { simpl. rep_lia. }
  Intros bp. change (if eq_dec bp nullval then emp else _) with (mres (tarray tulong 64) bp).
  forward_call (tarray tulong 64, gv).
  { simpl. rep_lia. }
  Intros rp. change (if eq_dec rp nullval then emp else _) with (mres (tarray tulong 64) rp).
  forward_call (t_states, gv).
  { simpl. rep_lia. }
  Intros sp. change (if eq_dec sp nullval then emp else _) with (mres t_states sp).
  (* the return when a malloc failed *)
  assert_PROP (is_pointer_or_null cp) as Ncp by (unfold mres; destruct (eq_dec cp nullval); entailer!).
  assert_PROP (is_pointer_or_null cep) as Ncep by (unfold mres; destruct (eq_dec cep nullval); entailer!).
  assert_PROP (is_pointer_or_null ip) as Nip by (unfold mres; destruct (eq_dec ip nullval); entailer!).
  assert_PROP (is_pointer_or_null iep) as Niep by (unfold mres; destruct (eq_dec iep nullval); entailer!).
  assert_PROP (is_pointer_or_null up) as Nup by (unfold mres; destruct (eq_dec up nullval); entailer!).
  assert_PROP (is_pointer_or_null bp) as Nbp by (unfold mres; destruct (eq_dec bp nullval); entailer!).
  assert_PROP (is_pointer_or_null rp) as Nrp by (unfold mres; destruct (eq_dec rp nullval); entailer!).
  assert_PROP (is_pointer_or_null sp) as Nsp by (unfold mres; destruct (eq_dec sp nullval); entailer!).
  forward_if (temp _t'19 (Vint (Int.repr (Z.b2z (isnul cp || isnul cep))))).
  { apply (mres_tc' (tarray tulong (copy_len X)) cp _ TT). cancel. }
  { forward. entailer!. }
  { forward. { entailer!. apply (mres_tc' (tarray tulong (copy_len X)) cep _ TT). cancel. }
    entailer!. rewrite null_test by auto. rewrite (isnul_false cp) by auto. reflexivity. }
  forward_if (temp _t'20 (Vint (Int.repr (Z.b2z (isnul cp || isnul cep || isnul ip))))).
  { try b2z_hyp. forward. entailer!. rw_bools. reflexivity. }
  { try b2z_hyp. forward. { entailer!. apply (mres_tc' (tarray tulong (info_len X)) ip _ TT). cancel. }
    entailer!. rewrite null_test by auto. rw_bools. reflexivity. }
  forward_if (temp _t'21 (Vint (Int.repr (Z.b2z (isnul cp || isnul cep || isnul ip || isnul iep))))).
  { try b2z_hyp. forward. entailer!. rw_bools. reflexivity. }
  { try b2z_hyp. forward. { entailer!. apply (mres_tc' (tarray tulong (info_len X)) iep _ TT). cancel. }
    entailer!. rewrite null_test by auto. rw_bools. reflexivity. }
  forward_if (temp _t'22 (Vint (Int.repr (Z.b2z (isnul cp || isnul cep || isnul ip || isnul iep || isnul up))))).
  { try b2z_hyp. forward. entailer!. rw_bools. reflexivity. }
  { try b2z_hyp. forward. { entailer!. apply (mres_tc' (tarray tulong 64) up _ TT). cancel. }
    entailer!. rewrite null_test by auto. rw_bools. reflexivity. }
  forward_if (temp _t'23 (Vint (Int.repr (Z.b2z (isnul cp || isnul cep || isnul ip || isnul iep || isnul up || isnul bp))))).
  { try b2z_hyp. forward. entailer!. rw_bools. reflexivity. }
  { try b2z_hyp. forward. { entailer!. apply (mres_tc' (tarray tulong 64) bp _ TT). cancel. }
    entailer!. rewrite null_test by auto. rw_bools. reflexivity. }
  forward_if (temp _t'24 (Vint (Int.repr (Z.b2z (isnul cp || isnul cep || isnul ip || isnul iep || isnul up || isnul bp || isnul rp))))).
  { try b2z_hyp. forward. entailer!. rw_bools. reflexivity. }
  { try b2z_hyp. forward. { entailer!. apply (mres_tc' (tarray tulong 64) rp _ TT). cancel. }
    entailer!. rewrite null_test by auto. rw_bools. reflexivity. }
  forward_if (temp _t'25 (Vint (Int.repr (Z.b2z (isnul cp || isnul cep || isnul ip || isnul iep || isnul up || isnul bp || isnul rp || isnul sp))))).
  { try b2z_hyp. forward. entailer!. rw_bools. reflexivity. }
  { try b2z_hyp. forward. { entailer!. apply (mres_tc' t_states sp _ TT). cancel. }
    entailer!. rewrite null_test by auto. rw_bools. reflexivity. }
  forward_if.
  { forward. Exists (Int.repr 0). entailer!. }
  try b2z_hyp.
  repeat match goal with H: (_ || _) = false |- _ => apply orb_false_iff in H; destruct H end.
  rewrite (mres_ptr (tarray tulong (copy_len X)) cp) by assumption.
  rewrite (mres_ptr (tarray tulong (copy_len X)) cep) by assumption.
  rewrite (mres_ptr (tarray tulong (info_len X)) ip) by assumption.
  rewrite (mres_ptr (tarray tulong (info_len X)) iep) by assumption.
  rewrite (mres_ptr (tarray tulong 64) up) by assumption.
  rewrite (mres_ptr (tarray tulong 64) bp) by assumption.
  rewrite (mres_ptr (tarray tulong 64) rp) by assumption.
  rewrite (mres_ptr t_states sp) by assumption.
  Intros.
  sep_apply (drop_TT (malloc_token Ews (tarray tulong (copy_len X)) cp)).
  sep_apply (drop_TT (malloc_token Ews (tarray tulong (copy_len X)) cep)).
  sep_apply (drop_TT (malloc_token Ews (tarray tulong (info_len X)) ip)).
  sep_apply (drop_TT (malloc_token Ews (tarray tulong (info_len X)) iep)).
  sep_apply (drop_TT (malloc_token Ews (tarray tulong 64) up)).
  sep_apply (drop_TT (malloc_token Ews (tarray tulong 64) bp)).
  sep_apply (drop_TT (malloc_token Ews (tarray tulong 64) rp)).
  sep_apply (drop_TT (malloc_token Ews t_states sp)).
  assert_PROP (isptr cp /\ isptr cep /\ isptr ip /\ isptr iep /\ isptr up /\ isptr bp /\ isptr rp /\ isptr sp)
    as PP by entailer!.
  destruct PP as (Pcp & Pcep & Pip & Piep & Pup & Pbp & Prp & Psp).
  eapply semax_pre; [ | apply (TF gv cc mg ad T0 cd cp cep ip iep up bp rp sp vtr vlr vcr vpj Hx); auto ].
  unfold fill_pre, fields0, lraw. rewrite x0_call, call_code_of by lia.
  entailer!.
Qed.
