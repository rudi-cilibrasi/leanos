(* The body of boot_handoff_project: the copy (boot_handoff_stream_copy), its length check, the decoder with the
   projection (boot_handoff_decode_projection) and the decoder's acceptance of its final state; against
   Defs.copy_end, begin_decode, projection_end and rejected_check. *)
Require Import VST.floyd.proofauto.
Require Import LeanosHandoff.handoff.code.
Require Import LeanosHandoff.proof.Defs.
Require Import LeanosHandoff.proof.HandoffSpecs.
Require Import LeanosHandoff.proof.InternalSpecs.
Require Import LeanosHandoff.proof.HdLemmas.
Require Import LeanosHandoff.proof.HdStates.
Require Import LeanosHandoff.proof.HdFast.
#[local] Ltac simplify_remove_localdef_temp ::= fast_remove_localdef_temp.
#[local] Existing Instance HandoffSpecs.CS.
Local Open Scope Z_scope.

Lemma status_zero: forall st, status_ok st -> Int.repr st = Int.repr 0 -> st = 0.
Proof. intros. apply repr_inj_unsigned in H0; unfold status_ok, S_AUTHORITY_REJECTED_TARGET in *; rep_lia. Qed.

Lemma status_nonzero: forall st, Int.repr st <> Int.repr 0 -> st <> S_OK.
Proof. intros st N E. apply N. rewrite E. reflexivity. Qed.

Lemma copy_end_alloc (x: inputs) (m: mem) : i_call x = FAllocate -> copy_end x S_OK m = begin_decode x m.
Proof. intros C. unfold copy_end. rewrite C. reflexivity. Qed.

Lemma projection_end_alloc (x: inputs) (m: mem) :
  i_call x = FAllocate -> projection_end x S_OK m = Return (rejected_check (current m)) m.
Proof. intros C. unfold projection_end. rewrite C. reflexivity. Qed.

Ltac jfail hs M R HC st :=
  forward; Exists hs st M; rewrite out_current_fail by sne; cbn [m_copy m_states m_at with_states with_bitmaps];
  entailer!;
  post_split;
  first [ apply returns_return; rewrite R; do 2 f_equal; unfold rejected_check; zb; reflexivity
        | unfold keeps; rewrite HC; cbn; repeat split | auto ].

Lemma body_boot_handoff_project (Ora: ORA) :
  semax_body Vprog (Gprog Ora) f_boot_handoff_project (boot_project_spec Ora).
Proof.
  start_function.
  rename H into HC, H0 into IX, H1 into LC, H2 into R0, H3 into EF.
  pose proof IX as IX'. destruct IX' as (UM & UA & _).
  pose proof UM as UM'. pose proof UA as UA'. unfold u32_ok in UM', UA'.
  set (M0 := with_extent (initial x) T).
  assert (UT: u32_ok T) by (destruct EF; unfold u32_ok; rep_lia).
  pose proof UT as UT'. unfold u32_ok in UT'.
  forward.
  Time forward_call (gv, read, ctx, rctx, x, h, M0, cp, csh, v_length, Tsh, Vint (Int.repr 0)).
  Intros vret. destruct vret as [[hs1 st] c]. cbn [fst snd] in *.
  match goal with H: run _ _ (h ++ hs1) = _ |- _ => rename H into R1 end.
  match goal with H: status_ok st |- _ => rename H into SO1 end.
  match goal with H: Zlength c = _ |- _ => rename H into Lc end.
  set (M1 := with_copy M0 c) in *.
  forward_if.
  { (* the copy failed *)
    apply status_nonzero in H. rewrite copy_end_fail in R1 by auto.
    forward. Exists (h ++ hs1) st M1.
    rewrite out_current_fail by auto. rewrite (proj2 (Z.eqb_neq _ _) H).
    entailer!.
    split; [ apply returns_return; auto | unfold keeps; rewrite HC; cbn; repeat split ]. }
  apply status_zero in H; auto. subst st. rewrite Z.eqb_refl.
  forward.
  forward_if; [ contradiction | ].
  match goal with H: T = T |- _ => clear H end.
  forward.
  rewrite copy_end_alloc in R1 by auto.
  assert (DC: decoded x M1 = c) by (unfold decoded; rewrite HC; reflexivity).
  assert (MO1: mem_ok M1).
  { destruct IX as (_ & _ & _ & _ & U & B & R & S & F & _). unfold mem_ok; cbn. repeat split; auto. }
  assert (P: projection x = true) by (unfold projection; rewrite HC; reflexivity).
  assert (L8: m_total M1 / 8 <= Zlength (decoded x M1))
    by (rewrite DC, Lc; cbn; destruct EF; apply Z.div_le_upper_bound; lia).
  replace (data_at csh (tarray tulong 8192) (map vl c) cp)
    with (data_at csh (tarray tulong (Zlength (decoded x M1))) (map vl (decoded x M1)) cp)
    by (rewrite DC, Lc; reflexivity).
  forward_call (gv, ctx, rctx, record, x, h ++ hs1, M1, cp, csh, pp, psh, up, bp, rp, bsh, sp, ssh,
                v_decoded, Tsh, Vint (Int.repr 0)).
  Intros vret. destruct vret as [[[[[[hs2 st] u] b] r] ss] i]. cbn [fst snd] in *.
  rewrite DC, Lc.
  rewrite <- app_assoc in *.
  match goal with H: run _ _ (h ++ hs1 ++ hs2) = _ |- _ => rename H into R2 end.
  match goal with H: status_ok st |- _ => rename H into SO2 end.
  match goal with H: mem_ok _ |- _ => rename H into MO2 end.
  match goal with H: Forall u64_ok _ |- _ => rename H into F2 end.
  set (M2 := with_states (with_bitmaps M1 u b r) ss i) in *.
  forward_if.
  { (* the decoder failed *)
    apply status_nonzero in H. rewrite projection_end_fail in R2 by auto.
    forward. Exists (h ++ hs1 ++ hs2) st M2.
    rewrite out_current_fail by auto. rewrite (proj2 (Z.eqb_neq _ _) H).
    cbn [m_copy m_states m_at m_usable m_blocked m_reserved with_states with_bitmaps M2 M1 with_copy].
    entailer!.
    split; [ apply returns_return; auto | unfold keeps; rewrite HC; cbn; repeat split ]. }
  apply status_zero in H; auto. subst st. rewrite Z.eqb_refl.
  rewrite projection_end_alloc in R2 by auto. change (current M2) with (Znth i ss) in R2.
  assert (SO3: states_ok ss) by (apply (mem_ok_states M2); auto).
  assert (I2: 0 <= i < 2) by (destruct MO2 as (_ & _ & _ & _ & _ & I); cbn in I; lia).
  assert (LI2: Zlength (Znth i ss) = 41) by (apply states_ok_row; auto).
  forward. sload. forward_if. { w64. jfail (h ++ hs1 ++ hs2) M2 R2 HC S_DECODE_REJECTED_STATUS. } w64.
  forward. sload. forward_if. { w64. jfail (h ++ hs1 ++ hs2) M2 R2 HC S_DECODE_REJECTED_ERROR. } w64.
  forward. forward. forward.
  Exists (h ++ hs1 ++ hs2) S_OK M2.
  rewrite out_current_ok by (rewrite HC; discriminate).
  cbn [m_copy m_states m_at m_usable m_blocked m_reserved with_states with_bitmaps M2 M1 with_copy].
  entailer!.
  post_split;
  first [ apply returns_return; rewrite R2; do 2 f_equal; unfold rejected_check; zb; reflexivity
        | unfold keeps; rewrite HC; cbn; repeat split | auto ].
Qed.
