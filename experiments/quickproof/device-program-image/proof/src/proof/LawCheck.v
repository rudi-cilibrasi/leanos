(* Law image_exact: the bodies of the harness's declares_sink, declares_desc and within (the law's Within). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env.
Require Import LeanosDeviceProgramImage.harness.image_exact.code.
Require Import LeanosDeviceProgramImage.proof.Defs.
Require Import LeanosDeviceProgramImage.proof.LawProg LeanosDeviceProgramImage.proof.LawSpecs
  LeanosDeviceProgramImage.proof.LawLib LeanosDeviceProgramImage.proof.LawSplit
  LeanosDeviceProgramImage.proof.LawFocus.
Local Open Scope Z_scope.
#[local] Existing Instance LawProg.LCS.

Lemma existsb_sub_step {A} {d: Inhabitant A}: forall (f: A -> bool) (l: list A) i, 0 <= i < Zlength l ->
  existsb f (sublist 0 (i + 1) l) = (existsb f (sublist 0 i l) || f (Znth i l))%bool.
Proof.
  intros. rewrite (sublist_split 0 i (i + 1)) by lia. rewrite sublist_len_1 by lia.
  rewrite existsb_app. simpl. rewrite orb_false_r. reflexivity.
Qed.

Lemma forallb_sub_step {A} {d: Inhabitant A}: forall (f: A -> bool) (l: list A) i, 0 <= i < Zlength l ->
  forallb f (sublist 0 (i + 1) l) = (forallb f (sublist 0 i l) && f (Znth i l))%bool.
Proof.
  intros. rewrite (sublist_split 0 i (i + 1)) by lia. rewrite sublist_len_1 by lia.
  rewrite forallb_app. simpl. rewrite andb_true_r. reflexivity.
Qed.

Lemma desc_eqb_sym: forall a b, desc_eqb a b = desc_eqb b a.
Proof. intros. unfold desc_eqb. rewrite (Z.eqb_sym (ds_trb a)), (Z.eqb_sym (ds_start a)),
  (Z.eqb_sym (ds_count a)), (Z.eqb_sym (ds_stride a)). reflexivity. Qed.

Ltac unfocus :=
  match goal with |- context [?A -* ?B] => sep_apply (modus_ponens_wand A B) end.

Lemma body_declares_sink : semax_body Vlaw Glaw f_declares_sink declares_sink_spec.
Proof.
  start_function.
  destruct H as (W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8 & Ls & Fs & W9 & Ld & Fd).
  unfold MAX_SINKS, MAX_DESCS in *.
  assert (C: 0 <= pl_sink_count P) by (unfold u32_ok in W8; lia).
  rewrite pol_val_vals, pol_split. unfold pol_fields. Intros.
  forward. forward.
  forward_loop (EX i: Z,
    PROP (0 <= i <= pl_sink_count P)
    LOCAL (temp _i (Vint (Int.repr i));
           temp _found (Vint (Int.repr (Z.b2z (existsb (Z.eqb off) (sublist 0 i (pl_sinks P))))));
           temp _p pp; temp _off (Vint (Int.repr off)))
    SEP (pol_fields psh pp (Vint (Int.repr (pl_present P))) (Vint (Int.repr (pl_dma P)))
          (Vint (Int.repr (pl_window P))) (Vlong (Int64.repr (pl_cfg_read P))) (Vlong (Int64.repr (pl_cfg_write P)))
          (Vint (Int.repr (pl_cmd_clear P))) (Vint (Int.repr (pl_cmd_set P))) (Vint (Int.repr (pl_sink_count P)))
          (words_val (pl_sinks P)) (Vint (Int.repr (pl_desc_count P))) (map desc_val (pl_descs P))))
  break: (PROP ()
    LOCAL (temp _found (Vint (Int.repr (Z.b2z (is_sink P off)))))
    SEP (pol_fields psh pp (Vint (Int.repr (pl_present P))) (Vint (Int.repr (pl_dma P)))
          (Vint (Int.repr (pl_window P))) (Vlong (Int64.repr (pl_cfg_read P))) (Vlong (Int64.repr (pl_cfg_write P)))
          (Vint (Int.repr (pl_cmd_clear P))) (Vint (Int.repr (pl_cmd_set P))) (Vint (Int.repr (pl_sink_count P)))
          (words_val (pl_sinks P)) (Vint (Int.repr (pl_desc_count P))) (map desc_val (pl_descs P)))).
  { Exists 0. unfold pol_fields. entailer!. }
  { Intros i. unfold pol_fields. Intros.
    forward.
    forward_if.
    - assert (Si: u32_ok (Znth i (pl_sinks P))) by (apply Forall_Znth; auto; lia).
      forward.
      forward_if (temp _found (Vint (Int.repr (Z.b2z (existsb (Z.eqb off) (sublist 0 (i + 1) (pl_sinks P))))))).
      + forward. entailer!. rewrite existsb_sub_step by lia. bfix.
        destruct (Z.eqb_spec off (Znth i (pl_sinks P))); [ rewrite orb_true_r; reflexivity | congruence ].
      + forward. entailer!. rewrite existsb_sub_step by lia. bfix.
        rewrite (proj2 (Z.eqb_neq off (Znth i (pl_sinks P)))) by congruence. rewrite orb_false_r. reflexivity.
      + forward. Exists (i + 1). unfold pol_fields. entailer!.
    - forward. unfold pol_fields. entailer!.
      unfold is_sink, declared_sinks. replace i with (pl_sink_count P) by lia. reflexivity. }
  forward.
  rewrite pol_val_vals, pol_split. unfold pol_fields. entailer!.
Qed.

Lemma body_declares_desc : semax_body Vlaw Glaw f_declares_desc declares_desc_spec.
Proof.
  start_function.
  destruct H as (W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8 & Ls & Fs & W9 & Ld & Fd).
  unfold MAX_SINKS, MAX_DESCS in *.
  assert (C: 0 <= pl_desc_count P) by (unfold u32_ok in W9; lia).
  rewrite pol_val_vals, pol_split. unfold pol_fields. Intros.
  forward. forward.
  forward_loop (EX i: Z,
    PROP (0 <= i <= pl_desc_count P)
    LOCAL (temp _i (Vint (Int.repr i));
           temp _found (Vint (Int.repr (Z.b2z (existsb (desc_eqb d) (sublist 0 i (pl_descs P))))));
           temp _p pp; temp _d dp)
    SEP (pol_fields psh pp (Vint (Int.repr (pl_present P))) (Vint (Int.repr (pl_dma P)))
          (Vint (Int.repr (pl_window P))) (Vlong (Int64.repr (pl_cfg_read P))) (Vlong (Int64.repr (pl_cfg_write P)))
          (Vint (Int.repr (pl_cmd_clear P))) (Vint (Int.repr (pl_cmd_set P))) (Vint (Int.repr (pl_sink_count P)))
          (words_val (pl_sinks P)) (Vint (Int.repr (pl_desc_count P))) (map desc_val (pl_descs P));
         data_at dsh t_desc (desc_val d) dp))%assert
  break: (PROP ()
    LOCAL (temp _found (Vint (Int.repr (Z.b2z (has_desc P d)))))
    SEP (pol_fields psh pp (Vint (Int.repr (pl_present P))) (Vint (Int.repr (pl_dma P)))
          (Vint (Int.repr (pl_window P))) (Vlong (Int64.repr (pl_cfg_read P))) (Vlong (Int64.repr (pl_cfg_write P)))
          (Vint (Int.repr (pl_cmd_clear P))) (Vint (Int.repr (pl_cmd_set P))) (Vint (Int.repr (pl_sink_count P)))
          (words_val (pl_sinks P)) (Vint (Int.repr (pl_desc_count P))) (map desc_val (pl_descs P));
         data_at dsh t_desc (desc_val d) dp))%assert.
  { Exists 0. unfold pol_fields. entailer!. }
  { Intros i. unfold pol_fields. Intros.
    forward.
    forward_if.
    - assert (Di: desc_wf (Znth i (pl_descs P))) by (apply Forall_Znth; auto; lia).
      sep_apply (descs_focus psh (map desc_val (pl_descs P)) pp i ltac:(lia)).
      rewrite Znth_map by lia. Intros.
      forward_call (psh, field_address t_policy (DOT _descs SUB i) pp, Znth i (pl_descs P), dsh, dp, d).
      { entailer!. desc_arg. }
      unfocus.
      forward_if (temp _found (Vint (Int.repr (Z.b2z (existsb (desc_eqb d) (sublist 0 (i + 1) (pl_descs P))))))).
      + forward. entailer!. rewrite existsb_sub_step by lia. rewrite desc_eqb_sym. bfix.
        match goal with H: desc_eqb _ _ = true |- _ => rewrite H end. rewrite orb_true_r. reflexivity.
      + forward. entailer!. rewrite existsb_sub_step by lia. rewrite desc_eqb_sym. bfix.
        match goal with H: desc_eqb _ _ = false |- _ => rewrite H end. rewrite orb_false_r. reflexivity.
      + forward. Exists (i + 1). unfold pol_fields. entailer!.
    - forward. unfold pol_fields. entailer!.
      unfold has_desc, declared_descs. replace i with (pl_desc_count P) by lia. reflexivity. }
  forward.
  rewrite pol_val_vals, pol_split. unfold pol_fields. entailer!.
Qed.

(* The scalar part of Within, in the order the law's within computes it. *)
Definition wscal (P M: policy) : bool :=
  ((pl_window P <=? pl_window M) && (pl_dma P <=? pl_dma M) && bits_in64 (pl_cfg_read P) (pl_cfg_read M) &&
   bits_in64 (pl_cfg_write P) (pl_cfg_write M) && bits_in32 (pl_cmd_clear P) (pl_cmd_clear M) &&
   bits_in32 (pl_cmd_set P) (pl_cmd_set M))%bool.

Lemma within_law: forall P M,
  within P M = (wscal P M && forallb (is_sink P) (declared_sinks M) && forallb (has_desc P) (declared_descs M))%bool.
Proof.
  intros. unfold within, wscal.
  destruct (forallb (is_sink P) (declared_sinks M)), (forallb (has_desc P) (declared_descs M));
    simpl; rewrite ?andb_true_r, ?andb_false_r; reflexivity.
Qed.

Lemma body_within : semax_body Vlaw Glaw f_within law_within_spec.
Proof.
  start_function.
  destruct H as [WP [SP DP]]. destruct H0 as [WM [SM DM]].
  pose proof WP as WP'. pose proof WM as WM'.
  destruct WP' as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & PLs & PFs & P9 & PLd & PFd).
  destruct WM' as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & MLs & MFs & M9 & MLd & MFd).
  unfold MAX_SINKS, MAX_DESCS in *.
  rewrite (pol_val_vals M), pol_split. unfold pol_fields. Intros.
  forward. forward.
  forward_if (temp _t'1 (Vint (Int.repr (Z.b2z ((pl_window P <=? pl_window M) && (pl_dma P <=? pl_dma M))%bool)))).
  { forward. forward. forward. entailer!. bfix. bdec. }
  { forward. entailer!. bfix. bdec. }
  forward_if (temp _t'2 (Vint (Int.repr (Z.b2z ((pl_window P <=? pl_window M) && (pl_dma P <=? pl_dma M) &&
    bits_in64 (pl_cfg_read P) (pl_cfg_read M))%bool)))).
  { forward. forward. forward. entailer!. bfix. bdec. }
  { forward. entailer!. bfix. bdec. }
  forward_if (temp _t'3 (Vint (Int.repr (Z.b2z ((pl_window P <=? pl_window M) && (pl_dma P <=? pl_dma M) &&
    bits_in64 (pl_cfg_read P) (pl_cfg_read M) && bits_in64 (pl_cfg_write P) (pl_cfg_write M))%bool)))).
  { forward. forward. forward. entailer!. bfix. bdec. }
  { forward. entailer!. bfix. bdec. }
  forward_if (temp _t'4 (Vint (Int.repr (Z.b2z ((pl_window P <=? pl_window M) && (pl_dma P <=? pl_dma M) &&
    bits_in64 (pl_cfg_read P) (pl_cfg_read M) && bits_in64 (pl_cfg_write P) (pl_cfg_write M) &&
    bits_in32 (pl_cmd_clear P) (pl_cmd_clear M))%bool)))).
  { forward. forward. forward. entailer!. bfix. bdec. }
  { forward. entailer!. bfix. bdec. }
  forward_if (temp _t'5 (Vint (Int.repr (Z.b2z (wscal P M))))).
  { forward. forward. forward. entailer!. unfold wscal. bfix. bdec. }
  { forward. entailer!. unfold wscal. bfix. bdec. }
  forward.
  assert (CS: 0 <= pl_sink_count M) by (unfold u32_ok in M8; lia).
  assert (CD: 0 <= pl_desc_count M) by (unfold u32_ok in M9; lia).
  forward.
  forward_loop (EX k: Z,
    PROP (0 <= k <= pl_sink_count M)
    LOCAL (temp _k (Vint (Int.repr k));
           temp _ok (Vint (Int.repr (Z.b2z (wscal P M && forallb (is_sink P) (sublist 0 k (pl_sinks M)))%bool)));
           temp _p pp; temp _max mp)
    SEP (data_at psh t_policy (policy_val P) pp;
         pol_fields msh mp (Vint (Int.repr (pl_present M))) (Vint (Int.repr (pl_dma M)))
          (Vint (Int.repr (pl_window M))) (Vlong (Int64.repr (pl_cfg_read M))) (Vlong (Int64.repr (pl_cfg_write M)))
          (Vint (Int.repr (pl_cmd_clear M))) (Vint (Int.repr (pl_cmd_set M))) (Vint (Int.repr (pl_sink_count M)))
          (words_val (pl_sinks M)) (Vint (Int.repr (pl_desc_count M))) (map desc_val (pl_descs M))))%assert
  break: (PROP ()
    LOCAL (temp _ok (Vint (Int.repr (Z.b2z (wscal P M && forallb (is_sink P) (declared_sinks M))%bool)));
           temp _p pp; temp _max mp)
    SEP (data_at psh t_policy (policy_val P) pp;
         pol_fields msh mp (Vint (Int.repr (pl_present M))) (Vint (Int.repr (pl_dma M)))
          (Vint (Int.repr (pl_window M))) (Vlong (Int64.repr (pl_cfg_read M))) (Vlong (Int64.repr (pl_cfg_write M)))
          (Vint (Int.repr (pl_cmd_clear M))) (Vint (Int.repr (pl_cmd_set M))) (Vint (Int.repr (pl_sink_count M)))
          (words_val (pl_sinks M)) (Vint (Int.repr (pl_desc_count M))) (map desc_val (pl_descs M))))%assert.
  { Exists 0. unfold pol_fields. entailer!. simpl. rewrite andb_true_r. reflexivity. }
  { Intros k. unfold pol_fields. Intros.
    forward.
    forward_if.
    - assert (Sk: u32_ok (Znth k (pl_sinks M))) by (apply Forall_Znth; auto; lia).
      forward.
      forward_call (psh, pp, P, Znth k (pl_sinks M)).
      forward_if (temp _ok (Vint (Int.repr (Z.b2z (wscal P M && forallb (is_sink P) (sublist 0 (k + 1) (pl_sinks M)))%bool)))).
      + forward. entailer!. rewrite forallb_sub_step by lia. bfix. rewrite !andb_false_r. reflexivity.
      + forward. entailer!. rewrite forallb_sub_step by lia.
        bfix. rewrite !andb_true_r. reflexivity.
      + forward. Exists (k + 1). unfold pol_fields. entailer!.
    - forward. unfold pol_fields. entailer!.
      unfold declared_sinks. replace k with (pl_sink_count M) by lia. reflexivity. }
  unfold pol_fields. Intros.
  forward.
  forward_loop (EX k: Z,
    PROP (0 <= k <= pl_desc_count M)
    LOCAL (temp _k__1 (Vint (Int.repr k));
           temp _ok (Vint (Int.repr (Z.b2z (wscal P M && forallb (is_sink P) (declared_sinks M) &&
                                           forallb (has_desc P) (sublist 0 k (pl_descs M)))%bool)));
           temp _p pp; temp _max mp)
    SEP (data_at psh t_policy (policy_val P) pp;
         pol_fields msh mp (Vint (Int.repr (pl_present M))) (Vint (Int.repr (pl_dma M)))
          (Vint (Int.repr (pl_window M))) (Vlong (Int64.repr (pl_cfg_read M))) (Vlong (Int64.repr (pl_cfg_write M)))
          (Vint (Int.repr (pl_cmd_clear M))) (Vint (Int.repr (pl_cmd_set M))) (Vint (Int.repr (pl_sink_count M)))
          (words_val (pl_sinks M)) (Vint (Int.repr (pl_desc_count M))) (map desc_val (pl_descs M))))%assert
  break: (PROP ()
    LOCAL (temp _ok (Vint (Int.repr (Z.b2z (within P M)))))
    SEP (data_at psh t_policy (policy_val P) pp;
         pol_fields msh mp (Vint (Int.repr (pl_present M))) (Vint (Int.repr (pl_dma M)))
          (Vint (Int.repr (pl_window M))) (Vlong (Int64.repr (pl_cfg_read M))) (Vlong (Int64.repr (pl_cfg_write M)))
          (Vint (Int.repr (pl_cmd_clear M))) (Vint (Int.repr (pl_cmd_set M))) (Vint (Int.repr (pl_sink_count M)))
          (words_val (pl_sinks M)) (Vint (Int.repr (pl_desc_count M))) (map desc_val (pl_descs M))))%assert.
  { Exists 0. unfold pol_fields. entailer!. simpl. rewrite andb_true_r. reflexivity. }
  { Intros k. unfold pol_fields. Intros.
    forward.
    forward_if.
    - assert (Dk: desc_wf (Znth k (pl_descs M))) by (apply Forall_Znth; auto; lia).
      sep_apply (descs_focus msh (map desc_val (pl_descs M)) mp k ltac:(lia)).
      rewrite Znth_map by lia. Intros.
      forward_call (psh, pp, P, msh, field_address t_policy (DOT _descs SUB k) mp, Znth k (pl_descs M)).
      { entailer!. desc_arg. }
      unfocus.
      forward_if (temp _ok (Vint (Int.repr (Z.b2z (wscal P M && forallb (is_sink P) (declared_sinks M) &&
                                                   forallb (has_desc P) (sublist 0 (k + 1) (pl_descs M)))%bool)))).
      + forward. entailer!. rewrite forallb_sub_step by lia.
        bfix. rewrite !andb_false_r. reflexivity.
      + forward. entailer!. rewrite forallb_sub_step by lia.
        bfix. rewrite !andb_true_r. reflexivity.
      + forward. Exists (k + 1). unfold pol_fields. entailer!.
    - forward. unfold pol_fields. entailer!.
      rewrite within_law. unfold declared_descs. replace k with (pl_desc_count M) by lia. reflexivity. }
  forward.
  rewrite (pol_val_vals M), pol_split. unfold pol_fields. entailer!.
Qed.
