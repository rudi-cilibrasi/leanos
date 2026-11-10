(* Law image_exact: the bodies of the harness's any_policy and copy_policy. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env.
Require Import LeanosDeviceProgramImage.harness.image_exact.code.
Require Import LeanosDeviceProgramImage.proof.Defs.
Require Import LeanosDeviceProgramImage.proof.LawProg LeanosDeviceProgramImage.proof.LawSpecs
  LeanosDeviceProgramImage.proof.LawLib LeanosDeviceProgramImage.proof.LawSplit.
Local Open Scope Z_scope.
#[local] Existing Instance LawProg.LCS.

Lemma upd_fill {A} {d: Inhabitant A}: forall (l: list A) x i n (u: A), Zlength l = i -> i < n ->
  upd_Znth i (l ++ Zrepeat u (n - i)) x = (l ++ [x]) ++ Zrepeat u (n - (i + 1)).
Proof. intros. subst i. list_solve. Qed.

Lemma Znth_fill {A} {d: Inhabitant A}: forall (l: list A) i n (u: A), Zlength l = i -> i < n ->
  Znth i (l ++ Zrepeat u (n - i)) = u.
Proof. intros. subst i. list_solve. Qed.

Lemma upd_sub_map {A B} {da: Inhabitant A} {db: Inhabitant B}: forall (f: A -> B) (l: list A) i n (u: B),
  0 <= i < n -> Zlength l = n ->
  upd_Znth i (map f (sublist 0 i l) ++ Zrepeat u (n - i)) (f (Znth i l)) =
  map f (sublist 0 (i + 1) l) ++ Zrepeat u (n - (i + 1)).
Proof. intros. list_solve. Qed.

(* The fields of descriptor i of a policy object after a load. *)
Ltac desc_open D i :=
  rewrite (Znth_map i desc_val D) by lia;
  change (desc_val (Znth i D)) with (Vint (Int.repr (ds_trb (Znth i D))), (Vint (Int.repr (ds_start (Znth i D))),
    (Vint (Int.repr (ds_count (Znth i D))), Vint (Int.repr (ds_stride (Znth i D))))));
  cbn beta iota.

Lemma body_any_policy : semax_body Vlaw Glaw f_any_policy any_policy_spec.
Proof.
  start_function.
  rewrite data_at__eq, pol_default, pol_split. unfold pol_fields.
  forward_call. Intros a1. forward.
  forward_call. Intros a2. forward.
  forward_call. Intros a3. forward.
  forward_call. Intros a4. forward.
  forward_call. Intros a5. forward.
  forward_call. Intros a6. forward.
  forward_call. Intros a7. forward.
  forward_call. Intros a8. forward.
  forward_for_simple_bound 8 (EX i: Z, EX ss: list Z,
    PROP (Zlength ss = i; Forall u32_ok ss)
    LOCAL (temp _p p; temp _bounded (Vint (Int.repr (Z.b2z bounded))))
    SEP (pol_fields sh p (Vint (Int.repr a1)) (Vint (Int.repr a2)) (Vint (Int.repr a3))
           (Vlong (Int64.repr a4)) (Vlong (Int64.repr a5)) (Vint (Int.repr a6)) (Vint (Int.repr a7))
           (Vint (Int.repr a8)) (words_val ss ++ Zrepeat Vundef (8 - i)) Vundef (Zrepeat udesc 16)))%assert.
  { Exists (@nil Z). unfold pol_fields. entailer!. }
  { unfold pol_fields. forward_call. Intros x. forward.
    Exists (ss ++ [x]).
    rewrite (upd_fill (words_val ss) _ i 8) by (try rewrite Zlength_map; lia).
    rewrite map_app. unfold pol_fields. entailer!.
    split; [ list_solve | apply Forall_app; split; [ auto | repeat constructor; unfold u32_ok; lia ] ]. }
  Intros ss. change (8 - 8) with 0. rewrite Zrepeat_0, app_nil_r.
  unfold pol_fields. forward_call. Intros a9. forward.
  forward_for_simple_bound 16 (EX i: Z, EX ds: list desc,
    PROP (Zlength ds = i; Forall desc_wf ds)
    LOCAL (temp _p p; temp _bounded (Vint (Int.repr (Z.b2z bounded))))
    SEP (pol_fields sh p (Vint (Int.repr a1)) (Vint (Int.repr a2)) (Vint (Int.repr a3))
           (Vlong (Int64.repr a4)) (Vlong (Int64.repr a5)) (Vint (Int.repr a6)) (Vint (Int.repr a7))
           (Vint (Int.repr a8)) (words_val ss) (Vint (Int.repr a9))
           (map desc_val ds ++ Zrepeat udesc (16 - i))))%assert.
  { Exists (@nil desc). unfold pol_fields. entailer!. }
  { unfold pol_fields. Intros.
    assert (Lm: Zlength (map desc_val ds) = i) by (rewrite Zlength_map; auto).
    forward_call. Intros x1. forward.
    rewrite (Znth_fill (map desc_val ds) i 16) by (auto; lia).
    forward_call. Intros x2. forward.
    rewrite upd_Znth_same by (rewrite Zlength_app, Zlength_Zrepeat; lia). rewrite upd_Znth_twice by (rewrite Zlength_app, Zlength_Zrepeat; lia).
    forward_call. Intros x3. forward.
    rewrite upd_Znth_same by (rewrite Zlength_app, Zlength_Zrepeat; lia). rewrite upd_Znth_twice by (rewrite Zlength_app, Zlength_Zrepeat; lia).
    forward_call. Intros x4. forward.
    rewrite upd_Znth_same by (rewrite Zlength_app, Zlength_Zrepeat; lia). rewrite upd_Znth_twice by (rewrite Zlength_app, Zlength_Zrepeat; lia).
    simpl fst; simpl snd.
    Exists (ds ++ [mk_desc x1 x2 x3 x4]).
    rewrite (upd_fill (map desc_val ds) _ i 16) by (auto; lia).
    rewrite map_app. unfold pol_fields. entailer!.
    split; [ list_solve | apply Forall_app; split; [ auto | repeat constructor; unfold u32_ok; simpl; lia ] ]. }
  Intros ds. change (16 - 16) with 0. rewrite Zrepeat_0, app_nil_r.
  unfold pol_fields. Intros.
  forward_if.
  - forward. forward. forward. forward.
    bfix. subst bounded.
    Exists (mk_policy a1 a2 a3 a4 a5 a6 a7 (a8 mod 9) ss (a9 mod 17) ds).
    rewrite pol_val_vals, pol_split. unfold pol_fields.
    cbn [pl_present pl_dma pl_window pl_cfg_read pl_cfg_write pl_cmd_clear pl_cmd_set pl_sink_count pl_sinks
         pl_desc_count pl_descs].
    change (Int.add (Int.repr 8) (Int.repr 1)) with (Int.repr 9).
    change (Int.add (Int.repr 16) (Int.repr 1)) with (Int.repr 17).
    rewrite !modu_u32 by (unfold u32_ok; rep_lia).
    assert (0 <= a8 mod 9 < 9) by (apply Z.mod_pos_bound; lia).
    assert (0 <= a9 mod 17 < 17) by (apply Z.mod_pos_bound; lia).
    entailer!.
    assert (W: policy_wf (mk_policy a1 a2 a3 a4 a5 a6 a7 (a8 mod 9) ss (a9 mod 17) ds))
      by (unfold policy_wf, u32_ok, MAX_SINKS, MAX_DESCS; unfold u64_ok in *; simpl; repeat split; auto; rep_lia).
    split; [ exact W | split; [ exact W | unfold MAX_SINKS, MAX_DESCS; simpl; lia ] ].
  - forward.
    bfix. subst bounded.
    Exists (mk_policy a1 a2 a3 a4 a5 a6 a7 a8 ss a9 ds).
    rewrite pol_val_vals, pol_split. unfold pol_fields.
    cbn [pl_present pl_dma pl_window pl_cfg_read pl_cfg_write pl_cmd_clear pl_cmd_set pl_sink_count pl_sinks
         pl_desc_count pl_descs].
    entailer!.
    unfold policy_wf, u32_ok, MAX_SINKS, MAX_DESCS; unfold u64_ok in *; simpl; repeat split; auto; rep_lia.
Qed.

Lemma body_copy_policy : semax_body Vlaw Glaw f_copy_policy copy_policy_spec.
Proof.
  start_function.
  destruct H as (W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8 & Ls & Fs & W9 & Ld & Fd).
  unfold MAX_SINKS, MAX_DESCS in Ls, Ld.
  rewrite data_at__eq, pol_default, pol_split. rewrite pol_val_vals, pol_split. unfold pol_fields. Intros.
  forward. forward. forward. forward. forward. forward. forward. forward.
  forward. forward. forward. forward. forward. forward. forward. forward.
  forward_for_simple_bound 8 (EX i: Z,
    PROP ()
    LOCAL (temp _d d; temp _s s)
    SEP (pol_fields dsh d (Vint (Int.repr (pl_present P))) (Vint (Int.repr (pl_dma P)))
          (Vint (Int.repr (pl_window P))) (Vlong (Int64.repr (pl_cfg_read P))) (Vlong (Int64.repr (pl_cfg_write P)))
          (Vint (Int.repr (pl_cmd_clear P))) (Vint (Int.repr (pl_cmd_set P))) (Vint (Int.repr (pl_sink_count P)))
          (words_val (sublist 0 i (pl_sinks P)) ++ Zrepeat Vundef (8 - i)) Vundef (Zrepeat udesc 16);
         pol_fields ssh s (Vint (Int.repr (pl_present P))) (Vint (Int.repr (pl_dma P)))
          (Vint (Int.repr (pl_window P))) (Vlong (Int64.repr (pl_cfg_read P))) (Vlong (Int64.repr (pl_cfg_write P)))
          (Vint (Int.repr (pl_cmd_clear P))) (Vint (Int.repr (pl_cmd_set P))) (Vint (Int.repr (pl_sink_count P)))
          (words_val (pl_sinks P)) (Vint (Int.repr (pl_desc_count P))) (map desc_val (pl_descs P))))%assert.
  { unfold pol_fields. entailer!. }
  { unfold pol_fields. Intros. forward. forward.
    rewrite (upd_sub_map (fun w => Vint (Int.repr w)) (pl_sinks P) i 8) by lia.
    unfold pol_fields. entailer!. }
  change (8 - 8) with 0. rewrite Zrepeat_0, app_nil_r, sublist_same by lia.
  unfold pol_fields. Intros. forward. forward.
  forward_for_simple_bound 16 (EX i: Z,
    PROP ()
    LOCAL (temp _d d; temp _s s)
    SEP (pol_fields dsh d (Vint (Int.repr (pl_present P))) (Vint (Int.repr (pl_dma P)))
          (Vint (Int.repr (pl_window P))) (Vlong (Int64.repr (pl_cfg_read P))) (Vlong (Int64.repr (pl_cfg_write P)))
          (Vint (Int.repr (pl_cmd_clear P))) (Vint (Int.repr (pl_cmd_set P))) (Vint (Int.repr (pl_sink_count P)))
          (words_val (pl_sinks P)) (Vint (Int.repr (pl_desc_count P)))
          (map desc_val (sublist 0 i (pl_descs P)) ++ Zrepeat udesc (16 - i));
         pol_fields ssh s (Vint (Int.repr (pl_present P))) (Vint (Int.repr (pl_dma P)))
          (Vint (Int.repr (pl_window P))) (Vlong (Int64.repr (pl_cfg_read P))) (Vlong (Int64.repr (pl_cfg_write P)))
          (Vint (Int.repr (pl_cmd_clear P))) (Vint (Int.repr (pl_cmd_set P))) (Vint (Int.repr (pl_sink_count P)))
          (words_val (pl_sinks P)) (Vint (Int.repr (pl_desc_count P))) (map desc_val (pl_descs P))))%assert.
  { unfold pol_fields. entailer!. }
  { unfold pol_fields. Intros.
    assert (Lm: Zlength (map desc_val (sublist 0 i (pl_descs P))) = i)
      by (rewrite Zlength_map, Zlength_sublist; lia).
    assert (DW: desc_wf (Znth i (pl_descs P))) by (apply Forall_Znth; auto; lia).
    destruct DW as (D1 & D2 & D3 & D4).
    forward; [ desc_open (pl_descs P) i; entailer! | desc_open (pl_descs P) i ].
    forward.
    rewrite (Znth_fill (map desc_val (sublist 0 i (pl_descs P))) i 16) by (auto; lia).
    forward; [ desc_open (pl_descs P) i; entailer! | desc_open (pl_descs P) i ].
    forward.
    rewrite upd_Znth_same by (rewrite Zlength_app, Zlength_Zrepeat; lia).
    rewrite upd_Znth_twice by (rewrite Zlength_app, Zlength_Zrepeat; lia).
    forward; [ desc_open (pl_descs P) i; entailer! | desc_open (pl_descs P) i ].
    forward.
    rewrite upd_Znth_same by (rewrite Zlength_app, Zlength_Zrepeat; lia).
    rewrite upd_Znth_twice by (rewrite Zlength_app, Zlength_Zrepeat; lia).
    forward; [ desc_open (pl_descs P) i; entailer! | desc_open (pl_descs P) i ].
    forward.
    rewrite upd_Znth_same by (rewrite Zlength_app, Zlength_Zrepeat; lia).
    rewrite upd_Znth_twice by (rewrite Zlength_app, Zlength_Zrepeat; lia).
    simpl fst; simpl snd.
    rewrite <- (upd_sub_map desc_val (pl_descs P) i 16) by lia.
    unfold pol_fields. entailer!. }
  change (16 - 16) with 0. rewrite Zrepeat_0, app_nil_r, sublist_same by lia.
  rewrite !pol_val_vals, !pol_split. unfold pol_fields. entailer!.
Qed.
