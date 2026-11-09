(* The body of boot_handoff_extent: the magic and address checks, the size read, the bounds checks and the extent
   written on OK; against Defs.start, size_done and extent_end. *)
Require Import VST.floyd.proofauto.
Require Import LeanosHandoff.handoff.code.
Require Import LeanosHandoff.proof.Defs.
Require Import LeanosHandoff.proof.HandoffSpecs.
Require Import LeanosHandoff.proof.InternalSpecs.
Require Import LeanosHandoff.proof.HdLemmas.
#[local] Existing Instance HandoffSpecs.CS.
Local Open Scope Z_scope.

Lemma extent_pointer_fail (x: inputs) (st: Z) :
  i_call x = FAllocate -> pointer_check x = st -> st <> S_OK ->
  run x (start x) [] = Some (extent_end x st 0).
Proof.
  intros C P N. cbn [run]. unfold start, extent_end. rewrite C, P.
  destruct (Z.eqb_spec st S_OK); [ contradiction | reflexivity ].
Qed.

Lemma extent_size (x: inputs) (v: Z) :
  i_call x = FAllocate -> pointer_check x = S_OK ->
  run x (start x) [(Read (i_address x), v)] = Some (size_done x (v mod 2 ^ 32) (initial x)).
Proof.
  intros C P. change [(Read (i_address x), v)] with ([] ++ [(expected x ExpectSize (initial x), v)]).
  apply run_snoc. cbn [run]. unfold start. rewrite C, P. reflexivity.
Qed.

Lemma extent_size_fail (x: inputs) (T st: Z) :
  bounds_check x T = st -> st <> S_OK -> size_done x T (initial x) = extent_end x st 0.
Proof.
  intros B N. unfold size_done, extent_end. rewrite B. destruct (Z.eqb_spec st S_OK); [ contradiction | reflexivity ].
Qed.

Lemma extent_size_ok (x: inputs) (T: Z) :
  bounds_check x T = S_OK -> size_done x T (initial x) = extent_end x S_OK T.
Proof. intros B. unfold size_done, extent_end. rewrite B. reflexivity. Qed.

Lemma body_boot_handoff_extent (Ora: ORA) :
  semax_body Vprog (Gprog Ora) f_boot_handoff_extent (boot_extent_spec Ora).
Proof.
  start_function.
  rename H into HC, H0 into IX.
  pose proof IX as IX'. destruct IX' as (UM & UA & _).
  pose proof UM as UM'. pose proof UA as UA'. unfold u32_ok in UM', UA'.
  forward_if.
  { (* the magic *)
    try apply repr32_neq in H.
    assert (P: pointer_check x = S_MAGIC) by (unfold pointer_check; rewrite (proj2 (Z.eqb_neq _ _) H); reflexivity).
    forward. Exists (@nil answer) S_MAGIC 0.
    entailer!. split; [ apply extent_pointer_fail; auto; sne | split; [ sok | sne ] ]. }
  try (apply repr32_inj in H; [ | auto | unfold u32_ok; rep_lia ]).
  forward_if.
  { (* the alignment *)
    assert (A: i_address x mod 8 <> 0) by (intro E; apply H0; apply and7_zero; auto).
    assert (P: pointer_check x = S_POINTER_ALIGNMENT).
    { unfold pointer_check. rewrite H, Z.eqb_refl. cbn. rewrite (proj2 (Z.eqb_neq _ _) A). reflexivity. }
    forward. Exists (@nil answer) S_POINTER_ALIGNMENT 0.
    entailer!. split; [ apply extent_pointer_fail; auto; sne | split; [ sok | sne ] ]. }
  apply and7_zero in H0; auto.
  try rewrite Int.unsigned_repr in * by auto.
  forward_if.
  { (* low *)
    assert (P: pointer_check x = S_POINTER_LOW).
    { unfold pointer_check. rewrite H, Z.eqb_refl, H0. cbn. rewrite (proj2 (Z.ltb_lt _ _) H1). reflexivity. }
    forward. Exists (@nil answer) S_POINTER_LOW 0.
    entailer!. split; [ apply extent_pointer_fail; auto; sne | split; [ sok | sne ] ]. }
  forward_if.
  { (* high *)
    assert (P: pointer_check x = S_POINTER_HIGH).
    { unfold pointer_check. rewrite H, Z.eqb_refl, H0. cbn. rewrite (proj2 (Z.ltb_ge _ _)) by lia.
      rewrite (proj2 (Z.leb_le _ _)) by lia. reflexivity. }
    forward. Exists (@nil answer) S_POINTER_HIGH 0.
    entailer!. split; [ apply extent_pointer_fail; auto; sne | split; [ sok | sne ] ]. }
  assert (P: pointer_check x = S_OK).
  { unfold pointer_check. rewrite H, Z.eqb_refl, H0. cbn. rewrite (proj2 (Z.ltb_ge _ _)) by lia.
    rewrite (proj2 (Z.leb_gt _ _)) by lia. reflexivity. }
  rewrite <- seq_assoc.
  forward_call (gv, ctx, rctx, x, @nil answer, i_address x).
  { apply (next_call_go x [] ExpectSize (initial x)). cbn [run]. unfold start. rewrite HC, P. reflexivity. }
  Intros v.
  pose proof (extent_size x v HC P) as R. rewrite app_nil_l.
  forward.
  rewrite Int64.unsigned_repr by (unfold u64_ok in *; auto). rewrite <- repr_mod32.
  pose proof (Z.mod_pos_bound v (2 ^ 32) ltac:(lia)) as TB.
  set (T := v mod 2 ^ 32) in *. clearbody T.
  assert (TR: 0 <= T <= Int.max_unsigned) by rep_lia.
  assert (FAIL: forall st, bounds_check x T = st -> st <> S_OK ->
                 run x (start x) [(Read (i_address x), v)] = Some (extent_end x st 0))
    by (intros; rewrite R; f_equal; apply extent_size_fail; auto).
  forward_if.
  { (* small *)
    forward. Exists [(Read (i_address x), v)] S_BOUNDS_SMALL 0.
    entailer!. split; [ apply FAIL; [ unfold bounds_check; zb; reflexivity | sne ] | split; [ sok | sne ] ]. }
  forward_if.
  { (* large *)
    forward. Exists [(Read (i_address x), v)] S_BOUNDS_LARGE 0.
    entailer!. split; [ apply FAIL; [ unfold bounds_check; zb; reflexivity | sne ] | split; [ sok | sne ] ]. }
  forward_if.
  { (* alignment *)
    assert (A: T mod 8 <> 0) by (intro E; match goal with H: Int.and _ _ <> _ |- _ => apply H end; apply and7_zero; auto).
    forward. Exists [(Read (i_address x), v)] S_BOUNDS_ALIGNMENT 0.
    entailer!. split; [ apply FAIL; [ unfold bounds_check; zb; reflexivity | sne ] | split; [ sok | sne ] ]. }
  match goal with H: Int.and _ _ = _ |- _ => apply and7_zero in H; auto end.
  forward_if.
  { (* limit *)
    forward. Exists [(Read (i_address x), v)] S_BOUNDS_LIMIT 0.
    entailer!. split; [ apply FAIL; [ unfold bounds_check; zb; reflexivity | sne ] | split; [ sok | sne ] ]. }
  assert (B: bounds_check x T = S_OK) by (unfold bounds_check; zb; reflexivity).
  forward. forward.
  Exists [(Read (i_address x), v)] S_OK T.
  entailer!.
  split; [ rewrite R; f_equal; apply extent_size_ok; auto | split; [ sok | intros _; split; lia ] ].
Qed.
