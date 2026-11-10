(* Law image_exact: facts of the model that the proof of the law's read_image needs: the law's forms of the target
   checks (bdf, BAR offset, window) and of the bus equal the model's. *)
Require Import VST.floyd.proofauto.
Require Import LeanosDeviceProgramImage.proof.Defs.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* Bits.                                                                  *)
(* ---------------------------------------------------------------------- *)

Lemma land_zero_bits: forall x m,
  Z.land x m = 0 <-> (forall n, 0 <= n -> Z.testbit m n = true -> Z.testbit x n = false).
Proof.
  intros x m. split.
  - intros E n N M. pose proof (f_equal (fun z => Z.testbit z n) E) as T. simpl in T.
    rewrite Z.land_spec, Z.bits_0, M, andb_true_r in T. exact T.
  - intros H. apply Z.bits_inj_iff'. intros n N. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.testbit m n) eqn:M; [ rewrite (H n N M); reflexivity | apply andb_false_r ].
Qed.

Lemma land_shiftr_zero_bits: forall x s m, 0 <= s ->
  Z.land (Z.shiftr x s) m = 0 <-> (forall n, 0 <= n -> Z.testbit m n = true -> Z.testbit x (n + s) = false).
Proof.
  intros x s m S. rewrite land_zero_bits. split.
  - intros H n N M. rewrite <- Z.shiftr_spec by lia. apply H; auto.
  - intros H n N M. rewrite Z.shiftr_spec by lia. apply H; auto.
Qed.

Lemma shiftr_zero_bits: forall x s, 0 <= s ->
  Z.shiftr x s = 0 <-> (forall n, 0 <= n -> Z.testbit x (n + s) = false).
Proof.
  intros x s S. split.
  - intros E n N. rewrite <- Z.shiftr_spec by lia. rewrite E. apply Z.bits_0.
  - intros H. apply Z.bits_inj_iff'. intros n N. rewrite Z.shiftr_spec, Z.bits_0 by lia. apply H; auto.
Qed.

Lemma bits_above32: forall x n, 0 <= x < 2 ^ 32 -> 32 <= n -> Z.testbit x n = false.
Proof.
  intros x n X N. destruct (Z.eq_dec x 0) as [->|NZ]; [ apply Z.bits_0 | ].
  apply Z.bits_above_log2; [ lia | ].
  apply Z.lt_le_trans with 32; [ | lia ]. apply Z.log2_lt_pow2; lia.
Qed.

Lemma bits_small: forall m n, 0 <= m -> m < 2 ^ n -> 0 <= n -> forall k, n <= k -> Z.testbit m k = false.
Proof.
  intros m n M L N k K. destruct (Z.eq_dec m 0) as [->|NZ]; [ apply Z.bits_0 | ].
  apply Z.bits_above_log2; [ lia | ]. apply Z.lt_le_trans with n; [ | lia ]. apply Z.log2_lt_pow2; lia.
Qed.

(* The law's BDF check: (bdf >> 24) != 0 || ((bdf >> 13) & 7) != 0 || ((bdf >> 3) & 31) != 0 is negb bdf_ok. *)
Lemma bdf_law: forall x, 0 <= x < 2 ^ 32 ->
  ((Z.shiftr x 24 =? 0) && (Z.land (Z.shiftr x 13) 7 =? 0) && (Z.land (Z.shiftr x 3) 31 =? 0))%bool = bdf_ok x.
Proof.
  intros x X. unfold bdf_ok.
  apply eq_true_iff_eq. rewrite !andb_true_iff, !Z.eqb_eq.
  rewrite shiftr_zero_bits, !land_shiftr_zero_bits, land_zero_bits by lia.
  split.
  - intros [[A B] D] n N M.
    destruct (zlt n 32) as [L|L]; [ | apply bits_above32; auto; lia ].
    assert (A': forall n, 24 <= n -> Z.testbit x n = false)
      by (intros k K; replace k with ((k - 24) + 24) by lia; apply A; lia).
    assert (B': forall n, 13 <= n <= 15 -> Z.testbit x n = false).
    { intros k K. assert (k = 13 \/ k = 14 \/ k = 15) as [-> | [-> | ->]] by lia.
      - apply (B 0); [ lia | reflexivity ].
      - apply (B 1); [ lia | reflexivity ].
      - apply (B 2); [ lia | reflexivity ]. }
    assert (D': forall n, 3 <= n <= 7 -> Z.testbit x n = false).
    { intros k K. assert (k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7) as [-> | [-> | [-> | [-> | ->]]]] by lia.
      - apply (D 0); [ lia | reflexivity ].
      - apply (D 1); [ lia | reflexivity ].
      - apply (D 2); [ lia | reflexivity ].
      - apply (D 3); [ lia | reflexivity ].
      - apply (D 4); [ lia | reflexivity ]. }
    rewrite <- (Z2Nat.id n) in * by lia. remember (Z.to_nat n) as k eqn:Ek. clear Ek A B D.
    unfold BDF_OUTSIDE in M.
    do 32 (destruct k as [|k]; [ simpl in M;
      first [ discriminate M | apply A'; lia | apply B'; lia | apply D'; lia ] | ]).
    lia.
  - intros E. split; [ split | ].
    + intros n N. destruct (zlt (n + 24) 32) as [L|L]; [ | apply bits_above32; auto; lia ].
      apply E; [ lia | ]. unfold BDF_OUTSIDE.
      assert (n = 0 \/ n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5 \/ n = 6 \/ n = 7) by lia.
      repeat match goal with H: _ \/ _ |- _ => destruct H as [-> | H] end; try (subst n); reflexivity.
    + intros n N M. destruct (zlt n 3) as [L|L]; [ | rewrite (bits_small 7 3) in M by lia; discriminate ].
      apply E; [ lia | ]. unfold BDF_OUTSIDE.
      assert (n = 0 \/ n = 1 \/ n = 2) as [-> | [-> | ->]] by lia; reflexivity.
    + intros n N M. destruct (zlt n 5) as [L|L]; [ | rewrite (bits_small 31 5) in M by lia; discriminate ].
      apply E; [ lia | ]. unfold BDF_OUTSIDE.
      assert (n = 0 \/ n = 1 \/ n = 2 \/ n = 3 \/ n = 4) as [-> | [-> | [-> | [-> | ->]]]] by lia; reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* 32-bit shifts and masks of a u32.                                      *)
(* ---------------------------------------------------------------------- *)

Lemma shiftr_u32: forall x n, 0 <= x <= Int.max_unsigned -> 0 <= n -> 0 <= Z.shiftr x n <= Int.max_unsigned.
Proof.
  intros x n X N. rewrite Z.shiftr_div_pow2 by lia. split; [ apply Z.div_pos; [ lia | apply Z.pow_pos_nonneg; lia ] | ].
  apply Z.le_trans with x; [ apply Z.div_le_upper_bound; [ apply Z.pow_pos_nonneg; lia | ] | lia ].
  assert (1 <= 2 ^ n) by (apply Z.pow_le_mono_r with (a := 2) in N; [ simpl in N; lia | lia ]). nia.
Qed.

Lemma shru_u32: forall x n, 0 <= x <= Int.max_unsigned -> 0 <= n <= Int.max_unsigned ->
  Int.shru (Int.repr x) (Int.repr n) = Int.repr (Z.shiftr x n).
Proof. intros. unfold Int.shru. rewrite !Int.unsigned_repr by lia. reflexivity. Qed.

Lemma and_u32: forall x y, 0 <= x <= Int.max_unsigned -> 0 <= y <= Int.max_unsigned ->
  Int.and (Int.repr x) (Int.repr y) = Int.repr (Z.land x y).
Proof. intros. unfold Int.and. rewrite !Int.unsigned_repr by lia. reflexivity. Qed.

Lemma land_u32: forall x y, 0 <= x <= Int.max_unsigned -> 0 <= y -> 0 <= Z.land x y <= Int.max_unsigned.
Proof.
  intros x y X Y.
  assert (E: Z.land x y = Z.land (Z.land x y) (Z.ones 32)).
  { apply Z.bits_inj'. intros n N. rewrite !Z.land_spec.
    destruct (zlt n 32) as [L|L].
    - rewrite Z.ones_spec_low by lia. rewrite andb_true_r. reflexivity.
    - rewrite (bits_above32 x n) by rep_lia. reflexivity. }
  rewrite E, Z.land_ones by lia. pose proof (Z.mod_pos_bound (Z.land x y) (2 ^ 32) ltac:(lia)). rep_lia.
Qed.

(* The law's bus bdf >> 16 is the model's (bdf >> 16) & 0xff once bdf_ok holds. *)
Lemma bus_law: forall x, 0 <= x < 2 ^ 32 -> bdf_ok x = true -> Z.land (Z.shiftr x 16) 255 = Z.shiftr x 16.
Proof.
  intros x X B. rewrite <- bdf_law in B by auto.
  apply andb_true_iff in B as [B _]. apply andb_true_iff in B as [B _]. apply Z.eqb_eq in B.
  assert (S: Z.shiftr x 24 = Z.shiftr x 16 / 256).
  { rewrite !Z.shiftr_div_pow2 by lia. rewrite Z.div_div by (try apply Z.pow_pos_nonneg; lia). reflexivity. }
  assert (0 <= Z.shiftr x 16) by (apply Z.shiftr_nonneg; lia).
  assert (Z.shiftr x 16 < 256).
  { rewrite B in S. assert (Z.shiftr x 16 / 256 = 0) by lia. apply Z.div_small_iff in H0; lia. }
  change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_small. change (2 ^ 8) with 256. lia.
Qed.
