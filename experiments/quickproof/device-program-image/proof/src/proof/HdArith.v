(* The arithmetic of wifi_image_header's tests and fields, as the model states them: the target's bus, device and
   function, the BAR and window tests, the BDF mask, the flags mask, the bitmaps, the sink and descriptor
   addresses, and the prefixes of the sink and descriptor arrays the loops fill. *)
Require Import VST.floyd.proofauto.
Require Import LeanosDeviceProgramImage.device_program.code.
Require Import LeanosDeviceProgramImage.proof.Specs.
Require Import LeanosDeviceProgramImage.proof.BodyLookup.
Require Import LeanosDeviceProgramImage.proof.BodyPolicy.
#[local] Existing Instance Specs.CS.
Local Open Scope Z_scope.

Lemma shru_and: forall x n m, 0 <= x <= Int.max_unsigned -> 0 <= n < 32 ->
  Int.and (Int.shru (Int.repr x) (Int.repr n)) (Int.repr m) = Int.repr (Z.land (Z.shiftr x n) m).
Proof.
  intros x n m X N. unfold Int.shru. rewrite !Int.unsigned_repr by rep_lia. apply and_repr.
Qed.

(* x & 3 and x & 511 as remainders. *)
Lemma land3: forall x, 0 <= x -> Z.land x 3 = x mod 4.
Proof. intros. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma land511: forall x, 0 <= x -> Z.land x 511 = x mod 512.
Proof. intros. change 511 with (Z.ones 9). rewrite Z.land_ones by lia. reflexivity. Qed.

(* ~0xff1f07 in 32 bits. *)
Lemma not_bdf_mask: Int.not (Int.repr 16719623) = Int.repr BDF_OUTSIDE.
Proof. apply Int.same_if_eq. reflexivity. Qed.

Lemma not_3: Int.not (Int.repr 3) = Int.repr 4294967292.
Proof. apply Int.same_if_eq. reflexivity. Qed.

(* flags & ~3 is zero exactly when flags <= 3. *)
Lemma flags_land: forall f, 0 <= f <= Int.max_unsigned -> Z.land f 4294967292 = f / 4 * 4.
Proof.
  intros f F.
  replace 4294967292 with (Z.land (Z.lnot 3) (Z.ones 32)) by reflexivity.
  rewrite (Z.land_comm (Z.lnot 3) (Z.ones 32)), Z.land_assoc, Z.land_ones by lia.
  rewrite Z.mod_small by (change (2 ^ 32) with 4294967296; rep_lia).
  rewrite <- Z.ldiff_land. change 3 with (Z.ones 2). rewrite Z.ldiff_ones_r by lia.
  rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

Lemma flags_mask: forall f, 0 <= f <= Int.max_unsigned -> (Z.land f 4294967292 = 0 <-> f <= 3).
Proof.
  intros f F. rewrite flags_land by auto. split; intros E.
  - assert (f / 4 = 0) by lia. pose proof (Z.div_mod f 4 ltac:(lia)). pose proof (Z.mod_pos_bound f 4 ltac:(lia)). lia.
  - rewrite Z.div_small by lia. reflexivity.
Qed.

(* A word's bits outside a mask, as the C tests them. *)
Lemma land_u32: forall x m, 0 <= x <= Int.max_unsigned -> 0 <= m -> 0 <= Z.land x m <= Int.max_unsigned.
Proof.
  intros x m X M. split; [ apply Z.land_nonneg; lia | ].
  rewrite <- (Z.mod_small x (2 ^ 32)) by (change (2 ^ 32) with 4294967296; rep_lia).
  rewrite <- Z.land_ones by lia. rewrite <- Z.land_assoc, (Z.land_comm (Z.ones 32) m), Z.land_assoc.
  pose proof (land_range (Z.land x m) 32 ltac:(lia)). change (2 ^ 32) with 4294967296 in *. rep_lia.
Qed.

(* (tbool)(x & m) as the C computes it. *)
Lemma land_test: forall x m, 0 <= x <= Int.max_unsigned -> 0 <= m ->
  bool2val (negb (Int.eq (Int.and (Int.repr x) (Int.repr m)) Int.zero)) =
  Vint (Int.repr (Z.b2z (negb (Z.land x m =? 0)))).
Proof.
  intros x m X M. rewrite and_repr. change Int.zero with (Int.repr 0).
  pose proof (land_u32 x m X M).
  destruct (Z.eqb_spec (Z.land x m) 0) as [E | N].
  - rewrite E. reflexivity.
  - rewrite Int.eq_false; [ reflexivity | ]. intros E. apply N. apply repr_inj_unsigned; auto; rep_lia.
Qed.

Lemma bar_ok_neg: forall b, bar_ok b = negb ((b <? 16) || (36 <? b) || negb (b mod 4 =? 0))%bool.
Proof.
  intros. unfold bar_ok. rewrite (Z.leb_antisym b 16), (Z.leb_antisym 36 b).
  destruct (b <? 16), (36 <? b), (b mod 4 =? 0); reflexivity.
Qed.

Lemma window_ok_neg: forall w, window_ok w = negb ((w =? 0) || (65536 <? w) || negb (w mod 512 =? 0))%bool.
Proof.
  intros. unfold window_ok. rewrite (Z.leb_antisym 65536 w).
  destruct (w =? 0), (65536 <? w), (w mod 512 =? 0); reflexivity.
Qed.

Lemma bar_of_range: forall w, 0 <= w <= Int.max_unsigned -> 0 <= bar_of w <= Int.max_unsigned.
Proof. intros. unfold bar_of. destruct (w =? 0); rep_lia. Qed.

Lemma ifeq_b2z: forall y, 0 <= y <= Int.max_unsigned ->
  Vint (if Int.eq (Int.repr y) Int.zero then Int.zero else Int.one) = Vint (Int.repr (Z.b2z (negb (y =? 0)))).
Proof.
  intros y Y. change Int.zero with (Int.repr 0). rewrite u32_eq by (unfold u32_ok; rep_lia).
  destruct (y =? 0); reflexivity.
Qed.

(* A 64-bit bitmap as the C assembles it from its two words. *)
Lemma cfg_val: forall bs k k', Forall u8_ok bs -> k' = k + 4 ->
  Int64.or (Int64.repr (Int.unsigned (Int.repr (le32 bs k))))
    (Int64.shl (Int64.repr (Int.unsigned (Int.repr (le32 bs k')))) (Int64.repr (Int.unsigned (Int.repr 32)))) =
  Int64.repr (le64 bs k).
Proof.
  intros bs k k' F E. subst k'.
  pose proof (le32_range bs k F) as A. pose proof (le32_range bs (k + 4) F) as B. unfold u32_ok in *.
  rewrite !Int.unsigned_repr by rep_lia. rewrite or64_lo_hi by (unfold u32_ok; rep_lia). reflexivity.
Qed.

(* The sink array after the loop's step i. *)
Lemma sinks_step: forall bs i (s0: list Z), 0 <= i < 8 -> Zlength s0 = 8 ->
  upd_Znth i (words_val (sinks_at bs i ++ sublist i 8 s0)) (Vint (Int.repr (le32 bs (68 + 4 * i)))) =
  words_val (sinks_at bs (i + 1) ++ sublist (i + 1) 8 s0).
Proof.
  intros bs i s0 I L.
  assert (La: forall j, 0 <= j -> Zlength (sinks_at bs j) = j) by (intros; apply Zlength_sinks_at; lia).
  apply Znth_eq_ext.
  { rewrite upd_Znth_Zlength by (rewrite Zlength_map, Zlength_app, La, Zlength_sublist; lia).
    rewrite !Zlength_map, !Zlength_app, !La, !Zlength_sublist by lia. lia. }
  intros j J. rewrite upd_Znth_Zlength in J by (rewrite Zlength_map, Zlength_app, La, Zlength_sublist; lia).
  rewrite Zlength_map, Zlength_app, La, Zlength_sublist in J by lia.
  rewrite (Znth_map j) by (rewrite Zlength_app, La, Zlength_sublist; lia).
  destruct (Z.lt_trichotomy j i) as [Lt | [Eq | Gt]].
  - rewrite upd_Znth_diff by (rewrite ?Zlength_map, ?Zlength_app, ?La, ?Zlength_sublist; lia).
    rewrite (Znth_map j) by (rewrite Zlength_app, La, Zlength_sublist; lia).
    rewrite !Znth_app1 by (rewrite La; lia). rewrite !Znth_sinks_at by lia. reflexivity.
  - subst j. rewrite upd_Znth_same by (rewrite Zlength_map, Zlength_app, La, Zlength_sublist; lia).
    rewrite Znth_app1 by (rewrite La; lia). rewrite Znth_sinks_at by lia. reflexivity.
  - rewrite upd_Znth_diff by (rewrite ?Zlength_map, ?Zlength_app, ?La, ?Zlength_sublist; lia).
    rewrite (Znth_map j) by (rewrite Zlength_app, La, Zlength_sublist; lia).
    rewrite !Znth_app2 by (rewrite La; lia). rewrite La, La by lia.
    rewrite !Znth_sublist by lia. f_equal. f_equal. f_equal. lia.
Qed.

Lemma pol_store_v3: forall bs P0, policy_wf P0 -> 0 <= le32 bs 64 <= 8 ->
  policy_val (store (v3_policy bs (le32 bs 64) 0 nil) P0) =
  pol_tuple (Vint (Int.repr 1)) (Vint (Int.repr (Z.land (le32 bs 32) 1))) (Vint (Int.repr (le32 bs 36)))
    (Vlong (Int64.repr (le64 bs 40))) (Vlong (Int64.repr (le64 bs 48))) (Vint (Int.repr (le32 bs 56)))
    (Vint (Int.repr (le32 bs 60))) (Vint (Int.repr (le32 bs 64)))
    (words_val (sinks_at bs (le32 bs 64) ++ sublist (le32 bs 64) 8 (pl_sinks P0))) (Vint (Int.repr 0))
    (map desc_val (pl_descs P0)).
Proof.
  intros bs P0 PW S. destruct PW as (_ & _ & _ & _ & _ & _ & _ & _ & Ls & _ & _ & Ld & _).
  unfold store, v3_policy, policy_val, policy_rep, pol_tuple.
  cbn [pl_present pl_dma pl_window pl_cfg_read pl_cfg_write pl_cmd_clear pl_cmd_set pl_sink_count pl_sinks
       pl_desc_count pl_descs app].
  rewrite (sublist_same 0 MAX_DESCS (pl_descs P0)) by (unfold MAX_DESCS in *; lia). reflexivity.
Qed.

(* The descriptor array with descs[i] replaced. *)
Lemma descs_join: forall sh (L: list desc_t) i x q, 0 <= i < 16 -> Zlength L = 16 ->
  field_compatible (tarray t_desc 16) [] q ->
  (data_at sh (tarray t_desc i) (sublist 0 i L) q *
   data_at sh t_desc x (offset_val (16 * i) q) *
   data_at sh (tarray t_desc (16 - (i + 1))) (sublist (i + 1) 16 L) (offset_val (16 * (i + 1)) q))%logic |--
  data_at sh (tarray t_desc 16) (upd_Znth i L x) q.
Proof.
  intros. rewrite (descs_split sh (upd_Znth i L x) i q) by (auto; rewrite upd_Znth_Zlength; lia).
  rewrite upd_Znth_same by lia. rewrite sublist_upd_Znth_l by lia. rewrite sublist_upd_Znth_r by lia.
  apply derives_refl.
Qed.

Lemma descs_at_snoc: forall bs A i, 0 <= i ->
  descs_at bs A (i + 1) = descs_at bs A i ++ [desc_at bs (A + 4 + 16 * i)].
Proof.
  intros bs A i I.
  apply Znth_eq_ext.
  { rewrite Zlength_app, !Zlength_descs_at by lia. rewrite Zlength_cons, Zlength_nil. lia. }
  intros j J. rewrite Zlength_descs_at in J by lia.
  rewrite Znth_descs_at by lia.
  destruct (zlt j i).
  - rewrite Znth_app1 by (rewrite Zlength_descs_at; lia). rewrite Znth_descs_at by lia. reflexivity.
  - rewrite Znth_app2 by (rewrite Zlength_descs_at; lia). rewrite Zlength_descs_at by lia.
    replace (j - i) with 0 by lia. replace j with i by lia. reflexivity.
Qed.

Lemma descs_step: forall bs A i (d0: list desc), 0 <= i < 16 -> Zlength d0 = 16 ->
  upd_Znth i (map desc_val (descs_at bs A i ++ sublist i 16 d0)) (desc_val (desc_at bs (A + 4 + 16 * i))) =
  map desc_val (descs_at bs A (i + 1) ++ sublist (i + 1) 16 d0).
Proof.
  intros bs A i d0 I L.
  rewrite descs_at_snoc by lia.
  assert (La: Zlength (descs_at bs A i) = i) by (apply Zlength_descs_at; lia).
  rewrite <- app_assoc. cbn [app].
  rewrite (sublist_split i (i + 1) 16 d0) by lia. rewrite (sublist_one i (i + 1) d0) by lia. cbn [app].
  rewrite !map_app. cbn [map].
  rewrite upd_Znth_app2 by (rewrite Zlength_map; rewrite ?Zlength_cons, ?Zlength_map, ?Zlength_sublist; lia).
  rewrite Zlength_map, La, Z.sub_diag. rewrite upd_Znth0. reflexivity.
Qed.

Lemma desc_limit_range: forall d, desc_wf d -> 1 <= ds_count d -> 0 <= desc_limit d <= Int64.max_unsigned.
Proof.
  intros d (Wt & Ws & Wc & Wd) C. unfold u32_ok in *. unfold desc_limit, desc_size.
  assert (0 <= ds_stride d * (ds_count d - 1) <= Int.max_unsigned * Int.max_unsigned) by nia.
  destruct (ds_trb d =? 0); rep_lia.
Qed.

Lemma ltu64_b2z: forall a b, 0 <= a <= Int64.max_unsigned -> 0 <= b <= Int64.max_unsigned ->
  bool2val (Int64.ltu (Int64.repr a) (Int64.repr b)) = Vint (Int.repr (Z.b2z (a <? b))).
Proof.
  intros. unfold Int64.ltu. rewrite !Int64.unsigned_repr by lia.
  destruct (zlt a b), (Z.ltb_spec a b); try lia; reflexivity.
Qed.

Lemma pol_store_v3d: forall bs P0 A, policy_wf P0 -> 0 <= le32 bs 64 <= 8 -> 0 <= le32 bs A <= 16 ->
  policy_val (store (v3_policy bs (le32 bs 64) (le32 bs A) (descs_at bs A (le32 bs A))) P0) =
  pol_tuple (Vint (Int.repr 1)) (Vint (Int.repr (Z.land (le32 bs 32) 1))) (Vint (Int.repr (le32 bs 36)))
    (Vlong (Int64.repr (le64 bs 40))) (Vlong (Int64.repr (le64 bs 48))) (Vint (Int.repr (le32 bs 56)))
    (Vint (Int.repr (le32 bs 60))) (Vint (Int.repr (le32 bs 64)))
    (words_val (sinks_at bs (le32 bs 64) ++ sublist (le32 bs 64) 8 (pl_sinks P0))) (Vint (Int.repr (le32 bs A)))
    (map desc_val (descs_at bs A (le32 bs A) ++ sublist (le32 bs A) 16 (pl_descs P0))).
Proof.
  intros bs P0 A PW S D.
  unfold store, v3_policy, policy_val, policy_rep, pol_tuple.
  cbn [pl_present pl_dma pl_window pl_cfg_read pl_cfg_write pl_cmd_clear pl_cmd_set pl_sink_count pl_sinks
       pl_desc_count pl_descs app].
  reflexivity.
Qed.

Lemma desc_ok_neg: forall d,
  desc_ok d = negb ((1 <? ds_trb d) || (ds_count d <? 1) || (4096 <? ds_count d) || (SCRATCH <? desc_limit d))%bool.
Proof.
  intros. unfold desc_ok. rewrite (Z.leb_antisym 1 (ds_trb d)), (Z.leb_antisym (ds_count d) 1),
    (Z.leb_antisym 4096 (ds_count d)), (Z.leb_antisym SCRATCH (desc_limit d)).
  destruct (1 <? ds_trb d), (ds_count d <? 1), (4096 <? ds_count d), (SCRATCH <? desc_limit d); reflexivity.
Qed.
