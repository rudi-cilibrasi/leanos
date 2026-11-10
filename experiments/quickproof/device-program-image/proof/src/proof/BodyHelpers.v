(* The bodies of the two arithmetic helpers of wifi-exec.h: wifi_le32 (word@k of the image object, through a
   four-byte window split out of the image array) and wifi_desc_limit (64-bit arithmetic without wrap). *)
Require Import VST.floyd.proofauto.
Require Import LeanosDeviceProgramImage.device_program.code.
Require Import LeanosDeviceProgramImage.proof.Specs.
#[local] Existing Instance Specs.CS.
Local Open Scope Z_scope.

Lemma u8_Znth: forall bs j, Forall u8_ok bs -> 0 <= j < Zlength bs -> 0 <= Znth j bs <= 255.
Proof.
  intros bs j F J. assert (I: In (Znth j bs) bs) by (apply Znth_In; lia).
  rewrite Forall_forall in F. specialize (F _ I). unfold u8_ok in F. rep_lia.
Qed.

(* The four bytes k..k+3 of an image as values. *)
Lemma sublist_bytes4: forall (bs: list Z) k, 0 <= k -> k + 4 <= Zlength bs ->
  sublist k (k + 4) (bytes_val bs) =
  [Vint (Int.repr (Znth k bs)); Vint (Int.repr (Znth (k + 1) bs));
   Vint (Int.repr (Znth (k + 2) bs)); Vint (Int.repr (Znth (k + 3) bs))].
Proof.
  intros bs k K0 K4.
  apply Znth_eq_ext; [ rewrite Zlength_sublist by (rewrite ?Zlength_map; lia); rewrite !Zlength_cons, Zlength_nil; lia | ].
  intros i I. rewrite Zlength_sublist in I by (rewrite ?Zlength_map; lia).
  rewrite Znth_sublist by (rewrite ?Zlength_map; lia). rewrite Znth_map by lia.
  assert (i = 0 \/ i = 1 \/ i = 2 \/ i = 3) as [-> | [-> | [-> | ->]]] by lia; cbn; do 3 f_equal; lia.
Qed.

(* The image array around the four bytes at k. *)
Lemma bytes_window: forall sh (bs: list Z) k b, 0 <= k -> k + 4 <= Zlength bs ->
  field_compatible (tarray tuchar (Zlength bs)) [] b ->
  data_at sh (tarray tuchar (Zlength bs)) (bytes_val bs) b =
  (data_at sh (tarray tuchar k) (sublist 0 k (bytes_val bs)) b *
  data_at sh (tarray tuchar 4)
    [Vint (Int.repr (Znth k bs)); Vint (Int.repr (Znth (k + 1) bs));
     Vint (Int.repr (Znth (k + 2) bs)); Vint (Int.repr (Znth (k + 3) bs))] (offset_val k b) *
  data_at sh (tarray tuchar (Zlength bs - (k + 4))) (sublist (k + 4) (Zlength bs) (bytes_val bs))
    (offset_val (k + 4) b))%logic.
Proof.
  intros sh bs k b K0 K4 FC. unfold tarray.
  rewrite (split3_data_at_Tarray_tuchar sh (Zlength bs) k (k + 4)) by (rewrite ?Zlength_map; lia).
  rewrite sublist_bytes4 by lia.
  rewrite !field_address0_offset by auto with field_compatible.
  simpl nested_field_offset. replace (0 + 1 * k) with k by lia. replace (0 + 1 * (k + 4)) with (k + 4) by lia.
  replace (k + 4 - k) with 4 by lia. reflexivity.
Qed.

Lemma Znth4_0: forall A (d: Inhabitant A) (a0 a1 a2 a3: A), @Znth A d 0 [a0; a1; a2; a3] = a0.
Proof. reflexivity. Qed.
Lemma Znth4_1: forall A (d: Inhabitant A) (a0 a1 a2 a3: A), @Znth A d 1 [a0; a1; a2; a3] = a1.
Proof. reflexivity. Qed.
Lemma Znth4_2: forall A (d: Inhabitant A) (a0 a1 a2 a3: A), @Znth A d 2 [a0; a1; a2; a3] = a2.
Proof. reflexivity. Qed.
Lemma Znth4_3: forall A (d: Inhabitant A) (a0 a1 a2 a3: A), @Znth A d 3 [a0; a1; a2; a3] = a3.
Proof. reflexivity. Qed.

Lemma body_wifi_le32 : semax_body Vprog Gprog f_wifi_le32 le32_spec.
Proof.
  start_function.
  rename H into K0, H0 into K4, H1 into U8.
  assert_PROP (field_compatible (tarray tuchar (Zlength bs)) [] b) as FC by entailer!.
  pose proof (u8_Znth bs k U8 ltac:(lia)) as B0.
  pose proof (u8_Znth bs (k + 1) U8 ltac:(lia)) as B1.
  pose proof (u8_Znth bs (k + 2) U8 ltac:(lia)) as B2.
  pose proof (u8_Znth bs (k + 3) U8 ltac:(lia)) as B3.
  rewrite (bytes_window sh bs k b) by auto. Intros.
  do 4 (forward; [ entailer!; rep_lia | ]).
  forward.
  rewrite Znth4_0, Znth4_1, Znth4_2, Znth4_3.
  entailer!.
  - cbn. rewrite le32_or by (unfold u8_ok; rep_lia). unfold le32. reflexivity.
  - rewrite (bytes_window sh bs k b) by auto. cancel.
Qed.

Lemma body_wifi_desc_limit : semax_body Vprog Gprog f_wifi_desc_limit desc_limit_spec.
Proof.
  start_function.
  rename H into DW, H0 into C1.
  destruct d as [trb st cnt strd]. unfold desc_wf in DW; cbn [ds_trb ds_start ds_count ds_stride] in *.
  destruct DW as (Wt & Ws & Wc & Wd). unfold u32_ok in *.
  unfold desc_val; cbn [ds_trb ds_start ds_count ds_stride].
  forward.
  forward_if (PROP () LOCAL (temp _t'1 (Vint (Int.repr (if trb =? 0 then 8 else 16))); temp _d p)
              SEP (data_at sh t_desc (Vint (Int.repr trb), (Vint (Int.repr st), (Vint (Int.repr cnt),
                     Vint (Int.repr strd)))) p)).
  { forward. entailer!. destruct (Z.eqb_spec trb 0); [ subst; contradiction | reflexivity ]. }
  { forward. entailer!. rewrite (proj2 (Z.eqb_eq trb 0)); [ reflexivity | ].
    apply repr_inj_unsigned; auto; rep_lia. }
  forward. forward. forward.
  forward.
  apply prop_right. unfold desc_limit, desc_size; cbn [ds_trb ds_start ds_count ds_stride].
  destruct (trb =? 0); reflexivity.
Qed.
