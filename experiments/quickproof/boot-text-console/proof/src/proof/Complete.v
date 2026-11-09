(* The buffer the law boot_text_parse_complete builds, and parse_model on it: pure Coq on lists. *)
Require Import VST.floyd.proofauto.
Require Import LeanosConsole.proof.Defs.

(* put32(p + k, v): the four little-endian bytes of v at k. *)
Definition upd4 (bs: list Z) (k v: Z) : list Z :=
  upd_Znth (k + 3) (upd_Znth (k + 2) (upd_Znth (k + 1) (upd_Znth k bs (v mod 256)) (v / 256 mod 256))
    (v / 65536 mod 256)) (v / 16777216 mod 256).

(* The stages of the harness: the fixed header, an optional other tag, the framebuffer tag, the end tag. *)
Definition stage_hdr (bs: list Z) (total: Z) : list Z := upd4 (upd4 bs 0 total) 4 0.
Definition stage_tag (b: bool) (bs: list Z) (o t s: Z) : list Z :=
  if b then upd4 (upd4 bs o t) (o + 4) s else bs.
Definition adv (b: bool) (s: Z) : Z := if b then round8 s else 0.
Definition stage_fields (bs: list Z) (o fb pitch width height: Z) : list Z :=
  upd4 (upd4 (upd4 (upd4 (upd4 (upd4 (upd4 bs o 8) (o + 4) fb) (o + 8) 753664) (o + 12) 0)
    (o + 16) pitch) (o + 20) width) (o + 24) height.
Definition stage_fb (bs: list Z) (o fb pitch width height: Z) : list Z :=
  upd_Znth (o + 29) (upd_Znth (o + 28) (stage_fields bs o fb pitch width height) 16) 2.
Definition stage_end (bs: list Z) (o: Z) : list Z := upd4 (upd4 bs o 0) (o + 4) 8.

(* ---------------------------------------------------------------------- *)
(* Bytes and words                                                        *)
(* ---------------------------------------------------------------------- *)

Lemma Zlength_upd4: forall bs k v, Zlength (upd4 bs k v) = Zlength bs.
Proof. intros. unfold upd4. rewrite !Zlength_upd_Znth. reflexivity. Qed.

Lemma Zlength_stage_hdr: forall bs t, Zlength (stage_hdr bs t) = Zlength bs.
Proof. intros. unfold stage_hdr. rewrite !Zlength_upd4. reflexivity. Qed.
Lemma Zlength_stage_tag: forall b bs o t s, Zlength (stage_tag b bs o t s) = Zlength bs.
Proof. intros. unfold stage_tag. destruct b; rewrite ?Zlength_upd4; reflexivity. Qed.
Lemma Zlength_stage_fields: forall bs o fb p w h, Zlength (stage_fields bs o fb p w h) = Zlength bs.
Proof. intros. unfold stage_fields. rewrite !Zlength_upd4. reflexivity. Qed.
Lemma Zlength_stage_fb: forall bs o fb p w h, Zlength (stage_fb bs o fb p w h) = Zlength bs.
Proof. intros. unfold stage_fb. rewrite !Zlength_upd_Znth, Zlength_stage_fields. reflexivity. Qed.
Lemma Zlength_stage_end: forall bs o, Zlength (stage_end bs o) = Zlength bs.
Proof. intros. unfold stage_end. rewrite !Zlength_upd4. reflexivity. Qed.

Lemma Znth_upd4_other: forall bs k v i, i < k \/ k + 4 <= i -> Znth i (upd4 bs k v) = Znth i bs.
Proof. intros. unfold upd4. rewrite !Znth_upd_Znth_diff by lia. reflexivity. Qed.

Lemma le32_upd4_other: forall bs k v j, j + 4 <= k \/ k + 4 <= j -> le32 (upd4 bs k v) j = le32 bs j.
Proof. intros. unfold le32. rewrite !Znth_upd4_other by lia. reflexivity. Qed.

Lemma le32_upd_other: forall bs i x j, i < j \/ j + 4 <= i -> le32 (upd_Znth i bs x) j = le32 bs j.
Proof. intros. unfold le32. rewrite !Znth_upd_Znth_diff by lia. reflexivity. Qed.

Lemma le32_upd4_same: forall bs k v,
  0 <= k -> k + 4 <= Zlength bs -> 0 <= v <= Int.max_unsigned -> le32 (upd4 bs k v) k = v.
Proof.
  intros bs k v Hk Hl Hv. unfold le32, upd4.
  assert (L1: Zlength (upd_Znth k bs (v mod 256)) = Zlength bs) by apply Zlength_upd_Znth.
  assert (L2: Zlength (upd_Znth (k + 1) (upd_Znth k bs (v mod 256)) (v / 256 mod 256)) = Zlength bs)
    by (rewrite !Zlength_upd_Znth; reflexivity).
  assert (L3: Zlength (upd_Znth (k + 2) (upd_Znth (k + 1) (upd_Znth k bs (v mod 256)) (v / 256 mod 256))
                 (v / 65536 mod 256)) = Zlength bs) by (rewrite !Zlength_upd_Znth; reflexivity).
  rewrite (Znth_upd_Znth_same _ _ (k + 3)) by lia.
  rewrite (Znth_upd_Znth_diff _ _ (k + 2) (k + 3)) by lia.
  rewrite (Znth_upd_Znth_same _ _ (k + 2)) by lia.
  rewrite (Znth_upd_Znth_diff _ _ (k + 1) (k + 3)) by lia.
  rewrite (Znth_upd_Znth_diff _ _ (k + 1) (k + 2)) by lia.
  rewrite (Znth_upd_Znth_same _ _ (k + 1)) by lia.
  rewrite (Znth_upd_Znth_diff _ _ k (k + 3)) by lia.
  rewrite (Znth_upd_Znth_diff _ _ k (k + 2)) by lia.
  rewrite (Znth_upd_Znth_diff _ _ k (k + 1)) by lia.
  rewrite (Znth_upd_Znth_same _ _ k) by lia.
  assert (D1: v = 256 * (v / 256) + v mod 256) by (apply Z_div_mod_eq_full).
  assert (D2: v / 256 = 256 * (v / 65536) + v / 256 mod 256).
  { replace (v / 65536) with (v / 256 / 256) by (rewrite Z.div_div by lia; reflexivity).
    apply Z_div_mod_eq_full. }
  assert (D3: v / 65536 = 256 * (v / 16777216) + v / 65536 mod 256).
  { replace (v / 16777216) with (v / 65536 / 256) by (rewrite Z.div_div by lia; reflexivity).
    apply Z_div_mod_eq_full. }
  assert (B4: 0 <= v / 16777216 < 256).
  { split; [ apply Z.div_pos; lia | apply Z.div_lt_upper_bound; rep_lia ]. }
  rewrite (Z.mod_small (v / 16777216) 256) by lia.
  lia.
Qed.

Lemma Znth_upd_same': forall (bs: list Z) i x, 0 <= i < Zlength bs -> Znth i (upd_Znth i bs x) = x.
Proof. intros. apply upd_Znth_same. lia. Qed.

(* ---------------------------------------------------------------------- *)
(* round8 and the walk, one tag at a time                                 *)
(* ---------------------------------------------------------------------- *)

Lemma round8_range: forall s, 8 <= s <= 64 ->
  s <= round8 s <= 64 /\ round8 s mod 8 = 0 /\ round8 s <= s + 7.
Proof.
  intros s Hs. unfold round8.
  assert (D: s + 7 = 8 * ((s + 7) / 8) + (s + 7) mod 8) by (apply Z_div_mod_eq_full).
  assert (M: 0 <= (s + 7) mod 8 < 8) by (apply Z.mod_pos_bound; lia).
  rewrite Z.mod_mul by lia. lia.
Qed.

Lemma adv_range: forall b s, 8 <= s <= 64 -> 0 <= adv b s <= 64 /\ adv b s mod 8 = 0.
Proof. intros. unfold adv. destruct b; [ pose proof (round8_range s H); lia | split; [ lia | reflexivity ] ]. Qed.

Lemma round8_8: round8 8 = 8.
Proof. reflexivity. Qed.

Lemma walk_other_step: forall f bs total offset seen t sz,
  le32 bs offset = t -> le32 bs (offset + 4) = sz ->
  offset <= total - 8 -> 8 <= sz -> round8 sz <= total - offset -> sz <= round8 sz -> t <> 0 -> t <> 8 ->
  walk (S f) bs total offset seen = walk f bs total (offset + round8 sz) seen.
Proof.
  intros f bs total offset seen t sz Et Es. intros. simpl. rewrite Et, Es.
  rewrite (proj2 (Z.leb_le offset (total - 8))) by lia.
  rewrite (proj2 (Z.ltb_ge sz 8)) by lia.
  rewrite (proj2 (Z.ltb_ge (total - offset) sz)) by lia.
  rewrite (proj2 (Z.ltb_ge (total - offset) (round8 sz))) by lia.
  rewrite (proj2 (Z.eqb_neq t 0)) by lia.
  rewrite (proj2 (Z.eqb_neq t 8)) by lia.
  reflexivity.
Qed.

Lemma walk_fb_step: forall f bs total offset sz,
  le32 bs offset = 8 -> le32 bs (offset + 4) = sz ->
  offset <= total - 8 -> 32 <= sz -> round8 sz <= total - offset -> sz <= round8 sz ->
  walk (S f) bs total offset None = walk f bs total (offset + round8 sz) (Some (geo_at bs offset)).
Proof.
  intros f bs total offset sz Et Es. intros. simpl. rewrite Et, Es.
  rewrite (proj2 (Z.leb_le offset (total - 8))) by lia.
  rewrite (proj2 (Z.ltb_ge sz 8)) by lia.
  rewrite (proj2 (Z.ltb_ge (total - offset) sz)) by lia.
  rewrite (proj2 (Z.ltb_ge (total - offset) (round8 sz))) by lia.
  simpl.
  rewrite (proj2 (Z.ltb_ge sz 32)) by lia.
  reflexivity.
Qed.

Lemma walk_end_step: forall f bs total offset g,
  le32 bs offset = 0 -> le32 bs (offset + 4) = 8 -> offset + 8 = total -> geo_valid g = true ->
  walk (S f) bs total offset (Some g) = Some g.
Proof.
  intros f bs total offset g Et Es. intros. simpl. rewrite Et, Es, round8_8.
  rewrite (proj2 (Z.leb_le offset (total - 8))) by lia.
  rewrite (proj2 (Z.ltb_ge 8 8)) by lia.
  rewrite (proj2 (Z.ltb_ge (total - offset) 8)) by lia.
  rewrite H0. simpl.
  replace (offset + 8 =? total) with true by (symmetry; apply Z.eqb_eq; lia).
  reflexivity.
Qed.

Lemma parse_model_walk: forall bs total,
  Zlength bs = total -> 16 <= total <= 65536 -> total mod 8 = 0 -> le32 bs 0 = total -> le32 bs 4 = 0 ->
  parse_model bs total = walk (Z.to_nat total) bs total 8 None.
Proof.
  intros bs total L T M E0 E4. unfold parse_model. rewrite E0, E4.
  rewrite (proj2 (Z.ltb_ge total 16)) by lia.
  rewrite (proj2 (Z.ltb_ge total total)) by lia.
  rewrite (proj2 (Z.ltb_ge 65536 total)) by lia.
  rewrite M. reflexivity.
Qed.

Lemma fuel_S: forall t, 1 <= t -> Z.to_nat t = S (Z.to_nat (t - 1)).
Proof. intros. rewrite <- Z2Nat.inj_succ by lia. f_equal. lia. Qed.

(* ---------------------------------------------------------------------- *)
(* The model on the law's buffer                                          *)
(* ---------------------------------------------------------------------- *)

Definition final_buf (bs0: list Z) (others type0 size0 type1 size1 fb pitch width height: Z) : list Z :=
  let b1 := 1 <=? others in let b2 := 2 <=? others in
  let o2 := 8 + adv b1 size0 in let o3 := o2 + adv b2 size1 in let o4 := o3 + round8 fb in
  stage_end (stage_fb (stage_tag b2 (stage_tag b1 (stage_hdr bs0 (o4 + 8)) 8 type0 size0) o2 type1 size1)
                      o3 fb pitch width height) o4.

Definition final_total (others size0 size1 fb: Z) : Z :=
  8 + adv (1 <=? others) size0 + adv (2 <=? others) size1 + round8 fb + 8.

Lemma le32_upd4_at: forall bs k v j,
  j = k -> 0 <= k -> k + 4 <= Zlength bs -> 0 <= v <= Int.max_unsigned -> le32 (upd4 bs k v) j = v.
Proof. intros. subst. apply le32_upd4_same; auto. Qed.

Lemma Znth_upd_at: forall (bs: list Z) i j x, j = i -> 0 <= i < Zlength bs -> Znth j (upd_Znth i bs x) = x.
Proof. intros. subst. apply upd_Znth_same. lia. Qed.

Ltac len := repeat (rewrite Zlength_upd4 || rewrite Zlength_upd_Znth).

(* Peel the writes off a le32 or Znth read: the disjoint ones go, the one at the read gives its value. *)
Ltac peel :=
  repeat first
    [ rewrite le32_upd4_at by (len; rep_lia)
    | rewrite le32_upd4_other by lia
    | rewrite le32_upd_other by lia
    | rewrite Znth_upd_at by (len; rep_lia)
    | rewrite Znth_upd4_other by lia
    | rewrite Znth_upd_Znth_diff by lia ].

Ltac stages := unfold stage_end, stage_fb, stage_fields, stage_tag, stage_hdr.

(* A side condition of a walk step: arithmetic, or a read of the buffer BB. *)
Ltac side :=
  first [ lia
        | (Z.div_mod_to_equations; lia)
        | match goal with BB := _ |- _ => unfold BB; stages; cbv iota; peel; lia end ].

Lemma complete_model: forall bs0 others type0 size0 type1 size1 fb pitch width height,
  0 <= others <= 2 ->
  0 <= type0 <= Int.max_unsigned -> type0 <> 0 -> type0 <> 8 -> 8 <= size0 <= 64 ->
  0 <= type1 <= Int.max_unsigned -> type1 <> 0 -> type1 <> 8 -> 8 <= size1 <= 64 ->
  32 <= fb <= 64 ->
  0 <= pitch <= Int.max_unsigned -> 0 <= width <= Int.max_unsigned -> 0 <= height <= Int.max_unsigned ->
  valid_geo 2 16 753664 pitch width height = true ->
  Zlength bs0 = final_total others size0 size1 fb ->
  parse_model (final_buf bs0 others type0 size0 type1 size1 fb pitch width height)
              (final_total others size0 size1 fb)
  = Some (mkgeo 753664 pitch width height 2 16).
Proof.
  intros until height. intros Ho Ht0 Ht0a Ht0b Hs0 Ht1 Ht1a Ht1b Hs1 Hfb Hp Hw Hh Hv Hlen.
  destruct (round8_range size0 Hs0) as (R0 & R0m & R0u).
  destruct (round8_range size1 Hs1) as (R1 & R1m & R1u).
  destruct (round8_range fb ltac:(lia)) as (Rf & Rfm & Rfu).
  assert (GV: geo_valid (mkgeo 753664 pitch width height 2 16) = true) by exact Hv.
  unfold final_buf, final_total in *. cbv zeta.
  assert (Ho3: others = 0 \/ others = 1 \/ others = 2) by lia.
  unfold adv in *.
  destruct Ho3 as [-> | [-> | ->]];
    [ replace (1 <=? 0) with false in * by reflexivity; replace (2 <=? 0) with false in * by reflexivity
    | replace (1 <=? 1) with true in * by reflexivity; replace (2 <=? 1) with false in * by reflexivity
    | replace (1 <=? 2) with true in * by reflexivity; replace (2 <=? 2) with true in * by reflexivity ];
    cbv iota in *;
    match goal with |- parse_model ?B ?T = _ => set (BB := B) end;
    match goal with |- parse_model _ ?T = _ =>
      assert (LB: Zlength BB = T) by (unfold BB; stages; cbv iota; len; lia) end;
    rewrite parse_model_walk by side;
    rewrite fuel_S by lia.
  - (* the framebuffer tag at 8, the end tag after it *)
    rewrite (walk_fb_step _ BB _ 8 fb) by side.
    assert (GA: geo_at BB 8 = mkgeo 753664 pitch width height 2 16).
    { unfold BB, geo_at; stages; cbv iota; peel. f_equal; lia. }
    rewrite GA, fuel_S by lia.
    apply walk_end_step; [ side .. | exact GV ].
  - (* one other tag at 8 *)
    rewrite (walk_other_step _ BB _ 8 None type0 size0) by side.
    rewrite fuel_S by lia.
    rewrite (walk_fb_step _ BB _ (8 + round8 size0) fb) by side.
    assert (GA: geo_at BB (8 + round8 size0) = mkgeo 753664 pitch width height 2 16).
    { unfold BB, geo_at; stages; cbv iota; peel. f_equal; lia. }
    rewrite GA, fuel_S by lia.
    apply walk_end_step; [ side .. | exact GV ].
  - (* two other tags *)
    rewrite (walk_other_step _ BB _ 8 None type0 size0) by side.
    rewrite fuel_S by lia.
    rewrite (walk_other_step _ BB _ (8 + round8 size0) None type1 size1)
      by side.
    rewrite fuel_S by lia.
    rewrite (walk_fb_step _ BB _ (8 + round8 size0 + round8 size1) fb)
      by side.
    assert (GA: geo_at BB (8 + round8 size0 + round8 size1) = mkgeo 753664 pitch width height 2 16).
    { unfold BB, geo_at; stages; cbv iota; peel. f_equal; lia. }
    rewrite GA, fuel_S by lia.
    apply walk_end_step; [ side .. | exact GV ].
Qed.

(* Every byte the harness writes is a byte. *)
Definition bytes_in (bs: list Z) : Prop := Forall (fun b => 0 <= b <= 255) bs.

Lemma bytes_in_upd: forall bs i x, bytes_in bs -> 0 <= x <= 255 -> bytes_in (upd_Znth i bs x).
Proof. intros. apply Forall_upd_Znth; auto. Qed.

Lemma bytes_in_upd4: forall bs k v, bytes_in bs -> bytes_in (upd4 bs k v).
Proof.
  intros. unfold upd4.
  repeat apply bytes_in_upd; auto;
    match goal with |- 0 <= ?a mod 256 <= 255 => pose proof (Z.mod_pos_bound a 256 ltac:(lia)); lia end.
Qed.

Lemma bytes_in_final: forall bs0 others type0 size0 type1 size1 fb pitch width height,
  bytes_in bs0 -> bytes_in (final_buf bs0 others type0 size0 type1 size1 fb pitch width height).
Proof.
  intros. unfold final_buf. cbv zeta.
  unfold stage_end, stage_fb, stage_fields.
  repeat apply bytes_in_upd4.
  apply bytes_in_upd; [ | lia ]. apply bytes_in_upd; [ | lia ].
  repeat apply bytes_in_upd4.
  unfold stage_tag. destruct (2 <=? others); [ repeat apply bytes_in_upd4 | ];
  (destruct (1 <=? others); [ repeat apply bytes_in_upd4 | ]); unfold stage_hdr; repeat apply bytes_in_upd4; auto.
Qed.
