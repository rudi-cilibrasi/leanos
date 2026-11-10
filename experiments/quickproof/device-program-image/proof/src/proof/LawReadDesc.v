(* Law image_exact: read_image's descriptor map (version 3 with flags bit 1): the map's length and count checks,
   and each descriptor's checks and fields. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env.
Require Import LeanosDeviceProgramImage.harness.image_exact.code.
Require Import LeanosDeviceProgramImage.proof.Defs.
Require Import LeanosDeviceProgramImage.proof.LawProg LeanosDeviceProgramImage.proof.LawSpecs
  LeanosDeviceProgramImage.proof.LawLib LeanosDeviceProgramImage.proof.LawSplit
  LeanosDeviceProgramImage.proof.LawFacts LeanosDeviceProgramImage.proof.LawReadDefs.
Local Open Scope Z_scope.
#[local] Existing Instance LawProg.LCS.
Local Opaque Z.shiftr Z.land.

(* The state at the descriptor map: the version-3 scalars and sinks written, at = 68 + 4S. *)
Definition ri_predesc (sh: share) (b: val) (bs: list Z) (wsh: share) (r: val) : environ -> mpred :=
  (PROP (v3s_ok bs; Z.land (le32 bs 32) 2 <> 0)
   LOCAL (temp _at (Vint (Int.repr (68 + 4 * le32 bs 64))); temp _p (offset_val 32 r); temp _b b;
          temp _len (Vint (Int.repr (Zlength bs))); temp _r r)
   SEP (data_at sh (tarray tuchar (Zlength bs)) (bytes_val bs) b;
        ri_rep wsh r (Vint (Int.repr 2)) Vundef (target_val (target_of bs))
          (Vint (Int.repr 1)) (Vint (Int.repr (Z.land (le32 bs 32) 1))) (Vint (Int.repr (le32 bs 36)))
          (Vlong (Int64.repr (le64 bs 40))) (Vlong (Int64.repr (le64 bs 48))) (Vint (Int.repr (le32 bs 56)))
          (Vint (Int.repr (le32 bs 60))) (Vint (Int.repr (le32 bs 64)))
          (words_val (sinks_at bs (le32 bs 64)) ++ Zrepeat Vundef (8 - le32 bs 64)) z32 (Zrepeat udesc 16)
          Vundef Vundef (Vint (Int.repr 2))))%assert.

Lemma add64_repr': forall a b, Int64.add (Int64.repr a) (Int64.repr b) = Int64.repr (a + b).
Proof.
  intros. unfold Int64.add. apply Int64.eqm_samerepr. apply Int64.eqm_add; apply Int64.eqm_sym, Int64.eqm_unsigned_repr.
Qed.

Lemma mul64_repr': forall a b, Int64.mul (Int64.repr a) (Int64.repr b) = Int64.repr (a * b).
Proof.
  intros. unfold Int64.mul. apply Int64.eqm_samerepr. apply Int64.eqm_mult; apply Int64.eqm_sym, Int64.eqm_unsigned_repr.
Qed.

Lemma Int64_ltu_u64: forall a b, u64_ok a -> u64_ok b -> Int64.ltu (Int64.repr a) (Int64.repr b) = (a <? b).
Proof.
  intros a b Ha Hb. unfold u64_ok in *. unfold Int64.ltu. rewrite !Int64.unsigned_repr by auto.
  destruct (zlt a b); destruct (Z.ltb_spec a b); auto; lia.
Qed.

Lemma forallb_sub_step {A} {d: Inhabitant A}: forall (f: A -> bool) (l: list A) i, 0 <= i < Zlength l ->
  forallb f (sublist 0 (i + 1) l) = (forallb f (sublist 0 i l) && f (Znth i l))%bool.
Proof.
  intros. rewrite (sublist_split 0 i (i + 1)) by lia. rewrite sublist_len_1 by lia.
  rewrite forallb_app. simpl. rewrite andb_true_r. reflexivity.
Qed.

Lemma forallb_Znth_false {A} {d: Inhabitant A}: forall (f: A -> bool) (l: list A) i, 0 <= i < Zlength l ->
  f (Znth i l) = false -> forallb f l = false.
Proof.
  intros f l i I E. destruct (forallb f l) eqn:F; [ | reflexivity ].
  rewrite forallb_forall in F. rewrite F in E; [ discriminate | apply Znth_In; lia ].
Qed.

Lemma upd_sub_fill {A B} {da: Inhabitant A} {db: Inhabitant B}: forall (f: A -> B) (l: list A) i n (u: B),
  0 <= i < n -> i < Zlength l ->
  upd_Znth i (map f (sublist 0 i l) ++ Zrepeat u (n - i)) (f (Znth i l)) =
  map f (sublist 0 (i + 1) l) ++ Zrepeat u (n - (i + 1)).
Proof. intros. list_solve. Qed.

Lemma Znth_fill {A} {d: Inhabitant A}: forall (l: list A) i n (u: A), Zlength l = i -> i < n ->
  Znth i (l ++ Zrepeat u (n - i)) = u.
Proof. intros. subst i. list_solve. Qed.

Lemma lim64: forall st sd c sz, u32_ok st -> u32_ok sd -> 1 <= c <= 4096 -> 0 <= sz <= 16 ->
  Int64.unsigned (Int64.add (Int64.add (Int64.repr (Int.unsigned (Int.repr st)))
    (Int64.mul (Int64.repr (Int.unsigned (Int.repr sd))) (Int64.repr (Int.unsigned (Int.repr (c - 1))))))
    (Int64.repr (Int.unsigned (Int.repr sz)))) = st + sd * (c - 1) + sz.
Proof.
  intros st sd c sz A B C D. unfold u32_ok in *.
  rewrite !Int.unsigned_repr by rep_lia. rewrite mul64_repr', !add64_repr'.
  rewrite Int64.unsigned_repr; [ reflexivity | ].
  assert (0 <= sd * (c - 1) <= Int.max_unsigned * 4095) by nia. rep_lia.
Qed.

Lemma desc_limit_at: forall bs e, desc_limit (desc_at bs e) =
  le32 bs (e + 4) + le32 bs (e + 12) * (le32 bs (e + 8) - 1) + (if le32 bs e =? 0 then 8 else 16).
Proof. reflexivity. Qed.

Lemma ri_desc {Espec: OracleKind}: forall sh b bs wsh r,
  readable_share sh -> writable_share wsh -> image_ok bs -> field_compatible t_law_image nil r ->
  semax ri_delta (ri_predesc sh b bs wsh r) s_desc (overridePost (ri_join sh b bs wsh r) (ri_post sh b bs wsh r)).
Proof.
  intros sh b bs wsh r SH WSH IM FCr.
  start_part. unfold ri_predesc. Intros.
  rename H into V3s, H0 into FL. pose proof IM as [Hlen F].
  pose proof V3s as (V3 & C1 & C2 & C3 & C4).
  assert (W: forall k, u32_ok (le32 bs k)) by (intros; apply le32_range; auto).
  pose proof (W 64) as W64. pose proof W64 as [W64a W64b].
  unfold ri_rep, pol_fields. Intros.
  forward_if.
  { bfix. ri_ret FCr.
    assert (D: decode bs = None) by (apply dec_v3_shortA; auto; lia).
    unfold reading_ok, header_status, start_status, start. rewrite D. auto. }
  bfix.
  forward_call (sh, b, bs, 68 + 4 * le32 bs 64).
  pose proof (W (68 + 4 * le32 bs 64)) as WD.
  forward_if (temp _t'31 (Vint (Int.repr (Z.b2z ((16 <? le32 bs (68 + 4 * le32 bs 64)) ||
    (Zlength bs <? 68 + 4 * le32 bs 64 + 4 + 16 * le32 bs (68 + 4 * le32 bs 64)))%bool)))).
  { forward. entailer!. bfix. bdec. }
  { forward. entailer!. bfix. bsplit. bdec. }
  forward_if.
  { bfix. ri_ret FCr.
    assert (D: decode bs = None).
    { apply dec_v3_badD; auto; try lia.
      all: destruct (Z.ltb_spec 16 (le32 bs (68 + 4 * le32 bs 64))); [ left; lia | right ].
      all: destruct (Z.ltb_spec (Zlength bs) (68 + 4 * le32 bs 64 + 4 + 16 * le32 bs (68 + 4 * le32 bs 64)));
        [ lia | ].
      all: match goal with H: (_ || _)%bool = true |- _ => simpl in H; discriminate end. }
    unfold reading_ok, header_status, start_status, start. rewrite D. auto. }
  bfix. bsplit.
  remember (68 + 4 * le32 bs 64) as A eqn:EA.
  remember (le32 bs A) as D eqn:ED.
  set (DS := descs_at bs A D).
  assert (LD: Zlength DS = D) by (apply Zlength_descs_at; unfold u32_ok in WD; lia).
  forward_for_simple_bound D (EX i: Z,
    PROP (forallb desc_ok (sublist 0 i DS) = true)
    LOCAL (temp _descs (Vint (Int.repr D)); temp _at (Vint (Int.repr A));
           temp _p (offset_val 32 r); temp _b b; temp _len (Vint (Int.repr (Zlength bs))); temp _r r)
    SEP (data_at sh (tarray tuchar (Zlength bs)) (bytes_val bs) b;
         ri_rep wsh r (Vint (Int.repr 2)) Vundef (target_val (target_of bs))
           (Vint (Int.repr 1)) (Vint (Int.repr (Z.land (le32 bs 32) 1))) (Vint (Int.repr (le32 bs 36)))
           (Vlong (Int64.repr (le64 bs 40))) (Vlong (Int64.repr (le64 bs 48))) (Vint (Int.repr (le32 bs 56)))
           (Vint (Int.repr (le32 bs 60))) (Vint (Int.repr (le32 bs 64)))
           (words_val (sinks_at bs (le32 bs 64)) ++ Zrepeat Vundef (8 - le32 bs 64)) z32
           (map desc_val (sublist 0 i DS) ++ Zrepeat udesc (16 - i))
           Vundef Vundef (Vint (Int.repr 2))))%assert.
  { unfold ri_rep, pol_fields. entailer!. }
  { unfold ri_rep, pol_fields. Intros.
    forward. rewrite mul_repr, !add_repr.
    assert (Ei: A + 4 + 16 * i + 16 <= Zlength bs) by lia.
    assert (Di: Znth i DS = desc_at bs (A + 4 + 16 * i)) by (apply Znth_descs_at; lia).
    forward_call (sh, b, bs, A + 4 + 16 * i).
    forward_call (sh, b, bs, A + 4 + 16 * i + 4).
    forward_call (sh, b, bs, A + 4 + 16 * i + 8).
    forward_call (sh, b, bs, A + 4 + 16 * i + 12).
    set (e := A + 4 + 16 * i) in *.
    pose proof (W e) as K0. pose proof (W (e + 4)) as K4. pose proof (W (e + 8)) as K8.
    pose proof (W (e + 12)) as K12.
    forward_if (temp _t'36 (Vint (Int.repr (Z.b2z ((1 <? le32 bs e) || (le32 bs (e + 8) =? 0))%bool)))).
    { forward. entailer!. bfix. bdec. }
    { forward. entailer!. bfix. bdec. }
    forward_if (temp _t'37 (Vint (Int.repr (Z.b2z ((1 <? le32 bs e) || (le32 bs (e + 8) =? 0) ||
      (4096 <? le32 bs (e + 8)))%bool)))).
    { forward. entailer!. bfix. bdec. }
    { forward. entailer!. bfix. bdec. }
    forward_if.
    { bfix.
      assert (DF: desc_ok (Znth i DS) = false).
      { rewrite Di. fold e. unfold desc_ok, desc_at; cbn [ds_trb ds_start ds_count ds_stride].
        destruct (Z.leb_spec (le32 bs e) 1); [ | reflexivity ].
        destruct (Z.leb_spec 1 (le32 bs (e + 8))); [ | reflexivity ].
        destruct (Z.leb_spec (le32 bs (e + 8)) 4096); [ | reflexivity ].
        exfalso.
        match goal with Hb: (_ || _)%bool = true |- _ =>
          rewrite (proj2 (Z.ltb_ge 1 _)), (proj2 (Z.eqb_neq _ 0)), (proj2 (Z.ltb_ge 4096 _)) in Hb by lia;
          discriminate end. }
      assert (D0: decode bs = None).
      { clear - V3s FL H H0 H1 EA ED DF LD H2 Hlen. subst A D.
        rewrite (dec_v3_descs bs) by (auto; lia). fold DS.
        rewrite (forallb_Znth_false desc_ok DS i) by (auto; lia). reflexivity. }
      ri_ret FCr.
      unfold reading_ok, header_status, start_status, start. rewrite D0. auto. }
    bfix. bsplit.
    forward_if (temp _t'38 (Vint (Int.repr (if le32 bs e =? 0 then 8 else 16)))).
    { forward. entailer!. change Int.zero with (Int.repr 0) in *. bfix.
      destruct (Z.eqb_spec (le32 bs e) 0); [ congruence | reflexivity ]. }
    { forward. entailer!. change Int.zero with (Int.repr 0) in *. bfix.
      destruct (Z.eqb_spec (le32 bs e) 0); [ reflexivity | congruence ]. }
    assert (SZ: 0 <= (if le32 bs e =? 0 then 8 else 16) <= 16) by (destruct (le32 bs e =? 0); lia).
    forward_if.
    { match goal with Hl: context [Int64.add] |- _ =>
        rewrite lim64 in Hl by (try assumption; unfold u32_ok in *; lia); rewrite Int64.unsigned_repr in Hl by (unfold u32_ok in *; rep_lia) end.
      assert (DF: desc_ok (Znth i DS) = false).
      { rewrite Di. fold e. unfold desc_ok. rewrite desc_limit_at. unfold SCRATCH.
        rewrite (proj2 (Z.leb_gt (le32 bs (e + 4) + le32 bs (e + 12) * (le32 bs (e + 8) - 1) +
          (if le32 bs e =? 0 then 8 else 16)) 262144)) by lia.
        rewrite !andb_false_r. reflexivity. }
      assert (D0: decode bs = None).
      { clear - V3s FL H H0 H1 EA ED DF LD H2 Hlen. subst A D.
        rewrite (dec_v3_descs bs) by (auto; lia). fold DS.
        rewrite (forallb_Znth_false desc_ok DS i) by (auto; lia). reflexivity. }
      ri_ret FCr.
      unfold reading_ok, header_status, start_status, start. rewrite D0. auto. }
    match goal with Hl: context [Int64.add] |- _ =>
      rewrite lim64 in Hl by (try assumption; unfold u32_ok in *; lia); rewrite Int64.unsigned_repr in Hl by (unfold u32_ok in *; rep_lia) end.
    assert (DT: desc_ok (Znth i DS) = true).
    { pose proof K8 as [K8a K8b]. rewrite Di. fold e. unfold desc_ok. rewrite desc_limit_at. unfold SCRATCH. cbn [desc_at ds_trb ds_count].
      rewrite (proj2 (Z.leb_le (le32 bs (e + 4) + le32 bs (e + 12) * (le32 bs (e + 8) - 1) +
          (if le32 bs e =? 0 then 8 else 16)) 262144)) by lia.
      rewrite (proj2 (Z.leb_le _ 1)) by lia.
      rewrite (proj2 (Z.leb_le 1 _)) by lia. rewrite (proj2 (Z.leb_le _ 4096)) by lia. reflexivity. }
    assert (Lm: Zlength (map desc_val (sublist 0 i DS)) = i) by (rewrite Zlength_map, Zlength_sublist; lia).
    forward.
    rewrite (Znth_fill (map desc_val (sublist 0 i DS)) i 16) by (auto; lia).
    forward.
    rewrite upd_Znth_same by (rewrite Zlength_app, Zlength_Zrepeat; lia).
    rewrite upd_Znth_twice by (rewrite Zlength_app, Zlength_Zrepeat; lia).
    forward.
    rewrite upd_Znth_same by (rewrite Zlength_app, Zlength_Zrepeat; lia).
    rewrite upd_Znth_twice by (rewrite Zlength_app, Zlength_Zrepeat; lia).
    forward.
    rewrite upd_Znth_same by (rewrite Zlength_app, Zlength_Zrepeat; lia).
    rewrite upd_Znth_twice by (rewrite Zlength_app, Zlength_Zrepeat; lia).
    simpl fst; simpl snd.
    replace (Vint (Int.repr (le32 bs e)), (Vint (Int.repr (le32 bs (e + 4))), (Vint (Int.repr (le32 bs (e + 8))),
      Vint (Int.repr (le32 bs (e + 12)))))) with (desc_val (Znth i DS)) by (rewrite Di; reflexivity).
    rewrite (upd_sub_fill desc_val DS i 16) by lia.
    unfold ri_rep, pol_fields. entailer!.
    rewrite forallb_sub_step by lia. rewrite H3, DT. reflexivity. }
  Intros. rename H2 into FA. rewrite sublist_same in * by lia.
  assert (D0: decode bs = Some (target_of bs, v3_policy bs (le32 bs 64) D DS, A + 4 + 16 * D)).
  { clear - V3s FL H H0 H1 EA ED FA LD Hlen. subst A D.
    rewrite (dec_v3_descs bs) by (auto; lia). fold DS. rewrite FA. reflexivity. }
  unfold ri_rep, pol_fields. Intros.
  forward. forward.
  unfold ri_join.
  Exists (target_of bs) (v3_policy bs (le32 bs 64) D DS) (A + 4 + 16 * D) (Zrepeat Vundef (8 - le32 bs 64))
    (Zrepeat udesc (16 - D)).
  unfold v3_policy;
    cbn [pl_present pl_dma pl_window pl_cfg_read pl_cfg_write pl_cmd_clear pl_cmd_set pl_sink_count
         pl_sinks pl_desc_count pl_descs].
  unfold ri_rep, pol_fields. entailer!.
Qed.
