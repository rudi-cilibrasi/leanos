(* Body proof of qotom_build_copy_roots (include/qotom_copy_root_builder.h) against build_copy_roots_spec. *)
Require Import VST.floyd.proofauto.
Require Import LeanosRoots.roots.code.
Require Import LeanosRoots.proof.Defs.
Require Import LeanosRoots.proof.RootsSpecs.
Require Import LeanosRoots.proof.BuildLemmas.
#[local] Existing Instance RootsSpecs.CS.
Local Open Scope Z_scope.

Ltac orb_l := match goal with
  | H: ?c = true |- context [(?c || _)%bool] => rewrite (orb_true_l' _ _ H)
  | H: ?c = false |- context [(?c || _)%bool] => rewrite (orb_false_l' _ _ H)
  end.
Ltac t_then := forward; entailer!; bfix; orb_l; reflexivity.
Ltac t_ptr := bfix; forward; [ entailer!; tc_ptr | entailer!; rewrite notbool_ptr by auto; orb_l; reflexivity ].
Ltac t_call_fin := entailer!; orb_l; match goal with |- context [b2z (negb ?c)] => destruct c; reflexivity end.
Ltac ptr_else_first :=
  forward; [ entailer!; tc_ptr
           | entailer!; rewrite notbool_ptr by auto; rewrite isnull_nonnull by assumption; reflexivity ].

Ltac al_tc := entailer!; rewrite Znth_app1 by (rewrite Zlength_map; lia); rewrite Znth_map by lia; unfold alias_val; simpl; auto.
Ltac al_val := rewrite Znth_app1 by (rewrite Zlength_map; lia); rewrite Znth_map by lia; cbn [alias_val].
Ltac u64 := repeat match goal with H: context [Int64.unsigned (Int64.repr ?x)] |- _ =>
  rewrite (Int64.unsigned_repr x) in H by (unfold word_ok in *; rep_lia) end.

Lemma body_qotom_build_copy_roots : semax_body Vprog Gprog f_qotom_build_copy_roots build_copy_roots_spec.
Proof.
  start_function.
  (* The NULL tests and the physical-range checks: status 1. *)
  forward_if (temp _t'1 (Vint (Int.repr (b2z (isnull source || isnull closed)))));
    [ tc_ptr | forward; entailer! | ptr_else_first | ].
  forward_if (temp _t'2 (Vint (Int.repr (b2z ((isnull source || isnull closed) || isnull copy))))); [ t_then | t_ptr | ].
  forward_if (temp _t'3 (Vint (Int.repr (b2z ((isnull source || isnull closed) || isnull copy || isnull frames))))); [ t_then | t_ptr | ].
  forward_if (temp _t'4 (Vint (Int.repr (b2z ((isnull source || isnull closed) || isnull copy || isnull frames || isnull aliases))))); [ t_then | t_ptr | ].
  forward_if (temp _t'5 (Vint (Int.repr (b2z ((isnull source || isnull closed) || isnull copy || isnull frames || isnull aliases || isnull result))))); [ t_then | t_ptr | ].
  forward_if (temp _t'6 (Vint (Int.repr (b2z ((isnull source || isnull closed) || isnull copy || isnull frames || isnull aliases || isnull result || negb (phys_ok sp)))))); [ t_then | bfix; forward_call sp; forward; t_call_fin | ].
  forward_if (temp _t'8 (Vint (Int.repr (b2z ((isnull source || isnull closed) || isnull copy || isnull frames || isnull aliases || isnull result || negb (phys_ok sp) || negb (phys_ok kp)))))); [ t_then | bfix; forward_call kp; forward; t_call_fin | ].
  forward_if (temp _t'10 (Vint (Int.repr (b2z ((isnull source || isnull closed) || isnull copy || isnull frames || isnull aliases || isnull result || negb (phys_ok sp) || negb (phys_ok kp) || negb (phys_ok cp)))))); [ t_then | bfix; forward_call cp; forward; t_call_fin | ].
  forward_if (temp _t'12 (Vint (Int.repr (b2z ((isnull source || isnull closed) || isnull copy || isnull frames || isnull aliases || isnull result || negb (phys_ok sp) || negb (phys_ok kp) || negb (phys_ok cp) || negb (disjoint sp kp)))))); [ t_then | bfix; forward_call (sp, kp); forward; t_call_fin | ].
  forward_if (temp _t'14 (Vint (Int.repr (b2z ((isnull source || isnull closed) || isnull copy || isnull frames || isnull aliases || isnull result || negb (phys_ok sp) || negb (phys_ok kp) || negb (phys_ok cp) || negb (disjoint sp kp) || negb (disjoint sp cp)))))); [ t_then | bfix; forward_call (sp, cp); forward; t_call_fin | ].
  forward_if (temp _t'16 (Vint (Int.repr (b2z ((isnull source || isnull closed) || isnull copy || isnull frames || isnull aliases || isnull result || negb (phys_ok sp) || negb (phys_ok kp) || negb (phys_ok cp) || negb (disjoint sp kp) || negb (disjoint sp cp) || negb (disjoint kp cp)))))); [ t_then | bfix; forward_call (kp, cp); forward; t_call_fin | ].
  deadvars!.
  forward_if.
  { forward. Exists 1. entailer!.
    - split; [ lia | intro X; exfalso; exact (phys_fail _ _ _ _ _ _ _ _ _ _ _ _ _ _ H17 X) ].
    - replace (1 =? 0) with false by reflexivity; cancel. }
  bfix.
  destruct (phys_pass _ _ _ _ _ _ _ _ _ H17) as (Nsource & Nclosed & Ncopy & Nframes & Naliases & Nresult & Bphys); clear H17.
  rewrite !maybe_at_nonnull by assumption.
  (* The source check: status 2. *)
  deadvars!.
  forward_call (source, ssh, src, sp).
  forward_if.
  { bfix; forward; Exists 2; rewrite !maybe_at_nonnull by assumption; entailer!.
    iff_fail (build_anc_false src sp kp cp fs n al m H17). }
  bfix.
  deadvars!.
  (* The inventory count: status 3. *)
  forward_if (temp _t'19 (Vint (Int.repr (b2z ((n =? 0) || (16 <? n)))))).
  { l64; subst n; forward; entailer!. }
  { l64; forward; entailer!.
    rewrite cmpu_z by (unfold word_ok in *; rep_lia); rewrite bool2val_b2z;
    rewrite (orb_false_l' _ _ (proj2 (Z.eqb_neq n 0) H18)); reflexivity. }
  forward_if.
  { bfix; forward; Exists 3; rewrite !maybe_at_nonnull by assumption; entailer!;
    iff_fail (build_inv_false src sp kp cp fs n al m (inv_count_false fs n H18 H3)). }
  bfix. destruct (count_ok n H18 H3) as [Hn1 Hn16].
  assert (Hnfs: n <= Zlength fs) by lia.
  deadvars!.
  (* The inventory loop: status 3. *)
  forward_for_simple_bound n (EX i: Z,
    PROP (forallb (fun f => f <? 2 ^ 40) (sublist 0 i fs) = true; distinct (sublist 0 i fs) = true)
    LOCAL (temp _source source; temp _closed closed; temp _closed_phys (Vlong (Int64.repr kp));
           temp _copy copy; temp _copy_phys (Vlong (Int64.repr cp)); temp _protected_frames frames;
           temp _protected_count (Vlong (Int64.repr n)); temp _aliases aliases;
           temp _alias_count (Vlong (Int64.repr m)); temp _result result;
           lvar _alias_writable (tarray tulong 2) v_alias_writable; lvar _alias_frame (tarray tulong 2) v_alias_frame;
           lvar _alias_page (tarray tulong 2) v_alias_page; lvar _frames (tarray tulong 16) v_frames)
    SEP (data_at ssh t_root (root_val src) source;
         data_at_ Tsh (tarray tulong 2) v_alias_writable; data_at_ Tsh (tarray tulong 2) v_alias_frame;
         data_at_ Tsh (tarray tulong 2) v_alias_page;
         data_at Tsh (tarray tulong 16) (longs (sublist 0 i fs) ++ Zrepeat Vundef (16 - i)) v_frames;
         data_at Tsh t_root kold closed; data_at Tsh t_root cold copy;
         data_at fsh (tarray tulong (Zlength fs)) (longs fs) frames;
         data_at ash (tarray t_alias (Zlength al + Zlength arest)) (map alias_val al ++ arest) aliases;
         data_at Tsh t_result rold result))%assert.
  { entailer!. }
  { cbv beta. Intros.
    forward.
    { entailer!; rewrite Znth_longs by lia; exact I. }
    rewrite Znth_longs by lia.
    assert (Wi: word_ok (Znth i fs)) by (apply Forall_Znth; auto; lia).
    forward_if.
    { assert (Big: 2 ^ 40 <= Znth i fs) by (rewrite Int64.unsigned_repr in H22 by (unfold word_ok in Wi; lia); change (Int64.unsigned (Int64.shl (Int64.repr 1) (Int64.repr 40))) with (2 ^ 40) in H22; lia).
      forward; Exists 3; rewrite !maybe_at_nonnull by assumption; entailer!;
      iff_fail (build_inv_false src sp kp cp fs n al m (inv_big_false fs n i H19 Hnfs Big)). }
    assert (Small: Znth i fs < 2 ^ 40) by (rewrite Int64.unsigned_repr in H22 by (unfold word_ok in Wi; lia); change (Int64.unsigned (Int64.shl (Int64.repr 1) (Int64.repr 40))) with (2 ^ 40) in H22; lia).
    clear H22.
    forward_for_simple_bound i (EX j: Z,
      PROP (member (Znth i fs) (sublist 0 j fs) = false)
      LOCAL (temp _frame (Vlong (Int64.repr (Znth i fs))); temp _i (Vlong (Int64.repr i));
             temp _source source; temp _closed closed; temp _closed_phys (Vlong (Int64.repr kp));
             temp _copy copy; temp _copy_phys (Vlong (Int64.repr cp)); temp _protected_frames frames;
             temp _protected_count (Vlong (Int64.repr n)); temp _aliases aliases;
             temp _alias_count (Vlong (Int64.repr m)); temp _result result;
             lvar _alias_writable (tarray tulong 2) v_alias_writable; lvar _alias_frame (tarray tulong 2) v_alias_frame;
             lvar _alias_page (tarray tulong 2) v_alias_page; lvar _frames (tarray tulong 16) v_frames)
      SEP (data_at ssh t_root (root_val src) source;
           data_at_ Tsh (tarray tulong 2) v_alias_writable; data_at_ Tsh (tarray tulong 2) v_alias_frame;
           data_at_ Tsh (tarray tulong 2) v_alias_page;
           data_at Tsh (tarray tulong 16) (longs (sublist 0 i fs) ++ Zrepeat Vundef (16 - i)) v_frames;
           data_at Tsh t_root kold closed; data_at Tsh t_root cold copy;
           data_at fsh (tarray tulong (Zlength fs)) (longs fs) frames;
           data_at ash (tarray t_alias (Zlength al + Zlength arest)) (map alias_val al ++ arest) aliases;
           data_at Tsh t_result rold result))%assert.
    { entailer!. }
    { cbv beta. Intros.
      forward.
      { entailer!; rewrite Znth_prefix by lia; exact I. }
      rewrite Znth_prefix by lia.
      assert (Wj: word_ok (Znth i0 fs)) by (apply Forall_Znth; auto; lia).
      forward_if.
      { rewrite eq_z in H24 by assumption; apply Z.eqb_eq in H24.
        forward; Exists 3; rewrite !maybe_at_nonnull by assumption; entailer!;
        iff_fail (build_inv_false src sp kp cp fs n al m (inv_dup_false fs n i i0 H22 (proj2 H19) Hnfs H24)). }
      forward; entailer!; rewrite member_snoc_sub by lia; rewrite H23; simpl; apply Z.eqb_neq; congruence. }
    Intros. forward.
    rewrite upd_prefix by lia.
    entailer!.
    rewrite forallb_snoc_sub, distinct_snoc_sub by lia;
      match goal with H1: forallb _ (sublist 0 i fs) = true, H2: distinct (sublist 0 i fs) = true,
                      H3: member _ (sublist 0 i fs) = false |- _ => rewrite H1, H2, H3 end;
      simpl; split; [ apply Z.ltb_lt; exact Small | reflexivity ]. }
  Intros.
  assert (Hinv: inventory_ok fs n = true) by (apply inv_ok; auto).
  deadvars!.
  (* The alias count: status 4. *)
  forward_if (temp _t'20 (Vint (Int.repr (b2z ((m =? 0) || (2 <? m)))))).
  { l64; subst m; forward; entailer!. }
  { l64; forward; entailer!. rewrite cmpu_z by (unfold word_ok in *; rep_lia); rewrite bool2val_b2z;
    match goal with Hm: m <> 0 |- _ => rewrite (orb_false_l' _ _ (proj2 (Z.eqb_neq m 0) Hm)) end; reflexivity. }
  forward_if.
  { bfix; forward; Exists 4; rewrite !maybe_at_nonnull by assumption; entailer!;
    match goal with Hc: ((m =? 0) || (2 <? m))%bool = true |- _ =>
      iff_fail (build_al_false src sp kp cp fs n al m (al_count_false src (sublist 0 n fs) al m Hc H4)) end. }
  bfix.
  match goal with Hc: ((m =? 0) || (2 <? m))%bool = false |- _ =>
    destruct (al_count_ok m Hc H4) as [Hm1 Hm2]; clear Hc end.
  assert (Hmal: m <= Zlength al) by lia.
  deadvars!.
  (* The alias loop: status 4. *)
  forward_for_simple_bound m (EX i: Z,
    PROP (forallb (alias_ok src (sublist 0 n fs)) (sublist 0 i al) = true;
          distinct (sublist 0 i (map a_page al)) = true; distinct (sublist 0 i (map a_frame al)) = true)
    LOCAL (temp _source source; temp _closed closed; temp _closed_phys (Vlong (Int64.repr kp));
           temp _copy copy; temp _copy_phys (Vlong (Int64.repr cp)); temp _protected_count (Vlong (Int64.repr n));
           temp _aliases aliases; temp _alias_count (Vlong (Int64.repr m)); temp _result result;
           lvar _alias_writable (tarray tulong 2) v_alias_writable; lvar _alias_frame (tarray tulong 2) v_alias_frame;
           lvar _alias_page (tarray tulong 2) v_alias_page; lvar _frames (tarray tulong 16) v_frames)
    SEP (data_at ssh t_root (root_val src) source;
         data_at Tsh (tarray tulong 2) (longs (sublist 0 i (map a_writable al)) ++ Zrepeat Vundef (2 - i)) v_alias_writable;
         data_at Tsh (tarray tulong 2) (longs (sublist 0 i (map a_frame al)) ++ Zrepeat Vundef (2 - i)) v_alias_frame;
         data_at Tsh (tarray tulong 2) (longs (sublist 0 i (map a_page al)) ++ Zrepeat Vundef (2 - i)) v_alias_page;
         data_at Tsh (tarray tulong 16) (longs (sublist 0 n fs) ++ Zrepeat Vundef (16 - n)) v_frames;
         data_at Tsh t_root kold closed; data_at Tsh t_root cold copy;
         data_at fsh (tarray tulong (Zlength fs)) (longs fs) frames;
         data_at ash (tarray t_alias (Zlength al + Zlength arest)) (map alias_val al ++ arest) aliases;
         data_at Tsh t_result rold result))%assert.
  { entailer!. }
  { cbv beta. Intros.
    assert (Wa: alias_wf (Znth i al)) by (apply Forall_Znth; auto; lia).
    destruct Wa as (Wpg & Wfr & Wwr).
    forward; [ entailer! | al_tc | al_val ].
    forward; [ entailer! | al_tc | al_val ].
    forward; [ entailer! | al_tc | al_val ].
    forward_if (temp _t'21 (Vint (Int.repr (b2z ((4096 <=? a_page (Znth i al)) || (1 <? a_writable (Znth i al))))))).
    { u64; forward; entailer!; rewrite (proj2 (Z.leb_le 4096 _)) by lia; reflexivity. }
    { u64; forward; entailer!.
      rewrite cmpu_z by (unfold word_ok in *; rep_lia); rewrite bool2val_b2z;
      rewrite (proj2 (Z.leb_gt 4096 _)) by lia; reflexivity. }
    forward_if (temp _t'22 (Vint (Int.repr (b2z ((4096 <=? a_page (Znth i al)) || (1 <? a_writable (Znth i al)) ||
                                                 negb (Znth (a_page (Znth i al)) (pt src) =? 0)))))).
    { t_then. }
    { match goal with Hc: ((4096 <=? a_page (Znth i al)) || (1 <? a_writable (Znth i al)))%bool = false |- _ =>
        apply orb_false_iff in Hc; destruct Hc as [Hpg Hwr]; apply Z.leb_gt in Hpg; apply Z.ltb_ge in Hwr end.
      assert (Lpt: Zlength (pt src) = 4096) by (destruct H as (_ & _ & _ & L & _); exact L).
      assert (Wpt: words_ok (pt src)) by (destruct H as (_ & _ & _ & _ & _ & _ & _ & L); exact L).
      forward.
      { entailer!. unfold word_ok in Wpg; lia. }
      { entailer!. rewrite Znth_longs by (unfold word_ok in Wpg; lia); exact I. }
      rewrite root_pt, Znth_longs by (unfold word_ok in Wpg; lia).
      forward.
      entailer!.
      rewrite cmpu_z by (try apply word_Znth; auto; unfold word_ok; rep_lia). rewrite bool2val_b2z.
      rewrite (proj2 (Z.leb_gt 4096 _)) by lia. rewrite (proj2 (Z.ltb_ge 1 _)) by lia. reflexivity. }
    match goal with Hi: 0 <= i < m |- _ => rename Hi into Him end.
    forward_if (temp _t'23 (Vint (Int.repr (b2z (negb (alias_ok src (sublist 0 n fs) (Znth i al))))))).
    { forward; entailer!; rewrite alias_ok_split;
        match goal with Hc: ?c = true |- context [negb (negb ?c && _)] => rewrite Hc end; reflexivity. }
    { bfix.
      rewrite (retype16 Tsh (sublist 0 n fs) n v_frames) by (try rewrite Zlength_sublist by lia; lia).
      forward_call (a_frame (Znth i al), v_frames, Tsh, sublist 0 n fs, Zrepeat Vundef (16 - n), n).
      { rewrite Zlength_sublist, Zlength_Zrepeat by lia; split; [ apply Forall_sublist; auto | rep_lia ]. }
      rewrite <- retype16 by (try rewrite Zlength_sublist by lia; lia).
      forward.
      entailer!.
      rewrite alias_ok_split, sub_sub by lia;
        match goal with Hc: ?c = false |- context [negb (negb ?c && _)] => rewrite Hc end;
        destruct (member (a_frame (Znth i al)) (sublist 0 n fs)); reflexivity. }
    forward_if.
    { forward; Exists 4; rewrite !maybe_at_nonnull by assumption; entailer!;
        match goal with Hc: alias_ok _ _ (Znth i al) = false |- _ =>
          iff_fail (build_al_false src sp kp cp fs n al m (al_bad_false src (sublist 0 n fs) al m i Him Hmal Hc)) end. }
    match goal with Hc: alias_ok _ _ (Znth i al) = true |- _ => rename Hc into Hok end.
    forward_for_simple_bound i (EX j: Z,
      PROP (member (a_page (Znth i al)) (sublist 0 j (map a_page al)) = false;
            member (a_frame (Znth i al)) (sublist 0 j (map a_frame al)) = false)
      LOCAL (temp _writable (Vlong (Int64.repr (a_writable (Znth i al))));
             temp _frame__1 (Vlong (Int64.repr (a_frame (Znth i al))));
             temp _page (Vlong (Int64.repr (a_page (Znth i al))));
             temp _i__1 (Vlong (Int64.repr i));
             temp _source source; temp _closed closed; temp _closed_phys (Vlong (Int64.repr kp));
             temp _copy copy; temp _copy_phys (Vlong (Int64.repr cp)); temp _protected_count (Vlong (Int64.repr n));
             temp _aliases aliases; temp _alias_count (Vlong (Int64.repr m)); temp _result result;
             lvar _alias_writable (tarray tulong 2) v_alias_writable; lvar _alias_frame (tarray tulong 2) v_alias_frame;
             lvar _alias_page (tarray tulong 2) v_alias_page; lvar _frames (tarray tulong 16) v_frames)
      SEP (data_at ssh t_root (root_val src) source;
           data_at Tsh (tarray tulong 2) (longs (sublist 0 i (map a_writable al)) ++ Zrepeat Vundef (2 - i)) v_alias_writable;
           data_at Tsh (tarray tulong 2) (longs (sublist 0 i (map a_frame al)) ++ Zrepeat Vundef (2 - i)) v_alias_frame;
           data_at Tsh (tarray tulong 2) (longs (sublist 0 i (map a_page al)) ++ Zrepeat Vundef (2 - i)) v_alias_page;
           data_at Tsh (tarray tulong 16) (longs (sublist 0 n fs) ++ Zrepeat Vundef (16 - n)) v_frames;
           data_at Tsh t_root kold closed; data_at Tsh t_root cold copy;
           data_at fsh (tarray tulong (Zlength fs)) (longs fs) frames;
           data_at ash (tarray t_alias (Zlength al + Zlength arest)) (map alias_val al ++ arest) aliases;
           data_at Tsh t_result rold result))%assert.
    { entailer!. }
    { cbv beta. Intros.
      assert (Wb: alias_wf (Znth i0 al)) by (apply Forall_Znth; auto; lia).
      destruct Wb as (Wpg0 & Wfr0 & Wwr0).
      match goal with Hj: 0 <= i0 < i |- _ => rename Hj into Hji end.
      forward.
      { entailer!; rewrite Znth_prefix_map by lia; exact I. }
      rewrite Znth_prefix_map by lia.
      forward_if (temp _t'25 (Vint (Int.repr (b2z ((a_page (Znth i al) =? a_page (Znth i0 al)) ||
                                                   (a_frame (Znth i al) =? a_frame (Znth i0 al))))))).
      { match goal with E: Int64.eq _ _ = true |- _ => rewrite eq_z in E by assumption;
          forward; entailer!; rewrite E; reflexivity end. }
      { match goal with E: Int64.repr _ <> Int64.repr _ |- _ => apply repr64_neq in E; rename E into Ene end.
        forward; [ entailer!; rewrite Znth_prefix_map by lia; exact I | ].
        rewrite Znth_prefix_map by lia.
        forward.
        entailer!.
        rewrite cmpu_z by assumption; rewrite bool2val_b2z; rewrite (proj2 (Z.eqb_neq _ _) Ene); reflexivity. }
      forward_if.
      { match goal with E: ((_ =? _) || (_ =? _))%bool = true |- _ =>
          assert (Hdup: aliases_ok src (sublist 0 n fs) al m = false)
            by (apply orb_prop in E; destruct E as [E | E]; apply Z.eqb_eq in E;
                [ apply (al_dup_page_false src _ al m i i0) | apply (al_dup_frame_false src _ al m i i0) ]; auto; lia) end.
        forward; Exists 4; rewrite !maybe_at_nonnull by assumption; entailer!;
          iff_fail (build_al_false src sp kp cp fs n al m Hdup). }
      match goal with E: ((_ =? _) || (_ =? _))%bool = false |- _ => apply orb_false_iff in E; destruct E as [E1 E2] end.
      forward; entailer!; rewrite !member_snoc_sub by (rewrite Zlength_map; lia); rewrite !Znth_map by lia;
        match goal with M1: member (a_page _) _ = false, M2: member (a_frame _) _ = false |- _ => rewrite M1, M2 end;
        rewrite E1, E2; split; reflexivity. }
    Intros.
    forward. forward. forward.
    rewrite !upd_prefix_map by lia.
    entailer!.
    rewrite forallb_snoc_sub by lia; rewrite !distinct_snoc_sub by (rewrite Zlength_map; lia); rewrite !Znth_map by lia;
      match goal with F: forallb _ (sublist 0 i al) = true, D1: distinct (sublist 0 i (map a_page al)) = true,
                      D2: distinct (sublist 0 i (map a_frame al)) = true,
                      M1: member (a_page _) (sublist 0 i _) = false, M2: member (a_frame _) (sublist 0 i _) = false |- _ =>
        rewrite F, D1, D2, M1, M2 end; rewrite Hok; split3; reflexivity. }
  Intros.
  assert (Hal: aliases_ok src (sublist 0 n fs) al m = true) by (apply al_ok'; auto).
  assert (Hbuild: build_ok src sp kp cp fs n al m = true) by (apply build_true; auto).
  (* The writes. *)
  destruct kold as [k1 [k2 [k3 k4]]]. destruct cold as [c1 [c2 [c3 c4]]]. destruct rold as [r0 [r1 [r2 r3]]].
  change (list val) in k1, k2, k3, k4, c1, c2, c3, c4.
  change val in r0, r1, r2, r3.
  rewrite !root_fields, result_fields.
  assert_PROP (Zlength k1 = 512 /\ Zlength k2 = 512 /\ Zlength k3 = 512 /\ Zlength k4 = 4096 /\
               Zlength c1 = 512 /\ Zlength c2 = 512 /\ Zlength c3 = 512 /\ Zlength c4 = 4096) as LK.
  { entailer!.
    repeat match goal with H: value_fits (Tarray tulong _ _) ?k |- _ =>
      rewrite value_fits_eq in H; simpl in H; destruct H as [?L _] end.
    repeat match goal with H: value_fits (tarray tulong _) ?k |- _ =>
      rewrite value_fits_eq in H; simpl in H; destruct H as [?L _] end.
    repeat split; assumption. }
  destruct LK as (Lk1 & Lk2 & Lk3 & Lk4 & Lc1 & Lc2 & Lc3 & Lc4).
  deadvars!.
  forward_for_simple_bound 512 (EX i: Z,
    PROP ()
    LOCAL (temp _source source; temp _closed closed; temp _closed_phys (Vlong (Int64.repr kp));
           temp _copy copy; temp _copy_phys (Vlong (Int64.repr cp)); temp _protected_count (Vlong (Int64.repr n));
           temp _alias_count (Vlong (Int64.repr m)); temp _result result;
           lvar _alias_writable (tarray tulong 2) v_alias_writable; lvar _alias_frame (tarray tulong 2) v_alias_frame;
           lvar _alias_page (tarray tulong 2) v_alias_page; lvar _frames (tarray tulong 16) v_frames)
    SEP (data_at ssh t_root (root_val src) source;
         data_at Tsh (tarray tulong 2) (longs (sublist 0 m (map a_writable al)) ++ Zrepeat Vundef (2 - m)) v_alias_writable;
         data_at Tsh (tarray tulong 2) (longs (sublist 0 m (map a_frame al)) ++ Zrepeat Vundef (2 - m)) v_alias_frame;
         data_at Tsh (tarray tulong 2) (longs (sublist 0 m (map a_page al)) ++ Zrepeat Vundef (2 - m)) v_alias_page;
         data_at Tsh (tarray tulong 16) (longs (sublist 0 n fs) ++ Zrepeat Vundef (16 - n)) v_frames;
         field_at Tsh t_root (DOT _pml4) (Zrepeat (Vlong (Int64.repr 0)) i ++ sublist i 512 k1) closed;
         field_at Tsh t_root (DOT _pdpt) (Zrepeat (Vlong (Int64.repr 0)) i ++ sublist i 512 k2) closed;
         field_at Tsh t_root (DOT _pd) (Zrepeat (Vlong (Int64.repr 0)) i ++ sublist i 512 k3) closed;
         field_at Tsh t_root (DOT _pt) k4 closed;
         field_at Tsh t_root (DOT _pml4) (Zrepeat (Vlong (Int64.repr 0)) i ++ sublist i 512 c1) copy;
         field_at Tsh t_root (DOT _pdpt) (Zrepeat (Vlong (Int64.repr 0)) i ++ sublist i 512 c2) copy;
         field_at Tsh t_root (DOT _pd) (Zrepeat (Vlong (Int64.repr 0)) i ++ sublist i 512 c3) copy;
         field_at Tsh t_root (DOT _pt) c4 copy;
         data_at fsh (tarray tulong (Zlength fs)) (longs fs) frames;
         data_at ash (tarray t_alias (Zlength al + Zlength arest)) (map alias_val al ++ arest) aliases;
         field_at Tsh t_result (DOT _protected_count) r0 result;
         field_at Tsh t_result (DOT _removed_aliases) r1 result;
         field_at Tsh t_result (DOT _retained_present) r2 result;
         field_at Tsh t_result (DOT _alias_count) r3 result))%assert.
  { rewrite !zero_start by assumption; entailer!. }
  { cbv beta. Intros.
    (* The source is frozen during the stores: the store tactic otherwise tries, slowly, to unify it. *)
    freeze FR := (data_at ssh t_root _ source).
    forward. forward. forward. forward. forward. forward.
    thaw FR.
    rewrite !zero_step by assumption.
    entailer!. }
  rewrite !zero_end by assumption.
  freeze FR := (data_at ssh t_root _ source).
  forward_call (kp, 1). forward.
  forward_call (kp, 2). forward.
  forward_call (cp, 1). forward.
  forward_call (cp, 2). forward.
  rewrite !table0.
  forward_for_simple_bound 8 (EX i: Z,
    PROP ()
    LOCAL (temp _source source; temp _closed closed; temp _closed_phys (Vlong (Int64.repr kp));
           temp _copy copy; temp _copy_phys (Vlong (Int64.repr cp)); temp _protected_count (Vlong (Int64.repr n));
           temp _alias_count (Vlong (Int64.repr m)); temp _result result;
           lvar _alias_writable (tarray tulong 2) v_alias_writable; lvar _alias_frame (tarray tulong 2) v_alias_frame;
           lvar _alias_page (tarray tulong 2) v_alias_page; lvar _frames (tarray tulong 16) v_frames)
    SEP (FRZL FR;
         data_at Tsh (tarray tulong 2) (longs (sublist 0 m (map a_writable al)) ++ Zrepeat Vundef (2 - m)) v_alias_writable;
         data_at Tsh (tarray tulong 2) (longs (sublist 0 m (map a_frame al)) ++ Zrepeat Vundef (2 - m)) v_alias_frame;
         data_at Tsh (tarray tulong 2) (longs (sublist 0 m (map a_page al)) ++ Zrepeat Vundef (2 - m)) v_alias_page;
         data_at Tsh (tarray tulong 16) (longs (sublist 0 n fs) ++ Zrepeat Vundef (16 - n)) v_frames;
         field_at Tsh t_root (DOT _pml4) (longs (upd_Znth 0 (Zrepeat 0 512) (table_entry kp 1))) closed;
         field_at Tsh t_root (DOT _pdpt) (longs (upd_Znth 0 (Zrepeat 0 512) (table_entry kp 2))) closed;
         field_at Tsh t_root (DOT _pd) (longs (pd_part kp i)) closed;
         field_at Tsh t_root (DOT _pt) k4 closed;
         field_at Tsh t_root (DOT _pml4) (longs (upd_Znth 0 (Zrepeat 0 512) (table_entry cp 1))) copy;
         field_at Tsh t_root (DOT _pdpt) (longs (upd_Znth 0 (Zrepeat 0 512) (table_entry cp 2))) copy;
         field_at Tsh t_root (DOT _pd) (longs (pd_part cp i)) copy;
         field_at Tsh t_root (DOT _pt) c4 copy;
         data_at fsh (tarray tulong (Zlength fs)) (longs fs) frames;
         data_at ash (tarray t_alias (Zlength al + Zlength arest)) (map alias_val al ++ arest) aliases;
         field_at Tsh t_result (DOT _protected_count) r0 result;
         field_at Tsh t_result (DOT _removed_aliases) r1 result;
         field_at Tsh t_result (DOT _retained_present) r2 result;
         field_at Tsh t_result (DOT _alias_count) r3 result))%assert.
  { rewrite !pd_part_0; entailer!. }
  { cbv beta. Intros.
    forward_call (kp, 3 + i). forward.
    forward_call (cp, 3 + i). forward.
    rewrite !pd_part_step by lia.
    entailer!. }
  rewrite !pd_part_8.
  thaw FR.
  forward. forward.
  deadvars!.
  assert (Lpt: Zlength (pt src) = 4096) by (destruct H as (_ & _ & _ & L & _); exact L).
  assert (Wpt: words_ok (pt src)) by (destruct H as (_ & _ & _ & _ & _ & _ & _ & L); exact L).
  forward_for_simple_bound 4096 (EX p: Z,
    PROP ()
    LOCAL (temp _removed (Vlong (Int64.repr (removed_count (sublist 0 n fs) (sublist 0 p (pt src)))));
           temp _retained (Vlong (Int64.repr (retained_count (sublist 0 n fs) (sublist 0 p (pt src)))));
           temp _source source; temp _closed closed; temp _copy copy; temp _protected_count (Vlong (Int64.repr n));
           temp _alias_count (Vlong (Int64.repr m)); temp _result result;
           lvar _alias_writable (tarray tulong 2) v_alias_writable; lvar _alias_frame (tarray tulong 2) v_alias_frame;
           lvar _alias_page (tarray tulong 2) v_alias_page; lvar _frames (tarray tulong 16) v_frames)
    SEP (data_at ssh t_root (root_val src) source;
         data_at Tsh (tarray tulong 2) (longs (sublist 0 m (map a_writable al)) ++ Zrepeat Vundef (2 - m)) v_alias_writable;
         data_at Tsh (tarray tulong 2) (longs (sublist 0 m (map a_frame al)) ++ Zrepeat Vundef (2 - m)) v_alias_frame;
         data_at Tsh (tarray tulong 2) (longs (sublist 0 m (map a_page al)) ++ Zrepeat Vundef (2 - m)) v_alias_page;
         data_at Tsh (tarray tulong 16) (longs (sublist 0 n fs) ++ Zrepeat Vundef (16 - n)) v_frames;
         field_at Tsh t_root (DOT _pml4) (longs (upd_Znth 0 (Zrepeat 0 512) (table_entry kp 1))) closed;
         field_at Tsh t_root (DOT _pdpt) (longs (upd_Znth 0 (Zrepeat 0 512) (table_entry kp 2))) closed;
         field_at Tsh t_root (DOT _pd) (longs (map (pd_entry kp) (idx 512))) closed;
         field_at Tsh t_root (DOT _pt) (longs (map (closed_leaf (sublist 0 n fs)) (sublist 0 p (pt src))) ++ sublist p 4096 k4) closed;
         field_at Tsh t_root (DOT _pml4) (longs (upd_Znth 0 (Zrepeat 0 512) (table_entry cp 1))) copy;
         field_at Tsh t_root (DOT _pdpt) (longs (upd_Znth 0 (Zrepeat 0 512) (table_entry cp 2))) copy;
         field_at Tsh t_root (DOT _pd) (longs (map (pd_entry cp) (idx 512))) copy;
         field_at Tsh t_root (DOT _pt) (longs (map (closed_leaf (sublist 0 n fs)) (sublist 0 p (pt src))) ++ sublist p 4096 c4) copy;
         data_at fsh (tarray tulong (Zlength fs)) (longs fs) frames;
         data_at ash (tarray t_alias (Zlength al + Zlength arest)) (map alias_val al ++ arest) aliases;
         field_at Tsh t_result (DOT _protected_count) r0 result;
         field_at Tsh t_result (DOT _removed_aliases) r1 result;
         field_at Tsh t_result (DOT _retained_present) r2 result;
         field_at Tsh t_result (DOT _alias_count) r3 result))%assert.
  { rewrite !leaf_start by assumption; entailer!. }
  { cbv beta. Intros.
    assert (Wp: word_ok (Znth i (pt src))) by (apply word_Znth; auto).
    forward.
    { entailer!; rewrite Znth_longs by lia; exact I. }
    rewrite root_pt, Znth_longs by lia.
    forward_if (temp _t'32 (Vint (Int.repr (b2z (removes (sublist 0 n fs) (Znth i (pt src))))))).
    { match goal with Hc: Int64.and _ _ <> Int64.zero |- _ =>
        assert (Odd: Z.odd (Znth i (pt src)) = true)
          by (rewrite and1_int in Hc by assumption; destruct (Z.odd _); [ reflexivity | contradiction ]) end.
      rewrite (retype16 Tsh (sublist 0 n fs) n v_frames) by (try rewrite Zlength_sublist by lia; lia).
      forward_call (frame_of (Znth i (pt src)), v_frames, Tsh, sublist 0 n fs, Zrepeat Vundef (16 - n), n).
      { entailer!.
        assert (FO: Int64.shru (Int64.repr (Z.land (Znth i (pt src)) 4503599627366400)) (Int64.repr 12) =
                    Int64.repr (frame_of (Znth i (pt src))))
          by (unfold Int64.shru; rewrite Int64.unsigned_repr by (apply (land_mask_range _ Wp));
              rewrite (Int64.unsigned_repr 12) by rep_lia; reflexivity).
        rewrite FO. simpl. reflexivity. }
      { rewrite Zlength_sublist, Zlength_Zrepeat by lia;
          split; [ apply frame_of_range; auto | split; [ apply Forall_sublist; auto | rep_lia ] ]. }
      rewrite <- retype16 by (try rewrite Zlength_sublist by lia; lia).
      forward.
      entailer!.
      rewrite sub_sub by lia; unfold removes; rewrite Odd; simpl andb;
        destruct (member (frame_of (Znth i (pt src))) (sublist 0 n fs)); reflexivity. }
    { match goal with Hc: Int64.and _ _ = Int64.zero |- _ =>
        assert (Even: Z.odd (Znth i (pt src)) = false)
          by (rewrite and1_int in Hc by assumption; destruct (Z.odd _); [ discriminate | reflexivity ]) end.
      forward; entailer!; unfold removes; rewrite Even; reflexivity. }
    forward.
    forward_if (temp _t'34 (Vlong (Int64.repr (closed_leaf (sublist 0 n fs) (Znth i (pt src)))))).
    { bfix; forward; entailer!; unfold closed_leaf;
        match goal with Hr: removes _ _ = true |- _ => rewrite Hr end; reflexivity. }
    { bfix; forward; entailer!; unfold closed_leaf;
        match goal with Hr: removes _ _ = false |- _ => rewrite Hr end; reflexivity. }
    freeze FR := (data_at ssh t_root _ source).
    forward.
    thaw FR.
    forward_if (temp _t'35 (Vlong (Int64.repr (closed_leaf (sublist 0 n fs) (Znth i (pt src)))))).
    { bfix; forward; entailer!; unfold closed_leaf;
        match goal with Hr: removes _ _ = true |- _ => rewrite Hr end; reflexivity. }
    { bfix; forward; entailer!; unfold closed_leaf;
        match goal with Hr: removes _ _ = false |- _ => rewrite Hr end; reflexivity. }
    freeze FR := (data_at ssh t_root _ source).
    forward.
    thaw FR.
    rewrite !(leaf_step (closed_leaf (sublist 0 n fs))) by assumption.
    forward_if.
    { bfix. forward; entailer!.
      rewrite removed_step, retained_step by lia;
        match goal with Hr: removes _ (Znth i (pt src)) = true |- _ =>
          rewrite Hr; unfold removes in Hr; apply andb_prop in Hr; destruct Hr as [Ho Hm]; rewrite Ho, Hm end;
        simpl; split; f_equal; f_equal; lia. }
    bfix.
    forward_if.
    { match goal with Hc: Int64.and _ _ <> Int64.zero |- _ =>
        assert (Odd: Z.odd (Znth i (pt src)) = true)
          by (rewrite and1_int in Hc by assumption; destruct (Z.odd _); [ reflexivity | contradiction ]) end.
      forward; entailer!.
      rewrite removed_step, retained_step by lia;
        match goal with Hr: removes _ (Znth i (pt src)) = false |- _ =>
          rewrite Hr; unfold removes in Hr; rewrite Odd in Hr; simpl in Hr; rewrite Odd, Hr end;
        simpl; split; f_equal; f_equal; lia. }
    { match goal with Hc: Int64.and _ _ = Int64.zero |- _ =>
        assert (Even: Z.odd (Znth i (pt src)) = false)
          by (rewrite and1_int in Hc by assumption; destruct (Z.odd _); [ discriminate | reflexivity ]) end.
      forward; entailer!.
      rewrite removed_step, retained_step by lia;
        match goal with Hr: removes _ (Znth i (pt src)) = false |- _ => rewrite Hr end;
        rewrite Even; simpl; split; f_equal; f_equal; lia. } }
  rewrite !(leaf_end (closed_leaf (sublist 0 n fs))) by assumption.
  deadvars!.
  forward_for_simple_bound m (EX i: Z,
    PROP ()
    LOCAL (temp _removed (Vlong (Int64.repr (removed_count (sublist 0 n fs) (sublist 0 4096 (pt src)))));
           temp _retained (Vlong (Int64.repr (retained_count (sublist 0 n fs) (sublist 0 4096 (pt src)))));
           temp _copy copy; temp _protected_count (Vlong (Int64.repr n));
           temp _alias_count (Vlong (Int64.repr m)); temp _result result;
           lvar _alias_writable (tarray tulong 2) v_alias_writable; lvar _alias_frame (tarray tulong 2) v_alias_frame;
           lvar _alias_page (tarray tulong 2) v_alias_page; lvar _frames (tarray tulong 16) v_frames)
    SEP (data_at ssh t_root (root_val src) source;
         data_at Tsh (tarray tulong 2) (longs (sublist 0 m (map a_writable al)) ++ Zrepeat Vundef (2 - m)) v_alias_writable;
         data_at Tsh (tarray tulong 2) (longs (sublist 0 m (map a_frame al)) ++ Zrepeat Vundef (2 - m)) v_alias_frame;
         data_at Tsh (tarray tulong 2) (longs (sublist 0 m (map a_page al)) ++ Zrepeat Vundef (2 - m)) v_alias_page;
         data_at Tsh (tarray tulong 16) (longs (sublist 0 n fs) ++ Zrepeat Vundef (16 - n)) v_frames;
         field_at Tsh t_root (DOT _pml4) (longs (upd_Znth 0 (Zrepeat 0 512) (table_entry kp 1))) closed;
         field_at Tsh t_root (DOT _pdpt) (longs (upd_Znth 0 (Zrepeat 0 512) (table_entry kp 2))) closed;
         field_at Tsh t_root (DOT _pd) (longs (map (pd_entry kp) (idx 512))) closed;
         field_at Tsh t_root (DOT _pt) (longs (map (closed_leaf (sublist 0 n fs)) (pt src))) closed;
         field_at Tsh t_root (DOT _pml4) (longs (upd_Znth 0 (Zrepeat 0 512) (table_entry cp 1))) copy;
         field_at Tsh t_root (DOT _pdpt) (longs (upd_Znth 0 (Zrepeat 0 512) (table_entry cp 2))) copy;
         field_at Tsh t_root (DOT _pd) (longs (map (pd_entry cp) (idx 512))) copy;
         field_at Tsh t_root (DOT _pt) (longs (install (sublist 0 i al) (map (closed_leaf (sublist 0 n fs)) (pt src)))) copy;
         data_at fsh (tarray tulong (Zlength fs)) (longs fs) frames;
         data_at ash (tarray t_alias (Zlength al + Zlength arest)) (map alias_val al ++ arest) aliases;
         field_at Tsh t_result (DOT _protected_count) r0 result;
         field_at Tsh t_result (DOT _removed_aliases) r1 result;
         field_at Tsh t_result (DOT _retained_present) r2 result;
         field_at Tsh t_result (DOT _alias_count) r3 result))%assert.
  { rewrite install_start; entailer!. }
  { cbv beta. Intros.
    assert (Wa: alias_wf (Znth i al)) by (apply Forall_Znth; auto; lia).
    destruct Wa as (Wpg & Wfr & Wwr).
    assert (Pg: a_page (Znth i al) < 4096)
      by (apply (alias_ok_page src (sublist 0 n fs));
          match goal with F: forallb _ (sublist 0 m al) = true |- _ => apply (forallb_Znth_sub _ al i m); auto; lia end).
    forward.
    { entailer!; rewrite Znth_prefix_map by lia; exact I. }
    rewrite Znth_prefix_map by lia.
    forward_if (temp _t'36 (Vlong (Int64.repr (if a_writable (Znth i al) =? 0 then 0 else 2)))).
    { l64; forward; entailer!;
        match goal with Hw: a_writable (Znth i al) <> 0 |- _ => rewrite (proj2 (Z.eqb_neq _ 0) Hw) end; reflexivity. }
    { l64; forward; entailer!;
        match goal with Hw: a_writable (Znth i al) = 0 |- _ => rewrite Hw end; reflexivity. }
    forward; [ entailer!; rewrite Znth_prefix_map by lia; exact I | ].
    rewrite Znth_prefix_map by lia.
    forward; [ entailer!; rewrite Znth_prefix_map by lia; exact I | ].
    rewrite Znth_prefix_map by lia.
    freeze FR := (data_at ssh t_root _ source).
    forward.
    { entailer!; unfold word_ok in Wpg; lia. }
    thaw FR.
    change (Int.unsigned (Int.repr 12)) with 12. change (Int.unsigned (Int.repr 63)) with 63.
    rewrite alias_leaf_int by assumption.
    rewrite install_step by lia.
    entailer!. }
  (* The result record and the return. *)
  forward. forward. forward. forward.
  forward.
  Exists 0.
  rewrite (sublist_same 0 4096 (pt src)) by lia.
  rewrite !maybe_at_nonnull by assumption.
  rewrite Z.eqb_refl.
  rewrite (root_val_eq (closed_out _ _ _)), (root_val_eq (copy_out _ _ _ _)), !root_fields.
  unfold result_val; rewrite result_fields.
  cbn [closed_out copy_out built_root pml4 pdpt pd pt].
  entailer!.
  split; [ intros _; repeat split; assumption | reflexivity ].
Qed.
