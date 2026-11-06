(* Law copy_roots_exact: the bodies of the harness's checks tables_at, inventory_ok and aliases_ok. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import QuickProof.Env.
Require Import LeanosRoots.proof.Defs.
Require Import LeanosRoots.proof.RootsSpecs.
Require Import LeanosRoots.proof.Law1Specs.
Require Import LeanosRoots.proof.Law1Pure.
Require Import LeanosRoots.proof.Law1Small.
Require Import LeanosRoots.harness.copy_roots_exact.code.
Local Open Scope Z_scope.

Lemma body_tables_at: semax_body Vharness Gharness f_tables_at tables_at_spec.
Proof.
  start_function. rewrite root_val_v.
  pose proof H as Hok. destruct H as (L1 & L2 & L3 & L4 & W1 & W2 & W3 & W4). unfold LEAVES in L4.
  assert (Wa: word_ok (Znth 0 (pml4 rv))) by (apply word_Znth; auto; lia).
  assert (Wb: word_ok (Znth 0 (pdpt rv))) by (apply word_Znth; auto; lia).
  remember ((Z.land (Znth 0 (pml4 rv)) (Z.lnot ig) =? table_entry phys 1) &&
               (Z.land (Znth 0 (pdpt rv)) (Z.lnot ig) =? table_entry phys 2))%bool as c12 eqn:Ec12.
  forward_call (phys, 1).
  unfold rootv. ld. rewrite Znth_longs by lia.
  forward_if (temp _t'2 (Vint (Int.repr (b2z (negb c12))))).
  - forward. entailer!. w64. bcase.
  - forward_call (phys, 2). ld. rewrite Znth_longs by lia. forward. entailer!. w64.
    rewrite H, Z.eqb_refl. reflexivity.
  - forward_if.
    + forward. entailer!. unfold tables_ok. rewrite H. reflexivity.
    + forward_for_simple_bound 512
        (EX i: Z,
         PROP (1 <= i; forall j, 1 <= j < i -> Znth j (pml4 rv) = 0 /\ Znth j (pdpt rv) = 0)
         LOCAL (temp _r r; temp _phys (Vlong (Int64.repr phys)); temp _ignore (Vlong (Int64.repr ig)))
         SEP (data_at sh t_root (rootv (longs (pml4 rv)) (longs (pdpt rv)) (longs (pd rv)) (longs (pt rv))) r)).
      * entailer!; intros; lia.
      * assert (Wi1: word_ok (Znth i (pml4 rv))) by (apply word_Znth; auto; lia).
        assert (Wi2: word_ok (Znth i (pdpt rv))) by (apply word_Znth; auto; lia).
        unfold rootv. ld. rewrite Znth_longs by lia.
        forward_if (temp _t'4 (Vint (Int.repr (b2z (negb ((Znth i (pml4 rv) =? 0) && (Znth i (pdpt rv) =? 0))%bool))))).
        -- forward. entailer!. w64. bcase.
        -- ld. rewrite Znth_longs by lia. forward. entailer!. w64. bcase.
        -- forward_if.
           ++ forward. entailer!. unfold tables_ok. rewrite H.
              rewrite (forallb_idx1_false _ i) by (try lia; assumption). reflexivity.
           ++ forward. entailer!. intros j Hj. destruct (zeq j i); [ subst j | apply H4; lia ].
              destruct (Z.eqb_spec (Znth i (pml4 rv)) 0); destruct (Z.eqb_spec (Znth i (pdpt rv)) 0);
                simpl in *; first [ split; assumption | discriminate ].
      * Intros. rename H2 into Z1.
        forward_for_simple_bound 512
          (EX i: Z,
           PROP (forall j, 0 <= j < i -> Z.land (Znth j (pd rv)) (Z.lnot ig) = pd_entry phys j)
           LOCAL (temp _r r; temp _phys (Vlong (Int64.repr phys)); temp _ignore (Vlong (Int64.repr ig)))
           SEP (data_at sh t_root (rootv (longs (pml4 rv)) (longs (pdpt rv)) (longs (pd rv)) (longs (pt rv))) r)).
        -- entailer!; intros; lia.
        -- cbv beta. Intros. assert (Wi: word_ok (Znth i (pd rv))) by (apply word_Znth; auto; lia).
           forward_if (temp _t'5 (Vlong (Int64.repr (pd_entry phys i)))).
           ++ forward_call (phys, 3 + i). { w64. lia. }
              forward. entailer!. w64. unfold pd_entry. destruct (Z.ltb_spec i 8); [ reflexivity | lia ].
           ++ forward. entailer!. w64. unfold pd_entry. destruct (Z.ltb_spec i 8); [ lia | reflexivity ].
           ++ unfold rootv. ld. rewrite Znth_longs by lia.
              forward_if.
              ** forward. entailer!. w64. unfold tables_ok. rewrite H.
                 rewrite (forallb_idx_false _ 512 i) by (try lia; apply Z.eqb_neq; assumption).
                 rewrite andb_false_r. reflexivity.
              ** w64. assert (Hn: forall j, 0 <= j < i + 1 -> Z.land (Znth j (pd rv)) (Z.lnot ig) = pd_entry phys j).
                 { intros j Hj. destruct (zeq j i); [ subst j; assumption | apply H4; lia ]. }
                 forward. entailer!.
        -- forward. entailer!. unfold tables_ok. rewrite H.
           rewrite (proj2 (forallb_idx1 _)).
           2: { intros j Hj. destruct (H3 j Hj) as [A B]. rewrite A, B. reflexivity. }
           rewrite (proj2 (forallb_idx _ 512 ltac:(lia))). reflexivity.
           intros j Hj. match goal with Hinv: forall j, 0 <= j < 512 -> _ |- _ => rewrite (Hinv j Hj) end.
           apply Z.eqb_refl.
Qed.

Lemma body_inventory_ok: semax_body Vharness Gharness f_inventory_ok inventory_ok_spec.
Proof.
  start_function.
  forward_if (temp _t'1 (Vint (Int.repr (b2z ((n <? 1) || (16 <? n))%bool)))).
  - forward. entailer!. w64. bcase.
  - forward. entailer!. w64. bcase.
  - forward_if.
    + forward. entailer!. unfold inventory_ok. bcase.
    + assert (Hn: 1 <= n <= 16) by (destruct (Z.ltb_spec n 1); destruct (Z.ltb_spec 16 n); simpl in *; first [ lia | congruence ]).
      forward_for_simple_bound n
        (EX i: Z,
         PROP (forall k, 0 <= k < i -> Znth k fs < 2 ^ 40 /\ forall j, k < j < n -> Znth k fs <> Znth j fs)
         LOCAL (temp _frames p; temp _n (Vlong (Int64.repr n)))
         SEP (data_at sh (tarray tulong (Zlength fs)) (longs fs) p)).
      * entailer!; intros; lia.
      * cbv beta. Intros. assert (Wi: word_ok (Znth i fs)) by (apply word_Znth; auto; lia).
        ld. rewrite Znth_longs by lia.
        forward_if.
        -- forward. entailer!. change (Int64.shl (Int64.repr 1) (Int64.repr 40)) with (Int64.repr 1099511627776) in *.
           w64. unfold inventory_ok.
           rewrite (forallb_Znth_false _ (sublist 0 n fs) i).
           ++ rewrite andb_false_r. reflexivity.
           ++ rewrite Zlength_sublist by lia. lia.
           ++ rewrite Znth_sublist by lia. rewrite Z.add_0_r. apply Z.ltb_ge. change (2 ^ 40) with 1099511627776. lia.
        -- change (Int64.shl (Int64.repr 1) (Int64.repr 40)) with (Int64.repr 1099511627776) in *. w64.
           forward_for_simple_bound n
             (EX j: Z,
              PROP (i + 1 <= j; forall j', i < j' < j -> Znth i fs <> Znth j' fs)
              LOCAL (temp _i (Vlong (Int64.repr i)); temp _frames p; temp _n (Vlong (Int64.repr n)))
              SEP (data_at sh (tarray tulong (Zlength fs)) (longs fs) p)).
           ++ forward. Exists (i + 1). entailer!; intros; lia.
           ++ cbv beta. Intros. rename i0 into j.
              assert (Wj: word_ok (Znth j fs)) by (apply word_Znth; auto; lia).
              ld. ld. rewrite !Znth_longs by lia.
              forward_if.
              ** forward. entailer!. w64.
                 assert (D: distinct (sublist 0 n fs) = false).
                 { destruct (distinct (sublist 0 n fs)) eqn:E; auto. rewrite distinct_Znth in E. exfalso.
                   apply (E i j); try lia. rewrite Zlength_sublist; lia. rewrite !Znth_sublist by lia.
                   rewrite !Z.add_0_r. auto. }
                 unfold inventory_ok. rewrite D, andb_false_r. reflexivity.
              ** w64. assert (Hs: forall j', i < j' < j + 1 -> Znth i fs <> Znth j' fs).
                 { intros j' Hj'. destruct (zeq j' j); [ subst j'; assumption | apply H8; lia ]. }
                 forward. entailer!.
           ++ Intros.
              assert (Hs: forall k, 0 <= k < i + 1 -> Znth k fs < 2 ^ 40 /\ forall j, k < j < n -> Znth k fs <> Znth j fs).
              { intros k Hk. destruct (zeq k i).
                - subst k. split; [ change (2 ^ 40) with 1099511627776; lia | ].
                  match goal with Hj: forall j', i < j' < n -> _ |- _ => exact Hj end.
                - apply H4; lia. }
              entailer!.
      * forward. entailer!. unfold inventory_ok.
        rewrite (proj2 (Z.leb_le 1 n)), (proj2 (Z.leb_le n 16)) by lia.
        rewrite forallb_Znth.
        2: { intros k Hk. rewrite Zlength_sublist in Hk by lia. rewrite Znth_sublist by lia.
             rewrite Z.add_0_r. apply Z.ltb_lt. match goal with Hinv: forall k, 0 <= k < n -> _ |- _ => apply Hinv; lia end. }
        replace (distinct (sublist 0 n fs)) with true; [ reflexivity | symmetry ].
        apply distinct_Znth. intros k j Hk Hkj Hj. rewrite Zlength_sublist in Hj by lia.
        rewrite !Znth_sublist by lia. rewrite !Z.add_0_r.
        match goal with Hinv: forall k, 0 <= k < n -> _ |- _ => apply Hinv; lia end.
Qed.

Lemma alias_ok_c: forall src inv pg fr wr, alias_ok src inv (mkalias pg fr wr) =
  negb ((((4096 <=? pg) || negb (Znth pg (pt src) =? 0)) || negb (member fr inv)) || (1 <? wr))%bool.
Proof.
  intros. unfold alias_ok, LEAVES; cbn [a_page a_frame a_writable].
  destruct (Z.ltb_spec pg 4096), (Z.leb_spec 4096 pg), (Z.leb_spec wr 1), (Z.ltb_spec 1 wr); try lia; simpl;
    destruct (Znth pg (pt src) =? 0), (member fr inv); reflexivity.
Qed.

Lemma body_aliases_ok: semax_body Vharness Gharness f_aliases_ok aliases_ok_spec.
Proof.
  start_function.
  forward_if (temp _t'1 (Vint (Int.repr (b2z ((m <? 1) || (2 <? m))%bool)))).
  - forward. entailer!. w64. bcase.
  - forward. entailer!. w64. bcase.
  - forward_if.
    + forward. entailer!. unfold aliases_ok. bcase.
    + assert (Hm: 1 <= m <= 2) by (destruct (Z.ltb_spec m 1); destruct (Z.ltb_spec 2 m); simpl in *; first [ lia | congruence ]).
      rewrite root_val_v.
      forward_for_simple_bound m
        (@exp (environ -> mpred) _ Z (fun i =>
         PROP (forall k, 0 <= k < i -> alias_ok src (sublist 0 n fs) (Znth k al) = true /\
                 forall j, k < j < m -> a_page (Znth k al) <> a_page (Znth j al) /\ a_frame (Znth k al) <> a_frame (Znth j al))
         LOCAL (temp _a a; temp _m (Vlong (Int64.repr m)); temp _source s; temp _frames fp; temp _n (Vlong (Int64.repr n)))
         SEP (data_at ash (tarray t_alias (Zlength al)) (map alias_val al) a;
              data_at ssh t_root (rootv (longs (pml4 src)) (longs (pdpt src)) (longs (pd src)) (longs (pt src))) s;
              data_at fsh (tarray tulong (Zlength fs)) (longs fs) fp))).
      * entailer!; intros; lia.
      * cbv beta. Intros.
        assert (Wa: alias_wf (Znth i al)) by (apply (Forall_Znth al alias_wf); auto; lia).
        destruct (Znth i al) as [pg fr wr] eqn:Ea. destruct Wa as (Wp & Wf & Ww). simpl in Wp, Wf, Ww. unfold word_ok in Wp, Wf, Ww.
        destruct H2 as (L1 & L2 & L3 & L4 & W1 & W2 & W3 & W4). unfold LEAVES in L4.
        ldA.
        forward_if (temp _t'2 (Vint (Int.repr (b2z ((4096 <=? pg) || negb (Znth pg (pt src) =? 0))%bool)))).
        -- forward. entailer!. w64. bcase.
        -- w64. ldA. unfold rootv. ld. rewrite Znth_longs by lia.
           assert (Wpt: word_ok (Znth pg (pt src))) by (apply word_Znth; auto; lia).
           forward. entailer!. w64. bcase.
        -- forward_if (temp _t'3 (Vint (Int.repr (b2z (((4096 <=? pg) || negb (Znth pg (pt src) =? 0)) || negb (member fr (sublist 0 n fs)))%bool)))).
           ++ forward. entailer!. rewrite H2. reflexivity.
           ++ ldA. forward_call (fr, fp, fsh, fs, n). forward. entailer!. rewrite H2.
              destruct (member fr (sublist 0 n fs)); reflexivity.
           ++ forward_if (temp _t'5 (Vint (Int.repr (b2z ((((4096 <=? pg) || negb (Znth pg (pt src) =? 0)) || negb (member fr (sublist 0 n fs))) || (1 <? wr))%bool)))).
              ** forward. entailer!. rewrite H2. reflexivity.
              ** ldA. forward. entailer!. rewrite H2. w64. reflexivity.
              ** forward_if.
                 --- forward. entailer!. unfold aliases_ok.
                     rewrite (forallb_Znth_false _ (sublist 0 m al) i).
                     +++ rewrite andb_false_r. reflexivity.
                     +++ rewrite Zlength_sublist by lia. lia.
                     +++ rewrite Znth_sublist by lia. rewrite Z.add_0_r, Ea, alias_ok_c, H2. reflexivity.
                 --- forward_for_simple_bound m
                       (@exp (environ -> mpred) _ Z (fun j =>
                        PROP (i + 1 <= j; forall j', i < j' < j -> pg <> a_page (Znth j' al) /\ fr <> a_frame (Znth j' al))
                        LOCAL (temp _i (Vlong (Int64.repr i)); temp _a a; temp _m (Vlong (Int64.repr m)); temp _source s;
                               temp _frames fp; temp _n (Vlong (Int64.repr n)))
                        SEP (data_at ash (tarray t_alias (Zlength al)) (map alias_val al) a;
                             data_at ssh t_root (rootv (longs (pml4 src)) (longs (pdpt src)) (longs (pd src)) (longs (pt src))) s;
                             data_at fsh (tarray tulong (Zlength fs)) (longs fs) fp))).
                     +++ forward. Exists (i + 1). entailer!; intros; lia.
                     +++ cbv beta. Intros. rename i0 into j.
                         assert (Wb: alias_wf (Znth j al)) by (apply (Forall_Znth al alias_wf); auto; lia).
                         destruct (Znth j al) as [pg2 fr2 wr2] eqn:Eb. destruct Wb as (Wp2 & Wf2 & Ww2).
                         simpl in Wp2, Wf2, Ww2. unfold word_ok in Wp2, Wf2, Ww2.
                         ldA. ldA.
                         forward_if (temp _t'6 (Vint (Int.repr (b2z ((pg =? pg2) || (fr =? fr2))%bool)))).
                         *** forward. entailer!. w64. bcase.
                         *** ldA. ldA. forward. entailer!. w64. bcase.
                         *** forward_if.
                             ---- forward. entailer!. unfold aliases_ok.
                                  assert (Zm: Zlength (sublist 0 m al) = m) by (rewrite Zlength_sublist; lia).
                                  destruct (Z.eqb_spec pg pg2).
                                  ++++ assert (D: distinct (map a_page (sublist 0 m al)) = false).
                                       { destruct (distinct _) eqn:E; auto. rewrite distinct_Znth in E. exfalso.
                                         apply (E i j); try lia. rewrite Zlength_map; lia.
                                         rewrite !Znth_map by lia. rewrite !Znth_sublist by lia.
                                         rewrite !Z.add_0_r, Ea, Eb. simpl. auto. }
                                       rewrite D, andb_false_r. reflexivity.
                                  ++++ assert (Ef: fr = fr2) by (destruct (Z.eqb_spec fr fr2); simpl in *; congruence).
                                       assert (D: distinct (map a_frame (sublist 0 m al)) = false).
                                       { destruct (distinct _) eqn:E; auto. rewrite distinct_Znth in E. exfalso.
                                         apply (E i j); try lia. rewrite Zlength_map; lia.
                                         rewrite !Znth_map by lia. rewrite !Znth_sublist by lia.
                                         rewrite !Z.add_0_r, Ea, Eb. simpl. auto. }
                                       rewrite D, andb_false_r. reflexivity.
                             ---- assert (Hs: forall j', i < j' < j + 1 -> pg <> a_page (Znth j' al) /\ fr <> a_frame (Znth j' al)).
                                  { intros j' Hj'. destruct (zeq j' j).
                                    - subst j'. rewrite Eb. simpl.
                                      destruct (Z.eqb_spec pg pg2), (Z.eqb_spec fr fr2); simpl in *; first [ discriminate | split; auto ].
                                    - match goal with Hinv: forall j', i < j' < j -> _ |- _ => apply Hinv; lia end. }
                                  forward. entailer!.
                     +++ Intros.
                         assert (Hs: forall k, 0 <= k < i + 1 -> alias_ok src (sublist 0 n fs) (Znth k al) = true /\
                                   forall j, k < j < m -> a_page (Znth k al) <> a_page (Znth j al) /\ a_frame (Znth k al) <> a_frame (Znth j al)).
                         { intros k Hk. destruct (zeq k i).
                           - subst k. rewrite Ea, alias_ok_c, H2. split; [ reflexivity | ]. simpl.
                             match goal with Hj: forall j', i < j' < m -> _ |- _ => exact Hj end.
                           - apply H8; lia. }
                         entailer!.
      * forward. entailer!. unfold aliases_ok.
        assert (Zm: Zlength (sublist 0 m al) = m) by (rewrite Zlength_sublist; lia).
        rewrite (proj2 (Z.leb_le 1 m)), (proj2 (Z.leb_le m 2)) by lia.
        rewrite forallb_Znth.
        2: { intros k Hk. rewrite Zm in Hk. rewrite Znth_sublist by lia. rewrite Z.add_0_r.
             match goal with Hinv: forall k, 0 <= k < m -> _ |- _ => apply Hinv; lia end. }
        replace (distinct (map a_page (sublist 0 m al))) with true.
        replace (distinct (map a_frame (sublist 0 m al))) with true. reflexivity.
        all: symmetry; apply distinct_Znth; intros k j Hk Hkj Hj; rewrite Zlength_map, Zm in Hj;
             rewrite !Znth_map by lia; rewrite !Znth_sublist by lia; rewrite !Z.add_0_r;
             match goal with Hinv: forall k, 0 <= k < ?mm -> alias_ok _ _ _ = true /\ _ |- _ => destruct (Hinv k ltac:(lia)) as [_ Hd] end;
             apply Hd; lia.
Qed.
