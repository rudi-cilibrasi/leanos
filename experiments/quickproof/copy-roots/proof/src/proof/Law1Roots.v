(* Law copy_roots_exact: the bodies of the harness's helpers root_fill, root_copy and root_same. *)
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

Lemma fill_step: forall (a: list Z) x i k, Zlength a = i -> 0 < k ->
  upd_Znth i (longs a ++ Zrepeat Vundef k) (Vlong (Int64.repr x)) = longs (a ++ [x]) ++ Zrepeat Vundef (k - 1).
Proof. intros. subst i. unfold longs. rewrite map_app. list_solve. Qed.
Lemma body_root_fill: semax_body Vharness Gharness f_root_fill root_fill_spec.
Proof.
  start_function.
  forward_for_simple_bound 512
    (EX i: Z, EX a: list Z, EX b: list Z, EX c: list Z,
     PROP (Zlength a = i; Zlength b = i; Zlength c = i; words_ok a; words_ok b; words_ok c)
     LOCAL (temp _r r)
     SEP (data_at Tsh t_root (rootv (longs a ++ Zrepeat Vundef (512 - i)) (longs b ++ Zrepeat Vundef (512 - i))
            (longs c ++ Zrepeat Vundef (512 - i)) (Zrepeat Vundef 4096)) r)).
  - Exists (@nil Z) (@nil Z) (@nil Z). entailer!. repeat split; constructor.
  - forward_call. Intros x. unfold rootv. forward.
    forward_call. Intros y. forward.
    forward_call. Intros z. forward.
    Exists (a ++ [x]) (b ++ [y]) (c ++ [z]).
    rewrite !(fill_step _ _ i) by lia. unfold rootv.
    replace (512 - i - 1) with (512 - (i + 1)) by lia.
    entailer!. unfold words_ok in *. rewrite !Zlength_app, !Zlength_cons, !Zlength_nil.
    repeat split; try lia; apply Forall_app; split; auto; repeat constructor; unfold word_ok; lia.
  - Intros a b c. change (Zrepeat Vundef (512 - 512)) with (@nil val). rewrite !app_nil_r.
    forward_for_simple_bound 4096
      (EX i: Z, EX d: list Z,
       PROP (Zlength d = i; words_ok d)
       LOCAL (temp _r r)
       SEP (data_at Tsh t_root (rootv (longs a) (longs b) (longs c) (longs d ++ Zrepeat Vundef (4096 - i))) r)).
    + Exists (@nil Z). entailer!. constructor.
    + forward_call. Intros x. unfold rootv. forward.
      Exists (d ++ [x]). rewrite (fill_step _ _ i) by lia. unfold rootv.
      replace (4096 - i - 1) with (4096 - (i + 1)) by lia.
      entailer!. unfold words_ok in *. rewrite !Zlength_app, !Zlength_cons, !Zlength_nil.
      repeat split; try lia; apply Forall_app; split; auto; repeat constructor; unfold word_ok; lia.
    + Intros d. change (Zrepeat Vundef (4096 - 4096)) with (@nil val). rewrite !app_nil_r.
      Exists (mkroot a b c d). unfold root_val, rootv. cbn [pml4 pdpt pd pt].
      entailer!. unfold root_ok. cbn [pml4 pdpt pd pt]. repeat split; auto.
Qed.
Lemma copy_step: forall (l: list Z) i k, 0 <= i < Zlength l -> 0 < k ->
  upd_Znth i (longs (sublist 0 i l) ++ Zrepeat Vundef k) (Vlong (Int64.repr (Znth i l))) =
  longs (sublist 0 (i + 1) l) ++ Zrepeat Vundef (k - 1).
Proof. intros. rewrite fill_step by (try rewrite Zlength_sublist; lia). rewrite (sublist_last_1 0 i l) by lia. reflexivity. Qed.

Lemma body_root_copy: semax_body Vharness Gharness f_root_copy root_copy_spec.
Proof.
  start_function. rewrite root_val_v.
  destruct H as (L1 & L2 & L3 & L4 & W1 & W2 & W3 & W4).
  forward_for_simple_bound 512
    (EX i: Z,
     PROP ()
     LOCAL (temp _d d; temp _s s)
     SEP (data_at Tsh t_root (rootv (longs (sublist 0 i (pml4 rv)) ++ Zrepeat Vundef (512 - i))
            (longs (sublist 0 i (pdpt rv)) ++ Zrepeat Vundef (512 - i))
            (longs (sublist 0 i (pd rv)) ++ Zrepeat Vundef (512 - i)) (Zrepeat Vundef 4096)) d;
          data_at sh t_root (rootv (longs (pml4 rv)) (longs (pdpt rv)) (longs (pd rv)) (longs (pt rv))) s)).
  - entailer!.
  - unfold rootv.
    forward. { entailer!; rewrite ?Znth_longs by lia; simpl; auto. } rewrite Znth_longs by lia. forward.
    forward. { entailer!; rewrite ?Znth_longs by lia; simpl; auto. } rewrite Znth_longs by lia. forward.
    forward. { entailer!; rewrite ?Znth_longs by lia; simpl; auto. } rewrite Znth_longs by lia. forward.
    rewrite !copy_step by lia. replace (512 - i - 1) with (512 - (i + 1)) by lia.
    entailer!.
  - change (Zrepeat Vundef (512 - 512)) with (@nil val). rewrite !app_nil_r.
    rewrite !(sublist_same 0 512) by lia.
    unfold LEAVES in L4.
    forward_for_simple_bound 4096
      (EX i: Z,
       PROP ()
       LOCAL (temp _d d; temp _s s)
       SEP (data_at Tsh t_root (rootv (longs (pml4 rv)) (longs (pdpt rv)) (longs (pd rv))
              (longs (sublist 0 i (pt rv)) ++ Zrepeat Vundef (4096 - i))) d;
            data_at sh t_root (rootv (longs (pml4 rv)) (longs (pdpt rv)) (longs (pd rv)) (longs (pt rv))) s)).
    + entailer!.
    + unfold rootv.
      forward. { entailer!; rewrite ?Znth_longs by lia; simpl; auto. } rewrite Znth_longs by lia. forward.
      rewrite !copy_step by lia. replace (4096 - i - 1) with (4096 - (i + 1)) by lia.
      entailer!.
    + change (Zrepeat Vundef (4096 - 4096)) with (@nil val). rewrite !app_nil_r.
      rewrite !(sublist_same 0 4096) by lia.
      entailer!.
Qed.
Lemma body_root_same: semax_body Vharness Gharness f_root_same root_same_spec.
Proof.
  start_function. rewrite root_val_v.
  destruct H as (L1 & L2 & L3 & L4 & W1 & W2 & W3 & W4). unfold LEAVES in L4.
  forward_for_simple_bound 512
    (EX i: Z,
     PROP ()
     LOCAL (temp _a a; temp _b b)
     SEP (data_at sha t_root (rootv (longs (pml4 rv)) (longs (pdpt rv)) (longs (pd rv)) (longs (pt rv))) a;
          data_at shb t_root (rootv (longs (pml4 rv)) (longs (pdpt rv)) (longs (pd rv)) (longs (pt rv))) b)).
  - entailer!.
  - unfold rootv.
    ld.
    ld.
    rewrite !Znth_longs by lia.
    forward_if (temp _t'1 (Vint Int.zero)).
    { exfalso. auto. }
    { ld.
      ld.
      rewrite !Znth_longs by lia. forward. entailer!. unfold Int64.cmpu. rewrite Int64.eq_true. reflexivity. }
    forward_if (temp _t'2 (Vint Int.zero)).
    { exfalso. auto. }
    { ld.
      ld.
      rewrite !Znth_longs by lia. forward. entailer!. unfold Int64.cmpu. rewrite Int64.eq_true. reflexivity. }
    forward_if.
    { exfalso. auto. }
    forward. entailer!.
  - forward_for_simple_bound 4096
      (EX i: Z,
       PROP ()
       LOCAL (temp _a a; temp _b b)
       SEP (data_at sha t_root (rootv (longs (pml4 rv)) (longs (pdpt rv)) (longs (pd rv)) (longs (pt rv))) a;
            data_at shb t_root (rootv (longs (pml4 rv)) (longs (pdpt rv)) (longs (pd rv)) (longs (pt rv))) b)).
    + entailer!.
    + unfold rootv.
      ld.
      ld.
      rewrite !Znth_longs by lia.
      forward_if.
      { exfalso. auto. }
      forward. entailer!.
    + forward.
Qed.
