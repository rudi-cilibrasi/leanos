(* Law window_scan_exact: the body of the harness's tables_at (ancestors_ok of Defs.v). *)
Require Import VST.floyd.proofauto.
Require Import QuickProof.Env.
Require Import LeanosRoots.harness.window_scan_exact.code.
Require Import LeanosRoots.proof.Defs.
Require Import LeanosRoots.proof.Law3Facts.
Require Import LeanosRoots.proof.Law3Specs.
Local Open Scope Z_scope.
#[local] Existing Instance HCS.

Lemma body_tables_at: semax_body Vh Gh f_tables_at tables_at_spec.
Proof.
  start_function.
  pose proof H as Hok. destruct H as (L1 & L2 & L3 & L4 & W1 & W2 & W3 & W4).
  pose proof (root_ranges rv Hok) as R.
  destruct (proj1 (R 0) ltac:(lia)) as (R10 & R20 & R30). unfold word_ok in H0.
  forward_call (phys, 1).
  unfold root_val. ld.
  forward_if (temp _t'2 (Vint (Int.repr (b2z (negb (anc_head rv phys)))))).
  { z64. forward. entailer!. unfold anc_head. bsubst. reflexivity. }
  { z64. forward_call (phys, 2). ld. forward. entailer!. z64. unfold anc_head. bsubst. apply b2z_bool2val. }
  destruct (anc_head rv phys) eqn:C12.
  2: { forward_if; [ forward; entailer!; rewrite ancestors_ok_eq, C12; reflexivity | neq_absurd ]. }
  forward_if; [ neq_absurd | ].
  forward_for_simple_bound 512
    (EX i: Z,
     PROP (forallb (anc_top rv) (map (Z.add 1) (idx (i - 1))) = true)
     LOCAL (temp _r r; temp _phys (Vlong (Int64.repr phys)))
     SEP (data_at sh t_root (root_val rv) r)).
  { entailer!. }
  { cbv beta. unfold root_val. destruct (proj1 (R i) ltac:(lia)) as (Ri1 & Ri2 & Ri3).
    ld.
    forward_if (temp _t'4 (Vint (Int.repr (b2z (negb (anc_top rv i)))))).
    { z64. forward. entailer!. unfold anc_top. bsubst. reflexivity. }
    { z64. ld. forward. entailer!. z64. unfold anc_top. bsubst. apply b2z_bool2val. }
    destruct (anc_top rv i) eqn:Ci.
    2: { forward_if; [ | neq_absurd ].
         forward. entailer!.
         rewrite ancestors_ok_eq, (forallb_false _ _ i (in_top i ltac:(lia)) Ci). rewrite andb_false_r. reflexivity. }
    forward_if; [ neq_absurd | ].
    forward. entailer!. rewrite forallb_map_succ by lia. bsubst. reflexivity. }
  Intros. change (512 - 1) with 511 in *.
  forward_for_simple_bound 512
    (EX i: Z,
     PROP (forallb (anc_pd rv phys) (idx i) = true)
     LOCAL (temp _r r; temp _phys (Vlong (Int64.repr phys)))
     SEP (data_at sh t_root (root_val rv) r)).
  { entailer!. }
  { cbv beta. unfold root_val. destruct (proj1 (R i) ltac:(lia)) as (Ri1 & Ri2 & Ri3).
    forward_if (temp _t'5 (Vlong (Int64.repr (pd_entry phys i)))).
    { to_z. forward_call (phys, 3 + i). forward. entailer!.
      unfold pd_entry. destruct (Z.ltb_spec i 8); [ reflexivity | lia ]. }
    { to_z. forward. entailer!. unfold pd_entry. destruct (Z.ltb_spec i 8); [ lia | reflexivity ]. }
    ld.
    forward_if.
    { z64. forward. entailer!.
      assert (Cp: anc_pd rv phys i = false) by (unfold anc_pd; assumption).
      rewrite ancestors_ok_eq, (forallb_false _ _ i (in_idx i 512 ltac:(lia)) Cp). rewrite andb_false_r. reflexivity. }
    { z64. forward. entailer!. rewrite forallb_idx_succ by lia. bsubst. unfold anc_pd. bsubst. reflexivity. } }
  Intros. forward. entailer!. rewrite ancestors_ok_eq. bsubst. reflexivity.
Qed.
