(* Law window_scan_exact: the bodies of the harness's root_same and root_copy. *)
Require Import VST.floyd.proofauto.
Require Import QuickProof.Env.
Require Import LeanosRoots.harness.window_scan_exact.code.
Require Import LeanosRoots.proof.Defs.
Require Import LeanosRoots.proof.Law3Facts.
Require Import LeanosRoots.proof.Law3Specs.
Local Open Scope Z_scope.
#[local] Existing Instance HCS.

Lemma body_root_same: semax_body Vh Gh f_root_same root_same_spec.
Proof.
  start_function.
  destruct H as (L1 & L2 & L3 & L4 & W1 & W2 & W3 & W4).
  forward_for_simple_bound 512
    (EX i: Z,
     PROP ()
     LOCAL (temp _a a; temp _b b)
     SEP (data_at sha t_root (root_val rv) a; data_at shb t_root (root_val rv) b)).
  { entailer!. }
  { cbv beta. unfold root_val. ld. ld.
    forward_if (temp _t'1 (Vint (Int.repr 0))).
    { neq_absurd. }
    { ld. ld. forward. entailer!. unfold Int64.cmpu. rewrite Int64.eq_true. reflexivity. }
    forward_if (temp _t'2 (Vint (Int.repr 0))).
    { neq_absurd. }
    { ld. ld. forward. entailer!. unfold Int64.cmpu. rewrite Int64.eq_true. reflexivity. }
    forward_if.
    { neq_absurd. }
    forward. entailer!. }
  forward_for_simple_bound 4096
    (EX i: Z,
     PROP ()
     LOCAL (temp _a a; temp _b b)
     SEP (data_at sha t_root (root_val rv) a; data_at shb t_root (root_val rv) b)).
  { entailer!. }
  { cbv beta. unfold root_val. ld. ld.
    forward_if.
    { neq_absurd. }
    forward. entailer!. }
  forward.
Qed.

Lemma body_root_copy: semax_body Vh Gh f_root_copy root_copy_spec.
Proof.
  start_function.
  destruct H as (L1 & L2 & L3 & L4 & W1 & W2 & W3 & W4). unfold LEAVES in L4.
  forward_for_simple_bound 512
    (EX i: Z,
     PROP ()
     LOCAL (temp _d d; temp _s s)
     SEP (data_at Tsh t_root (root_part (longs (sublist 0 i (pml4 rv)) ++ Zrepeat Vundef (512 - i))
                                        (longs (sublist 0 i (pdpt rv)) ++ Zrepeat Vundef (512 - i))
                                        (longs (sublist 0 i (pd rv)) ++ Zrepeat Vundef (512 - i))
                                        (Zrepeat Vundef 4096)) d;
          data_at sh t_root (root_val rv) s)).
  { entailer!. }
  { cbv beta. unfold root_val, root_part. ld. forward. ld. forward. ld. forward.
    rewrite !upd_prefix by lia. entailer!. }
  rewrite !prefix_full by lia.
  forward_for_simple_bound 4096
    (EX i: Z,
     PROP ()
     LOCAL (temp _d d; temp _s s)
     SEP (data_at Tsh t_root (root_part (longs (pml4 rv)) (longs (pdpt rv)) (longs (pd rv))
                                        (longs (sublist 0 i (pt rv)) ++ Zrepeat Vundef (4096 - i))) d;
          data_at sh t_root (root_val rv) s)).
  { rewrite prefix_0. entailer!. }
  { cbv beta. unfold root_val, root_part. ld. forward.
    rewrite !upd_prefix by lia. entailer!. }
  rewrite !prefix_full by lia. rewrite <- root_val_part.
  entailer!.
Qed.
