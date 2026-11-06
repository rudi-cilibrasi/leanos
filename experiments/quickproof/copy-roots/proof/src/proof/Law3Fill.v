(* Law window_scan_exact: the body of the harness's root_fill. *)
Require Import VST.floyd.proofauto.
Require Import QuickProof.Env.
Require Import LeanosRoots.harness.window_scan_exact.code.
Require Import LeanosRoots.proof.Defs.
Require Import LeanosRoots.proof.Law3Facts.
Require Import LeanosRoots.proof.Law3Specs.
Local Open Scope Z_scope.
#[local] Existing Instance HCS.

Lemma body_root_fill: semax_body Vh Gh f_root_fill root_fill_spec.
Proof.
  start_function.
  forward_for_simple_bound 512
    (EX i: Z, EX a: list Z, EX b: list Z, EX c: list Z,
     PROP (Zlength a = i; Zlength b = i; Zlength c = i; words_ok a; words_ok b; words_ok c)
     LOCAL (temp _r r)
     SEP (data_at Tsh t_root (root_part (longs a ++ Zrepeat Vundef (512 - i)) (longs b ++ Zrepeat Vundef (512 - i))
                                        (longs c ++ Zrepeat Vundef (512 - i)) (Zrepeat Vundef 4096)) r)).
  { Exists (@nil Z) (@nil Z) (@nil Z). entailer!. repeat split; constructor. }
  { cbv beta. Intros. unfold root_part.
    forward_call. Intros x. forward.
    forward_call. Intros y. forward.
    forward_call. Intros z. forward.
    Exists (a ++ [x]) (b ++ [y]) (c ++ [z]).
    rewrite !upd_app by lia.
    entailer!. repeat split; try list_solve; apply words_ok_snoc; auto. }
  Intros a b c. rewrite !app_full by lia.
  forward_for_simple_bound 4096
    (EX i: Z, EX t: list Z,
     PROP (Zlength t = i; words_ok t)
     LOCAL (temp _r r)
     SEP (data_at Tsh t_root (root_part (longs a) (longs b) (longs c) (longs t ++ Zrepeat Vundef (4096 - i))) r)).
  { Exists (@nil Z). entailer!. constructor. }
  { cbv beta. Intros. unfold root_part.
    forward_call. Intros x. forward.
    Exists (t ++ [x]).
    rewrite !upd_app by lia.
    entailer!. split; [ list_solve | apply words_ok_snoc; auto ]. }
  Intros t. rewrite !app_full by lia.
  Exists (mkroot a b c t). rewrite (root_val_part (mkroot a b c t)). simpl pml4; simpl pdpt; simpl pd; simpl pt.
  entailer!. unfold root_ok. simpl. repeat split; auto.
Qed.
