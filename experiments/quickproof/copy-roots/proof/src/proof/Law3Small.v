(* Law window_scan_exact: the bodies of the harness's member and table. *)
Require Import VST.floyd.proofauto.
Require Import QuickProof.Env.
Require Import LeanosRoots.harness.window_scan_exact.code.
Require Import LeanosRoots.proof.Defs.
Require Import LeanosRoots.proof.Law3Facts.
Require Import LeanosRoots.proof.Law3Specs.
Local Open Scope Z_scope.
#[local] Existing Instance HCS.

Lemma body_table: semax_body Vh Gh f_table table_spec.
Proof.
  start_function.
  forward.
  entailer!. f_equal. unfold table_entry. rewrite (Z.mul_comm k 4096). apply repr_lor_mod.
Qed.

Lemma body_member: semax_body Vh Gh f_member member_spec.
Proof.
  start_function.
  forward_for_simple_bound n
    (EX i: Z,
     PROP (member f (sublist 0 i fs) = false)
     LOCAL (temp _frame (Vlong (Int64.repr f)); temp _frames p; temp _n (Vlong (Int64.repr n)))
     SEP (data_at sh (tarray tulong (Zlength fs)) (longs fs) p)).
  { entailer!. }
  { assert (Wi: word_ok (Znth i fs)) by (apply Forall_Znth; first [ lia | exact H0 ]).
    cbv beta. forward.
    { entailer!. unfold longs. rewrite Znth_map by lia. exact I. }
    unfold longs. rewrite Znth_map by lia.
    forward_if.
    { forward. entailer!. eq_to_z.
      match goal with E: Z.eqb _ _ = true |- _ => apply Z.eqb_eq in E; rename E into Ef end.
      assert (M: member f (sublist 0 n fs) = true).
      { rewrite (sublist_split 0 (i + 1) n) by lia. unfold member. rewrite existsb_app.
        fold (member f (sublist 0 (i + 1) fs)). rewrite member_sublist_succ by lia.
        rewrite Ef, Z.eqb_refl, orb_true_r. reflexivity. }
      rewrite M. reflexivity. }
    { forward. entailer!. eq_to_z.
      rewrite member_sublist_succ by lia.
      match goal with E: member f (sublist 0 i fs) = false |- _ => rewrite E end.
      simpl. rewrite Z.eqb_sym. apply Z.eqb_neq. intro E.
      match goal with N: Int64.repr _ <> Int64.repr _ |- _ => apply N; rewrite E; reflexivity end. } }
  forward. entailer!. match goal with E: member f (sublist 0 n fs) = false |- _ => rewrite E end. reflexivity.
Qed.

