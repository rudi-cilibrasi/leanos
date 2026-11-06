(* Law capabilities_adversarial: the body of the harness's named_pointer. *)
Require Import VST.floyd.proofauto.
Require Import QuickProof.Env.
Require Import LeanosCaps.harness.capabilities_adversarial.code.
Require Import LeanosCaps.proof.Defs.
Require LeanosCaps.proof.CapsSpecs.
Require Import LeanosCaps.proof.AdvProg LeanosCaps.proof.AdvWalk LeanosCaps.proof.AdvFacts LeanosCaps.proof.AdvSpecs
  LeanosCaps.proof.AdvLib.
Local Open Scope Z_scope.
#[local] Existing Instance AdvProg.LCS.

Lemma body_named_pointer: semax_body Vh Gh f_named_pointer named_pointer_spec.
Proof.
  start_function.
  unfold Dev_adv. Intros offs oks vals.
  match goal with L: log_at _ _ _ _ |- _ => pose proof L as (L1 & L2 & L3 & F) end.
  unfold dev_val, hdr_val.
  assert (W1: 0 <= Znth 1 words <= Int.max_unsigned) by (apply words_Znth; auto; lia).
  assert (W13: 0 <= Znth 13 words <= Int.max_unsigned) by (apply words_Znth; auto; lia).
  assert (Ln: 0 <= Zlength h <= 52) by (pose proof (Zlength_nonneg h); lia).
  forward.
  forward_if.
  - try match goal with E: Int.repr (Zlength h) = Int.repr 4 |- _ =>
      apply repr_eq_unsigned in E; [ | rep_lia | rep_lia ] end.
    forward.
    forward_if (temp _t'1 (Vint (Int.repr (list_head words)))).
    + forward. forward.
      entailer!. unfold list_head.
      destruct (Z.land (Znth 1 words) 1048576 =? 0) eqn:E; [ | reflexivity ].
      apply Z.eqb_eq in E. exfalso.
      match goal with N: _ <> _ |- _ => apply N end. rewrite ?and_repr, E. reflexivity.
    + forward. entailer!. unfold list_head.
      match goal with N: _ = _ |- _ => rewrite ?and_repr in N; apply repr_eq_unsigned in N;
        [ rewrite N; reflexivity | apply land_range; auto | rep_lia ] end.
    + forward. unfold named. replace (Zlength h =? 4) with true by (symmetry; apply Z.eqb_eq; auto).
      unfold Dev_adv. Exists offs oks vals. unfold dev_val, hdr_val. entailer!.
  - try match goal with E: Int.repr (Zlength h) <> Int.repr 4 |- _ => apply repr_neq_unsigned in E end.
    assert (Ev: Znth (Zlength h - 1) vals = Vint (Int.repr (aval (Znth (Zlength h - 1) h)))).
    { apply (F (Zlength h - 1) ltac:(lia)). auto. }
    assert (Rv: 0 <= aval (Znth (Zlength h - 1) h) <= Int.max_unsigned) by (apply answers_ok_Znth; auto; lia).
    forward. forward. { entailer!. znth_val. rewrite Ev. exact I. }
    znth_val. rewrite Ev. forward.
    unfold named. replace (Zlength h =? 4) with false by (symmetry; apply Z.eqb_neq; auto).
    unfold Dev_adv. Exists offs oks vals. unfold dev_val, hdr_val. entailer!.
    rewrite nptr_repr by auto. reflexivity.
Qed.
