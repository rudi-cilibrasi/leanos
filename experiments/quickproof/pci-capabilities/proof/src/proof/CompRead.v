(* Law capabilities_complete: the body of the harness's callback space_read, against the read protocol of the
   law's device (read_spec Dev_comp): it answers every read with success and the word of the fixed space. *)
Require Import VST.floyd.proofauto.
Require Import QuickProof.Env.
Require Import LeanosCaps.proof.Defs.
Require LeanosCaps.proof.CapsSpecs.
Require Import LeanosCaps.proof.CompPure.
Require Import LeanosCaps.proof.CompSpecs.
Require Import LeanosCaps.harness.capabilities_complete.code.
Local Open Scope Z_scope.
#[local] Existing Instance LCS.

Definition Gread : funspecs := [gp_assert_spec].

Lemma body_space_read: semax_body nil Gread f_space_read space_read_spec.
Proof.
  start_function.
  unfold Dev_comp. Intros W.
  rewrite uint__cs.
  destruct bdf as [[b d] f].
  unfold CapsSpecs.bus_of, CapsSpecs.dev_of, CapsSpecs.fn_of, CapsSpecs.u8_ok in *. simpl fst in *. simpl snd in *.
  forward.
  unfold space_val, CapsSpecs.bus_of, CapsSpecs.dev_of, CapsSpecs.fn_of. simpl fst. simpl snd. unfold vint.
  forward.
  forward_if (temp _t'1 (Vint Int.one)).
  { forward. forward. entailer!. }
  { contradiction. }
  forward_if (temp _t'2 (Vint Int.one)).
  { forward. forward. entailer!. }
  { discriminate. }
  forward_call (Int.one).
  forward_if (temp _t'3 (Vint Int.one)).
  { forward. entailer!. destruct (zlt 252 off); [ lia | reflexivity ]. }
  { exfalso. match goal with N: Int.and _ _ <> _ |- _ => apply N end.
    rewrite int_and by rep_lia. rewrite H0. reflexivity. }
  forward_call (Int.one).
  assert (Q: 0 <= off / 4 < 64) by (Z.div_mod_to_equations; lia).
  assert (I4: 0 <= Int.signed (Int.divs (Int.repr off) (Int.repr 4)) < Zlength W) by (rewrite divs4 by lia; lia).
  forward.
  { go_lower. unfold denote_tc_assert. simpl.
    apply andp_right; [ apply TT_right | apply prop_right ].
    intros [_ E]. apply (f_equal Int.unsigned) in E. vm_compute in E. discriminate E. }
  rewrite divs4 by lia.
  forward.
  forward.
  Exists true (Znth (off / 4) W).
  unfold Dev_comp. Exists W.
  rewrite uint_cs.
  entailer!.
  split.
  - apply Forall_Znth; first [ assumption | lia ].
  - apply Forall_app. split; [ assumption | ].
    constructor; [ split; reflexivity | constructor ].
Qed.
