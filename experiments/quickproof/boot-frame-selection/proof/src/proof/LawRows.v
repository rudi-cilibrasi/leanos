(* Law frame_selection_exact: the law's model of the two states (states_expect) as two rows, which the harness
   reads through a pointer `s = m->states_expect[k]`, and the address the harness computes for row k. *)
Require Import VST.floyd.proofauto.
Require Import LeanosFrameSelection.harness.frame_selection_exact.code.
Require Import LeanosFrameSelection.proof.Defs.
Require Import LeanosFrameSelection.proof.FrameSpecs.
Require Import LeanosFrameSelection.proof.LawProg LeanosFrameSelection.proof.LawDefs LeanosFrameSelection.proof.LawFacts
  LeanosFrameSelection.proof.LawLib.
Local Open Scope Z_scope.
#[export] Existing Instance LawProg.LCS.

Definition OFS_STATES : Z := 2128.

(* Row k of states_expect. *)
Definition srow (q: val) (k: Z) : val := offset_val (OFS_STATES + 328 * k) q.

Lemma ofs_states: forall q, field_compatible t_law (DOT _states_expect) q ->
  field_address t_law (DOT _states_expect) q = offset_val OFS_STATES q.
Proof. intros. rewrite field_compatible_field_address by auto. reflexivity. Qed.

Lemma states_val_rows: forall ss, Zlength ss = 2 -> states_val ss = [map vl (Znth 0 ss); map vl (Znth 1 ss)].
Proof.
  intros ss L. destruct ss as [ | r0 [ | r1 [ | r2 ss]]]; try (rewrite ?Zlength_cons, ?Zlength_nil in L; rep_lia).
  reflexivity.
Qed.

Lemma states_rows: forall q ss, field_compatible t_law (DOT _states_expect) q -> Zlength ss = 2 ->
  Zlength (Znth 0 ss) = WORDS -> Zlength (Znth 1 ss) = WORDS ->
  field_at Ews t_law (DOT _states_expect) (states_val ss) q =
  (data_at Ews t_state (map vl (Znth 0 ss)) (srow q 0) * data_at Ews t_state (map vl (Znth 1 ss)) (srow q 1))%logic.
Proof.
  intros q ss FC L L0 L1. rewrite (states_val_rows ss L).
  rewrite field_at_data_at, ofs_states by auto.
  pose proof (field_compatible_nested_field _ _ _ FC) as FCa.
  change (nested_field_offset t_law (DOT _states_expect)) with OFS_STATES in FCa.
  change (nested_field_type t_law (DOT _states_expect)) with (tarray t_state 2) in FCa |- *.
  change [map vl (Znth 0 ss); map vl (Znth 1 ss)] with ([map vl (Znth 0 ss)] ++ [map vl (Znth 1 ss)]).
  rewrite (split2_data_at_Tarray_app 1 2) by (rewrite ?Zlength_cons, ?Zlength_nil; reflexivity).
  rewrite field_address0_offset by auto with field_compatible.
  rewrite (data_at_singleton_array_eq Ews t_state (map vl (Znth 0 ss))) by reflexivity.
  replace (2 - 1) with 1 by lia.
  rewrite (data_at_singleton_array_eq Ews t_state (map vl (Znth 1 ss))) by reflexivity.
  unfold srow. rewrite offset_offset_val. f_equal.
Qed.

(* The address `m->states_expect[k]` the harness computes. *)
Lemma srow_eval: forall q k, isptr q -> 0 <= k <= 1 ->
  force_val (sem_add_ptr_int (tarray tulong 41) Unsigned (offset_val OFS_STATES q) (vi k)) = srow q k.
Proof.
  intros q k P K. destruct q; try contradiction.
  unfold srow, vi, OFS_STATES, offset_val. simpl.
  rewrite Ptrofs.add_assoc. f_equal. f_equal.
  unfold Ptrofs.of_intu, Ptrofs.of_int. rewrite Int.unsigned_repr by rep_lia.
  rewrite ptrofs_mul_repr, ptrofs_add_repr. f_equal.
Qed.

Lemma srow_eval0: forall q, isptr q ->
  force_val (sem_add_ptr_int (tarray tulong 41) Signed (offset_val OFS_STATES q) (Vint (Int.repr 0))) = srow q 0.
Proof.
  intros q P. destruct q; try contradiction.
  unfold srow, OFS_STATES, offset_val. simpl.
  rewrite Ptrofs.add_assoc. f_equal.
Qed.

(* `m->states_expect[k]` as VST evaluates it, with k the uint32_t scan or the int 0. *)
Lemma srow_field: forall q k, isptr q -> 0 <= k <= 1 ->
  force_val (sem_binary_operation' Oadd (tarray (tarray tulong 41) 2) tuint
     (eval_field (Tstruct _law__1 noattr) _states_expect q) (vi k)) = srow q k.
Proof.
  intros q k P K. destruct q; try contradiction. unfold srow, OFS_STATES, offset_val, vi. simpl.
  f_equal. rewrite Ptrofs.add_assoc. f_equal.
  unfold Ptrofs.of_intu, Ptrofs.of_int. rewrite Int.unsigned_repr by rep_lia.
  rewrite ptrofs_mul_repr, ptrofs_add_repr. reflexivity.
Qed.

Lemma srow_field0: forall q, isptr q ->
  force_val (sem_binary_operation' Oadd (tarray (tarray tulong 41) 2) tint
     (eval_field (Tstruct _law__1 noattr) _states_expect q) (Vint (Int.repr 0))) = srow q 0.
Proof.
  intros q P. destruct q; try contradiction. unfold srow, OFS_STATES, offset_val. simpl.
  f_equal. rewrite Ptrofs.add_assoc. f_equal.
Qed.
