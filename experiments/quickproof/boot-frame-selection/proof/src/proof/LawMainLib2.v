(* Law frame_selection_exact: the states object folded back from its two rows (the steps that take state 0 or
   state 1 alone). *)
Require Import VST.floyd.proofauto.
Require Import LeanosFrameSelection.proof.Defs.
Require Import LeanosFrameSelection.proof.FrameSpecs.
Local Open Scope Z_scope.

Lemma states_fold (sh: share) (ss: list (list Z)) (sp: val) :
  Zlength ss = 2 -> field_compatible t_states nil sp ->
  (data_at sh t_state (map vl (Znth 0 ss)) sp * data_at sh t_state (map vl (Znth 1 ss)) (row_ptr sp 1))%logic
  |-- data_at sh t_states (states_val ss) sp.
Proof. intros L FC. rewrite (states_split sh ss sp L FC). apply derives_refl. Qed.
