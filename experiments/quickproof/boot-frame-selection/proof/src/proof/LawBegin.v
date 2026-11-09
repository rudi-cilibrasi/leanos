(* Law frame_selection_exact: the bodies of main's begin_cross_check, begin_publication_check and begin_rescan:
   each computes the verdict of a step that makes no call (the cross-check, the publication check) or the rescan's
   order checks before its decoder, as the model's start of the step. *)
Require Import VST.floyd.proofauto.
Require Import QuickProof.Env.
Require Import LeanosFrameSelection.harness.frame_selection_exact.code.
Require Import LeanosFrameSelection.proof.Defs.
Require Import LeanosFrameSelection.proof.FrameSpecs.
Require Import LeanosFrameSelection.proof.LawProg LeanosFrameSelection.proof.LawDefs LeanosFrameSelection.proof.LawFacts
  LeanosFrameSelection.proof.LawLib LeanosFrameSelection.proof.LawLib2 LeanosFrameSelection.proof.LawRows
  LeanosFrameSelection.proof.LawLib3.
Local Open Scope Z_scope.
Local Open Scope bool_scope.
#[local] Existing Instance LawProg.LCS.

Lemma J_begin_ret: forall x s st, lst_ok s -> status_ok st -> i_step x <> FScrub -> i_step x <> FPublicationResult ->
  forall stp, u32_ok stp -> J x (Return st (i_mem x)) (set_stop (set_step s stp) st).
Proof.
  intros x s st L S F1 F2 stp U. pose proof (statuses_u32 _ S) as U'. lst_facts L. Jtac.
Qed.

Lemma states_rows_fold': forall q ss, field_compatible t_law (DOT _states_expect) q -> Zlength ss = 2 ->
  Zlength (Znth 0 ss) = WORDS -> Zlength (Znth 1 ss) = WORDS ->
  (data_at Ews (tarray tulong 41) (map vl (Znth 0 ss)) (srow q 0) *
   data_at Ews (tarray tulong 41) (map vl (Znth 1 ss)) (srow q 1))%logic
  |-- field_at Ews t_law (DOT _states_expect) (states_val ss) q.
Proof. intros. rewrite states_rows by auto. apply derives_refl. Qed.

(* The verdict of a chain of checks, the branch conditions known: one if at a time. *)
Ltac chk1 :=
  match goal with
  | |- context [if negb (Z.eqb ?a ?b) then _ else _] => destruct (Z.eqb_spec a b); cbn [negb]
  | |- context [if Z.leb ?a ?b then _ else _] => destruct (Z.leb_spec a b)
  | |- context [if Z.eqb ?a ?b then _ else _] => destruct (Z.eqb_spec a b)
  end.
Ltac chk_cond := repeat (first [ reflexivity | solve [ exfalso; lia ] | chk1 ]).

