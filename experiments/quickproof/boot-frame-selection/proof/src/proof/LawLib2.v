(* Law frame_selection_exact: the record's ranges under a change of its scalar fields, shared by the callees. *)
Require Import VST.floyd.proofauto.
Require Import LeanosFrameSelection.proof.Defs.
Require Import LeanosFrameSelection.proof.FrameSpecs.
Require Import LeanosFrameSelection.proof.LawProg LeanosFrameSelection.proof.LawDefs LeanosFrameSelection.proof.LawFacts.
Local Open Scope Z_scope.

Lemma lst_ok_mk: forall s c r st e v b w ca sc ms me cm f fm se sb,
  lst_ok s -> u32_ok c -> u32_ok r -> u32_ok st -> u32_ok e -> u32_ok v -> u64_ok b -> u64_ok w -> u64_ok ca ->
  u32_ok sc -> u64_ok ms -> u64_ok me -> u64_ok cm -> u64_ok f -> u64_ok fm -> u64_ok se -> u32_ok sb ->
  lst_ok (mk_lst c r st e v b w ca sc ms me (w_free s) cm f fm se (w_answer s) sb).
Proof. intros. unfold lst_ok in *; lst_cbn. tauto. Qed.

Require Import LeanosFrameSelection.proof.LawLib.

(* The array words, as VST leaves it after the n stores of the words of l (LawLib.stores_words). *)
Ltac words_fill l n :=
  match goal with |- context [data_at Tsh (tarray tulong ?m) ?L ?p] =>
    lazymatch L with context [upd_Znth] =>
      replace L with (map vl l)
        by (symmetry;
            transitivity (stores (Zrepeat Vundef (Z.of_nat n))
                            (map (fun i => vl (Znth (Z.of_nat i - Z.of_nat 0) l)) (seq 0 n)) 0);
            [ reflexivity | apply stores_words; assumption ])
    end
  end.
