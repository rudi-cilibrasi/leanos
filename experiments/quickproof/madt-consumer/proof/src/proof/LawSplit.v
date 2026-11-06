(* Law consumer_obligations: the harness's struct oracle as its fields (LawDefs.ofields), proved once: VST's
   unfold_data_at on the 18 fields is slow, and every function of the harness works on the fields. *)
Require Import VST.floyd.proofauto.
Require Import LeanosMadt.harness.consumer_obligations.code.
Require Import LeanosMadt.proof.Defs.
Require Import LeanosMadt.proof.MadtSpecs.
Require Import LeanosMadt.proof.LawProg LeanosMadt.proof.LawDefs.
Local Open Scope Z_scope.
#[local] Existing Instance LawProg.LCS.

Lemma oval_split: forall q p n ob s,
  data_at Ews t_oracle (oval p n ob s) q = ofields q p n ob s.
Proof.
  intros. unfold oval, ofields.
  unfold_data_at (data_at _ _ _ q).
  apply pred_ext; cancel.
Qed.
