(* Law admission_exact: the harness's struct law as its fields with any values (lraw) and its padding, proved once
   (VST's unfold_data_at on the struct is slow), and the global `law` as main finds it: all zeros. *)
Require Import VST.floyd.proofauto.
Require Import LeanosMadtAdmission.harness.admission_exact.code.
Require Import LeanosMadtAdmission.proof.Defs.
Require Import LeanosMadtAdmission.proof.MgaSpecs.
Require Import LeanosMadtAdmission.proof.LawProg LeanosMadtAdmission.proof.LawDefs.
Local Open Scope Z_scope.
#[local] Existing Instance LawProg.LCS.

(* struct law with the values of its fields, in its order. *)
Definition law_val (c len ex: Z) (cp: val) (args: list Z) (e v t w: Z) (st an: list Z) (id: Z) : reptype t_law :=
  (vi c, (vi len, (vi ex, (cp, (map vl args, (vi e, (vi v, (vl t, (vl w, (map vl st, (map vl an, vl id))))))))))).

Definition lraw (q: val) (c len ex: Z) (cp: val) (args: list Z) (e v t w: Z) (st an: list Z) (id: Z) : mpred :=
 (field_at Ews t_law (DOT _call) (vi c) q *
  field_at Ews t_law (DOT _length) (vi len) q *
  field_at Ews t_law (DOT _executing) (vi ex) q *
  field_at Ews t_law (DOT _copy) cp q *
  field_at Ews t_law (DOT _args) (map vl args) q *
  field_at Ews t_law (DOT _expect) (vi e) q *
  field_at Ews t_law (DOT _verdict) (vi v) q *
  field_at Ews t_law (DOT _at) (vl t) q *
  field_at Ews t_law (DOT _word) (vl w) q *
  field_at Ews t_law (DOT _state) (map vl st) q *
  field_at Ews t_law (DOT _answer) (map vl an) q *
  field_at Ews t_law (DOT _id) (vl id) q)%logic.

(* The struct's fields, and its padding after `executing`. *)
Lemma law_split: forall q c len ex cp args e v t w st an id,
  data_at Ews t_law (law_val c len ex cp args e v t w st an id) q |-- lraw q c len ex cp args e v t w st an id * TT.
Proof.
  intros. unfold law_val, lraw.
  unfold_data_at (data_at _ _ _ q).
  cancel.
Qed.

Lemma zero_law: zero_val t_law = law_val 0 0 0 nullval (Zrepeat 0 10) 0 0 0 0 (Zrepeat 0 12) (Zrepeat 0 16) 0.
Proof.
  apply JMeq_eq. eapply JMeq_trans; [ apply JMeq_zero_val_zero_val' | ].
  Timeout 60 vm_compute. apply JMeq_refl.
Qed.

Lemma law_zero: forall gv, headptr (gv _law) ->
  globvars2pred gv [(_law, v_law)] |--
  lraw (gv _law) 0 0 0 nullval (Zrepeat 0 10) 0 0 0 0 (Zrepeat 0 12) (Zrepeat 0 16) 0 * TT.
Proof.
  intros gv H. eapply derives_trans; [ | apply law_split ]. rewrite <- zero_law.
  unfold globvars2pred, globvar2pred. simpl. rewrite ?sepcon_emp.
  change 360 with (sizeof t_law).
  apply mapsto_zero_data_at_zero.
  - apply writable_readable, writable_Ews.
  - reflexivity.
  - reflexivity.
  - apply headptr_field_compatible; auto;
      first [ reflexivity | exact I | (vm_compute; reflexivity) | (apply la_env_cs_sound; reflexivity) ].
Qed.
