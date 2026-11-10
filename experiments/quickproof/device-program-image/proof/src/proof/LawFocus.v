(* Law image_exact: a descriptor of a policy object as its own object (the harness passes &p->descs[i] to
   same_desc and declares_desc), with a wand that gives the policy back. *)
Require Import VST.floyd.proofauto.
Require Import LeanosDeviceProgramImage.harness.image_exact.code.
Require Import LeanosDeviceProgramImage.proof.Defs.
Require Import LeanosDeviceProgramImage.proof.LawProg LeanosDeviceProgramImage.proof.LawSpecs.
Local Open Scope Z_scope.
#[local] Existing Instance LawProg.LCS.

(* The descriptors of a policy object's value. *)
Definition pdescs (pv: policy_t) : list desc_t :=
  snd (snd (snd (snd (snd (snd (snd (snd (snd (snd pv))))))))).

Lemma pdescs_rep: forall a1 a2 a3 a4 a5 a6 a7 a8 ss dc ds,
  pdescs (policy_rep a1 a2 a3 a4 a5 a6 a7 a8 ss dc ds) = ds.
Proof. reflexivity. Qed.

Lemma upd_Znth_same_val {A} {d: Inhabitant A}: forall i (l: list A), upd_Znth i l (Znth i l) = l.
Proof.
  intros. destruct (zle 0 i); [ destruct (zlt i (Zlength l)) | ].
  - list_solve.
  - unfold upd_Znth. match goal with |- context [if ?c then _ else _] => destruct c end; [ lia | reflexivity ].
  - unfold upd_Znth. match goal with |- context [if ?c then _ else _] => destruct c end; [ lia | reflexivity ].
Qed.

Lemma desc_focus: forall sh (pv: policy_t) p i, 0 <= i < 16 ->
  data_at sh t_policy pv p |--
  data_at sh t_desc (Znth i (pdescs pv)) (field_address t_policy (DOT _descs SUB i) p) *
  (data_at sh t_desc (Znth i (pdescs pv)) (field_address t_policy (DOT _descs SUB i) p) -*
   data_at sh t_policy pv p).
Proof.
  intros sh pv p i I.
  unfold data_at at 1 4.
  eapply derives_trans.
  - eapply nested_field_ramif' with (gfs1 := [ArraySubsc i; StructField _descs]).
    + apply JMeq_refl.
    + simpl. repeat split; auto; try lia. unfold in_members; simpl. repeat (first [ left; reflexivity | right ]).
  - simpl app. rewrite field_at_data_at.
    destruct pv as (a1 & a2 & a3 & a4 & a5 & a6 & a7 & a8 & ss & dc & ds).
    simpl proj_reptype.
    apply sepcon_derives; [ apply derives_refl | ].
    apply allp_left with (Znth i ds). apply allp_left with (Znth i ds).
    rewrite prop_imp by apply JMeq_refl.
    apply wand_derives.
    + rewrite field_at_data_at. apply derives_refl.
    + apply derives_refl'. f_equal.
      assert (U: upd_Znth i ds (Znth i ds) = ds) by apply upd_Znth_same_val.
      transitivity (a1, (a2, (a3, (a4, (a5, (a6, (a7, (a8, (ss, (dc, upd_Znth i ds (Znth i ds)))))))))));
        [ reflexivity | rewrite U; reflexivity ].
Qed.

(* The same for the descriptor array as a field. *)
Lemma descs_focus: forall sh (ds: list desc_t) p i, 0 <= i < 16 ->
  field_at sh t_policy (DOT _descs) ds p |--
  data_at sh t_desc (Znth i ds) (field_address t_policy (DOT _descs SUB i) p) *
  (data_at sh t_desc (Znth i ds) (field_address t_policy (DOT _descs SUB i) p) -*
   field_at sh t_policy (DOT _descs) ds p).
Proof.
  intros sh ds p i I.
  eapply derives_trans.
  - eapply nested_field_ramif' with (gfs1 := [ArraySubsc i]).
    + apply JMeq_refl.
    + simpl. repeat split; auto; try lia. unfold in_members; simpl. repeat (first [ left; reflexivity | right ]).
  - simpl app. rewrite field_at_data_at.
    apply sepcon_derives; [ apply derives_refl | ].
    apply allp_left with (Znth i ds). apply allp_left with (Znth i ds).
    rewrite prop_imp by apply JMeq_refl.
    apply wand_derives.
    + rewrite field_at_data_at. apply derives_refl.
    + apply derives_refl'. f_equal.
      transitivity (upd_Znth i ds (Znth i ds)); [ reflexivity | apply upd_Znth_same_val ].
Qed.

(* &p->descs[i] as the harness computes it. *)
Lemma desc_addr: forall p i,
  field_compatible t_desc nil (field_address t_policy (DOT _descs SUB i) p) ->
  field_address t_policy (DOT _descs SUB i) p = offset_val (80 + sizeof t_desc * i) p.
Proof.
  intros p i FC. unfold field_address in *.
  destruct (field_compatible_dec t_policy (DOT _descs SUB i) p) as [Y|N].
  - f_equal.
  - destruct FC as [F _]. simpl in F. contradiction.
Qed.

Ltac desc_arg :=
  match goal with |- context [field_address t_policy (DOT _descs SUB ?i) ?p] =>
    rewrite (desc_addr p i) by assumption end;
  try reflexivity.
