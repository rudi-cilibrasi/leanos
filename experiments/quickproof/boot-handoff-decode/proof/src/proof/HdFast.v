(* A replacement for VST's simplify_remove_localdef_temp (floyd/forward.v), which forward_call runs to drop the
   temp a call assigns from the LOCAL clause (the ACPI pipeline's PipeFast.v, unchanged but for this comment).
   VST decides each `ident_eq i j` with `simpl`, which reduces the proof terms of Pos.eq_dec and is exponential
   in the common prefix of the two identifiers: here assigning `status` while `states` is live does not
   finish.  This version rewrites with a boolean comparison,
   computed on the identifiers' positives one entry at a time.  A body proof installs it for itself only, after
   importing this file, with
     #[local] Ltac simplify_remove_localdef_temp ::= fast_remove_localdef_temp.
   so that nothing that merely Requires a body proof (Bodies.v and what loads it) sees VST's tactic changed. *)
Require Import VST.floyd.proofauto.

Fixpoint remove_temp_b (i: ident) (l: list localdef) : list localdef :=
  match l with
  | nil => nil
  | d :: l0 =>
    match d with
    | temp j _ => if Pos.eqb i j then remove_temp_b i l0 else d :: remove_temp_b i l0
    | _ => d :: remove_temp_b i l0
    end
  end.

Lemma remove_temp_b_eq: forall i l, remove_localdef_temp i l = remove_temp_b i l.
Proof.
  intros i l. induction l as [ | d l IH]; [ reflexivity | ]. simpl. rewrite IH.
  destruct d; auto. unfold rlt_ident_eq, ident_eq, peq.
  destruct (Pos.eq_dec i i0); [ subst; rewrite Pos.eqb_refl | rewrite (proj2 (Pos.eqb_neq _ _) n) ]; reflexivity.
Qed.

Lemma remove_temp_b_nil: forall i, remove_temp_b i nil = nil.
Proof. reflexivity. Qed.

Lemma remove_temp_b_hit: forall i j v l, Pos.eqb i j = true -> remove_temp_b i (temp j v :: l) = remove_temp_b i l.
Proof. intros. simpl. rewrite H. reflexivity. Qed.

Lemma remove_temp_b_miss: forall i j v l, Pos.eqb i j = false ->
  remove_temp_b i (temp j v :: l) = temp j v :: remove_temp_b i l.
Proof. intros. simpl. rewrite H. reflexivity. Qed.

Lemma remove_temp_b_lvar: forall i j t v l, remove_temp_b i (lvar j t v :: l) = lvar j t v :: remove_temp_b i l.
Proof. reflexivity. Qed.

Lemma remove_temp_b_gvars: forall i gv l, remove_temp_b i (gvars gv :: l) = gvars gv :: remove_temp_b i l.
Proof. reflexivity. Qed.

Ltac remove_temp_b_step :=
  match goal with
  | |- context [remove_temp_b ?i (temp ?j ?v :: ?l)] =>
      let r := eval vm_compute in (Pos.eqb i j) in
      lazymatch r with
      | true => rewrite (remove_temp_b_hit i j v l) by reflexivity
      | false => rewrite (remove_temp_b_miss i j v l) by reflexivity
      end
  | |- context [remove_temp_b ?i (lvar ?j ?t ?v :: ?l)] => rewrite (remove_temp_b_lvar i j t v l)
  | |- context [remove_temp_b ?i (gvars ?gv :: ?l)] => rewrite (remove_temp_b_gvars i gv l)
  | |- context [remove_temp_b ?i nil] => rewrite (remove_temp_b_nil i)
  end.

Ltac fast_remove_localdef_temp :=
  match goal with |- context [remove_localdef_temp ?i ?L] =>
    rewrite (remove_temp_b_eq i L); repeat remove_temp_b_step
  end.
