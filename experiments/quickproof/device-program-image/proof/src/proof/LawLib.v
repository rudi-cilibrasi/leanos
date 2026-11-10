(* Law image_exact: arithmetic of the harness's 32- and 64-bit words and the tactics shared by the body proofs of
   the harness's functions. *)
Require Import VST.floyd.proofauto.
Require Import LeanosDeviceProgramImage.proof.Defs.
Local Open Scope Z_scope.

Lemma Forall_u8_Znth: forall bs i, Forall u8_ok bs -> 0 <= i < Zlength bs -> 0 <= Znth i bs <= Byte.max_unsigned.
Proof. intros bs i F I. exact (proj1 (Forall_Znth _ _) F i I). Qed.

Lemma Int_eq_u32: forall a b, u32_ok a -> u32_ok b -> Int.eq (Int.repr a) (Int.repr b) = (a =? b).
Proof.
  intros a b Ha Hb. unfold u32_ok in *. unfold Int.eq. rewrite !Int.unsigned_repr by auto.
  destruct (zeq a b); destruct (Z.eqb_spec a b); auto; lia.
Qed.

Lemma Int64_eq_u64: forall a b, u64_ok a -> u64_ok b -> Int64.eq (Int64.repr a) (Int64.repr b) = (a =? b).
Proof.
  intros a b Ha Hb. unfold u64_ok in *. unfold Int64.eq. rewrite !Int64.unsigned_repr by auto.
  destruct (zeq a b); destruct (Z.eqb_spec a b); auto; lia.
Qed.

Lemma Int_ltu_u32: forall a b, u32_ok a -> u32_ok b -> Int.ltu (Int.repr a) (Int.repr b) = (a <? b).
Proof.
  intros a b Ha Hb. unfold u32_ok in *. unfold Int.ltu. rewrite !Int.unsigned_repr by auto.
  destruct (zlt a b); destruct (Z.ltb_spec a b); auto; lia.
Qed.

Lemma repr_u32_inj: forall a b, u32_ok a -> u32_ok b -> Int.repr a = Int.repr b -> a = b.
Proof.
  intros a b Ha Hb E. unfold u32_ok in *. apply (f_equal Int.unsigned) in E.
  rewrite !Int.unsigned_repr in E by auto. exact E.
Qed.

Lemma repr_u64_inj: forall a b, u64_ok a -> u64_ok b -> Int64.repr a = Int64.repr b -> a = b.
Proof.
  intros a b Ha Hb E. unfold u64_ok in *. apply (f_equal Int64.unsigned) in E.
  rewrite !Int64.unsigned_repr in E by auto. exact E.
Qed.

Lemma repr_neq_e: forall a b, Int.repr a <> Int.repr b -> a <> b.
Proof. intros a b N E. subst. apply N. reflexivity. Qed.

Lemma repr64_neq_e: forall a b, Int64.repr a <> Int64.repr b -> a <> b.
Proof. intros a b N E. subst. apply N. reflexivity. Qed.

Lemma b2z_true: forall b, Int.repr (Z.b2z b) <> Int.repr 0 -> b = true.
Proof. intros [ ] E; [ reflexivity | exfalso; apply E; reflexivity ]. Qed.

Lemma b2z_false: forall b, Int.repr (Z.b2z b) = Int.repr 0 -> b = false.
Proof. intros [ ] E; [ discriminate | reflexivity ]. Qed.

Lemma u32_ok_b2z: forall b, u32_ok (Z.b2z b).
Proof. intros [ ]; unfold u32_ok; simpl; rep_lia. Qed.

Lemma modu_u32: forall a b, u32_ok a -> 0 < b <= Int.max_unsigned ->
  Int.modu (Int.repr a) (Int.repr b) = Int.repr (a mod b).
Proof. intros a b A B. unfold u32_ok in A. unfold Int.modu. rewrite !Int.unsigned_repr by lia. reflexivity. Qed.

Lemma divu_u32: forall a b, u32_ok a -> 0 < b <= Int.max_unsigned ->
  Int.divu (Int.repr a) (Int.repr b) = Int.repr (a / b).
Proof. intros a b A B. unfold u32_ok in A. unfold Int.divu. rewrite !Int.unsigned_repr by lia. reflexivity. Qed.

(* The hypotheses of a branch on a comparison of u32 (u64) values, as comparisons of Z, rewritten into the goal's
   booleans. *)
Ltac bfix :=
  repeat match goal with
  | H: Int.repr (Z.b2z ?b) <> Int.zero |- _ => change Int.zero with (Int.repr 0) in H
  | H: Int.repr (Z.b2z ?b) = Int.zero |- _ => change Int.zero with (Int.repr 0) in H
  | H: Int.repr (Z.b2z ?b) <> Int.repr 0 |- _ => apply b2z_true in H; try rewrite H; rewrite ?H in *
  | H: Int.repr (Z.b2z ?b) = Int.repr 0 |- _ => apply b2z_false in H; try rewrite H; rewrite ?H in *
  | H: Int.repr ?x = Int.repr ?y |- _ =>
      apply repr_u32_inj in H; [ rewrite ?(proj2 (Z.eqb_eq x y) H) in *
        | first [ assumption | unfold u32_ok in *; rep_lia ] | first [ assumption | unfold u32_ok in *; rep_lia ] ]
  | H: Int.repr ?x <> Int.repr ?y |- _ =>
      apply repr_neq_e in H; rewrite ?(proj2 (Z.eqb_neq x y) H) in *
  | H: Int64.repr ?x = Int64.repr ?y |- _ =>
      apply repr_u64_inj in H; [ rewrite ?(proj2 (Z.eqb_eq x y) H) in *
        | first [ assumption | unfold u64_ok in *; rep_lia ] | first [ assumption | unfold u64_ok in *; rep_lia ] ]
  | H: Int64.repr ?x <> Int64.repr ?y |- _ =>
      apply repr64_neq_e in H; rewrite ?(proj2 (Z.eqb_neq x y) H) in *
  | H: context [Int.unsigned (Int.repr ?x)] |- _ =>
      rewrite (Int.unsigned_repr x) in H by (unfold u32_ok in *; rep_lia)
  end;
  rewrite ?Int_eq_u32, ?Int64_eq_u64, ?Int_ltu_u32 by first [ assumption | unfold u32_ok, u64_ok in *; rep_lia ].

(* Decide a goal of booleans of comparisons of Z, case by case. *)
Ltac bdec :=
  unfold bool2val, bits_in64, bits_in32 in *; cbn [andb orb negb Int.cmpu Int64.cmpu] in *;
  change Int64.zero with (Int64.repr 0) in *; change Int.zero with (Int.repr 0) in *;
  repeat match goal with
  | |- context [Int64.eq ?a ?b] => destruct (Int64.eq a b)
  | |- context [Int.eq ?a ?b] => destruct (Int.eq a b)
  | |- context [?x =? ?y] => destruct (Z.eqb_spec x y)
  | |- context [?x <=? ?y] => destruct (Z.leb_spec x y)
  | |- context [?x <? ?y] => destruct (Z.ltb_spec x y)
  end;
  cbn [andb orb negb] in *; first [ reflexivity | discriminate | congruence | lia ].

(* A goal Vint (Int.repr (Z.b2z b)) = bool2val c (or = Vint (Int.repr 0)) of booleans of comparisons. *)
Ltac bfin :=
  unfold bool2val; cbn [andb orb negb] in *;
  repeat match goal with |- context [(?x =? ?y)] => destruct (x =? y) end;
  cbn [andb orb negb] in *; first [ reflexivity | discriminate | congruence ].
