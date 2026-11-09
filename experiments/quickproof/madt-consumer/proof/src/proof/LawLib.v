(* Law consumer_obligations: arithmetic of the harness's 64-bit words and tactics shared by the proofs of its
   functions. *)
Require Import VST.floyd.proofauto.
Require Import QuickProof.Env.
Require Import LeanosMadt.proof.Defs.
Require Import LeanosMadt.proof.MadtSpecs.
Require Import LeanosMadt.proof.LawProg LeanosMadt.proof.LawDefs LeanosMadt.proof.LawFacts.
Local Open Scope Z_scope.
Local Open Scope bool_scope.

(* The context of the exports: the environment functions and the helper they call. *)
Definition Gexp : funspecs := [any_u64_spec; gp_assert_spec].

Lemma Forall_u64_Znth: forall l i, Forall u64_ok l -> 0 <= i < Zlength l -> 0 <= Znth i l <= Int64.max_unsigned.
Proof. intros l i F I. exact (proj1 (Forall_Znth _ _) F i I). Qed.

Lemma Forall_byte_Znth: forall l i, Forall byte_ok l -> 0 <= i < Zlength l -> 0 <= Znth i l <= Byte.max_unsigned.
Proof. intros l i F I. exact (proj1 (Forall_Znth _ _) F i I). Qed.

Lemma Znth_map_vl: forall l i, 0 <= i < Zlength l -> Znth i (map vl l) = vl (Znth i l).
Proof. intros. rewrite Znth_map by auto. reflexivity. Qed.

Lemma upd_Znth_map_vl: forall l i v, upd_Znth i (map vl l) (vl v) = map vl (upd_Znth i l v).
Proof. intros. rewrite upd_Znth_map. reflexivity. Qed.

Lemma Int64_eq_repr: forall a b, 0 <= a <= Int64.max_unsigned -> 0 <= b <= Int64.max_unsigned ->
  Int64.eq (Int64.repr a) (Int64.repr b) = (a =? b).
Proof.
  intros a b Ha Hb. unfold Int64.eq. rewrite !Int64.unsigned_repr by auto.
  destruct (zeq a b); destruct (Z.eqb_spec a b); auto; lia.
Qed.

Lemma Int64_ltu_repr: forall a b, 0 <= a <= Int64.max_unsigned -> 0 <= b <= Int64.max_unsigned ->
  Int64.ltu (Int64.repr a) (Int64.repr b) = (a <? b).
Proof.
  intros a b Ha Hb. unfold Int64.ltu. rewrite !Int64.unsigned_repr by auto.
  destruct (zlt a b); destruct (Z.ltb_spec a b); auto; lia.
Qed.

Lemma add64_repr': forall a b, Int64.add (Int64.repr a) (Int64.repr b) = Int64.repr (a + b).
Proof.
  intros. unfold Int64.add. apply Int64.eqm_samerepr. apply Int64.eqm_add; apply Int64.eqm_sym, Int64.eqm_unsigned_repr.
Qed.

Lemma sub64_repr': forall a b, Int64.sub (Int64.repr a) (Int64.repr b) = Int64.repr (a - b).
Proof.
  intros. unfold Int64.sub. apply Int64.eqm_samerepr. apply Int64.eqm_sub; apply Int64.eqm_sym, Int64.eqm_unsigned_repr.
Qed.

Lemma repr64_inj: forall a b, 0 <= a <= Int64.max_unsigned -> 0 <= b <= Int64.max_unsigned ->
  Int64.repr a = Int64.repr b -> a = b.
Proof.
  intros a b Ha Hb E. apply (f_equal Int64.unsigned) in E. rewrite !Int64.unsigned_repr in E by auto. exact E.
Qed.

(* The ranges of the elements of the oracle's arrays, for rep_lia. *)
Ltac rng_list l n :=
  let rec go k :=
    lazymatch eval cbv in (k <? n) with
    | true =>
        assert (0 <= Znth k l <= Int64.max_unsigned) by (apply Forall_u64_Znth; [ assumption | rep_lia ]);
        let k' := eval cbv in (k + 1) in go k'
    | false => idtac
    end in
  go 0.

(* ---------------------------------------------------------------------- *)
(* The harness's checks: chains of && whose conditions all hold            *)
(* ---------------------------------------------------------------------- *)

Ltac first_stmt c := lazymatch c with Ssequence ?c1 _ => first_stmt c1 | _ => c end.

(* A comparison of 64-bit words as its truth value. *)
Ltac cmp_close :=
  unfold bool2val, Int64.cmpu; cbv beta iota;
  rewrite ?Int.unsigned_repr by rep_lia;
  rewrite ?Int64.eq_true;
  rewrite ?Int64_ltu_repr, ?Int64_eq_repr by rep_lia;
  repeat match goal with
  | |- context [zlt ?a ?b] => destruct (zlt a b); try lia
  | |- context [zeq ?a ?b] => destruct (zeq a b); try lia
  | |- context [?a <? ?b] => destruct (Z.ltb_spec a b); try lia
  | |- context [?a =? ?b] => destruct (Z.eqb_spec a b); try lia
  | |- context [Int64.ltu (Int64.repr ?a) (Int64.repr ?b)] => rewrite (Int64_ltu_repr a b) by rep_lia
  | |- context [Int64.eq (Int64.repr ?a) (Int64.repr ?b)] => rewrite (Int64_eq_repr a b) by rep_lia
  end; try reflexivity.

(* The branch of a condition that does not hold. *)
Ltac else_false :=
  exfalso;
  change Int64.zero with (Int64.repr 0) in *;
  match goal with
  | E: Int64.repr _ = Int64.repr _ |- _ => apply repr64_inj in E; [ lia | rep_lia | rep_lia ]
  | E: ?a <> ?a |- _ => apply E; reflexivity
  | E: Int.one = Int.zero |- _ => exact (Int.one_not_zero E)
  | E: Int64.repr _ <> Int64.repr _ |- _ => apply E; f_equal; lia
  | E: _ <> Int64.add _ _ |- _ => apply E; unfold Int64.add; rewrite !Int64.unsigned_repr by rep_lia; f_equal; lia
  | E: Int64.ltu _ _ = false |- _ => rewrite Int64_ltu_repr in E by rep_lia; apply Z.ltb_ge in E; lia
  | E: Int64.ltu _ _ = true |- _ => rewrite Int64_ltu_repr in E by rep_lia; apply Z.ltb_lt in E; lia
  | E: context [Int64.unsigned (Int64.repr _)] |- _ => rewrite !Int64.unsigned_repr in E by rep_lia; lia
  end.

(* Statements before the next if or call. *)
Ltac to_branch :=
  repeat match goal with |- semax _ _ ?c _ =>
    let s := first_stmt c in
    lazymatch s with Sifthenelse _ _ _ => fail | Scall _ _ _ => fail | _ => forward end
  end.

(* `if (c) t = (bool) c'; else t = 0;` with c and c' true. *)
Ltac if1 :=
  to_branch;
  match goal with |- semax _ _ ?c _ =>
    let s := first_stmt c in
    lazymatch s with
    | Sifthenelse _ _ (Sset ?t (Econst_int (Int.repr 0) tint)) => forward_if (temp t (Vint Int.one))
    end
  end;
  [ solve [ repeat forward; entailer!; cmp_close ] | solve [ else_false ] | ].

(* qp_assert(t) with t = 1. *)
Ltac gp := to_branch; forward_call Int.one.

(* Freeze every SEP item but the oracle's fields named in L (and, when sp is true, the span: a data_at of an
   array of bytes), so that entailer! does not saturate them. *)
Ltac keep_item x L sp :=
  lazymatch x with
  | field_at _ _ (StructField ?f :: nil) _ _ => lazymatch L with context [f] => constr:(true) | _ => constr:(false) end
  | data_at _ (tarray tuchar _) _ _ => constr:(sp)
  | _ => constr:(false)
  end.
Ltac idx_frozen R L sp i :=
  lazymatch R with
  | nil => constr:(@nil Z)
  | ?x :: ?R' =>
      let rest := idx_frozen R' L sp (Z.succ i) in
      let k := keep_item x L sp in
      lazymatch k with true => rest | false => let i' := eval cbn in i in constr:(i' :: rest) end
  end.
Ltac freeze_but L sp F :=
  match goal with |- semax _ (PROPx _ (LOCALx _ (SEPx ?R))) _ _ =>
    let I := idx_frozen R L sp 0 in freeze_tac I F
  end.

Lemma Znth_bytes_val: forall l i, 0 <= i < Zlength l -> Znth i (bytes_val l) = Vint (Int.repr (Znth i l)).
Proof. intros. unfold bytes_val. rewrite Znth_map by auto. reflexivity. Qed.

(* The step export's `last`. *)
Lemma last_val: forall i n, 0 <= i < n -> n <= 65536 ->
  Vlong (Int64.repr (Int.signed (Int.repr (Z.b2z (Int64.cmpu Ceq
    (Int64.add (Int64.repr i) (Int64.repr (Int.signed (Int.repr 1)))) (Int64.repr n)))))) =
  vl (if i + 1 =? n then 1 else 0).
Proof.
  intros i n I N. change (Int.signed (Int.repr 1)) with 1. rewrite add64_repr'. unfold Int64.cmpu.
  rewrite Int64_eq_repr by rep_lia. destruct (i + 1 =? n); reflexivity.
Qed.

(* The prefixes of the step export's test of the transition. *)
Definition acc1 (r: list Z) : bool := (Znth 0 r =? 1) && negb (Znth 1 r =? 2).
Definition acc2 (n i: Z) (r: list Z) : bool := acc1 r && (Znth 1 r =? (if i + 1 =? n then 3 else 1)).
Definition acc3 (n i: Z) (r: list Z) : bool := acc2 n i r && (Znth 2 r =? 0).
Definition acc4 (n i: Z) (r: list Z) : bool := acc3 n i r && (Znth 3 r =? 44 + i + 1).
Lemma accept_acc: forall n i b r, accept_b n i b r = acc4 n i r && (Znth 15 r =? b).
Proof. reflexivity. Qed.

(* The prefixes of the NMI export's test of the policy. *)
Definition pac1 (p: list Z) : bool := (Znth 0 p =? 1) && (Znth 1 p =? 1).
Definition pac2 (p: list Z) : bool := pac1 p && (Znth 2 p =? 0).
Definition pac3 (p: list Z) : bool := pac2 p && (Znth 3 p =? 1).
Lemma pacc_pac: forall p, pacc p = pac3 p && (Znth 4 p =? 4).
Proof. reflexivity. Qed.

Lemma signed_if: forall (b: bool) x y, Int.min_signed <= x <= Int.max_signed -> Int.min_signed <= y <= Int.max_signed ->
  Int.signed (Int.repr (if b then x else y)) = if b then x else y.
Proof. intros [ ] x y Hx Hy; apply Int.signed_repr; auto. Qed.

Lemma repr64_neq: forall a b, Int64.repr a <> Int64.repr b -> a <> b.
Proof. intros a b N E. subst. apply N. reflexivity. Qed.

(* The branch conditions on 64-bit words as facts on Z. *)
Ltac uns64_hyps :=
  repeat match goal with E: context [Int64.unsigned (Int64.repr ?k)] |- _ =>
    rewrite (Int64.unsigned_repr k) in E by rep_lia end.

(* Decide the goal by the comparisons in it and in the facts of the context that mention them. *)
Ltac uns_repr :=
  repeat match goal with |- context [Int.unsigned (Int.repr ?k)] => rewrite (Int.unsigned_repr k) by rep_lia end.
Ltac cmp_atoms :=
  repeat (uns_repr; cbn [andb negb orb Z.b2z proj_sumbool];
          match goal with
          | |- context [Z.eqb ?a ?b] => destruct (Z.eqb_spec a b)
          | |- context [Z.ltb ?a ?b] => destruct (Z.ltb_spec a b)
          | |- context [Z.leb ?a ?b] => destruct (Z.leb_spec a b)
          | |- context [zeq ?a ?b] => destruct (zeq a b)
          | |- context [zlt ?a ?b] => destruct (zlt a b)
          end);
  uns_repr; cbn [andb negb orb Z.b2z proj_sumbool].
Ltac bool_dec :=
  repeat match goal with
  | E: context [Z.eqb _ _] |- _ => revert E
  | E: context [Z.ltb _ _] |- _ => revert E
  | E: context [Z.leb _ _] |- _ => revert E
  | E: context [zeq _ _] |- _ => revert E
  | E: context [zlt _ _] |- _ => revert E
  end;
  uns_repr;
  cmp_atoms;
  rewrite ?Int.unsigned_repr by rep_lia;
  repeat match goal with
  | |- context [Int64.eq (Int64.repr ?a) (Int64.repr ?b)] => rewrite (Int64_eq_repr a b) by rep_lia
  | |- context [Int64.ltu (Int64.repr ?a) (Int64.repr ?b)] => rewrite (Int64_ltu_repr a b) by rep_lia
  end;
  cmp_atoms;
  intros; try discriminate; try (exfalso; lia); try reflexivity.

(* A truth value the C computed, against the model's boolean: the branch conditions as facts on Z, then every
   comparison of the goal and the context decided. *)
Ltac bool_fin :=
  change Int64.zero with (Int64.repr 0) in *; change Int64.one with (Int64.repr 1) in *;
  rewrite ?sub64_repr', ?add64_repr' in *; uns64_hyps;
  repeat match goal with
  | E: Int64.repr _ = Int64.repr _ |- _ => apply repr64_inj in E; [ | rep_lia | rep_lia ]
  | E: Int64.repr _ <> Int64.repr _ |- _ => apply repr64_neq in E
  | E: Int.repr (Z.b2z ?b) <> Int.zero |- _ =>
      assert (b = true) by (destruct b; [ reflexivity | exfalso; apply E; reflexivity ]); clear E
  | E: Int.repr (Z.b2z ?b) = Int.zero |- _ =>
      assert (b = false) by (destruct b; [ exfalso; exact (Int.one_not_zero E) | reflexivity ]); clear E
  | E: context [Int64.eq (Int64.repr ?a) (Int64.repr ?b)] |- _ => rewrite (Int64_eq_repr a b) in E by rep_lia
  | E: context [Int64.ltu (Int64.repr ?a) (Int64.repr ?b)] |- _ => rewrite (Int64_ltu_repr a b) in E by rep_lia
  end;
  unfold bool2val, Int64.cmpu; cbv beta iota;
  unfold acc4, acc3, acc2, acc1, accept_b, pac3, pac2, pac1, pacc in *;
  bool_dec.


Lemma b2z_true: forall b, Int.repr (Z.b2z b) <> Int.zero -> b = true.
Proof. intros [ ] E; [ reflexivity | exfalso; apply E; reflexivity ]. Qed.

Lemma b2z_false: forall b, Int.repr (Z.b2z b) = Int.zero -> b = false.
Proof. intros [ ] E; [ exfalso; exact (Int.one_not_zero E) | reflexivity ]. Qed.

(* The branch hypothesis of `if (t)` with t the truth value of b, as b. *)
Ltac b2z_hyp :=
  match goal with
  | E: Int.repr (Z.b2z _) <> Int.zero |- _ => apply b2z_true in E
  | E: Int.repr (Z.b2z _) = Int.zero |- _ => apply b2z_false in E
  end.

(* The record projections of the oracle's updates. *)
Ltac ost_cbn :=
  cbn [fst snd os_phase os_byte os_word os_state os_answer os_count os_nmi os_policy os_bound os_rejected
       s_answer s_policy s_bound s_accept s_reject s_policy_done s_bound_done].

Lemma repr_neq_e: forall a b, Int.repr a <> Int.repr b -> a <> b.
Proof. intros a b N E. subst. apply N. reflexivity. Qed.

(* The branch conditions of 64-bit arithmetic as facts on Z. *)
Ltac u64c :=
  rewrite ?sub64_repr', ?add64_repr' in *; uns64_hyps;
  repeat match goal with
  | E: Int.repr _ = Int.repr _ |- _ => apply repr_inj_unsigned in E; [ | rep_lia | rep_lia ]
  | E: Int.repr _ <> Int.repr _ |- _ => apply repr_neq_e in E
  | E: Int64.repr _ = Int64.repr _ |- _ => apply repr64_inj in E; [ | rep_lia | rep_lia ]
  | E: Int64.repr _ <> Int64.repr _ |- _ => apply repr64_neq in E
  | E: context [Int64.ltu (Int64.repr ?a) (Int64.repr ?b)] |- _ => rewrite (Int64_ltu_repr a b) in E by rep_lia
  | E: context [Int64.eq (Int64.repr ?a) (Int64.repr ?b)] |- _ => rewrite (Int64_eq_repr a b) in E by rep_lia
  end.
