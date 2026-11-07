(* Law admission_exact: arithmetic of the harness's words, the law's arrays as data_at at their field's address (the
   harness reads state and answer through pointers), and tactics shared by the proofs of its functions. *)
Require Import VST.floyd.proofauto.
Require Import QuickProof.Env.
Require Import LeanosMadtAdmission.harness.admission_exact.code.
Require Import LeanosMadtAdmission.proof.Defs.
Require Import LeanosMadtAdmission.proof.MgaSpecs.
Require Import LeanosMadtAdmission.proof.LawProg LeanosMadtAdmission.proof.LawDefs LeanosMadtAdmission.proof.LawFacts.
Local Open Scope Z_scope.
Local Open Scope bool_scope.
#[local] Existing Instance LawProg.LCS.

Lemma Forall_u64_Znth: forall l i, Forall u64_ok l -> 0 <= i < Zlength l -> 0 <= Znth i l <= Int64.max_unsigned.
Proof. intros l i F I. exact (proj1 (Forall_Znth _ _) F i I). Qed.

Lemma Forall_byte_Znth: forall l i, Forall byte_ok l -> 0 <= i < Zlength l -> 0 <= Znth i l <= Byte.max_unsigned.
Proof. intros l i F I. exact (proj1 (Forall_Znth _ _) F i I). Qed.

Lemma Znth_map_vl: forall l i, 0 <= i < Zlength l -> Znth i (map vl l) = vl (Znth i l).
Proof. intros. rewrite Znth_map by auto. reflexivity. Qed.

Lemma upd_Znth_map_vl: forall l i v, upd_Znth i (map vl l) (vl v) = map vl (upd_Znth i l v).
Proof. intros. rewrite upd_Znth_map. reflexivity. Qed.

Lemma Znth_bytes_val: forall l i, 0 <= i < Zlength l -> Znth i (bytes_val l) = Vint (Int.repr (Znth i l)).
Proof. intros. unfold bytes_val. rewrite Znth_map by auto. reflexivity. Qed.

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

Lemma Int_eq_repr: forall a b, 0 <= a <= Int.max_unsigned -> 0 <= b <= Int.max_unsigned ->
  Int.eq (Int.repr a) (Int.repr b) = (a =? b).
Proof.
  intros a b Ha Hb. unfold Int.eq. rewrite !Int.unsigned_repr by auto.
  destruct (zeq a b); destruct (Z.eqb_spec a b); auto; lia.
Qed.

Lemma Int_ltu_repr: forall a b, 0 <= a <= Int.max_unsigned -> 0 <= b <= Int.max_unsigned ->
  Int.ltu (Int.repr a) (Int.repr b) = (a <? b).
Proof.
  intros a b Ha Hb. unfold Int.ltu. rewrite !Int.unsigned_repr by auto.
  destruct (zlt a b); destruct (Z.ltb_spec a b); auto; lia.
Qed.

Lemma add64_repr': forall a b, Int64.add (Int64.repr a) (Int64.repr b) = Int64.repr (a + b).
Proof.
  intros. unfold Int64.add. apply Int64.eqm_samerepr. apply Int64.eqm_add; apply Int64.eqm_sym, Int64.eqm_unsigned_repr.
Qed.

Lemma add_repr': forall a b, Int.add (Int.repr a) (Int.repr b) = Int.repr (a + b).
Proof.
  intros. unfold Int.add. apply Int.eqm_samerepr. apply Int.eqm_add; apply Int.eqm_sym, Int.eqm_unsigned_repr.
Qed.

Lemma repr64_inj: forall a b, 0 <= a <= Int64.max_unsigned -> 0 <= b <= Int64.max_unsigned ->
  Int64.repr a = Int64.repr b -> a = b.
Proof.
  intros a b Ha Hb E. apply (f_equal Int64.unsigned) in E. rewrite !Int64.unsigned_repr in E by auto. exact E.
Qed.

Lemma repr64_neq: forall a b, Int64.repr a <> Int64.repr b -> a <> b.
Proof. intros a b N E. subst. apply N. reflexivity. Qed.

Lemma repr_neq_e: forall a b, Int.repr a <> Int.repr b -> a <> b.
Proof. intros a b N E. subst. apply N. reflexivity. Qed.

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

(* ---------------------------------------------------------------------- *)
(* The law's arrays as data_at at their field's address                    *)
(* ---------------------------------------------------------------------- *)

Lemma fa_state: forall v q,
  field_at Ews t_law (DOT _state) v q = data_at Ews (tarray tulong 12) v (field_address t_law (DOT _state) q).
Proof. intros. rewrite field_at_data_at. reflexivity. Qed.

Lemma fa_answer: forall v q,
  field_at Ews t_law (DOT _answer) v q = data_at Ews (tarray tulong 16) v (field_address t_law (DOT _answer) q).
Proof. intros. rewrite field_at_data_at. reflexivity. Qed.

Lemma state_at: forall v q, field_compatible t_law (DOT _state) q ->
  field_at Ews t_law (DOT _state) v q = data_at Ews (tarray tulong 12) v (offset_val 128 q).
Proof. intros. rewrite field_at_data_at, field_compatible_field_address by auto. reflexivity. Qed.

Lemma answer_at: forall v q, field_compatible t_law (DOT _answer) q ->
  field_at Ews t_law (DOT _answer) v q = data_at Ews (tarray tulong 16) v (offset_val 224 q).
Proof. intros. rewrite field_at_data_at, field_compatible_field_address by auto. reflexivity. Qed.

(* The value of a temp that the C set to an array field of the law, computed. *)
Ltac fix_offset t :=
  match goal with |- context [temp t (offset_val ?o ?q)] =>
    let o' := eval vm_compute in o in
    let E := fresh "E" in assert (E: o = o') by (vm_compute; reflexivity); rewrite E; clear E end.

(* ---------------------------------------------------------------------- *)
(* Ranges                                                                  *)
(* ---------------------------------------------------------------------- *)

(* The ranges of the elements of an array of 64-bit words, for rep_lia. *)
Ltac rng_list l n :=
  let rec go k :=
    lazymatch eval cbv in (k <? n) with
    | true =>
        assert (0 <= Znth k l <= Int64.max_unsigned) by (apply Forall_u64_Znth; [ assumption | rep_lia ]);
        let k' := eval cbv in (k + 1) in go k'
    | false => idtac
    end in
  go 0.

(* The facts of inputs_ok and lst_ok, named. *)
Ltac inputs_facts H :=
  let L := fresh "Lu" in let Lb := fresh "Lb" in let Fb := fresh "Fb" in let Le := fresh "Le" in
  let La := fresh "La" in let Fa := fresh "Fa" in let Lp := fresh "Lp" in
  destruct H as (L & Lb & Fb & Le & La & Fa & Lp); unfold u32_ok in L, Le, Lp.
Ltac lst_facts H :=
  let A1 := fresh "Sa" in let A2 := fresh "Sa" in let A3 := fresh "Se" in let A4 := fresh "Sv" in
  let A5 := fresh "St" in let A6 := fresh "Sw" in let A7 := fresh "Ss" in let A8 := fresh "Ss" in
  let A9 := fresh "Sn" in let A10 := fresh "Sn" in let A11 := fresh "Si" in
  destruct H as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11);
  unfold u32_ok in A3, A4; unfold u64_ok in A5, A6, A11.

(* ---------------------------------------------------------------------- *)
(* Decisions                                                               *)
(* ---------------------------------------------------------------------- *)

Ltac first_stmt c := lazymatch c with Ssequence ?c1 _ => first_stmt c1 | _ => c end.

(* The branch conditions on 64-bit words as facts on Z. *)
Ltac uns64_hyps :=
  repeat match goal with E: context [Int64.unsigned (Int64.repr ?k)] |- _ =>
    rewrite (Int64.unsigned_repr k) in E by rep_lia end.

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
  | |- context [Int.eq (Int.repr ?a) (Int.repr ?b)] => rewrite (Int_eq_repr a b) by rep_lia
  | |- context [Int.ltu (Int.repr ?a) (Int.repr ?b)] => rewrite (Int_ltu_repr a b) by rep_lia
  end;
  cmp_atoms;
  intros; try discriminate; try (exfalso; lia); try reflexivity.

Ltac uns32_hyps :=
  repeat match goal with E: context [Int.unsigned (Int.repr ?k)] |- _ =>
    rewrite (Int.unsigned_repr k) in E by rep_lia end.

(* The branch conditions of 64- and 32-bit arithmetic as facts on Z. *)
Ltac u64c :=
  change Int64.zero with (Int64.repr 0) in *; change Int64.one with (Int64.repr 1) in *;
  change Int.zero with (Int.repr 0) in *; change Int.one with (Int.repr 1) in *;
  rewrite ?add64_repr', ?add_repr' in *; uns64_hyps; uns32_hyps;
  repeat match goal with E: context [Int.signed (Int.repr ?k)] |- _ =>
    rewrite (Int.signed_repr k) in E by rep_lia end;
  repeat match goal with
  | E: (_ =? _) = true |- _ => apply Z.eqb_eq in E
  | E: (_ =? _) = false |- _ => apply Z.eqb_neq in E
  | E: (_ <? _) = true |- _ => apply Z.ltb_lt in E
  | E: (_ <? _) = false |- _ => apply Z.ltb_ge in E
  | E: Int.repr _ = Int.repr _ |- _ => apply repr_inj_unsigned in E; [ | rep_lia | rep_lia ]
  | E: Int.repr _ <> Int.repr _ |- _ => apply repr_neq_e in E
  | E: Int64.repr _ = Int64.repr _ |- _ => apply repr64_inj in E; [ | rep_lia | rep_lia ]
  | E: Int64.repr _ <> Int64.repr _ |- _ => apply repr64_neq in E
  | E: context [Int64.ltu (Int64.repr ?a) (Int64.repr ?b)] |- _ => rewrite (Int64_ltu_repr a b) in E by rep_lia
  | E: context [Int64.eq (Int64.repr ?a) (Int64.repr ?b)] |- _ => rewrite (Int64_eq_repr a b) in E by rep_lia
  | E: context [Int.ltu (Int.repr ?a) (Int.repr ?b)] |- _ => rewrite (Int_ltu_repr a b) in E by rep_lia
  | E: context [Int.eq (Int.repr ?a) (Int.repr ?b)] |- _ => rewrite (Int_eq_repr a b) in E by rep_lia
  end.

(* A truth value the C computed, against the model's boolean: the branch conditions as facts on Z, then every
   comparison of the goal and the context decided. *)
Ltac bool_fin :=
  u64c;
  repeat match goal with
  | E: Int.repr (Z.b2z ?b) <> Int.repr 0 |- _ =>
      assert (b = true) by (destruct b; [ reflexivity | exfalso; apply E; reflexivity ]); clear E
  | E: Int.repr (Z.b2z ?b) = Int.repr 0 |- _ =>
      assert (b = false) by (destruct b; [ exfalso; exact (Int.one_not_zero E) | reflexivity ]); clear E
  end;
  unfold bool2val, Int64.cmpu, Int.cmpu; cbv beta iota;
  bool_dec.

(* A comparison of words as its truth value. *)
Ltac cmp_close :=
  unfold bool2val, Int64.cmpu, Int.cmpu; cbv beta iota;
  rewrite ?Int.unsigned_repr by rep_lia;
  rewrite ?Int64.eq_true, ?Int.eq_true;
  rewrite ?Int64_ltu_repr, ?Int64_eq_repr, ?Int_ltu_repr, ?Int_eq_repr by rep_lia;
  repeat match goal with
  | |- context [zlt ?a ?b] => destruct (zlt a b); try lia
  | |- context [zeq ?a ?b] => destruct (zeq a b); try lia
  | |- context [?a <? ?b] => destruct (Z.ltb_spec a b); try lia
  | |- context [?a =? ?b] => destruct (Z.eqb_spec a b); try lia
  | |- context [Int64.ltu (Int64.repr ?a) (Int64.repr ?b)] => rewrite (Int64_ltu_repr a b) by rep_lia
  | |- context [Int64.eq (Int64.repr ?a) (Int64.repr ?b)] => rewrite (Int64_eq_repr a b) by rep_lia
  | |- context [Int.eq (Int.repr ?a) (Int.repr ?b)] => rewrite (Int_eq_repr a b) by rep_lia
  end; try reflexivity.

(* The branch of a condition that does not hold. *)
Ltac else_false :=
  exfalso;
  change Int64.zero with (Int64.repr 0) in *; change Int.zero with (Int.repr 0) in *;
  uns32_hyps;
  match goal with
  | E: Int.repr 1 = Int.repr 0 |- _ => exact (Int.one_not_zero E)
  | E: Int.one = Int.repr 0 |- _ => exact (Int.one_not_zero E)
  | _ => solve [ u64c; first [ lia | contradiction ] ]
  | E: Int64.repr _ = Int64.repr _ |- _ => apply repr64_inj in E; [ lia | rep_lia | rep_lia ]
  | E: ?a <> ?a |- _ => apply E; reflexivity
  | E: Int.one = Int.repr 0 |- _ => exact (Int.one_not_zero E)
  | E: Int.repr 1 = Int.repr 0 |- _ => exact (Int.one_not_zero E)
  | E: Int64.repr _ <> Int64.repr _ |- _ => apply E; f_equal; lia
  | E: Int.repr _ <> Int.repr _ |- _ => apply E; f_equal; lia
  | E: Int.repr _ = Int.repr _ |- _ => apply repr_inj_unsigned in E; [ lia | rep_lia | rep_lia ]
  | E: _ <> Int64.add _ _ |- _ => apply E; unfold Int64.add; rewrite !Int64.unsigned_repr by rep_lia; f_equal; lia
  | E: Int64.ltu _ _ = false |- _ => rewrite Int64_ltu_repr in E by rep_lia; apply Z.ltb_ge in E; lia
  | E: Int64.ltu _ _ = true |- _ => rewrite Int64_ltu_repr in E by rep_lia; apply Z.ltb_lt in E; lia
  | E: context [Int64.unsigned (Int64.repr _)] |- _ => rewrite !Int64.unsigned_repr in E by rep_lia; lia
  | E: context [Int.unsigned (Int.repr _)] |- _ => rewrite !Int.unsigned_repr in E by rep_lia; lia
  | _ => lia
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

(* Freeze every SEP item but the law's fields named in L (and, when sp is true, the copy: a data_at of an array of
   bytes), so that entailer! does not saturate them. *)
Ltac keep_item x L sp :=
  lazymatch x with
  | field_at _ _ (StructField ?f :: nil) _ _ => lazymatch L with context [f] => constr:(true) | _ => constr:(false) end
  | data_at _ (tarray tuchar _) _ _ => constr:(sp)
  | data_at _ (tarray tulong _) _ _ => constr:(true)
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

(* ---------------------------------------------------------------------- *)
(* Folding the law's fields                                                *)
(* ---------------------------------------------------------------------- *)

Lemma lfields_fold: forall q p x a e v t w st an id,
  (field_at Ews t_law (DOT _call) (vi (call_code (i_call x))) q *
   field_at Ews t_law (DOT _length) (vi (i_length x)) q *
   field_at Ews t_law (DOT _executing) (vi (i_executing x)) q *
   field_at Ews t_law (DOT _copy) p q *
   field_at Ews t_law (DOT _args) (map vl a) q *
   field_at Ews t_law (DOT _expect) (vi e) q *
   field_at Ews t_law (DOT _verdict) (vi v) q *
   field_at Ews t_law (DOT _at) (vl t) q *
   field_at Ews t_law (DOT _word) (vl w) q *
   field_at Ews t_law (DOT _state) (map vl st) q *
   field_at Ews t_law (DOT _answer) (map vl an) q *
   field_at Ews t_law (DOT _id) (vl id) q)%logic |-- lfields q p x (mk_lst a e v t w st an id).
Proof. intros. unfold lfields; simpl. cancel. Qed.

Lemma lfields_fold_s: forall q p x s,
  (field_at Ews t_law (DOT _call) (vi (call_code (i_call x))) q *
   field_at Ews t_law (DOT _length) (vi (i_length x)) q *
   field_at Ews t_law (DOT _executing) (vi (i_executing x)) q *
   field_at Ews t_law (DOT _copy) p q *
   field_at Ews t_law (DOT _args) (map vl (ls_args s)) q *
   field_at Ews t_law (DOT _expect) (vi (ls_expect s)) q *
   field_at Ews t_law (DOT _verdict) (vi (ls_verdict s)) q *
   field_at Ews t_law (DOT _at) (vl (ls_at s)) q *
   field_at Ews t_law (DOT _word) (vl (ls_word s)) q *
   field_at Ews t_law (DOT _state) (map vl (ls_state s)) q *
   field_at Ews t_law (DOT _answer) (map vl (ls_answer s)) q *
   field_at Ews t_law (DOT _id) (vl (ls_id s)) q)%logic |-- lfields q p x s.
Proof. intros. unfold lfields. cancel. Qed.

Lemma call_code_range: forall f, 0 <= call_code f <= 3.
Proof. intros [ ]; simpl; lia. Qed.

Lemma call_code_0: forall f, call_code f = 0 -> f = FEnvelope.
Proof. intros [ ]; simpl; intros; congruence || lia. Qed.

Lemma call_code_1: forall f, call_code f = 1 -> f = FEntries.
Proof. intros [ ]; simpl; intros; congruence || lia. Qed.

Lemma call_code_2: forall f, call_code f = 2 -> f = FResult.
Proof. intros [ ]; simpl; intros; congruence || lia. Qed.

(* stop(m, r) in a helper on the record s, then return (stop_ret) or the end of the function (stop_end): the record
   s_stop s r, which Jp needs to be the progress Return (r, None). *)
Ltac stop_post s r :=
  Exists (s_stop s r); unfold lfields, s_stop; lst_cbn; entailer!;
  (split; [ apply lst_ok_stop; auto; unfold u32_ok, r; rep_lia | ]).
Ltac stop_ret q s r := forward_call (q, vi (ls_expect s), vi (ls_verdict s), r); forward; stop_post s r.
Ltac stop_end q s r := forward_call (q, vi (ls_expect s), vi (ls_verdict s), r); stop_post s r.

(* The envelope export's `last` (and the entry export's): 1 at the last byte, 0 before. *)
Lemma last_val: forall x i, 0 <= i < i_length x -> i_length x <= Int.max_unsigned ->
  Vlong (Int64.repr (Int.signed (Int.repr (Z.b2z (Int64.cmpu Ceq
    (Int64.add (Int64.repr i) (Int64.repr (Int.signed (Int.repr 1)))) (Int64.repr (Int.unsigned (Int.repr (i_length x))))))))) =
  vl (terminal x i).
Proof.
  intros x i I N. change (Int.signed (Int.repr 1)) with 1. rewrite add64_repr', Int.unsigned_repr by rep_lia.
  unfold Int64.cmpu. rewrite Int64_eq_repr by rep_lia. unfold terminal. destruct (i + 1 =? i_length x); reflexivity.
Qed.

(* An export's rejection: stop(m, r), then the law's oracle at the record with the verdict r, the answers a and the
   progress Return (r, None) the model's step leads to (EL, with the check `chk` of the transition). *)
Ltac rej_close chk r :=
  split; [ unfold lst_ok; lst_cbn; split_and; auto; unfold u32_ok, E_NOTHING, r; rep_lia | ];
  apply J_snoc_intro; [ assumption | ];
  match goal with EL: step _ _ _ = _ |- _ => rewrite EL end;
  replace (chk) with r
    by (unfold envelope_check, entries_check, result_check; try change (2 ^ 32) with 4294967296; bool_dec);
  unfold Jp, result_end, ret_inv; simpl; auto.

(* Enter a tail lemma: VST's canonical form of the goal, as start_function leaves it. *)
Ltac start_tail :=
  repeat match goal with
  | |- context [Sloop (Ssequence (Sifthenelse ?e Sskip Sbreak) ?s) Sskip] => fold (Swhile e s)
  | |- context [Ssequence ?s1 (Sloop (Ssequence (Sifthenelse ?e Sskip Sbreak) ?s2) ?s3) ] =>
      match s3 with
      | Sset ?i _ => match s1 with Sset ?i' _ => unify i i' | Sskip => idtac end
      end;
      fold (Sfor s1 e s2 s3)
  end;
  simplify_func_tycontext;
  abbreviate_semax.
