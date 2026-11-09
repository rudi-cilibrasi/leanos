(* Law handoff_decode_exact: arithmetic of the harness's words, the law's arrays as data_at at their field's address
   (the harness reads the states and the answers through pointers), the law's oracle re-established after an
   answer, and tactics shared by the proofs of its functions. *)
Require Import VST.floyd.proofauto.
Require Import QuickProof.Env.
Require Import LeanosHandoff.harness.handoff_decode_exact.code.
Require Import LeanosHandoff.proof.Defs.
Require Import LeanosHandoff.proof.HandoffSpecs.
Require Import LeanosHandoff.proof.LawProg LeanosHandoff.proof.LawDefs LeanosHandoff.proof.LawFacts.
Local Open Scope Z_scope.
Local Open Scope bool_scope.
#[export] Existing Instance LawProg.LCS.

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

Lemma sub64_repr': forall a b, Int64.sub (Int64.repr a) (Int64.repr b) = Int64.repr (a - b).
Proof.
  intros. unfold Int64.sub. apply Int64.eqm_samerepr. apply Int64.eqm_sub; apply Int64.eqm_sym, Int64.eqm_unsigned_repr.
Qed.

Lemma mul64_repr': forall a b, Int64.mul (Int64.repr a) (Int64.repr b) = Int64.repr (a * b).
Proof.
  intros. unfold Int64.mul. apply Int64.eqm_samerepr. apply Int64.eqm_mult; apply Int64.eqm_sym, Int64.eqm_unsigned_repr.
Qed.

Lemma add_repr': forall a b, Int.add (Int.repr a) (Int.repr b) = Int.repr (a + b).
Proof.
  intros. unfold Int.add. apply Int.eqm_samerepr. apply Int.eqm_add; apply Int.eqm_sym, Int.eqm_unsigned_repr.
Qed.

Lemma sub_repr': forall a b, Int.sub (Int.repr a) (Int.repr b) = Int.repr (a - b).
Proof.
  intros. unfold Int.sub. apply Int.eqm_samerepr. apply Int.eqm_sub; apply Int.eqm_sym, Int.eqm_unsigned_repr.
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

Ltac b2z_hyp :=
  match goal with
  | E: Int.repr (Z.b2z _) <> Int.zero |- _ => apply b2z_true in E
  | E: Int.repr (Z.b2z _) = Int.zero |- _ => apply b2z_false in E
  | E: Int.repr (Z.b2z _) <> Int.repr 0 |- _ => apply b2z_true in E
  | E: Int.repr (Z.b2z _) = Int.repr 0 |- _ => apply b2z_false in E
  end.

(* The u32 and u64 values of the law. *)
Lemma vi_u32_long: forall a, 0 <= a <= Int.max_unsigned ->
  Vlong (Int64.repr (Int.unsigned (Int.repr a))) = vl a.
Proof. intros. rewrite Int.unsigned_repr by auto. reflexivity. Qed.

(* ---------------------------------------------------------------------- *)
(* The law's arrays as data_at at their field's address                    *)
(* ---------------------------------------------------------------------- *)

Definition OFS_STATES : Z := 1584.
Definition OFS_ANSWER : Z := 2352.

Lemma ofs_states: forall q, field_compatible t_law (DOT _states_expect) q ->
  field_address t_law (DOT _states_expect) q = offset_val OFS_STATES q.
Proof. intros. rewrite field_compatible_field_address by auto. reflexivity. Qed.

Lemma answer_at: forall v q, field_compatible t_law (DOT _answer) q ->
  field_at Ews t_law (DOT _answer) v q = data_at Ews (tarray tulong WORDS) v (offset_val OFS_ANSWER q).
Proof. intros. rewrite field_at_data_at, field_compatible_field_address by auto. reflexivity. Qed.

(* The two states, as two rows. *)
Definition row (q: val) (i: Z) : val := offset_val (OFS_STATES + 328 * i) q.

Lemma states_rows: forall q r0 r1, field_compatible t_law (DOT _states_expect) q ->
  Zlength r0 = WORDS -> Zlength r1 = WORDS ->
  field_at Ews t_law (DOT _states_expect) [map vl r0; map vl r1] q =
  (data_at Ews t_state (map vl r0) (row q 0) * data_at Ews t_state (map vl r1) (row q 1))%logic.
Proof.
  intros q r0 r1 FC L0 L1.
  rewrite field_at_data_at, ofs_states by auto.
  pose proof (field_compatible_nested_field _ _ _ FC) as FCa.
  change (nested_field_offset t_law (DOT _states_expect)) with OFS_STATES in FCa.
  change (nested_field_type t_law (DOT _states_expect)) with (tarray t_state 2) in FCa |- *.
  change [map vl r0; map vl r1] with ([map vl r0] ++ [map vl r1]).
  rewrite (split2_data_at_Tarray_app 1 2) by (rewrite ?Zlength_cons, ?Zlength_nil; reflexivity).
  rewrite field_address0_offset by auto with field_compatible.
  rewrite (data_at_singleton_array_eq Ews t_state (map vl r0)) by reflexivity.
  replace (2 - 1) with 1 by lia.
  rewrite (data_at_singleton_array_eq Ews t_state (map vl r1)) by reflexivity.
  unfold row. rewrite offset_offset_val. f_equal.
Qed.

Lemma states_val_rows: forall ss, Zlength ss = 2 -> states_val ss = [map vl (Znth 0 ss); map vl (Znth 1 ss)].
Proof.
  intros ss L. destruct ss as [ | r0 [ | r1 [ | r2 ss]]]; try (rewrite ?Zlength_cons, ?Zlength_nil in L; rep_lia).
  reflexivity.
Qed.

Lemma states_split: forall q ss, field_compatible t_law (DOT _states_expect) q ->
  Zlength ss = 2 -> state_ok (Znth 0 ss) -> state_ok (Znth 1 ss) ->
  field_at Ews t_law (DOT _states_expect) (states_val ss) q =
  (data_at Ews t_state (map vl (Znth 0 ss)) (row q 0) * data_at Ews t_state (map vl (Znth 1 ss)) (row q 1))%logic.
Proof.
  intros q ss FC L (L0 & _) (L1 & _). rewrite states_val_rows by auto. apply states_rows; auto.
Qed.

(* The current state's row and the other one. *)
Lemma rows_at: forall q ss i, (i = 0 \/ i = 1) ->
  (data_at Ews t_state (map vl (Znth 0 ss)) (row q 0) * data_at Ews t_state (map vl (Znth 1 ss)) (row q 1))%logic =
  (data_at Ews t_state (map vl (Znth i ss)) (row q i) *
   data_at Ews t_state (map vl (Znth (1 - i) ss)) (row q (1 - i)))%logic.
Proof. intros q ss i [-> | ->]; [ reflexivity | apply sepcon_comm ]. Qed.

(* ---------------------------------------------------------------------- *)
(* The oracle                                                              *)
(* The two rows folded back into the field. *)
Lemma rows_fold: forall q ss i, field_compatible t_law (DOT _states_expect) q ->
  Zlength ss = 2 -> state_ok (Znth 0 ss) -> state_ok (Znth 1 ss) -> (i = 0 \/ i = 1) ->
  (data_at Ews t_state (map vl (Znth i ss)) (row q i) *
   data_at Ews t_state (map vl (Znth (1 - i) ss)) (row q (1 - i)))%logic
  |-- field_at Ews t_law (DOT _states_expect) (states_val ss) q.
Proof.
  intros q ss i FC L R0 R1 I. rewrite <- (rows_at q ss i I). rewrite states_split by auto. apply derives_refl.
Qed.

(* The pointer `m->states_expect[i]` the harness computes. *)
Lemma row_addr: forall q i, isptr q -> 0 <= i <= 1 ->
  force_val (sem_binary_operation' Oadd (tarray (tarray tulong 41) 2) tuint
    (eval_field (Tstruct _law__1 noattr) _states_expect q) (vi i)) = row q i.
Proof.
  intros q i P I. destruct q; try contradiction.
  unfold row, vi. simpl. f_equal. rewrite Ptrofs.add_assoc. f_equal.
  unfold Ptrofs.of_intu, Ptrofs.of_int. rewrite Int.unsigned_repr by rep_lia.
  rewrite ptrofs_mul_repr, ptrofs_add_repr. reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)

(* The oracle after the answer v to the call of stage g, the model and the record then being p and s. *)
Lemma ora_close: forall gv x h g m v p s ce ie,
  inputs_ok x -> x_fit x -> run x (start x) h = Some (Go g m) -> step x g m v = p -> J x p s ->
  ptr_ok x ce ie ->
  (lfields (gv _law) x ce ie (mem_of p) s * arrays x ce ie (mem_of p))%logic
  |-- Ora_law gv (gv _law) (gv _law) x (h ++ [(expected x g m, v)]).
Proof.
  intros gv x h g m v p s ce ie Ix Xf R E HJ Pie. unfold Ora_law. Exists p s ce ie.
  rewrite (run_snoc' x h g m _ v R eq_refl). rewrite E. entailer!.
Qed.

(* ---------------------------------------------------------------------- *)
(* Ranges                                                                  *)
(* ---------------------------------------------------------------------- *)

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
(* Decisions                                                               *)
(* ---------------------------------------------------------------------- *)

Ltac first_stmt c := lazymatch c with Ssequence ?c1 _ => first_stmt c1 | _ => c end.

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
  rewrite ?add64_repr', ?add_repr', ?mul64_repr' in *; uns64_hyps; uns32_hyps;
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

(* Freeze every SEP item but the law's fields named in L and the data_at whose addresses are in A. *)
Ltac keep_item x L A :=
  lazymatch x with
  | field_at _ _ (StructField ?f :: nil) _ _ => lazymatch L with context [f] => constr:(true) | _ => constr:(false) end
  | data_at _ _ _ ?p => lazymatch A with context [p] => constr:(true) | _ => constr:(false) end
  | data_at_ _ _ ?p => lazymatch A with context [p] => constr:(true) | _ => constr:(false) end
  | _ => constr:(false)
  end.
Ltac idx_frozen R L A i :=
  lazymatch R with
  | nil => constr:(@nil Z)
  | ?x :: ?R' =>
      let rest := idx_frozen R' L A (Z.succ i) in
      let k := keep_item x L A in
      lazymatch k with true => rest | false => let i' := eval cbn in i in constr:(i' :: rest) end
  end.
Ltac freeze_but L A F :=
  match goal with |- semax _ (PROPx _ (LOCALx _ (SEPx ?R))) _ _ =>
    let I := idx_frozen R L A 0 in freeze_tac I F
  end.

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

(* The facts of the invariants, named. *)
Ltac lst_facts H :=
  let L := fresh "L" in pose proof H as L; unfold lst_ok in L;
  destruct L as (?Lr & ?Lrc & ?Le & ?Lv & ?Lc & ?Lw & ?Lb & ?Lva & ?Lsl & ?Lsf & ?Lal & ?Laf);
  unfold u32_ok, u64_ok in *.
Ltac mem_facts H :=
  let F := fresh "F" in pose proof H as F; unfold mem_fit in F;
  destruct F as (?Ft & ?Fcl & ?Fcf & ?Ful & ?Fuf & ?Fbl & ?Fbf & ?Frl & ?Frf & ?Fsl & ?Fs0 & ?Fs1 & ?Fat);
  unfold u32_ok in *.
Ltac inputs_facts H :=
  let I := fresh "I" in pose proof H as I; unfold inputs_ok in I;
  destruct I as (?Im & ?Ia & ?It & ?Ic & ?Iu & ?Ib & ?Ir & ?Isl & ?Isf & ?Itr & ?Ilr & ?Icr);
  unfold u32_ok, u64_ok in *.

(* The law's fields, folded. *)
Lemma lfields_fold: forall q x ce ie m s,
 (field_at Ews t_law (DOT _call) (vi (call_code (i_call x))) q *
  field_at Ews t_law (DOT _magic) (vi (i_magic x)) q *
  field_at Ews t_law (DOT _address) (vi (i_address x)) q *
  field_at Ews t_law (DOT _total) (vi (m_total m)) q *
  field_at Ews t_law (DOT _candidate) (vl (target x)) q *
  field_at Ews t_law (DOT _projection) (vi (proj_code x)) q *
  field_at Ews t_law (DOT _running) (vi (w_running s)) q *
  field_at Ews t_law (DOT _copy_expect) ce q *
  field_at Ews t_law (DOT _info_expect) ie q *
  field_at Ews t_law (DOT _usable_expect) (map vl (m_usable m)) q *
  field_at Ews t_law (DOT _blocked_expect) (map vl (m_blocked m)) q *
  field_at Ews t_law (DOT _reserved_expect) (map vl (m_reserved m)) q *
  field_at Ews t_law (DOT _states_expect) (states_val (m_states m)) q *
  field_at Ews t_law (DOT _at) (vi (m_at m)) q *
  field_at Ews t_law (DOT _extent_ok) (vi (Z.b2z (m_extent_ok m))) q *
  field_at Ews t_law (DOT _records) (vi (w_records s)) q *
  field_at Ews t_law (DOT _expect) (vi (w_expect s)) q *
  field_at Ews t_law (DOT _verdict) (vi (w_verdict s)) q *
  field_at Ews t_law (DOT _chunk) (vl (w_chunk s)) q *
  field_at Ews t_law (DOT _word) (vl (w_word s)) q *
  field_at Ews t_law (DOT _block) (vl (w_block s)) q *
  field_at Ews t_law (DOT _value) (vl (w_value s)) q *
  field_at Ews t_law (DOT _stream) (map vl (w_stream s)) q *
  field_at Ews t_law (DOT _answer) (map vl (w_answer s)) q)%logic |-- lfields q x ce ie m s.
Proof. intros. unfold lfields. apply derives_refl. Qed.

Lemma target_range: forall x, inputs_ok x -> 0 <= target x <= Int64.max_unsigned.
Proof.
  intros x (_ & _ & _ & C & _). unfold target. destruct (i_call x); auto; rep_lia.
Qed.

Lemma proj_code_range: forall x, 0 <= proj_code x <= 1.
Proof. intros. unfold proj_code. destruct (projection x); lia. Qed.
