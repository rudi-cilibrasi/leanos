(* Law handoff_decode_exact: what the parts of the proof of main share: main's context and return assertion, the
   statements from each cut point of main's body (then main's final return), the function main calls (call_of),
   the results of malloc, the arguments' types between the unit's compspecs and the law's. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env QuickProof.Assembly.
Require Import LeanosHandoff.harness.handoff_decode_exact.code.
Require Import LeanosHandoff.proof.Defs.
Require Import LeanosHandoff.proof.HandoffSpecs.
Require Import LeanosHandoff.proof.LawProg LeanosHandoff.proof.LawDefs LeanosHandoff.proof.LawFacts
  LeanosHandoff.proof.LawLib LeanosHandoff.proof.LawZero.
Local Open Scope Z_scope.
Local Open Scope bool_scope.
#[export] Existing Instance LawProg.LCS.

(* VST's simplification of LOCAL after a call, with the identifiers' comparisons computed by cbv: the lazy/simpl
   version of VST takes minutes on main's LOCAL here. *)
Ltac rlt_vm u :=
  lazymatch u with
  | context C [rlt_ident_eq ?a ?b] =>
      let r := eval vm_compute in (rlt_ident_eq a b) in
      let u' := context C [r] in rlt_vm u'
  | _ => u
  end.

Ltac simplify_remove_localdef_temp ::=
  match goal with |- context [remove_localdef_temp ?i ?L] =>
    let u := constr:(remove_localdef_temp i L) in
    let u' := eval lazy delta [remove_localdef_temp] beta iota in u in
    let u' := rlt_vm u' in
    let u' := eval lazy beta iota in u' in
    let u' := eval lazy zeta in u' in
    change u with u'
  end.

Definition read_fs : ident * funspec := (_bootloader_read, read_spec Ora_law).
Definition record_fs : ident * funspec := (_projection_record, record_spec Ora_law).

Definition Gmain : funspecs :=
  [any_u64_spec; stop_spec; begin_stream_spec; begin_decode_spec; read_fs; record_fs;
   extent_spec Ora_law; project_spec Ora_law; copy_spec Ora_law; projection_spec Ora_law; candidate_spec Ora_law;
   nondet_u32_spec; gp_assert_spec; (_quickproof_malloc, malloc_spec')].

(* main's type context and return assertion, as start_function makes them. *)
Definition Delta0 : tycontext := func_tycontext f_main Vlaw Gmain nil.
Definition Post0 : ret_assert :=
  frame_ret_assert (function_body_ret_assert tint (EX r : int, PROP () RETURN (Vint r) SEP (TT))%argsassert)
    (stackframe_of f_main).

(* The statements of main from the first statement of the inner block matched by `first` (then the rest of the
   block), then main's final return. *)
Ltac main_from first :=
  let b := eval cbv delta [f_main] beta iota zeta in (fn_body f_main) in
  match b with
  | context [Ssequence (Ssequence ?s1 ?s2) ?rest] =>
      first s1;
      exact (Ssequence (Ssequence (Ssequence s1 s2) rest) (Sreturn (Some (Econst_int (Int.repr 0) tint))))
  end.

(* From the loop filling the copy (`for (i = 0; i < copy_words; ++i) ...`). *)
Definition s_fill : statement :=
  ltac:(main_from ltac:(fun s => match s with Sset _i (Econst_int (Int.repr 0) tint) => idtac end)).

(* From the three records (`total_record = nondet_u32(), ...`). *)
Definition s_rest : statement :=
  ltac:(main_from ltac:(fun s => match s with Scall (Some _t'32) _ _ => idtac end)).

(* From `m->running = 1` on. *)
Definition s_call : statement := ltac:(
  let b := eval cbv delta [f_main] beta iota zeta in (fn_body f_main) in
  match b with
  | context [Ssequence (Sassign (Efield ?e _running tuint) ?v) ?rest] =>
      exact (Ssequence (Ssequence (Sassign (Efield e _running tuint) v) rest)
                       (Sreturn (Some (Econst_int (Int.repr 0) tint))))
  end).

(* From main's checks (`qp_assert(m->expect == EXPECT_NOTHING); ...`). *)
Definition s_check : statement :=
  ltac:(main_from ltac:(fun s => match s with Sset _t'70 _ => idtac end)).

(* main's call: nondet_u32 % 4, and the function it names. *)
Definition call_of (c: Z) : func :=
  if c =? 0 then FAllocate else if c =? 1 then FCopy else if c =? 2 then FProjection else FCandidate.

Lemma call_code_of: forall c, 0 <= c <= 3 -> call_code (call_of c) = c.
Proof.
  intros c H. unfold call_of.
  destruct (Z.eqb_spec c 0); [ subst; reflexivity | ].
  destruct (Z.eqb_spec c 1); [ subst; reflexivity | ].
  destruct (Z.eqb_spec c 2); [ subst; reflexivity | ].
  simpl. lia.
Qed.

(* A pointer malloc returned. *)
Definition mres (t: type) (p: val) : mpred :=
  if eq_dec p nullval then emp else (malloc_token Ews t p * data_at_ Ews t p)%logic.

Definition isnul (p: val) : bool := if eq_dec p nullval then true else false.

Lemma mres_ptr: forall t p, isnul p = false -> mres t p = (malloc_token Ews t p * data_at_ Ews t p)%logic.
Proof. intros t p E. unfold mres, isnul in *. destruct (eq_dec p nullval); [ discriminate | reflexivity ]. Qed.

Lemma isnul_false: forall p, p <> nullval -> isnul p = false.
Proof. intros. unfold isnul. destruct (eq_dec p nullval); [ contradiction | reflexivity ]. Qed.

Lemma mres_tc: forall t p (P: mpred), (mres t p * P)%logic |-- denote_tc_test_eq p (Vlong (Int64.repr 0)).
Proof.
  intros t p P. unfold mres. destruct (eq_dec p nullval) as [E | N].
  - subst. apply denote_tc_test_eq_split; apply valid_pointer_zero64; reflexivity.
  - apply denote_tc_test_eq_split; [ | apply valid_pointer_zero64; reflexivity ].
    rewrite sepcon_assoc.
    destruct (Z_le_gt_dec (sizeof t) 0) as [Z | Z].
    + apply sepcon_valid_pointer1. apply malloc_token_valid_pointer; auto.
    + apply sepcon_valid_pointer2. apply sepcon_valid_pointer1.
      apply data_at__valid_ptr; [ apply readable_nonidentity, writable_readable, writable_Ews | lia ].
Qed.

Lemma mres_tc': forall t p (P Q: mpred), P |-- (mres t p * Q)%logic -> P |-- denote_tc_test_eq p (Vlong (Int64.repr 0)).
Proof. intros. eapply derives_trans; [ exact H | apply mres_tc ]. Qed.

Lemma null_test: forall p, is_pointer_or_null p ->
  force_val (sem_cast_i2bool (force_val (sem_cmp_pp Ceq p (Vlong (Int64.repr 0))))) = Vint (Int.repr (Z.b2z (isnul p))).
Proof.
  intros p P. unfold isnul. destruct (eq_dec p nullval) as [E | N].
  - subst. vm_compute. reflexivity.
  - destruct p; try contradiction; simpl in *.
    + subst. exfalso. apply N. reflexivity.
    + vm_compute. reflexivity.
Qed.

Ltac rw_bools :=
  repeat match goal with
  | E: ?b = true |- context [?b] => match type of b with bool => rewrite E end
  | E: ?b = false |- context [?b] => match type of b with bool => rewrite E end
  end.

(* The arguments' types do not depend on the compspecs. *)
Lemma data_at_tuint_cs: forall sh v p, @data_at LCS sh tuint v p = @data_at HandoffSpecs.CS sh tuint v p.
Proof.
  intros. apply equal_f. symmetry.
  apply (@data_at_change_composite HandoffSpecs.CS LCS LCR); [ apply JMeq_refl | reflexivity ].
Qed.

Lemma data_at_words_cs: forall sh n v p,
  @data_at LCS sh (tarray tulong n) v p = @data_at HandoffSpecs.CS sh (tarray tulong n) v p.
Proof.
  intros. apply equal_f. symmetry.
  apply (@data_at_change_composite HandoffSpecs.CS LCS LCR); [ apply JMeq_refl | reflexivity ].
Qed.

Lemma data_at_states_cs: forall sh v p, @data_at LCS sh t_states v p = @data_at HandoffSpecs.CS sh t_states v p.
Proof.
  intros. apply equal_f. symmetry.
  apply (@data_at_change_composite HandoffSpecs.CS LCS LCR); [ apply JMeq_refl | reflexivity ].
Qed.

Lemma data_at_projection_cs: forall sh (v: val * (val * (val * (val * val)))) p,
  @data_at LCS sh t_projection v p = @data_at HandoffSpecs.CS sh t_projection v p.
Proof.
  intros. apply equal_f. symmetry.
  apply (@data_at_change_composite HandoffSpecs.CS LCS LCR); [ apply JMeq_refl | reflexivity ].
Qed.

(* Enter a tail lemma: VST's canonical form of the goal, as start_function leaves it. *)
Ltac start_tail_main :=
  unfold Delta0, Post0;
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
