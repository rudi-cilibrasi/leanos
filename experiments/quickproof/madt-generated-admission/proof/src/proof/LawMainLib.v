(* Law admission_exact: what main's proof needs besides the harness's functions: main's context and return
   assertion, the function main calls (call_of), the arguments' types between the unit's compspecs and the law's,
   and the law's oracle before the call (J at no answers, for each function). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env QuickProof.Assembly.
Require Import LeanosMadtAdmission.harness.admission_exact.code.
Require Import LeanosMadtAdmission.proof.Defs.
Require Import LeanosMadtAdmission.proof.MgaSpecs.
Require Import LeanosMadtAdmission.proof.LawProg LeanosMadtAdmission.proof.LawDefs LeanosMadtAdmission.proof.LawFacts
  LeanosMadtAdmission.proof.LawLib.
Local Open Scope Z_scope.
Local Open Scope bool_scope.
#[export] Existing Instance LawProg.LCS.

Definition Gmain : funspecs :=
  [any_u64_spec; begin_entries_spec; envelope_done_spec;
   envelope_spec Ora_law; entries_spec Ora_law; result_spec Ora_law; admission_spec Ora_law;
   nondet_u8_spec; nondet_u32_spec; nondet_bytes_spec; gp_assert_spec; (_quickproof_malloc, malloc_spec')].

(* main's type context and return assertion, as start_function makes them. *)
Definition Delta0 : tycontext := func_tycontext f_main Vlaw Gmain nil.
Definition Post0 : ret_assert :=
  frame_ret_assert (function_body_ret_assert tint (EX r : int, PROP () RETURN (Vint r) SEP (TT))%argsassert)
    (stackframe_of f_main).

(* The statements of main from the first statement of the inner block matched by `first` (then the rest of the
   block), then main's final return: the parts of main the tail lemmas prove. *)
Ltac main_from first :=
  let b := eval cbv delta [f_main] beta iota zeta in (fn_body f_main) in
  match b with
  | context [Ssequence (Ssequence ?s1 ?s2) ?rest] =>
      first s1;
      exact (Ssequence (Ssequence (Ssequence s1 s2) rest) (Sreturn (Some (Econst_int (Int.repr 0) tint))))
  end.

(* From the loop storing the result's arguments (`for (k = 0; k < 10; ++k) m->args[k] = any_u64();`). *)
Definition s_setup : statement :=
  ltac:(main_from ltac:(fun s => match s with Sset _k (Econst_int (Int.repr 0) tint) => idtac end)).

(* From the dispatch on the function (`if (m->call == CALL_ENVELOPE) status = madt_envelope(...); ...`). *)
Definition s_disp : statement :=
  ltac:(main_from ltac:(fun s => match s with Sset _t'26 _ => idtac end)).

(* From main's checks (`qp_assert(m->expect == EXPECT_NOTHING && status == m->verdict); ...`). *)
Definition s_check : statement :=
  ltac:(main_from ltac:(fun s => match s with Ssequence (Sset _t'24 _) _ => idtac end)).

(* The APIC ID record after the function returned st, writing w: the APIC ID on OK but for the envelope, else the
   prior value (main's last check). *)
Definition rec_ok (x: inputs) (st: Z) (w: option Z) (rec: Z) : Prop :=
  if (st =? S_OK) && negb (call_code (i_call x) =? 0) then w = Some rec else rec = i_prior x.

(* main's call: nondet_u8 capped at CALL_ADMISSION, and the function it names. *)
Definition cc (c: Z) : Z := if c <? 3 then c else 3.
Definition call_of (c: Z) : func :=
  if c =? 0 then FEnvelope else if c =? 1 then FEntries else if c =? 2 then FResult else FAdmission.

Lemma call_code_of: forall c, 0 <= c -> call_code (call_of (cc c)) = cc c.
Proof.
  intros c H. unfold cc, call_of.
  destruct (Z.ltb_spec c 3); [ | reflexivity ].
  destruct (Z.eqb_spec c 0); [ subst; reflexivity | ].
  destruct (Z.eqb_spec c 1); [ subst; reflexivity | ].
  destruct (Z.eqb_spec c 2); [ subst; reflexivity | lia ].
Qed.

Lemma cc_range: forall c, 0 <= c -> 0 <= cc c <= 3.
Proof. intros c H. unfold cc. destruct (Z.ltb_spec c 3); lia. Qed.

(* The arguments' types do not depend on the compspecs. *)
Lemma data_at_tuint_cs: forall (cs1 cs2: compspecs) sh v p, @data_at cs1 sh tuint v p = @data_at cs2 sh tuint v p.
Proof.
  intros. apply (f_equal (fun f => f p)).
  apply (@data_at_change_composite cs1 cs2 (CCE_any cs1 cs2)); [ apply JMeq_refl | reflexivity ].
Qed.

(* The law's oracle before the call. *)
Lemma ora_intro: forall gv x cp s, inputs_ok x -> lst_ok s -> J x nil s ->
  (lfields (gv _law) cp x s * data_at Ews (tarray tuchar (i_length x)) (bytes_val (i_bytes x)) cp)%logic
  |-- Ora_law gv x nil.
Proof. intros. unfold Ora_law. Exists cp s. entailer!. Qed.

Lemma J_start_result: forall x s, i_call x = FResult -> ls_expect s = E_RESULT -> ls_word s = 0 ->
  ls_args s = i_args x -> J x nil s.
Proof.
  intros x s C E W A. rewrite J_nil. unfold start. rewrite C. unfold Jp, go_inv. rewrite W, sublist_nil.
  split_and; auto; lia.
Qed.

Lemma J_start_entries: forall x s, i_call x = FEntries -> Jp x (begin_entries x) s -> J x nil s.
Proof. intros x s C K. rewrite J_nil. unfold start. rewrite C. exact K. Qed.

Lemma J_start_env0: forall x s, i_call x <> FEntries -> i_call x <> FResult -> i_length x = 0 ->
  Jp x (envelope_done x initial_envelope) s -> J x nil s.
Proof.
  intros x s C1 C2 L K. rewrite J_nil. unfold start.
  assert (E: envelope_from x 0 initial_envelope = envelope_done x initial_envelope)
    by (unfold envelope_from; rewrite L; reflexivity).
  destruct (i_call x); try congruence; rewrite E; exact K.
Qed.

Lemma J_start_env: forall x s, i_call x <> FEntries -> i_call x <> FResult -> 0 < i_length x ->
  ls_expect s = E_ENVELOPE -> ls_at s = 0 -> ls_word s = 0 -> sublist 0 3 (ls_state s) = initial_envelope ->
  ls_args s = i_args x -> J x nil s.
Proof.
  intros x s C1 C2 L E T W St A. rewrite J_nil. unfold start.
  assert (G: envelope_from x 0 initial_envelope = Go (ExpectEnvelope 0 initial_envelope nil))
    by (unfold envelope_from; destruct (Z.eqb_spec 0 (i_length x)); [ lia | reflexivity ]).
  assert (K: Jp x (Go (ExpectEnvelope 0 initial_envelope nil)) s)
    by (unfold Jp, go_inv; rewrite W, sublist_nil; split_and; auto; lia).
  destruct (i_call x); try congruence; rewrite G; exact K.
Qed.

(* The record as main leaves it before the function's first transition. *)
Definition s_init (al: list Z) (ex: Z) : lst := mk_lst al ex 0 0 0 (Zrepeat 0 12) (Zrepeat 0 16) 0.

Lemma lst_ok_init: forall al ex, Zlength al = 10 -> Forall u64_ok al -> 0 <= ex <= 3 -> lst_ok (s_init al ex).
Proof.
  intros al ex L F E. unfold lst_ok, s_init; lst_cbn.
  split_and; auto; try (unfold u32_ok, u64_ok; rep_lia); repeat constructor; unfold u64_ok; rep_lia.
Qed.

Lemma init_envelope: sublist 0 3 (Zrepeat 0 12) = initial_envelope.
Proof. reflexivity. Qed.
